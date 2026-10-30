module
import SQLite
public import SQLite.LowLevel
import Scripts.OeisIngest.Json
import Scripts.OeisIngest.Parse
public import Scripts.OeisTemplate.Source

/-!
The template interface and its single writer.

A template is a *pure* function `SeqSource → Verdict`. It gets no database handle, so the only
way a template can record a formalization is to return a `Candidate`, and `publish` refuses every
candidate whose `originalText` is not literally part of the stored section it claims to
formalize. That rule is the whole contract: a template that cannot recreate the original comment,
formula or program text writes nothing.

### Lean content of a candidate

All Lean text is name-free so a generator can re-render it under any names:

* `«self»` stands for the declaration being defined (`formula`), `«main»` for the sequence's main
  definition (`Axxxxxx`);
* `leanType` is the type of `«self»`, `leanCode` its body, `auxCode` declarations placed before it;
* `eqStatement` / `eqProof` are the statement and tactic proof of `formula_eq` (`«self»` ≙ `«main»`);
* `imports` are module names, parameters of the family are inlined as literals.
-/

namespace Oeis.Template

open SQLite

public section

inductive LeanKind where
  | prop | computable | nonComputable | thm
  deriving DecidableEq, Repr

def LeanKind.toDb : LeanKind → String
  | .prop => "prop"
  | .computable => "computable"
  | .nonComputable => "noncomputable"
  | .thm => "theorem"

/-- One formalization proposed by a template. -/
structure Candidate where
  /-- Section: `maindef`, `formula`, `comment`, or a program language (`pari`, `mathematica`...). -/
  language : String
  /-- Which block of that language (program sections only). -/
  blockIndex : Nat := 0
  /-- Verbatim text being formalized; must occur in the section text. -/
  originalText : String
  leanKind : LeanKind := .computable
  /-- `Nat`, `PNat`, ... — the argument shape of the main definition this refers to. -/
  argKind : String := ""
  leanType : String := ""
  leanCode : String := ""
  imports : Array String := #[]
  auxCode : String := ""
  eqStatement : String := ""
  eqProof : String := ""
  /-- Number of leading terms (from the offset) the template checked against `sequence.data`. -/
  verifiedUpto : Nat := 0
  /-- Family parameters as a JSON object, e.g. `{"g":5,"r":3}`. -/
  params : String := "{}"
  notes : String := ""

/-- What a template says about one sequence. -/
inductive Verdict where
  /-- Not a member of the family, or nothing to say. Existing items are left alone. -/
  | skip (msg : String)
  /-- A member, but something is inconsistent (e.g. values disagree). Items left alone. -/
  | fail (msg : String)
  /-- Everything the template can formalize; replaces its earlier items for the sequence. -/
  | items (cs : Array Candidate)

/-- A sequence family. -/
structure Template where
  name : String
  descr : String
  /-- SQL condition over `sequence` picking the candidates for `--all` / `--bucket`. -/
  selectWhere : String
  /-- Accepted private flags, written `--name=value`; the runner rejects any other. -/
  flags : Array String := #[]
  formalize : (extras : List String) → SeqSource → Verdict

/-- Value of `--name=K` among the template-private arguments. -/
def flagNat? (extras : List String) (name : String) : Option Nat :=
  extras.findSome? fun e =>
    if e.startsWith (name ++ "=") then (e.drop (name.length + 1)).toString.toNat? else none

/-! ## The original-text check -/

/-- First index at which `needle` occurs in `hay`. -/
def findSub? (hay needle : Array Char) : Option Nat := Id.run do
  if needle.isEmpty || hay.size < needle.size then return none
  for i in [0:hay.size - needle.size + 1] do
    let mut ok := true
    for j in [0:needle.size] do
      if hay[i + j]! != needle[j]! then
        ok := false
        break
    if ok then return some i
  return none

/-- Where a candidate sits: `(span start, span end, source hash)`, spans in characters. -/
def locate (src : SeqSource) (c : Candidate) : Except String (Nat × Nat × String) := do
  if c.originalText.trimAscii.isEmpty then throw "empty original text"
  let some text := src.sectionText? c.language c.blockIndex
    | throw s!"{src.name} has no '{c.language}' section (block {c.blockIndex})"
  let needle := c.originalText.toList.toArray
  match findSub? text.toList.toArray needle with
  | none =>
    throw s!"original text is not part of the '{c.language}' section of {src.name}: \
      «{(c.originalText.take 80).toString}»"
  | some start =>
    let hash := (src.sectionHash? c.language c.blockIndex).getD (formulaHash text)
    return (start, start + needle.size, hash)

/-! ## Writing -/

private def upsertSql : String :=
  "INSERT INTO formalization_item
     (oeis_name, producer, producer_params, language, block_index, source_hash, formula_hash,
      original_text, span_start, span_end, lean_kind, arg_kind, lean_type, lean_code, imports,
      aux_code, eq_statement, eq_proof, status, verified_upto, verified_ranges, notes,
      created_at, updated_at)
   VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18,
           ?19, ?20, ?21, ?22, datetime('now'), datetime('now'))
   ON CONFLICT(oeis_name, language, formula_hash, producer, lean_kind) DO UPDATE SET
     producer_params = excluded.producer_params,
     block_index = excluded.block_index,
     source_hash = excluded.source_hash,
     original_text = excluded.original_text,
     span_start = excluded.span_start,
     span_end = excluded.span_end,
     arg_kind = excluded.arg_kind,
     lean_type = excluded.lean_type,
     lean_code = excluded.lean_code,
     imports = excluded.imports,
     aux_code = excluded.aux_code,
     eq_statement = excluded.eq_statement,
     eq_proof = excluded.eq_proof,
     status = excluded.status,
     verified_upto = excluded.verified_upto,
     verified_ranges = excluded.verified_ranges,
     notes = excluded.notes,
     updated_at = datetime('now');"

private def verifiedRanges (offset : Int) (n : Nat) : String :=
  if n == 0 then "[]"
  else s!"[\{\"from\":{offset},\"to\":{offset + n - 1},\"result\":\"pass\"}]"

private def writeItem (db : SQLite) (src : SeqSource) (producer : String) (c : Candidate)
    (start stop : Nat) (sourceHash hash : String) : IO Unit := do
  let s ← db.prepare upsertSql
  s.bindText 1 src.name
  s.bindText 2 producer
  s.bindText 3 c.params
  s.bindText 4 c.language
  s.bindInt64 5 (Int64.ofNat c.blockIndex)
  s.bindText 6 sourceHash
  s.bindText 7 hash
  s.bindText 8 c.originalText
  s.bindInt64 9 (Int64.ofNat start)
  s.bindInt64 10 (Int64.ofNat stop)
  s.bindText 11 c.leanKind.toDb
  s.bindText 12 c.argKind
  s.bindText 13 c.leanType
  s.bindText 14 c.leanCode
  s.bindText 15 (Json.strArray c.imports)
  s.bindText 16 c.auxCode
  s.bindText 17 c.eqStatement
  s.bindText 18 c.eqProof
  s.bindText 19 (if c.verifiedUpto > 0 then "STATUS_VERIFIED" else "STATUS_UNKNOWN")
  s.bindInt64 20 (Int64.ofNat c.verifiedUpto)
  s.bindText 21 (verifiedRanges src.offset c.verifiedUpto)
  s.bindText 22 c.notes
  s.exec

/-- Drops this producer's items of the sequence that were not submitted again. -/
private def dropStale (db : SQLite) (name producer : String) (keep : Array String) : IO Unit := do
  let marks := String.intercalate ","
    ((List.range keep.size).map fun i => s!"?{i + 3}")
  let s ← db.prepare
    ("DELETE FROM formalization_item WHERE oeis_name = ?1 AND producer = ?2
        AND (language || char(31) || formula_hash || char(31) || lean_kind) NOT IN (" ++ marks ++ ")")
  s.bindText 1 name
  s.bindText 2 producer
  for i in [0:keep.size] do
    s.bindText (Int32.ofNat (i + 3)) keep[i]!
  s.exec

/-- Points `sequence.main_item_id` at this producer's `maindef` item, unless another producer
already owns the slot. -/
private def claimMain (db : SQLite) (name producer hash : String) : IO Unit := do
  let s ← db.prepare
    "UPDATE sequence SET main_item_id =
       (SELECT id FROM formalization_item
         WHERE oeis_name = ?1 AND language = 'maindef' AND formula_hash = ?3 AND producer = ?2
           AND lean_kind = 'computable')
     WHERE name = ?1 AND (main_item_id IS NULL
       OR NOT EXISTS (SELECT 1 FROM formalization_item WHERE id = sequence.main_item_id)
       OR main_item_id IN (SELECT id FROM formalization_item WHERE producer = ?2))"
  s.bindText 1 name
  s.bindText 2 producer
  s.bindText 3 hash
  s.exec

structure Report where
  accepted : Array (Candidate × Nat × Nat)
  rejected : Array String

/-- The only way into `formalization_item` for templates. Rejects candidates whose original text
is not in the stored section; with `dryRun` nothing is written. -/
def publish (db : SQLite) (src : SeqSource) (producer : String) (dryRun : Bool)
    (cs : Array Candidate) : IO Report := do
  let mut accepted := #[]
  let mut rejected := #[]
  let mut keep := #[]
  let mut mainHash : Option String := none
  for c in cs do
    match locate src c with
    | .error why => rejected := rejected.push why
    | .ok (start, stop, sourceHash) =>
      let hash := formulaHash c.originalText
      accepted := accepted.push (c, start, stop)
      keep := keep.push (c.language ++ "\x1f" ++ hash ++ "\x1f" ++ c.leanKind.toDb)
      if c.language == Section.maindef && c.leanKind == .computable then mainHash := some hash
      unless dryRun do
        writeItem db src producer c start stop sourceHash hash
  unless dryRun do
    dropStale db src.name producer keep
    if let some h := mainHash then claimMain db src.name producer h
  return { accepted, rejected }

/-- Human-readable form of a candidate, printed by `--dry-run`. -/
def Candidate.render (c : Candidate) (start stop : Nat) : String :=
  let indent (s : String) := "    " ++ s.replace "\n" "\n    "
  let opt (label body : String) := if body.isEmpty then "" else s!"\n  {label}:\n{indent body}"
  s!"[{c.language}#{c.blockIndex} {start}:{stop}] {c.leanKind.toDb}, verified {c.verifiedUpto}\n" ++
  s!"  original:\n{indent c.originalText}" ++
  opt "type" c.leanType ++ opt "code" c.leanCode ++ opt "aux" c.auxCode ++
  opt "eq statement" c.eqStatement ++ opt "eq proof" c.eqProof ++
  (if c.imports.isEmpty then "" else s!"\n  imports: {", ".intercalate c.imports.toList}")

end
end Oeis.Template
