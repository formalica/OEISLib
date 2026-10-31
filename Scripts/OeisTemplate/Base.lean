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
candidate one of whose `sources` is not literally part of the stored section it claims to
formalize. That rule is the whole contract: a template that cannot recreate the original comment,
formula or program text writes nothing.

A candidate has one or more `sources`: every original text (title, `%F` line, comment, program
snippet) that the one formalization stands for. The same recurrence stated in the title, in a
formula and in a program is one candidate with three sources.

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
  deriving DecidableEq, Repr, Inhabited

def LeanKind.toDb : LeanKind → String
  | .prop => "prop"
  | .computable => "computable"
  | .nonComputable => "noncomputable"
  | .thm => "theorem"

/-- One piece of original text a formalization stands for. -/
structure Source where
  /-- Section: `maindef`, `formula`, `comment`, or a program language (`pari`, `mathematica`...). -/
  language : String
  /-- Which block of that language (program sections only). -/
  blockIndex : Nat := 0
  /-- Verbatim text; must occur in the section text. -/
  originalText : String
  /-- Character offset of the text inside the section text, when the template knows it; without
  it the first occurrence is taken. -/
  start? : Option Nat := none
  deriving Inhabited

/-- One formalization proposed by a template. -/
structure Candidate where
  /-- Every original text formalized by this candidate; at least one. -/
  sources : Array Source
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
  deriving Inhabited

/-- What a template says about one sequence. -/
inductive Verdict where
  /-- Not a member of the family, or nothing to say. Existing items are left alone. -/
  | skip (msg : String)
  /-- A member, but something is inconsistent (e.g. values disagree). Items left alone. -/
  | fail (msg : String)
  /-- Everything the template can formalize; replaces its earlier items for the sequence. -/
  | items (cs : Array Candidate)

/-- How a template finds its sequences. -/
inductive TemplateKind where
  /-- A family picked by title: the template rebuilds the exact original text from the family's
  parameters and writes only when that text is really there. -/
  | family
  /-- Searches every section of any sequence for texts of one shape (a recurrence, a program
  idiom); `selectWhere` is only a cheap SQL prefilter and most selected sequences yield nothing. -/
  | scan
  deriving DecidableEq

/-- A sequence family or a search pattern. -/
structure Template where
  name : String
  descr : String
  kind : TemplateKind := .family
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

/-- A source placed in its section: span in characters and the hash of the section text. -/
structure Placed where
  src : Source
  start : Nat
  stop : Nat
  sourceHash : String
  deriving Inhabited

/-- Where a source sits. -/
def locate (src : SeqSource) (s : Source) : Except String Placed := do
  if s.originalText.trimAscii.isEmpty then throw "empty original text"
  let some text := src.sectionText? s.language s.blockIndex
    | throw s!"{src.name} has no '{s.language}' section (block {s.blockIndex})"
  let hay := text.toList.toArray
  let needle := s.originalText.toList.toArray
  let found :=
    match s.start? with
    | some i => if hay.extract i (i + needle.size) == needle then some i else none
    | none => findSub? hay needle
  match found with
  | none =>
    throw s!"original text is not part of the '{s.language}' section of {src.name}: \
      «{(s.originalText.take 80).toString}»"
  | some start =>
    let hash := (src.sectionHash? s.language s.blockIndex).getD (formulaHash text)
    return { src := s, start, stop := start + needle.size, sourceHash := hash }

/-- Canonical order of the sources of one item: title, formulas, comments, then programs. -/
private def sectionRank (language : String) : Nat :=
  if language == Section.maindef then 0
  else if language == Section.formula then 1
  else if language == Section.comment then 2
  else 3

private def placedBefore (a b : Placed) : Bool :=
  let ra := sectionRank a.src.language
  let rb := sectionRank b.src.language
  if ra != rb then ra < rb
  else if a.src.language != b.src.language then a.src.language < b.src.language
  else if a.src.blockIndex != b.src.blockIndex then a.src.blockIndex < b.src.blockIndex
  else a.start < b.start

/-- Sorts into canonical order and drops a source that sits at the same place as an earlier one. -/
def canonical (ps : Array Placed) : Array Placed :=
  (ps.qsort placedBefore).foldl (init := #[]) fun acc p =>
    if acc.any fun q => q.src.language == p.src.language &&
        q.src.blockIndex == p.src.blockIndex && q.start == p.start && q.stop == p.stop
    then acc else acc.push p

/-- The identity of an item: the hash of its original texts joined with a newline. -/
def itemHash (ps : Array Placed) : String :=
  formulaHash ("\n".intercalate (ps.map (·.src.originalText)).toList)

/-! ## Writing -/

private def upsertSql : String :=
  "INSERT INTO formalization_item
     (oeis_name, producer, producer_params, formula_hash, lean_kind, arg_kind, lean_type,
      lean_code, imports, aux_code, eq_statement, eq_proof, status, verified_upto,
      verified_ranges, notes, created_at, updated_at)
   VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16,
           datetime('now'), datetime('now'))
   ON CONFLICT(oeis_name, producer, formula_hash, lean_kind) DO UPDATE SET
     producer_params = excluded.producer_params,
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

/-- Upserts the item and replaces its source rows. -/
private def writeItem (db : SQLite) (src : SeqSource) (producer : String) (c : Candidate)
    (placed : Array Placed) (hash : String) : IO Unit := do
  let s ← db.prepare upsertSql
  s.bindText 1 src.name
  s.bindText 2 producer
  s.bindText 3 c.params
  s.bindText 4 hash
  s.bindText 5 c.leanKind.toDb
  s.bindText 6 c.argKind
  s.bindText 7 c.leanType
  s.bindText 8 c.leanCode
  s.bindText 9 (Json.strArray c.imports)
  s.bindText 10 c.auxCode
  s.bindText 11 c.eqStatement
  s.bindText 12 c.eqProof
  s.bindText 13 (if c.verifiedUpto > 0 then "STATUS_VERIFIED" else "STATUS_UNKNOWN")
  s.bindInt64 14 (Int64.ofNat c.verifiedUpto)
  s.bindText 15 (verifiedRanges src.offset c.verifiedUpto)
  s.bindText 16 c.notes
  s.exec
  let idStmt ← db.prepare
    "SELECT id FROM formalization_item
       WHERE oeis_name = ?1 AND producer = ?2 AND formula_hash = ?3 AND lean_kind = ?4"
  idStmt.bindText 1 src.name
  idStmt.bindText 2 producer
  idStmt.bindText 3 hash
  idStmt.bindText 4 c.leanKind.toDb
  unless ← idStmt.step do throw <| IO.userError s!"{src.name}: item vanished after upsert"
  let itemId ← idStmt.columnInt64 0
  let del ← db.prepare "DELETE FROM formalization_source WHERE item_id = ?1"
  del.bindInt64 1 itemId
  del.exec
  for h : i in [0:placed.size] do
    let p := placed[i]
    let ins ← db.prepare
      "INSERT INTO formalization_source
         (item_id, ord, language, block_index, source_hash, original_text, span_start, span_end)
       VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)"
    ins.bindInt64 1 itemId
    ins.bindInt64 2 (Int64.ofNat i)
    ins.bindText 3 p.src.language
    ins.bindInt64 4 (Int64.ofNat p.src.blockIndex)
    ins.bindText 5 p.sourceHash
    ins.bindText 6 p.src.originalText
    ins.bindInt64 7 (Int64.ofNat p.start)
    ins.bindInt64 8 (Int64.ofNat p.stop)
    ins.exec

/-- Drops this producer's items of the sequence that were not submitted again; their source rows
go with them (`ON DELETE CASCADE`). -/
private def dropStale (db : SQLite) (name producer : String) (keep : Array String) : IO Unit := do
  let marks := String.intercalate ","
    ((List.range keep.size).map fun i => s!"?{i + 3}")
  let s ← db.prepare
    ("DELETE FROM formalization_item WHERE oeis_name = ?1 AND producer = ?2
        AND (formula_hash || char(31) || lean_kind) NOT IN (" ++ marks ++ ")")
  s.bindText 1 name
  s.bindText 2 producer
  for i in [0:keep.size] do
    s.bindText (Int32.ofNat (i + 3)) keep[i]!
  s.exec

/-- Points `sequence.main_item_id` at this producer's computable item `hash`, unless another
producer already owns the slot. -/
private def claimMain (db : SQLite) (name producer hash : String) : IO Unit := do
  let s ← db.prepare
    "UPDATE sequence SET main_item_id =
       (SELECT id FROM formalization_item
         WHERE oeis_name = ?1 AND formula_hash = ?3 AND producer = ?2
           AND lean_kind = 'computable')
     WHERE name = ?1 AND (main_item_id IS NULL
       OR NOT EXISTS (SELECT 1 FROM formalization_item WHERE id = sequence.main_item_id)
       OR main_item_id IN (SELECT id FROM formalization_item WHERE producer = ?2))"
  s.bindText 1 name
  s.bindText 2 producer
  s.bindText 3 hash
  s.exec

/-- A candidate whose sources were all found, with their places in canonical order. -/
structure Accepted where
  cand : Candidate
  placed : Array Placed
  hash : String

structure Report where
  accepted : Array Accepted
  rejected : Array String

/-- The only way into `formalization_item` for templates. Rejects candidates one of whose original
texts is not in the stored section; with `dryRun` nothing is written. The first computable item
whose first source is the title becomes the sequence's main definition. -/
def publish (db : SQLite) (src : SeqSource) (producer : String) (dryRun : Bool)
    (cs : Array Candidate) : IO Report := do
  let mut accepted : Array Accepted := #[]
  let mut rejected := #[]
  let mut keep := #[]
  let mut mainHash : Option String := none
  for c in cs do
    match c.sources.mapM (locate src) with
    | .error why => rejected := rejected.push why
    | .ok located =>
      let placed := canonical located
      if placed.isEmpty then
        rejected := rejected.push "candidate without sources"
        continue
      let hash := itemHash placed
      accepted := accepted.push { cand := c, placed, hash }
      keep := keep.push (hash ++ "\x1f" ++ c.leanKind.toDb)
      if mainHash.isNone && c.leanKind == .computable &&
          (placed[0]?.map (·.src.language)) == some Section.maindef then
        mainHash := some hash
      unless dryRun do
        writeItem db src producer c placed hash
  unless dryRun do
    dropStale db src.name producer keep
    if let some h := mainHash then claimMain db src.name producer h
  return { accepted, rejected }

/-- Human-readable form of an accepted candidate, printed by `--dry-run`. -/
def Accepted.render (a : Accepted) : String :=
  let c := a.cand
  let indent (s : String) := "    " ++ s.replace "\n" "\n    "
  let opt (label body : String) := if body.isEmpty then "" else s!"\n  {label}:\n{indent body}"
  let places := ", ".intercalate
    (a.placed.map fun p => s!"{p.src.language}#{p.src.blockIndex} {p.start}:{p.stop}").toList
  let originals := String.join
    (a.placed.toList.map fun p => s!"\n  original ({p.src.language}):\n{indent p.src.originalText}")
  s!"[{places}] {c.leanKind.toDb}, verified {c.verifiedUpto}" ++ originals ++
  opt "type" c.leanType ++ opt "code" c.leanCode ++ opt "aux" c.auxCode ++
  opt "eq statement" c.eqStatement ++ opt "eq proof" c.eqProof ++
  (if c.imports.isEmpty then "" else s!"\n  imports: {", ".intercalate c.imports.toList}")

end
end Oeis.Template
