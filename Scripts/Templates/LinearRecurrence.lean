module
public import Scripts.Templates.LinearRecurrence.Scripting
public meta import Scripts.Templates.LinearRecurrence.Scripting

/-!
# Template `linearRecurrence` (a `scan` template)

Finds homogeneous linear recurrences with constant coefficients,
`a(n) = c₁·a(n-1) + … + c_k·a(n-k)`, in every section of every sequence, and formalizes each as
Mathlib's `LinearRecurrence`:

```lean
def linearrec : LinearRecurrence Nat := ⟨2, ![1, 1]⟩
def init : Fin 2 → Nat := ![2, 1]
def formula : Nat → Nat := fun n => linearrec.mkSol init n
theorem formula_eq (n : Nat) : formula n = A000032.fn n := sorry
```

Recognizers: statements in the title, `%F` and `%C` (`Statement`), Wolfram (`Mathematica`), PARI,
Maple and Magma programs (`Programs`), and Python/Sage and Haskell programs (`Scripting`). Texts that state a constant or `n`-dependent term, a
product of terms, a division or anything else outside the shape are not formalized.

* The initial values are the first `k` published terms, whatever the text states: stated values
  and a program's own output are only checked against the data (`Rec.verify`).
* A recurrence found in several places is one item with all those texts as sources: two texts
  are the same formalization when their coefficient lists are equal.
* A recurrence in the title is the main definition (`maindef`); every other item states its
  equality with `«main».fn` and leaves it `sorry`, since the sequence is abstract.
* The value type is `Nat` unless the sequence has negative terms or the recurrence has negative
  coefficients or initial values; a `Nat`-valued sequence over `Int` is wrapped in `Int.toNat`.

Private flags: `--check-cap=K` (compare at most `K` terms, default 2000) and `--min-extra=N`
(terms required beyond the first `k`, default 3).
-/

namespace Oeis.Template.LinearRecurrence
public section

open Recognize

private abbrev mathlibImport : String := "Mathlib.Algebra.LinearRecurrence"

/-! ## What is found in one sequence -/

/-- A recognized text with the section it was found in. -/
structure Found where
  raw : Raw
  language : String
  blockIndex : Nat
  text : String

/-- Scans one program block of a language we know. -/
def programScan (language : String) (offset : Int) (count : Nat) (text : String) :
    Array Raw × Array String :=
  match language with
  | "mathematica" => scanMathematica text
  | "pari" => scanPari offset count text
  | "maple" => scanMaple offset count text
  | "magma" => scanMagma offset count text
  | "python" | "sagemath" => scanPython offset count text
  | "haskell" => scanHaskell offset count text
  | _ => (#[], #[])

/-- Everything recognized in the title, formulas, comments and programs of the sequence. -/
def findAll (src : SeqSource) (count : Nat) : Array Found × Array String := Id.run do
  let names := #["a", src.name]
  let mut out : Array Found := #[]
  let mut why : Array String := #[]
  let add (language : String) (blockIndex : Nat) (text : String)
      (r : Array Raw × Array String) (out : Array Found) : Array Found :=
    out ++ r.1.map fun raw =>
      { raw, language, blockIndex, text := slice (chars text) raw.start raw.stop }
  for (language, text) in [(Section.maindef, src.title), (Section.formula, src.formulaText),
      (Section.comment, src.commentText)] do
    let r := scanText (plainSyn names) #["="] "statement" text
    out := add language 0 text r out
    why := why ++ r.2
  -- the title is about the sequence itself, so it may call it anything (`F(n) = F(n-1) + …`);
  -- formulas and comments also talk about other sequences and keep to `a` and the A-number
  for name in callNames src.title do
    unless names.contains name do
      let r := scanText (plainSyn #[name]) #["="] "statement" src.title
      out := add Section.maindef 0 src.title r out
      why := why ++ r.2
  for p in src.programs do
    let r := programScan p.language src.offset count p.text
    out := add p.language p.blockIndex p.text r out
    why := why ++ r.2
  return (out, why)

/-! ## The Lean text -/

private def lit (v : Int) : String := toString v

private def list (xs : Array Int) : String := ", ".intercalate (xs.toList.map lit)

/-- Everything the Lean text of a recurrence depends on. -/
structure Shape where
  recur : Rec
  init : Array Int
  offset : Nat
  retInt : Bool

def Shape.dtype (s : Shape) : String :=
  if s.retInt || s.recur.coeffs.any (· < 0) || s.init.any (· < 0) then "Int" else "Nat"

def Shape.ret (s : Shape) : String := if s.retInt then "Int" else "Nat"

/-- The value at `index` (a term of Lean code over `Nat`). -/
def Shape.value (s : Shape) (index : String) : String :=
  let v := s!"linearrec.mkSol init {index}"
  if s.dtype == "Int" && !s.retInt then s!"({v}).toNat" else v

def Shape.auxCode (s : Shape) : String :=
  let k := s.recur.order
  s!"def linearrec : LinearRecurrence {s.dtype} :=\n  ⟨{k}, ![{list s.recur.coeffs.reverse}]⟩\n\n\
     def init : Fin {k} → {s.dtype} :=\n  ![{list s.init}]"

/-- The index into the recurrence: the position of `n` among the terms. -/
private def Shape.position (s : Shape) (n : String) : String :=
  if s.offset == 0 then n else s!"({n} - {s.offset})"

/-- A recurrence the title states is the main definition itself, of the main definition's own
argument type; any other is an alternative with the signature of `fn`. -/
def Shape.candidate (s : Shape) (sources : Array Source) (isMain : Bool) (verified : Nat)
    (flavors : String) : Candidate :=
  let params := s!"\{\"order\":{s.recur.order},\"coeffs\":[{list s.recur.coeffs}],\
    \"dtype\":\"{s.dtype}\"}"
  let common : Candidate :=
    { sources, imports := #[mathlibImport], auxCode := s.auxCode, verifiedUpto := verified,
      params, notes := flavors }
  let byNat := s.value (s.position "n")
  let byVal := s.value (s.position "n.val")
  if isMain then
    if s.offset == 0 then
      { common with
        argKind := "Nat", leanType := s!"Nat → {s.ret}",
        leanCode := s!"fun n => {byNat}" }
    else if s.offset == 1 then
      { common with
        argKind := "PNat", leanType := s!"PNat → {s.ret}",
        leanCode := s!"fun n => {byVal}" }
    else
      { common with
        argKind := "NatSub", leanType := s!"\{n : Nat // {s.offset} ≤ n} → {s.ret}",
        leanCode := s!"fun n => {byVal}" }
  else
    { common with
      argKind := "Nat", leanType := s!"Nat → {s.ret}",
      leanCode := s!"fun n => {byNat}",
      eqStatement :=
        if s.offset == 0 then "∀ n : Nat, «self» n = «main».fn n"
        else s!"∀ n : Nat, {s.offset} ≤ n → «self» n = «main».fn n",
      eqProof := "sorry" }

/-! ## One item per distinct recurrence -/

structure Group where
  recur : Rec
  sources : Array Source
  /-- Where each source ends, to find sources inside other sources. -/
  ends : Array Nat
  flavors : Array String
  verified : Nat

private def Group.isMain (g : Group) : Bool := g.sources.any (·.language == Section.maindef)

private def Group.addFound (g : Group) (f : Found) : Group :=
  let src : Source := { language := f.language, blockIndex := f.blockIndex,
                        originalText := f.text, start? := some f.raw.start }
  { g with sources := g.sources.push src, ends := g.ends.push f.raw.stop,
           flavors := if g.flavors.contains f.raw.flavor then g.flavors
                      else g.flavors.push f.raw.flavor }

/-- Drops a source lying inside another source of the same section. -/
private def Group.prune (g : Group) : Group := Id.run do
  let mut keep : Array Nat := #[]
  for i in [0:g.sources.size] do
    let s := g.sources[i]!
    let st := s.start?.getD 0
    let inside := (List.range g.sources.size).any fun j =>
      j != i && (let t := g.sources[j]!
        let tt := t.start?.getD 0
        t.language == s.language && t.blockIndex == s.blockIndex &&
        tt ≤ st && g.ends[i]! ≤ g.ends[j]! && (tt < st || g.ends[i]! < g.ends[j]! || j < i))
    unless inside do keep := keep.push i
  return { g with sources := keep.map (g.sources[·]!), ends := keep.map (g.ends[·]!) }

private def termsInt (terms : Array String) : Option (Array Int) :=
  terms.mapM String.toInt?

/-- Verifies what was found and groups it by recurrence; also the reasons for what failed. -/
private def groupFound (src : SeqSource) (data : Array Int) (cap minExtra : Nat)
    (found : Array Found) (refused : Array String) : Array Group × Array String := Id.run do
  let mut groups : Array Group := #[]
  let mut failures := refused
  for f in found do
    match f.raw.recur.verify f.raw.claim src.offset data cap minExtra with
    | .error why => failures := failures.push why
    | .ok n =>
      match groups.findIdx? (·.recur == f.raw.recur) with
      | some i => groups := groups.modify i (·.addFound f)
      | none =>
        groups := groups.push (Group.addFound
          { recur := f.raw.recur, sources := #[], ends := #[], flavors := #[], verified := n } f)
  return (groups, failures)

def formalize (extras : List String) (src : SeqSource) : Verdict :=
  if src.offset < 0 then .skip s!"negative offset {src.offset}"
  else match termsInt src.terms with
    | none => .skip "a published term is not an integer"
    | some data =>
      let cap := (flagNat? extras "--check-cap").getD 2000
      let minExtra := (flagNat? extras "--min-extra").getD 3
      let (found, refused) := findAll src (min data.size cap)
      let (groups, failures) := groupFound src data cap minExtra found refused
      if groups.isEmpty then
        .skip (if failures.isEmpty then "no recurrence found"
               else s!"no recurrence verified: {"; ".intercalate (failures.toList.eraseDups.take 3)}")
      else
        let retInt := data.any (· < 0)
        let pruned := groups.map Group.prune
        -- the title's recurrence first: it is the main definition
        let ordered := pruned.filter Group.isMain ++ pruned.filter (!·.isMain)
        .items <| ordered.mapIdx fun i g =>
          let shape : Shape := { recur := g.recur, init := data.extract 0 g.recur.order,
                                 offset := src.offset.toNat, retInt }
          shape.candidate g.sources (i == 0 && g.isMain) g.verified
            (", ".intercalate g.flavors.toList)

/-- A cheap prefilter: some section mentions a lagged term, or a program a known idiom. -/
private def prefilter : String :=
  "data_count > 0 AND \"offset\" >= 0 AND keywords NOT LIKE '%\"tabl\"%' \
   AND keywords NOT LIKE '%\"tabf\"%' AND (\
     title LIKE '%(n-%' OR title LIKE '%(n+%' \
     OR formula_lines LIKE '%(n-%' OR formula_lines LIKE '%(n+%' \
     OR comment_lines LIKE '%(n-%' OR comment_lines LIKE '%(n+%' \
     OR EXISTS (SELECT 1 FROM program p WHERE p.oeis_name = sequence.name AND (\
       p.text LIKE '%LinearRecurrence%' OR p.text LIKE '%RecurrenceTable%' \
       OR p.text LIKE '%[n_%' OR p.text LIKE '%(n-%' OR p.text LIKE '%(n -%' \
       OR p.text LIKE '%Self(%' OR p.text LIKE '%[-1]%' OR p.text LIKE '%zipWith%')))"

def template : Template where
  name := "linearRecurrence"
  descr := "homogeneous linear recurrences with constant coefficients, in any section"
  kind := .scan
  selectWhere := prefilter
  flags := #["--check-cap", "--min-extra"]
  formalize := formalize

end
end Oeis.Template.LinearRecurrence
