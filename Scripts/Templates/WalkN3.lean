module
public import Scripts.OeisTemplate.Recognize
public meta import Scripts.OeisTemplate.Recognize

/-!
# Template `walkN3`

> Number of walks within `N^3` (the first octant of `Z^3`) starting at `(0,0,0)` and
> consisting of `n` steps taken from `{...}`

~3250 sequences (Bostan–Kauers 2008). The shared math is `OEISLib.Common.Walk3`; this module
does not import it, it verifies the data with its own transcription of the Wolfram recursion.
Every member carries a `%t` program of the shape

```wolfram
aux[i_Integer, j_Integer, k_Integer, n_Integer] := Which[
  Min[i, j, k, n] < 0 || Max[i, j, k] > n, 0,
  n == 0, KroneckerDelta[i, j, k, n],
  True, aux[i, j, k, n] = aux[<off1> + i, <off2> + j, <off3> + k, -1 + n] + ...];
Table[Sum[aux[i, j, k, n], {i, 0, n}, {j, 0, n}, {k, 0, n}], {n, 0, 10}]
```

* `maindef`      the title, as `fun n => count [steps] n`
* `mathematica`  that program (up to the closing `}]`), as `countDp [steps]`

The steps come from the title; the program's recursion offsets must encode the same set.
Private flags: `--table-max=K` (verify `K+1` values instead of the `Table` range) and
`--check-cap=K` (hard cap on the values verified, default 12).
-/

namespace Oeis.Template.WalkN3
public section

open Recognize

private abbrev lib : String := "OEISLib.Common.Walk3"

abbrev Step := Int × Int × Int

/-! ## 1. Title -/

private def titlePrefix : String :=
  "Number of walks within N^3 (the first octant of Z^3) starting at (0,0,0) and \
   consisting of n steps taken from {"

/-- The step vectors listed in the title. -/
def parseTitleSteps (title : String) : Option (Array Step) := do
  guard (title.startsWith titlePrefix)
  let rest := (title.drop titlePrefix.length).toString
  guard (rest.endsWith "}.")
  let mut steps := #[]
  for p in (rest.dropEnd 2).toString.splitOn "), (" do
    let mut p := p.trimAscii.toString
    if p.startsWith "(" then p := (p.drop 1).toString
    if p.endsWith ")" then p := (p.dropEnd 1).toString
    let parts := p.splitOn "," |>.map (·.trimAscii.toString)
    guard (parts.length == 3)
    steps := steps.push ((← parts[0]!.toInt?), (← parts[1]!.toInt?), (← parts[2]!.toInt?))
  return steps

/-! ## 2. Recognition

A whitespace-tolerant cursor over the Mathematica block; accepts `aux[i_Integer, …]` and
`aux[i_, …]`, any spacing, any `Table` range. -/

private def atStr (a : Array Char) (i : Nat) (lit : String) : Bool :=
  a.extract i (i + lit.length) == lit.toList.toArray

/-- A binder variable: `v`, `v_` or `v_Integer`. -/
private def eatVar (a : Array Char) (i0 : Nat) : Option (Char × Nat) :=
  let i := skipWs a i0
  match a[i]? with
  | some c =>
    if c == 'i' || c == 'j' || c == 'k' || c == 'n' then
      if atStr a (i + 1) "_" then
        if atStr a (i + 2) "Integer" then some (c, i + 9) else some (c, i + 2)
      else some (c, i + 1)
    else none
  | none => none

/-- One coordinate: `<int>+v` or bare `v`; returns the coefficient and the variable. -/
private def eatComp (a : Array Char) (i0 : Nat) : Option (Int × Char × Nat) :=
  let signed : Option (Int × Nat) := do
    let i := skipWs a i0
    match a[i]? with
    | some '-' =>
      let (v, j) ← digitsFrom a (i + 1)
      return (-(v : Int), j)
    | some c =>
      if c.isDigit then
        let (v, j) ← digitsFrom a i
        return ((v : Int), j)
      else none
    | none => none
  match signed with
  | some (c, j) => do
    let j ← eatLit a j "+"
    let (v, k) ← eatVar a j
    return (c, v, k)
  | none => do
    let (v, k) ← eatVar a i0
    return (0, v, k)

/-- `aux[c1+i, c2+j, c3+k, -1+n]`; returns the negated offsets, i.e. the forward step. -/
private def eatSummand (a : Array Char) (i0 : Nat) : Option (Step × Nat) := do
  let i ← eatLit a i0 "aux["
  let (c1, v1, i) ← eatComp a i
  guard (v1 == 'i')
  let i ← eatLit a i ","
  let (c2, v2, i) ← eatComp a i
  guard (v2 == 'j')
  let i ← eatLit a i ","
  let (c3, v3, i) ← eatComp a i
  guard (v3 == 'k')
  let i ← eatLit a i ", -1 + n]"
  return ((-c1, -c2, -c3), i)

private partial def eatSummands (a : Array Char) (i : Nat) (acc : Array Step) :
    Option (Array Step × Nat) := do
  let (o, j) ← eatSummand a i
  let acc := acc.push o
  let j2 := skipWs a j
  if a[j2]? == some '+' then eatSummands a (j2 + 1) acc else some (acc, j)

/-- First-occurrence dedup, keeping order. -/
partial def dedupSteps (xs : List Step) (seen : Array Step := #[]) : Array Step :=
  match xs with
  | [] => seen
  | x :: rest => dedupSteps rest (if seen.contains x then seen else seen.push x)

structure Recog where
  /-- End of the recognized program inside the block text. -/
  endPos : Nat
  steps : Array Step
  tableMax : Nat

/-- Recognizes the program at the start of `text`; the error names the piece that failed. -/
def recognize (text : String) : Except String Recog := do
  let a := chars text
  let need (o : Option Nat) (what : String) : Except String Nat :=
    match o with
    | some v => pure v
    | none => throw s!"did not find '{what}'"
  let var (i : Nat) : Except String Nat :=
    match eatVar a i with
    | some (_, j) => pure j
    | none => throw "did not find 'a binder variable (i/j/k/n)'"
  let mut i ← need (eatLit a 0 "aux[") "aux["
  for _ in [0:3] do
    i ← var i
    i ← need (eatLit a i ",") ","
  i ← var i
  i ← need (eatLit a i "] := Which[") "] := Which["
  i ← need (eatLit a i "Min[i, j, k, n] < 0 || Max[i, j, k] > n, 0,")
    "Min[i, j, k, n] < 0 || Max[i, j, k] > n, 0,"
  i ← need (eatLit a i "n == 0, KroneckerDelta[i, j, k, n], True,")
    "n == 0, KroneckerDelta[i, j, k, n], True,"
  i ← need (eatLit a i "aux[i, j, k, n] = ") "aux[i, j, k, n] = "
  let some (offsets, j) := eatSummands a i #[]
    | throw "did not find the step summands aux[c*i + ...]"
  i := j
  i ← need (eatLit a i "]; Table[ Sum[aux[i, j, k, n], {i, 0, n}, {j, 0, n}, {k, 0, n}]")
    "]; Table[ Sum[...]"
  i ← need (eatLit a i ", {n, 0,") ", {n, 0,"
  let some (tableMax, j) := digitsFrom a i
    | throw "did not find the Table range digits"
  i ← need (eatLit a j "}]") "}]"
  for o in offsets do
    unless o.1.natAbs ≤ 1 && o.2.1.natAbs ≤ 1 && o.2.2.natAbs ≤ 1 do
      throw s!"step offset {o} is outside the cube -1..1"
  return { endPos := i, steps := dedupSteps offsets.toList, tableMax }

/-! ## 3. Verification: the Wolfram dynamic program, evaluated -/

private abbrev Cube := Array (Array (Array Nat))

/-- Level 0: `KroneckerDelta[i,j,k,n]`. -/
private def baseLayer (sz : Nat) : Cube :=
  (Array.range sz).map fun i =>
    (Array.range sz).map fun j =>
      (Array.range sz).map fun k => if i = 0 ∧ j = 0 ∧ k = 0 then 1 else 0

/-- Level `m` from level `m-1`, with the exact pruning of the Wolfram code. -/
private def stepLayer (steps : Array Step) (m : Nat) (old : Cube) : Cube :=
  (Array.range old.size).map fun i =>
    (Array.range old.size).map fun j =>
      (Array.range old.size).map fun k =>
        if i ≤ m ∧ j ≤ m ∧ k ≤ m then
          steps.foldl (init := 0) fun v s =>
            let pi := (i : Int) - s.1
            let pj := (j : Int) - s.2.1
            let pk := (k : Int) - s.2.2
            if 0 ≤ pi ∧ pi ≤ m - 1 ∧ 0 ≤ pj ∧ pj ≤ m - 1 ∧ 0 ≤ pk ∧ pk ≤ m - 1 then
              v + old[pi.toNat]![pj.toNat]![pk.toNat]!
            else v
        else 0

private def boxSum (layer : Cube) (m : Nat) : Nat := Id.run do
  let mut t := 0
  for i in [0:m + 1] do
    for j in [0:m + 1] do
      for k in [0:m + 1] do
        t := t + layer[i]![j]![k]!
  return t

/-- `Sum[aux[i,j,k,n], …]` for `n = 0 .. last`. -/
def dpValues (steps : Array Step) (last : Nat) : Array Nat := Id.run do
  let mut layer := baseLayer (last + 1)
  let mut out := #[]
  for m in [0:last + 1] do
    if m > 0 then layer := stepLayer steps m layer
    out := out.push (boxSum layer m)
  return out

/-! ## 4. Candidates -/

private def stepsLit (steps : Array Step) : String :=
  "[" ++ ", ".intercalate (steps.toList.map fun s => s!"({s.1}, {s.2.1}, {s.2.2})") ++ "]"

private def paramsJson (steps : Array Step) (extra : String := "") : String :=
  s!"\{\"steps\":\"{stepsLit steps}\"{extra}}"

def mainDefinition (steps : Array Step) (title : String) (verified : Nat) : Candidate where
  sources := #[{ language := Section.maindef, originalText := title }]
  argKind := "Nat"
  leanType := "Nat → Nat"
  leanCode := s!"fun n => {lib}.count {stepsLit steps} n"
  imports := #[lib]
  verifiedUpto := verified
  params := paramsJson steps

/-- The dynamic program, equal to the high-level walk count. -/
def program (steps : Array Step) (h : Hit) (verified : Nat) : Candidate :=
  let lit := s!"({stepsLit steps} : List {lib}.Pnt)"
  { sources := #[h.source]
    argKind := "Nat"
    leanType := "Nat → Nat"
    leanCode := s!"{lib}.countDp {lit}"
    imports := #[lib]
    eqStatement := "∀ n : Nat, «self» n = «main» n"
    eqProof := "intro n\n" ++
      s!"have hcube : ∀ s ∈ {lit}, s ∈ {lib}.unitCube := by decide\n" ++
      s!"exact {lib}.countDp_eq_count {lit} hcube n"
    verifiedUpto := verified
    params := paramsJson steps ",\"flavor\":\"wolfram-dp\""
    notes := "wolfram-dp" }

/-! ## 5. The template -/

/-- Same set of steps? Both arrays are already deduplicated. -/
private def sameStepSet (a b : Array Step) : Bool :=
  a.size == b.size && a.all b.contains

def formalize (extras : List String) (src : SeqSource) : Verdict :=
  match parseTitleSteps src.title with
  | none => .skip "title does not match the walkN3 template"
  | some steps =>
    if src.offset != 0 then .skip s!"unsupported offset {src.offset} (template emits a Nat API)"
    else match termsNat src.terms with
      | .error e => .fail e
      | .ok terms =>
        if terms.isEmpty then .fail "sequence has no known terms"
        else
          -- the programs of this sequence that follow the family's pattern
          let programs := (src.blocksOf "mathematica").filterMap fun b =>
            match recognize b.text with
            | .ok r => some (b, r)
            | .error _ => none
          if let some (_, r) := programs.find? fun (_, r) => !sameStepSet r.steps steps then
            .fail s!"step set mismatch: title says {stepsLit steps} but the wolfram recursion \
              encodes {stepsLit r.steps}"
          else
            let cap := (flagNat? extras "--check-cap").getD 12
            let tableMax := (flagNat? extras "--table-max").orElse fun _ =>
              (programs[0]?).map (·.2.tableMax)
            let last := min (tableMax.getD (terms.size - 1)) (min (terms.size - 1) cap)
            if last < 2 then .fail "not enough known terms to verify"
            else match checkPrefix (dpValues steps last) (terms.extract 0 (last + 1)) with
              | .error e => .fail s!"verification failed: {e}"
              | .ok verified =>
                let snippets := programs.map fun (b, r) =>
                  program steps
                    { language := "mathematica", blockIndex := b.blockIndex,
                      flavor := "wolfram-dp", text := (b.text.take r.endPos).toString } verified
                .items (#[mainDefinition steps src.title verified] ++ snippets)

def template : Template where
  name := "walkN3"
  descr := "walks within N^3 (first octant of Z^3) from a fixed step set (Bostan-Kauers)"
  selectWhere := "title LIKE 'Number of walks within N^3%'"
  flags := #["--table-max", "--check-cap"]
  formalize := formalize

end
end Oeis.Template.WalkN3
