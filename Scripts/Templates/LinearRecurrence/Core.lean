module
public import Scripts.Templates.LinearRecurrence.Lin
public meta import Scripts.Templates.LinearRecurrence.Lin

/-!
Homogeneous linear recurrences `a(n) = c₁·a(n-1) + … + c_k·a(n-k)`, what a text can claim about
the sequence besides the recurrence, and the check of both against the published terms.

Initial values are never taken from the text: the formalization always starts from the first `k`
published terms. What the text states (`Claim`) is only cross-checked against the data, so a
text that lists wrong or shifted initial values is refused instead of silently repaired.
-/

namespace Oeis.Template.LinearRecurrence
public section

open Recognize

/-- `coeffs[i]` is `c_{i+1}`, the coefficient of `a(n-1-i)`; the last one is not zero. -/
structure Rec where
  coeffs : Array Int
  deriving BEq, Repr, Inhabited

def Rec.order (r : Rec) : Nat := r.coeffs.size

/-- What the text says about the sequence besides the recurrence. -/
inductive Claim where
  | none
  /-- `a(i) = v` stated at OEIS indices. -/
  | values (pairs : Array (Int × Int))
  /-- A program's output: running the kernel `ker` (as written, so possibly with trailing zeros)
  from `init`, placed at index `initAt`, the entries `from_ ...` are the listed terms, `count`
  of them. -/
  | listing (ker init : Array Int) (initAt from_ : Int) (count : Nat)
  deriving BEq, Repr, Inhabited

/-- A recurrence recognized in a text; positions are characters of the scanned section text. -/
structure Raw where
  recur : Rec
  claim : Claim := .none
  start : Nat
  stop : Nat
  flavor : String
  deriving Inhabited

/-! ## From an equation to a recurrence -/

/-- `total = 0` as a recurrence: the term with the largest shift must have coefficient ±1 and
every other term an earlier shift; a constant or an `n` term makes it non-homogeneous. -/
def Lin.toRec (total : Lin) : Except String Rec := do
  if total.c != 0 || total.nc != 0 then throw "has a constant or n-dependent term"
  if total.terms.isEmpty then throw "contains no term of the sequence"
  let top := total.terms.foldl (init := total.terms[0]!.1) fun m (s, _) => max m s
  let some (_, d) := total.terms.find? (·.1 == top) | throw "contains no term of the sequence"
  unless d == 1 || d == -1 do throw "the leading coefficient is not ±1"
  let lags := total.terms.filter (·.1 != top)
  let k := lags.foldl (init := 0) fun m (s, _) => max m (top - s).toNat
  -- `a(n+25239592216021) = a(n)` is a period, not a recurrence one can write down
  if k > 1000 then throw "the order is larger than 1000"
  let coeffs := (Array.range k).map fun i =>
    match lags.find? (·.1 == top - (i + 1 : Nat)) with
    | some (_, v) => -d * v
    | none => 0
  let trimmed := Id.run do
    let mut n := coeffs.size
    while n > 0 && coeffs[n - 1]! == 0 do n := n - 1
    return coeffs.extract 0 n
  if trimmed.isEmpty then throw "is not a recurrence (no earlier term)"
  return ⟨trimmed⟩

/-! ## Running a recurrence -/

/-- `init` followed by the terms the recurrence produces, `total` terms in all. -/
def Rec.run (r : Rec) (init : Array Int) (total : Nat) : Array Int := Id.run do
  let mut out := init
  while out.size < total do
    let i := out.size
    let mut s : Int := 0
    for l in [0:r.coeffs.size] do
      s := s + r.coeffs[l]! * out[i - 1 - l]!
    out := out.push s
  return out

/-- Compares `got` with the published terms from position 0; `none` if they agree. -/
private def firstMismatch (got data : Array Int) : Option Nat :=
  (List.range (min got.size data.size)).find? fun i => got[i]! != data[i]!

/-- Checks a recurrence and the claim of its text against the published terms (`data[0]` is the
term at `offset`). Returns how many terms agree with the recurrence started from the first
`order` terms. -/
def Rec.verify (r : Rec) (claim : Claim) (offset : Int) (data : Array Int) (cap minExtra : Nat) :
    Except String Nat := do
  let k := r.order
  if data.size < k + minExtra then
    throw s!"only {data.size} terms for a recurrence of order {k}"
  let n := min data.size cap
  let gen := r.run (data.extract 0 k) n
  if let some i := firstMismatch gen (data.extract 0 n) then
    throw s!"the recurrence disagrees with the data at term #{i} (computed {gen[i]!}, data {data[i]!})"
  match claim with
  | .none => pure ()
  | .values pairs =>
    for (i, v) in pairs do
      let j := i - offset
      if j < 0 || j.toNat ≥ data.size then
        throw s!"the stated value a({i}) is outside the published terms"
      unless data[j.toNat]! == v do
        throw s!"the stated value a({i}) = {v} disagrees with the data ({data[j.toNat]!})"
  | .listing ker init initAt from_ count =>
    unless init.size == ker.size do throw "the initial list does not have the order of the kernel"
    if from_ < initAt then throw "the listing starts before its initial values"
    let skip := (from_ - initAt).toNat
    let total := skip + min count data.size
    let listed := (({ coeffs := ker } : Rec).run init total).extract skip total
    if let some i := firstMismatch listed data then
      throw s!"the program's output disagrees with the data at term #{i}"
    if listed.size < min count data.size then throw "the listing is shorter than announced"
  return n

end
end Oeis.Template.LinearRecurrence
