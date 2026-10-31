module
public import Scripts.Templates.LinearRecurrence.Statement
public meta import Scripts.Templates.LinearRecurrence.Statement

/-!
Wolfram Language: `LinearRecurrence[{c₁, …}, {a₁, …}, n]` (with the list/`{m, n}` forms of the
third argument), `RecurrenceTable[{a[n] == …, a[0] == …}, a, {n, lo, hi}]`, and definitions
`a[n_] := …` (optionally memoized, `a[n_] := a[n] = …`) with the initial values `a[0] = …` beside
them. The listing forms also check that the program's own output matches the data, which is
where a shifted or truncated output is caught.
-/

namespace Oeis.Template.LinearRecurrence
public section

open Recognize

/-- Wolfram notation: `a[n - 1]`, `19 a[n - 1]`, `==`. -/
def mmaSyn (names : Array String) (var : String := "n") : Syn :=
  { names, openC := '[', closeC := ']', juxt := true, juxtSpace := true, pattern := true, var }

/-! ## Brackets -/

/-- The bracket closing the one at `i`. -/
partial def matching (a : Array Char) (i : Nat) : Option Nat :=
  go (i + 1) 1
where
  go (j depth : Nat) : Option Nat :=
    match a[j]? with
    | none => none
    | some c =>
      if c == '[' || c == '{' || c == '(' then go (j + 1) (depth + 1)
      else if c == ']' || c == '}' || c == ')' then
        if depth == 1 then some j else go (j + 1) (depth - 1)
      else go (j + 1) depth

/-- The pieces of `a[lo:hi]` between commas that are not inside brackets. -/
def splitTop (a : Array Char) (lo hi : Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut depth := 0
  let mut s := lo
  for j in [lo:hi] do
    let c := a[j]!
    if c == '[' || c == '{' || c == '(' then depth := depth + 1
    else if c == ']' || c == '}' || c == ')' then depth := depth - 1
    else if c == ',' && depth == 0 then
      out := out.push (s, j)
      s := j + 1
  return out.push (s, hi)

partial def intListGo (a : Array Char) (i : Nat) (acc : Array Int) : Option (Array Int × Nat) :=
  match intAt? a i with
  | none => none
  | some (v, j) =>
    let j := skipWs a j
    match a[j]? with
    | some ',' => intListGo a (j + 1) (acc.push v)
    | some '}' => some (acc.push v, j + 1)
    | _ => none

/-- `{1, -2, 3}`. -/
def intList (a : Array Char) (i : Nat) : Option (Array Int × Nat) :=
  let i := skipWs a i
  if a[i]? == some '{' then intListGo a (i + 1) #[] else none

private def trimmed (cs : Array Int) : Array Int := Id.run do
  let mut n := cs.size
  while n > 0 && cs[n - 1]! == 0 do n := n - 1
  return cs.extract 0 n

/-! ## `LinearRecurrence` -/

def parseLinearRecurrence (a : Array Char) (i : Nat) : Option Raw := do
  guard (startsAt a i "LinearRecurrence[")
  let (ker, j1) ← intList a (i + 17)
  let j2 := skipWs a j1
  guard (a[j2]? == some ',')
  let (init, j3) ← intList a (j2 + 1)
  let j4 := skipWs a j3
  guard (a[j4]? == some ',')
  let j5 := skipWs a (j4 + 1)
  let (first, count, j6) ←
    if a[j5]? == some '{' then do
      let (xs, e) ← intList a j5
      match xs.toList with
      | [m, n] => pure (m, n - m + 1, e)
      | _ => none
    else do
      let (n, e) ← natAt? a j5
      pure ((1 : Int), (n : Int), e)
  let j7 := skipWs a j6
  guard (a[j7]? == some ']' && count ≥ 1 && ker.size == init.size)
  let coeffs := trimmed ker
  guard (!coeffs.isEmpty)
  return { recur := ⟨coeffs⟩, claim := .listing ker init 1 first count.toNat,
           start := i, stop := j7 + 1, flavor := "wolfram-LinearRecurrence" }

/-! ## `RecurrenceTable` -/

def parseRecurrenceTable (a : Array Char) (i : Nat) : Option Raw := do
  guard (startsAt a i "RecurrenceTable[")
  let open_ := i + 15
  let close ← matching a open_
  let parts := splitTop a (open_ + 1) close
  guard (parts.size == 3)
  let s := skipWs a parts[0]!.1
  guard (a[s]? == some '{')
  let sc ← matching a s
  -- the function is `a`, or `a[n]`
  let (name, _) ← identAt? a (skipWs a parts[1]!.1)
  -- `{n, lo, hi}` or `{n, hi}`
  let t := skipWs a parts[2]!.1
  guard (a[t]? == some '{')
  let tc ← matching a t
  let it := splitTop a (t + 1) tc
  let var := (slice a it[0]!.1 it[0]!.2).trimAscii.toString
  let nums ← (it.extract 1 it.size).mapM fun (x, y) =>
    (intAt? a x).bind fun (v, e) => if skipWs a e ≥ y then some v else none
  let (lo, hi) ←
    match nums.toList with
    | [hi] => pure ((1 : Int), hi)
    | [lo, hi] => pure (lo, hi)
    | _ => none
  guard (hi ≥ lo)
  let syn := mmaSyn #[name] var
  let ops := #["==", "="]
  let mut recs : Array Rec := #[]
  let mut vals : Array (Int × Int) := #[]
  for (b0, b1) in splitTop a (s + 1) sc do
    match valuesAt? syn ops a b0 with
    | some (vs, e) =>
      guard (skipWs a e ≥ b1)
      vals := vals ++ vs
    | none =>
      match parseRel syn ops a b0 with
      | .ok total e =>
        guard (skipWs a e ≥ b1)
        recs := recs.push (← total.toRec.toOption)
      | _ => failure
  guard (recs.size == 1)
  let r := recs[0]!
  let i0 ← vals.foldl (init := (none : Option Int)) fun m (x, _) =>
    some (match m with | some y => min x y | none => x)
  let init ← (Array.range r.order).mapM fun (j : Nat) =>
    (vals.find? (·.1 == i0 + (j : Int))).map (·.2)
  return { recur := r, claim := .listing r.coeffs init i0 lo (hi - lo + 1).toNat,
           start := i, stop := close + 1, flavor := "wolfram-RecurrenceTable" }

/-! ## Definitions -/

/-- `(name, variable)` of every `name[var_ ...]` pattern: the functions the program defines. -/
def definedNames (a : Array Char) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for i in [0:a.size] do
    if i == 0 || !isIdChar a[i - 1]! then
      if let some (name, j) := identAt? a i then
        if a[j]? == some '[' then
          if let some (v, _) := identAt? a (j + 1) then
            -- the pattern `n_` or `n_Integer` is one identifier
            if let some k := v.toList.findIdx? (· == '_') then
              let var := String.ofList (v.toList.take k)
              if k > 0 && !out.contains (name, var) then out := out.push (name, var)
  return out

/-- Everything recognized in a Wolfram program block, and the reasons equations were refused. -/
def scanMathematica (text : String) : Array Raw × Array String := Id.run do
  let a := chars text
  let mut found : Array Raw := #[]
  let mut why : Array String := #[]
  for i in [0:a.size] do
    if i == 0 || !isIdChar a[i - 1]! then
      if let some r := parseLinearRecurrence a i then found := found.push r
      else if let some r := parseRecurrenceTable a i then found := found.push r
  for (name, var) in definedNames a do
    let (rs, ws) := scanText (mmaSyn #[name] var) #[":=", "==", "="] "wolfram-definition" text
    found := found ++ rs
    why := why ++ ws
  return (found, why)

end
end Oeis.Template.LinearRecurrence
