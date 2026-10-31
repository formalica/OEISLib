module
public import Scripts.Templates.LinearRecurrence.Core
public meta import Scripts.Templates.LinearRecurrence.Core

/-!
Recognizing a recurrence stated as an equation, together with the guard (`for n >= 2`) and the
initial values (`a(0)=1, a(1)=2`) written next to it: in a title, a formula, a comment, or a
`name[n_] := ...` definition in a program.

A *chain* is one relation plus the guards and initial values adjacent to it, in any order, joined
by `, ; :`, a sentence-ending `.` and filler words (`for`, `with`, `and`, ...). The text of the
whole chain is what gets quoted as the original text. The chain scanner is greedy and
non-overlapping; a second relation ends the chain and starts its own.
-/

namespace Oeis.Template.LinearRecurrence
public section

open Recognize

/-- Blanks the author credit and trailing comment of every line, keeping all positions. The blanked
part starts with a marker character that continues no clause, so a chain never reaches across a
credit into the next line. -/
def maskCredits (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").map fun line =>
    let stop := codeEnd line
    let tail := (line.drop stop).toString
    let blank := String.ofList (List.replicate (line.length - stop) ' ')
    (line.take stop).toString ++
      (if tail.any (!·.isWhitespace) then "\u0001" ++ (blank.drop 1).toString else blank))

private def fillers : List String :=
  ["for", "all", "and", "with", "if", "when", "where", "given", "initial", "conditions",
   "condition", "start", "starting", "from", "holds", "valid", "then"]

/-- Skips white space, `, ; :`, a sentence-ending `.` and filler words between clauses. -/
partial def skipGlue (a : Array Char) (i : Nat) : Nat :=
  let j := skipWs a i
  match a[j]? with
  | some c =>
    if c == ',' || c == ';' || c == ':' then skipGlue a (j + 1)
    else if c == '.' && !(a[j + 1]?.any Char.isDigit) then skipGlue a (j + 1)
    else
      match identAt? a j with
      | some (w, e) => if fillers.contains w.toLower then skipGlue a e else j
      | none => j
  | none => j

/-! ## Clauses -/

inductive RelRes where
  /-- Not an equation (also: an error before the `=`). -/
  | none
  /-- An equation whose right-hand side cannot be read. -/
  | bad (why : String)
  | ok (total : Lin) (stop : Nat)

/-- `f[n] =` right after `:=`: the memoization of a Mathematica definition `f[n_] := f[n] = rhs`. -/
private def skipMemo (syn : Syn) (a : Array Char) (i : Nat) : Nat :=
  let i0 := skipWs a i
  match identAt? a i0 with
  | some (name, j) =>
    let o := skipWs a j
    if syn.names.contains name && a[o]? == some syn.openC then
      match parseIndex syn a (o + 1) with
      | .ok (_, k) =>
        let k := skipWs a k
        if a[k]? == some '=' && a[k + 1]? != some '=' then k + 1 else i
      | .error _ => i
    else i
  | none => i

/-- `lhs = rhs` as `lhs - rhs`. -/
def parseRel (syn : Syn) (ops : Array String) (a : Array Char) (i : Nat) : RelRes :=
  match parseExpr syn a i with
  | .error _ => .none
  | .ok (l, j) =>
    let j := skipWs a j
    match ops.find? (startsAt a j ·) with
    | none => .none
    | some op =>
      let k := if syn.pattern then skipMemo syn a (j + op.length) else j + op.length
      match parseExpr syn a k with
      | .error e => .bad e
      | .ok (r, k) => .ok (l.sub r) k

/-- `n >= 2`, `n > 2`, `(n>1)`: the position after it. -/
def guardAt? (syn : Syn) (a : Array Char) (i : Nat) : Option Nat := do
  let mut j := skipWs a i
  let paren := a[j]? == some '('
  if paren then j := skipWs a (j + 1)
  let (name, e) ← identAt? a j
  guard (name == syn.var)
  j := skipWs a e
  let opLen ←
    if startsAt a j ">=" then some 2
    else if startsAt a j "≥" || startsAt a j ">" then some 1
    else none
  let (_, e) ← intAt? a (j + opLen)
  j := e
  if paren then
    j := skipWs a j
    guard (a[j]? == some ')')
    j := j + 1
  return j

/-- After a stated value: not the start of a longer expression or a fraction. -/
private def valueEnds (a : Array Char) (k : Nat) : Bool :=
  let j := skipWs a k
  match a[j]? with
  | some c =>
    !(c == '/' || c == '*' || c == '^' || c == '+' || c == '-' || c == '(' || c == '[' ||
      (c == '.' && (a[j + 1]?.any Char.isDigit)) || (j == k && c.isAlphanum))
  | none => true

/-- `a(i) = a(j) = v`: the values it states, as `(index, value)`. -/
partial def valuesGo (syn : Syn) (ops : Array String) (a : Array Char) (i : Nat)
    (idxs : Array Int) : Option (Array (Int × Int) × Nat) :=
  let i := skipWs a i
  match identAt? a i with
  | none => none
  | some (name, j) =>
    if !syn.names.contains name then none
    else
      let o := skipWs a j
      if a[o]? != some syn.openC then none
      else
        match intAt? a (o + 1) with
        | none => none
        | some (idx, e) =>
          let e := skipWs a e
          if a[e]? != some syn.closeC then none
          else
            let e := skipWs a (e + 1)
            match ops.find? (startsAt a e ·) with
            | none => none
            | some op =>
              let idxs := idxs.push idx
              let after := e + op.length
              match valuesGo syn ops a after idxs with
              | some r => some r
              | none =>
                match intAt? a after with
                | none => none
                | some (v, k) => if valueEnds a k then some (idxs.map (·, v), k) else none

def valuesAt? (syn : Syn) (ops : Array String) (a : Array Char) (i : Nat) :
    Option (Array (Int × Int) × Nat) :=
  valuesGo syn ops a i #[]

/-! ## Chains -/

structure Acc where
  recur : Option Rec := none
  vals : Array (Int × Int) := #[]
  stop : Nat := 0
  /-- The equation was read but is not a homogeneous recurrence. -/
  bad : Option String := none

/-- Extends the chain that ends at `acc.stop` by the clauses adjacent to it. -/
partial def extend (syn : Syn) (ops : Array String) (a : Array Char) (acc : Acc)
    (first : Bool) : Acc :=
  let j := if first then acc.stop else skipGlue a acc.stop
  match (if first then none else guardAt? syn a j) with
  | some e => extend syn ops a { acc with stop := e } false
  | none =>
  match valuesAt? syn ops a j with
  | some (vs, e) => extend syn ops a { acc with vals := acc.vals ++ vs, stop := e } false
  | none =>
    if acc.recur.isSome then acc
    else
      match parseRel syn ops a j with
      | .ok total e =>
        match total.toRec with
        | .ok r => extend syn ops a { acc with recur := some r, stop := e } false
        | .error why => { acc with bad := some why, stop := e }
      | .bad why => { acc with bad := some why }
      | .none => acc

/-- May a chain start at `i`: the name of the sequence, not part of a longer word or product. -/
def validStart (syn : Syn) (a : Array Char) (i : Nat) : Bool :=
  match identAt? a i with
  | some (name, _) =>
    syn.names.contains name &&
    (i == 0 || !isIdChar a[i - 1]!) &&
    (let p := Id.run do
      let mut p := i
      while p > 0 && a[p - 1]!.isWhitespace do p := p - 1
      return p
     p == 0 || !("+-*/^=<>!&|%~".contains a[p - 1]!))
  | none => false

/-- Every chain of the text with a recurrence in it, and the reasons equations were refused. -/
def scanText (syn : Syn) (ops : Array String) (flavor : String) (text : String) :
    Array Raw × Array String := Id.run do
  let a := chars (maskCredits text)
  let mut found : Array Raw := #[]
  let mut why : Array String := #[]
  let mut i := 0
  while i < a.size do
    if validStart syn a i then
      let acc := extend syn ops a { stop := i } true
      if acc.stop > i then
        if let some w := acc.bad then why := why.push w
        else if let some r := acc.recur then
          found := found.push
            { recur := r, claim := if acc.vals.isEmpty then .none else .values acc.vals,
              start := i, stop := acc.stop, flavor }
        i := acc.stop
        continue
    i := i + 1
  return (found, why)

/-- Plain OEIS notation: `a(n)`, `2a(n-1)`, `=`. -/
def plainSyn (names : Array String) : Syn := { names, juxt := true }

/-- The names `f` of every `f(n` in the text: what a title may call the sequence (`F(n)`). -/
def callNames (text : String) : Array String := Id.run do
  let a := chars text
  let mut out : Array String := #[]
  for i in [0:a.size] do
    if i == 0 || !isIdChar a[i - 1]! then
      if let some (name, j) := identAt? a i then
        if a[j]? == some '(' && (identAt? a (skipWs a (j + 1))).any (·.1 == "n") &&
            !out.contains name then
          out := out.push name
  return out

end
end Oeis.Template.LinearRecurrence
