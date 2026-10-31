module
public import Scripts.OeisTemplate.Recognize
public meta import Scripts.OeisTemplate.Recognize

/-!
Integer-affine combinations of shifted calls `a(n+s)` and a parser for them, shared by every
recognizer of the `linearRecurrence` template.

`Lin` is `c + nc·n + Σ k·a(n+s)`. A product is allowed only when one factor is a constant, so
`3*a(n-1)` and `2(a(n-1)+a(n-2))` parse while `n*a(n-1)` and `a(n-1)^2` are rejected with a
reason. The parser is configured by a `Syn`: the accepted function names, the bracket style
(`a(n-1)`, `a[n-1]`) and whether `19 a[n-1]` is a product.
-/

namespace Oeis.Template.LinearRecurrence
public section

open Recognize

/-! ## Characters -/

def startsAt (a : Array Char) (i : Nat) (s : String) : Bool :=
  a.extract i (i + s.length) == s.toList.toArray

def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The identifier starting at `i`: its name and the position after it. -/
def identAt? (a : Array Char) (i : Nat) : Option (String × Nat) :=
  match a[i]? with
  | some c =>
    if c.isAlpha || c == '_' then
      let j := Id.run do
        let mut j := i + 1
        while j < a.size && isIdChar a[j]! do j := j + 1
        return j
      some (slice a i j, j)
    else none
  | none => none

/-- The natural number literal starting exactly at `i`. -/
def natAt? (a : Array Char) (i : Nat) : Option (Nat × Nat) :=
  match a[i]? with
  | some c =>
    if c.isDigit then
      let r := Id.run do
        let mut j := i
        let mut v := 0
        while j < a.size && a[j]!.isDigit do
          v := v * 10 + (a[j]!.toNat - '0'.toNat)
          j := j + 1
        return (v, j)
      some r
    else none
  | none => none

/-- An optionally signed integer literal after optional whitespace. -/
def intAt? (a : Array Char) (i : Nat) : Option (Int × Nat) :=
  let i := skipWs a i
  match a[i]? with
  | some '-' => (natAt? a (skipWs a (i + 1))).map fun (v, j) => (-(v : Int), j)
  | some '+' => (natAt? a (skipWs a (i + 1))).map fun (v, j) => ((v : Int), j)
  | _ => (natAt? a i).map fun (v, j) => ((v : Int), j)

/-! ## Linear forms -/

structure Lin where
  c : Int := 0
  nc : Int := 0
  /-- `(shift, coefficient)` for `a(n + shift)`; no duplicate shifts, no zero coefficients. -/
  terms : Array (Int × Int) := #[]
  deriving BEq, Repr, Inhabited

namespace Lin

def isConst (l : Lin) : Bool := l.nc == 0 && l.terms.isEmpty

private def addTerm (ts : Array (Int × Int)) (s k : Int) : Array (Int × Int) :=
  match ts.findIdx? (·.1 == s) with
  | some i =>
    let v := ts[i]!.2 + k
    if v == 0 then ts.eraseIdx! i else ts.set! i (s, v)
  | none => if k == 0 then ts else ts.push (s, k)

def add (x y : Lin) : Lin :=
  y.terms.foldl (init := { x with c := x.c + y.c, nc := x.nc + y.nc }) fun acc (s, k) =>
    { acc with terms := addTerm acc.terms s k }

def scale (k : Int) (l : Lin) : Lin :=
  if k == 0 then {}
  else { c := k * l.c, nc := k * l.nc, terms := l.terms.map fun (s, v) => (s, k * v) }

def neg (l : Lin) : Lin := l.scale (-1)

def sub (x y : Lin) : Lin := x.add y.neg

def mul (x y : Lin) : Except String Lin :=
  if x.isConst then .ok (y.scale x.c)
  else if y.isConst then .ok (x.scale y.c)
  else .error "a product of two non-constant factors"

def pow (x : Lin) (e : Nat) : Except String Lin :=
  if e == 1 then .ok x
  else if e == 0 then .ok { c := 1 }
  else if x.isConst && e ≤ 200 then .ok { c := x.c ^ e }
  else .error "a power of a non-constant term"

end Lin

/-! ## Syntax of the host language -/

structure Syn where
  /-- Accepted names of the sequence function. -/
  names : Array String
  openC : Char := '('
  closeC : Char := ')'
  /-- `3a(n-1)` is a product when the two are written together. -/
  juxt : Bool := false
  /-- ... and `19 a[n-1]` also when separated by white space (Mathematica). -/
  juxtSpace : Bool := false
  /-- The index may be written `n_` (a Mathematica pattern). -/
  pattern : Bool := false
  /-- Spellings of the power operator. -/
  powers : Array String := #["^"]
  var : String := "n"
  /-- The index may be a negative literal, `a[-1]` (Python lists). -/
  negIndex : Bool := false

abbrev PR := Except String (Lin × Nat)

/-- `n`, `n+k` or `n-k` followed by the closing bracket: `(shift, position after)`. -/
def parseIndex (syn : Syn) (a : Array Char) (i : Nat) : Except String (Int × Nat) := do
  let i := skipWs a i
  if syn.negIndex && a[i]? == some '-' then
    let some (v, e) := natAt? a (skipWs a (i + 1)) | throw "the argument is not n±k"
    let k := skipWs a e
    if a[k]? == some syn.closeC then return (-(v : Int), k + 1)
    else throw "the argument is not n±k"
  let some (name, j) := identAt? a i | throw "the argument is not n±k"
  -- a Mathematica pattern `n_` or `n_Integer` is read as one identifier
  unless name == syn.var || (syn.pattern && name.startsWith (syn.var ++ "_")) do
    throw "the argument is not n±k"
  let j' := skipWs a j
  let (shift, k) ←
    match a[j']? with
    | some '+' =>
      let some (v, e) := natAt? a (skipWs a (j' + 1)) | throw "the argument is not n±k"
      pure ((v : Int), e)
    | some '-' =>
      let some (v, e) := natAt? a (skipWs a (j' + 1)) | throw "the argument is not n±k"
      pure (-(v : Int), e)
    | _ => pure (0, j)
  let k := skipWs a k
  if a[k]? == some syn.closeC then return (shift, k + 1)
  else throw "the argument is not n±k"

/-- Does a factor that can be juxtaposed start at `i`: a call of the sequence or `(`? -/
private def startsFactor (syn : Syn) (a : Array Char) (i : Nat) : Bool :=
  match a[i]? with
  | some '(' => true
  | _ =>
    match identAt? a i with
    | some (name, j) => syn.names.contains name && a[skipWs a j]? == some syn.openC
    | none => false

mutual

partial def parseExpr (syn : Syn) (a : Array Char) (i : Nat) : PR := do
  let (first, j) ← parseTerm syn a i
  exprLoop syn a first j

partial def exprLoop (syn : Syn) (a : Array Char) (acc : Lin) (i : Nat) : PR := do
  let j := skipWs a i
  match a[j]? with
  | some '+' =>
    let (t, k) ← parseTerm syn a (j + 1)
    exprLoop syn a (acc.add t) k
  | some '-' =>
    let (t, k) ← parseTerm syn a (j + 1)
    exprLoop syn a (acc.sub t) k
  | _ => return (acc, i)

partial def parseTerm (syn : Syn) (a : Array Char) (i : Nat) : PR := do
  let (first, j) ← parseFactor syn a i
  termLoop syn a first j

partial def termLoop (syn : Syn) (a : Array Char) (acc : Lin) (i : Nat) : PR := do
  let j := skipWs a i
  match a[j]? with
  | some '*' =>
    if a[j + 1]? == some '*' then return (acc, i)
    else
      let (f, k) ← parseFactor syn a (j + 1)
      termLoop syn a (← acc.mul f) k
  | some '/' => throw "a division"
  | _ =>
    let at_ := if syn.juxtSpace then j else i
    if syn.juxt && acc.isConst && startsFactor syn a at_ then
      match parseFactor syn a at_ with
      | .ok (f, k) => termLoop syn a (← acc.mul f) k
      | .error _ => return (acc, i)
    else return (acc, i)

partial def parseFactor (syn : Syn) (a : Array Char) (i : Nat) : PR := do
  let j := skipWs a i
  match a[j]? with
  | some '-' =>
    let (f, k) ← parseFactor syn a (j + 1)
    return (f.neg, k)
  | some '+' => parseFactor syn a (j + 1)
  | _ =>
    let (base, k) ← parsePrimary syn a j
    let k' := skipWs a k
    match syn.powers.find? (startsAt a k' ·) with
    | some p =>
      let (e, m) ← parseFactor syn a (k' + p.length)
      if e.isConst && e.c ≥ 0 then return (← base.pow e.c.toNat, m)
      else throw "a non-constant exponent"
    | none => return (base, k)

partial def parsePrimary (syn : Syn) (a : Array Char) (i : Nat) : PR := do
  match a[i]? with
  | none => throw "the expression ends early"
  | some c =>
    if c.isDigit then
      match natAt? a i with
      | some (v, j) =>
        if a[j]? == some '.' && (a[j + 1]?.any Char.isDigit) then throw "a non-integer number"
        else return ({ c := v }, j)
      | none => throw "bad number"
    else if c == '(' then
      let (l, j) ← parseExpr syn a (i + 1)
      let j := skipWs a j
      if a[j]? == some ')' then return (l, j + 1) else throw "a missing closing parenthesis"
    else
      match identAt? a i with
      | some (name, j) =>
        if syn.names.contains name then
          let o := skipWs a j
          if a[o]? == some syn.openC then
            let (shift, k) ← parseIndex syn a (o + 1)
            return ({ terms := #[(shift, 1)] }, k)
          else throw s!"`{name}` without an argument"
        else if name == syn.var then return ({ nc := 1 }, j)
        else throw s!"the unknown symbol `{name}`"
      | none => throw s!"the unexpected character `{c}`"

end

end
end Oeis.Template.LinearRecurrence
