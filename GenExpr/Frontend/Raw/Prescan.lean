module
public import GenExpr.Lexer
public meta import GenExpr.Lexer

/-!
Pre-parse scan for definition heads.

The parser has to decide whether `n(n+1)` is a call or a product, and it cannot wait for the
type checker: the decision changes what the segmenter sees. The information that settles it is
already in the text — `a(n) = …` says that `a` is a function and `n` is one of its variables — so
a cheap token-pattern scan runs first and hands the parser a classifier.
-/

namespace GenExpr.Raw
public section

/-- How the parser should read a bare identifier. -/
inductive SymClass where
  /-- A known function: `f(` opens an argument list. -/
  | func
  /-- A known value: `n(` is a product, never a call. -/
  | var
  | unknown
deriving DecidableEq, Repr, Inhabited, BEq

/-- Names the input itself introduces. -/
structure Prescan where
  heads : Array String := #[]
  params : Array String := #[]
  /-- Names written immediately before `(`. An unresolved one is a function hole wherever it
  occurs, including bare, which is what makes `1 + T(x)` fail rather than read as `1 + T*x`. -/
  applied : Array String := #[]
  /-- Names used as a plain operand somewhere. Such a name is a variable even where it is
  followed by `(`, which is what makes `n(n+1)/2` a product: `n + 1` shows `n` is a value. -/
  bare : Array String := #[]
deriving Inhabited, Repr

namespace Prescan

private def isAssign (t : Token) : Bool := t.isOp "=" || t.isOp "=="

/-- Reads `IDENT , IDENT , … )` starting at `i`, returning the names and the index past `)`. -/
private def readParams (toks : Array Token) (i : Nat) : Option (Array String × Nat) := Id.run do
  let mut names : Array String := #[]
  let mut j := i
  let mut expectName := true
  for _ in [0:toks.size - i + 1] do
    let some t := toks[j]? | return none
    if expectName then
      if t.kind == .ident then
        names := names.push t.text
        expectName := false
        j := j + 1
      else if t.kind == .rparen && names.isEmpty then
        return some (names, j + 1)
      else
        return none
    else if t.kind == .comma then
      expectName := true
      j := j + 1
    else if t.kind == .rparen then
      return some (names, j + 1)
    else
      return none
  return none

/-- A bare `x =` introduces a definition only where `x` could not be an operand of what precedes
it; that rules out the second `b` of `a = b = c` while keeping `… where c = …`. -/
private def bareHeadAllowed (toks : Array Token) (i : Nat) : Bool :=
  match toks[i - 1]? with
  | none => true
  | some p =>
    if i == 0 then true
    else p.kind == .ident || p.kind == .junk || p.kind == .comma || p.kind == .semi

def run (toks : Array Token) : Prescan := Id.run do
  let mut out : Prescan := {}
  let mut depth := 0
  for i in [0:toks.size] do
    let t := toks[i]!
    match t.kind with
    | .lparen | .lbrace | .lbrack => depth := depth + 1
    | .rparen | .rbrace | .rbrack => depth := depth - 1
    | .ident =>
      let next := toks[i + 1]?
      if next.any (fun n => n.kind == .lparen && !n.spaceBefore) then
        if !out.applied.contains t.text then
          out := { out with applied := out.applied.push t.text }
      -- `T^2(x)` and `log_2` are still applications, not operand uses.
      else if !next.any (fun n => (n.isOp "^" || n.isOp "_") && !n.spaceBefore) then
        if !out.bare.contains t.text then
          out := { out with bare := out.bare.push t.text }
      -- Only depth 0: `Sum_{k=0}^n` and `integral(x=0)^1` must not register `k` or `x`.
      if depth == 0 then
        if (toks[i + 1]?).any (·.kind == .lparen) then
          if let some (names, after) := readParams toks (i + 2) then
            if (toks[after]?).any isAssign then
              out := { heads := out.heads.push t.text, params := out.params ++ names }
        else if (toks[i + 1]?).any isAssign && bareHeadAllowed toks i then
          out := { out with heads := out.heads.push t.text }
    | _ => pure ()
  return out

end Prescan

/-- Everything the parser needs in order to classify a name. `functions` and `values` come from
the caller (catalogue, custom functions, desired names); `prescan` comes from the input. -/
structure Classifier where
  prescan : Prescan := {}
  functions : Array String := #[]
  values : Array String := #[]
deriving Inhabited

namespace Classifier

/-- `locals` are aggregator binders currently in scope, which shadow everything else. -/
def classify (c : Classifier) (locals : Array String) (name : String) : SymClass :=
  if locals.contains name then .var
  else if c.prescan.params.contains name then .var
  else if c.prescan.heads.contains name || c.functions.contains name then .func
  else if c.values.contains name then .var
  else .unknown

def isKnown (c : Classifier) (locals : Array String) (name : String) : Bool :=
  c.classify locals name != .unknown

end Classifier

end
end GenExpr.Raw
