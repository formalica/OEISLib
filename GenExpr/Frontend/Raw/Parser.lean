module
public import GenExpr.Ast
public meta import GenExpr.Ast
public import GenExpr.Frontend.Raw.Prescan
public meta import GenExpr.Frontend.Raw.Prescan
public import Std.Data.HashMap
public meta import Std.Data.HashMap

/-!
Pratt parser for the raw syntax.

Three properties make this parser unusual and are relied on by the segmenter:

* **every intermediate result is also a result.** `parseExpr` returns one entry per token position
  at which the expression so far is complete, so the segmenter gets all candidate end positions
  from one call instead of re-parsing prefixes;
* **ambiguity is a costed list, not a node.** Where the surface syntax genuinely admits several
  readings (`n(n+1)`, `2F1(a,b)`, an aggregator body's extent) the parser returns all of them with
  a penalty, and later stages pick;
* **whitespace matters.** Application and implicit multiplication are only offered for glued
  tokens, except for the deliberately weak `f (x)` readings.

Precedences mirror Lean's so that a rendered term re-parses with the same tree:
relations 50 · `+ -` 65 · `* / mod` 70 · juxtaposition 72 · unary `-` 75 · `^` 75 right ·
postfix `!` 90.
-/

namespace GenExpr.Raw
public section

/-- One parse: the tree, the next token index, and a penalty (lower is a more likely reading). -/
structure Res where
  ast : Ast
  pos : Nat
  cost : Nat
deriving Inhabited, Repr

structure PCtx where
  inp : Input
  toks : Array Token
  cls : Classifier
  /-- Alternatives kept per distinct end position. -/
  maxPerEnd : Nat := 4
deriving Inhabited

namespace PCtx

def tok? (ctx : PCtx) (i : Nat) : Option Token := ctx.toks[i]?

/-- Byte span of the token range `[i, j)`. -/
def range (ctx : PCtx) (i j : Nat) : Span :=
  if h : i < ctx.toks.size ∧ j > 0 ∧ j - 1 < ctx.toks.size then
    ctx.inp.span ctx.toks[i]!.start ctx.toks[j - 1]!.stop
  else
    let _ := h
    {}

def kindAt (ctx : PCtx) (i : Nat) : Option TokKind := (ctx.tok? i).map (·.kind)

end PCtx

/-! ## Operator tables -/

/-- `(operator, left binding power, right binding power)`.

`^` takes a right binding power of 72 rather than 75 so that a juxtaposition inside the exponent
is reachable: `2^2n` then yields both `2^(2n)` and `(2^2)*n`, the first being cheaper. -/
private def infixOp? (t : Token) : Option (BinOp × Nat × Nat) :=
  if t.kind == .op then
    match t.text with
    | "+" => some (.add, 65, 66)
    | "-" => some (.sub, 65, 66)
    | "*" => some (.mul, 70, 71)
    | "/" => some (.div, 70, 71)
    | "%" => some (.mod, 70, 71)
    | "^" | "**" => some (.pow, 75, 72)
    | _ => none
  else if t.kind == .ident && t.text == "mod" then some (.mod, 70, 71)
  else none

private def relOp? (t : Token) : Option RelOp :=
  if t.kind == .op then RelOp.ofString t.text else none

private def aggKind? (name : String) : Option AggKind :=
  match name.toLower with
  | "sum" | "summation" => some .sum
  | "prod" | "product" => some .prod
  | "int" | "integral" => some .integral
  | _ => none

private def relPrec : Nat := 50
private def juxtPrec : Nat := 72
private def negPrec : Nat := 75
private def factPrec : Nat := 90

/-- A relation is a proposition, so it may only be extended by further relations. This is what
keeps `a(n) = 0^n + n` from also parsing as `(a(n) = 0^n) + n`. -/
private def isRel : Ast → Bool
  | .rel .. => true
  | _ => false

/-! ## Alternative pruning -/

/-- Keeps the `k` cheapest distinct readings per end position. Without this the alternatives
introduced at every ambiguous juxtaposition would multiply along the infix loop. -/
private def prune (k : Nat) (rs : List Res) : List Res := Id.run do
  let sorted := rs.toArray.qsort fun a b =>
    a.pos < b.pos || (a.pos == b.pos && a.cost < b.cost)
  let mut out : Array Res := #[]
  let mut lastPos : Option Nat := none
  let mut cnt := 0
  for r in sorted do
    if lastPos != some r.pos then
      lastPos := some r.pos
      cnt := 0
    if cnt < k && !(out.any fun o => o.pos == r.pos && o.ast == r.ast) then
      out := out.push r
      cnt := cnt + 1
  return out.toList

/-! ## Parser -/

abbrev Memo := Std.HashMap (Nat × Nat × UInt64) (List Res)
abbrev P := StateM Memo

private def localsKey (locals : Array String) : UInt64 :=
  String.hash (String.intercalate "\u0000" locals.toList)

/-- Number of consecutive `!` tokens starting at `pos`. -/
private def bangRun (ctx : PCtx) (pos : Nat) : Nat := Id.run do
  let mut k := 0
  for _ in [0:ctx.toks.size - pos] do
    if (ctx.tok? (pos + k)).any (·.isOp "!") then k := k + 1 else break
  return k

/-- Which implicit multiplications are offered, and how strongly.

`ident ident` is never a product — that is what keeps prose out — and a spaced `(` after an
unknown name is only a weak reading, so `words (1+x)` loses to starting a fresh expression at `(`. -/
private def juxtCost (ctx : PCtx) (locals : Array String) (lhs : Ast) (pos : Nat) : Option Nat :=
  match ctx.tok? pos with
  | none => none
  | some t =>
    let glued := !t.spaceBefore
    let prevKind := (ctx.tok? (pos - 1)).map (·.kind)
    if t.kind != .lparen && t.kind != .ident && t.kind != .num then none
    else
      match lhs with
      | .ident name _ =>
        if t.kind != .lparen then none
        else
          match ctx.cls.classify locals name with
          | .var => if glued then some 0 else none
          | .unknown => some (if glued then 4 else 1)
          | .func => none
      | .num .. | .dec .. =>
        if glued && (t.kind == .ident || t.kind == .lparen) then some 0 else none
      | _ =>
        if prevKind == some .rparen then
          if t.kind == .lparen then some 0 else if glued then some 0 else none
        else if glued && (prevKind == some .num || prevKind == some .ident) then some 1
        else none

/-- Whether the reading `lhs` ending at `pos` could still absorb the next token.

Only readings that cannot are used as operands: `parseExpr` returns one entry per position at
which the expression is complete, and feeding those short entries back into operator construction
would make `3n^2 - 7*n` also parse as `(3n^2 - 7) * n`. -/
private def canExtend (ctx : PCtx) (locals : Array String) (lhs : Ast) (pos minPrec : Nat) : Bool :=
  match ctx.tok? pos with
  | none => false
  | some t =>
    let rel := isRel lhs
    (!rel && (infixOp? t).any fun (_, lbp, _) => lbp ≥ minPrec)
      || ((relOp? t).isSome && relPrec ≥ minPrec)
      || (!rel && t.isOp "!" && factPrec ≥ minPrec)
      || (!rel && juxtPrec ≥ minPrec && (juxtCost ctx locals lhs pos).isSome)

mutual

/-- All readings of an expression starting at `pos`, one per end position. -/
partial def parseExpr (ctx : PCtx) (locals : Array String) (pos minPrec : Nat) : P (List Res) := do
  let key := (pos, minPrec, localsKey locals)
  if let some cached := (← get)[key]? then return cached
  let prefixes ← parsePrefix ctx locals pos
  let mut out : List Res := []
  for p in prefixes do
    out := out ++ (← parseInfix ctx locals p.ast p.pos p.cost minPrec)
  let pruned := prune ctx.maxPerEnd out
  modify (·.insert key pruned)
  return pruned

/-- `parseExpr` restricted to readings that cannot absorb another token: the operand form. -/
partial def parseOperand (ctx : PCtx) (locals : Array String) (pos minPrec : Nat) : P (List Res) := do
  let all ← parseExpr ctx locals pos minPrec
  let maximal := all.filter fun r => !canExtend ctx locals r.ast r.pos minPrec
  -- An operator with no valid right-hand side leaves nothing maximal; keep what there is.
  return if maximal.isEmpty then all else maximal

partial def parsePrefix (ctx : PCtx) (locals : Array String) (pos : Nat) : P (List Res) := do
  match ctx.tok? pos with
  | none => return []
  | some t =>
    match t.kind with
    | .num =>
      let base : Res := { ast := .num (t.text.toNat!) (ctx.range pos (pos + 1)), pos := pos + 1,
                          cost := 0 }
      -- `2F1(a,b)`: a glued number and name spell one catalogue entry.
      match ctx.tok? (pos + 1), ctx.tok? (pos + 2) with
      | some idt, some lp =>
        if idt.kind == .ident && !idt.spaceBefore && lp.kind == .lparen && !lp.spaceBefore &&
            ctx.cls.classify locals (t.text ++ idt.text) == .func then
          let calls ← parseArgs ctx locals (pos + 3)
          -- The catalogue knows the glued name, so splitting it is the weaker reading.
          return { base with cost := 2 } :: calls.map fun (args, p, c) =>
            { ast := .app (t.text ++ idt.text) args (ctx.range pos p), pos := p, cost := c }
        else return [base]
      | _, _ => return [base]
    | .dec =>
      let parts := t.text.splitOn "."
      let whole := parts.headD "0"
      let frac := parts.getD 1 "0"
      return [{ ast := .dec whole frac (ctx.range pos (pos + 1)), pos := pos + 1, cost := 0 }]
    | .ident => parseHead ctx locals pos t
    | .lparen =>
      let inner ← parseOperand ctx locals (pos + 1) 0
      return inner.filterMap fun r =>
        if (ctx.kindAt r.pos) == some .rparen then
          some { r with pos := r.pos + 1, ast := r.ast.withSpan (ctx.range pos (r.pos + 1)) }
        else none
    | .op =>
      if t.text == "-" then
        let inner ← parseOperand ctx locals (pos + 1) negPrec
        return inner.map fun r =>
          { r with ast := .un .neg r.ast (ctx.range pos r.pos) }
      else if t.text == "+" then
        parseOperand ctx locals (pos + 1) negPrec
      else if t.text == "|" then
        -- The body is parsed above relation level so the closing bar is not read as `divides`.
        let inner ← parseOperand ctx locals (pos + 1) (relPrec + 1)
        return inner.filterMap fun r =>
          if (ctx.tok? r.pos).any (·.isOp "|") then
            some { r with pos := r.pos + 1, ast := .un .abs r.ast (ctx.range pos (r.pos + 1)) }
          else none
      else return []
    | _ => return []

/-- Extends `lhs` with infix, postfix and juxtaposition operators of precedence at least
`minPrec`. The unextended `lhs` is always among the results — those are the checkpoints. -/
partial def parseInfix (ctx : PCtx) (locals : Array String) (lhs : Ast)
    (pos cost minPrec : Nat) : P (List Res) := do
  let stop : Res := { ast := lhs, pos, cost }
  match ctx.tok? pos with
  | none => return [stop]
  | some t =>
    let mut out : List Res := [stop]
    let rel := isRel lhs
    if let some (op, lbp, rbp) := infixOp? t then
      if !rel && lbp ≥ minPrec then
        for r in ← parseOperand ctx locals (pos + 1) rbp do
          let node := Ast.bin op lhs r.ast (lhs.span.merge r.ast.span)
          out := out ++ (← parseInfix ctx locals node r.pos (cost + r.cost) minPrec)
    if let some relop := relOp? t then
      if relPrec ≥ minPrec then
        for r in ← parseOperand ctx locals (pos + 1) (relPrec + 1) do
          let node := Ast.appendRel lhs relop r.ast (lhs.span.merge r.ast.span)
          out := out ++ (← parseInfix ctx locals node r.pos (cost + r.cost) minPrec)
    if !rel && t.isOp "!" && factPrec ≥ minPrec then
      let k := bangRun ctx pos
      let node := Ast.fact k lhs (lhs.span.merge (ctx.range pos (pos + k)))
      out := out ++ (← parseInfix ctx locals node (pos + k) cost minPrec)
    if !rel && juxtPrec ≥ minPrec then
      if let some jc := juxtCost ctx locals lhs pos then
        for r in ← parseOperand ctx locals pos (juxtPrec + 1) do
          let node := Ast.bin .mul lhs r.ast (lhs.span.merge r.ast.span)
          out := out ++ (← parseInfix ctx locals node r.pos (cost + r.cost + jc) minPrec)
    return prune ctx.maxPerEnd out

/-- An identifier: aggregator head, subscripted call, plain call, or bare name. -/
partial def parseHead (ctx : PCtx) (locals : Array String) (pos : Nat) (t : Token) : P (List Res) := do
  let name := t.text
  if let some kind := aggKind? name then
    let aggs ← parseAgg ctx locals pos kind
    if !aggs.isEmpty then return aggs
  let cls := ctx.cls.classify locals name
  let subs ← parseSubscript ctx locals (pos + 1)
  let mut out : List Res := []
  for (sub, p1) in subs do
    let subArgs : Array Ast := sub.toArray
    let lp? := ctx.tok? p1
    let hasParen := (lp?.map (·.kind)) == some .lparen
    let spaced := (lp?.map (·.spaceBefore)).getD false
    let mut producedPow := false
    -- `T^2(x)` — the exponent is written between the name and the arguments.
    if sub.isNone && cls != .var && (lp?.any (·.isOp "^")) then
      for e in ← parseSup ctx locals (p1 + 1) do
        if (ctx.kindAt e.pos) == some .lparen then
          for (args, p3, c) in ← parseArgs ctx locals (e.pos + 1) do
            let call := Ast.app name args (ctx.range pos p3)
            producedPow := true
            out := out ++ [{ ast := .bin .pow call e.ast (ctx.range pos p3), pos := p3,
                             cost := c + e.cost }]
    if hasParen && cls != .var then
      let appCost := if !spaced then 0 else (if cls == .func then 0 else 2)
      for (args, p2, c) in ← parseArgs ctx locals (p1 + 1) do
        out := out ++ [{ ast := .app name (subArgs ++ args) (ctx.range pos p2), pos := p2,
                         cost := c + appCost }]
    let bareCost :=
      if producedPow then 3
      else if cls == .unknown && hasParen && !spaced then 3
      else 0
    if !(cls == .func && hasParen) then
      let bare :=
        if subArgs.isEmpty then Ast.ident name (ctx.range pos p1)
        else Ast.app name subArgs (ctx.range pos p1)
      out := out ++ [{ ast := bare, pos := p1, cost := bareCost }]
  return prune ctx.maxPerEnd out

/-- `_2`, `_{n-1}`, `_(k)` written directly after a name; the subscript becomes the first
argument, which is what turns `log_2(n)` into `log(2, n)` and `a_n` into `a(n)`. -/
partial def parseSubscript (ctx : PCtx) (locals : Array String) (pos : Nat) :
    P (List (Option Ast × Nat)) := do
  match ctx.tok? pos with
  | some u =>
    if !(u.isOp "_") || u.spaceBefore then return [(none, pos)]
    else
      match ctx.kindAt (pos + 1) with
      | some .lbrace =>
        let inner ← parseOperand ctx locals (pos + 2) 0
        let ok := inner.filterMap fun r =>
          if (ctx.kindAt r.pos) == some .rbrace then some ((some r.ast : Option Ast), r.pos + 1)
          else none
        return if ok.isEmpty then [(none, pos)] else ok
      | some .lparen =>
        let inner ← parseOperand ctx locals (pos + 2) 0
        let ok := inner.filterMap fun r =>
          if (ctx.kindAt r.pos) == some .rparen then some ((some r.ast : Option Ast), r.pos + 1)
          else none
        return if ok.isEmpty then [(none, pos)] else ok
      | some .num | some .ident =>
        -- A bare subscript is exactly one token; anything longer must be bracketed.
        let u2 := ctx.toks[pos + 1]!
        let sp := ctx.range (pos + 1) (pos + 2)
        let leaf := if u2.kind == .num then Ast.num u2.text.toNat! sp else Ast.ident u2.text sp
        return [(some leaf, pos + 2)]
      | _ => return [(none, pos)]
  | none => return [(none, pos)]

/-- An exponent or upper bound written after `^`: either an atom or a braced expression. -/
partial def parseSup (ctx : PCtx) (locals : Array String) (pos : Nat) : P (List Res) := do
  match ctx.kindAt pos with
  | some .lbrace =>
    let inner ← parseOperand ctx locals (pos + 1) 0
    return inner.filterMap fun r =>
      if (ctx.kindAt r.pos) == some .rbrace then some { r with pos := r.pos + 1 } else none
  | _ => parseAtom ctx locals pos

/-- A single atom: number, name or parenthesised expression. Used where a full expression would
over-consume, such as an exponent written before an argument list. -/
partial def parseAtom (ctx : PCtx) (locals : Array String) (pos : Nat) : P (List Res) := do
  match ctx.kindAt pos with
  | some .num | some .ident | some .lparen => parseOperand ctx locals pos factPrec
  | _ => return []

/-- `( e , e , … )`, also accepting `;` as a separator (`2F1(a,b;c;z)`). `pos` is just past `(`. -/
partial def parseArgs (ctx : PCtx) (locals : Array String) (pos : Nat) :
    P (List (Array Ast × Nat × Nat)) := do
  if (ctx.kindAt pos) == some .rparen then return [(#[], pos + 1, 0)]
  let firsts ← parseOperand ctx locals pos 0
  let mut out : List (Array Ast × Nat × Nat) := []
  for r in firsts do
    match ctx.kindAt r.pos with
    | some .rparen => out := out ++ [(#[r.ast], r.pos + 1, r.cost)]
    | some .comma | some .semi =>
      for (rest, p, c) in ← parseArgs ctx locals (r.pos + 1) do
        out := out ++ [(#[r.ast] ++ rest, p, r.cost + c)]
    | _ => pure ()
  return out.take 8

/-- `Sum_{k=0..n} body`, `sum_(k=0)^n body`, `Sum{k>=1} body`, `integral(x=0)^1 body`. -/
partial def parseAgg (ctx : PCtx) (locals : Array String) (pos : Nat) (kind : AggKind) :
    P (List Res) := do
  let mut p := pos + 1
  if (ctx.tok? p).any (·.isOp "_") then p := p + 1
  let close := match ctx.kindAt p with
    | some .lbrace => some TokKind.rbrace
    | some .lparen => some TokKind.rparen
    | _ => none
  let some closing := close | return []
  let groups ← parseBinders ctx locals (p + 1) closing
  let mut out : List Res := []
  for (binders, afterGroup, gcost) in groups do
    if binders.isEmpty then continue
    -- An upper bound may be written after the group: `Sum_{k=0}^n`.
    let mut ends : List (Array BinderSpec × Nat × Nat) := [(binders, afterGroup, gcost)]
    if (ctx.tok? afterGroup).any (·.isOp "^") then
      let ups ← parseSup ctx locals (afterGroup + 1)
      ends := ups.map fun u =>
        (binders.modify (binders.size - 1) fun b => { b with hi := some u.ast }, u.pos,
          gcost + u.cost)
    for (bs, bodyStart, bcost) in ends do
      if bs.any fun b => b.hi.isNone && b.lo.isNone && b.divisorOf.isNone then continue
      let vars := bs.map (·.var)
      let inner := locals ++ vars
      -- Primary reading: the body is a product chain, so `Sum_k f(k) + 1` adds outside the sum.
      let tight ← parseOperand ctx inner bodyStart 70
      let loose ← parseOperand ctx inner bodyStart 0
      let bodies := tight.map (fun r => (r, 0)) ++ loose.map (fun r => (r, 1))
      for (r, extra) in bodies do
        let mut bodyEnd := r.pos
        if kind == .integral then
          if let some dv := ctx.tok? bodyEnd then
            if dv.kind == .ident && vars.any (fun v => dv.text == "d" ++ v) then
              bodyEnd := bodyEnd + 1
        let sp := ctx.range pos bodyEnd
        let node := bs.foldr (fun b acc => Ast.mkAgg kind b acc sp) r.ast
        out := out ++ [{ ast := node, pos := bodyEnd, cost := bcost + r.cost + extra }]
  return prune ctx.maxPerEnd out

/-- Comma-separated binder specifications up to `closing`. -/
partial def parseBinders (ctx : PCtx) (locals : Array String) (pos : Nat) (closing : TokKind) :
    P (List (Array BinderSpec × Nat × Nat)) := do
  let firsts ← parseBinder ctx locals pos
  let mut out : List (Array BinderSpec × Nat × Nat) := []
  for (b, p, c) in firsts do
    if (ctx.kindAt p) == some closing then
      out := out ++ [(#[b], p + 1, c)]
    else if (ctx.kindAt p) == some .comma then
      for (rest, p2, c2) in ← parseBinders ctx locals (p + 1) closing do
        out := out ++ [(#[b] ++ rest, p2, c + c2)]
  return out.take 4

/-- One binder: `k=0..n`, `k=0`, `k>=1`, `k<=n`, `d|n`, or `0<=k<=n` with the variable in the
middle. Both shapes are offered; the caller keeps whichever ends at the closing bracket. -/
partial def parseBinder (ctx : PCtx) (locals : Array String) (pos : Nat) :
    P (List (BinderSpec × Nat × Nat)) := do
  let bound (p : Nat) : P (List Res) := parseOperand ctx locals p (relPrec + 1)
  let mut out : List (BinderSpec × Nat × Nat) := []
  match ctx.tok? pos, ctx.tok? (pos + 1) with
  | some v, some o =>
    if v.kind == .ident then
      let var := v.text
      if o.isOp "=" then
        for lo in ← bound (pos + 2) do
          if (ctx.tok? lo.pos).any (·.isOp "..") then
            for hi in ← bound (lo.pos + 1) do
              out := out ++ [({ var, lo := some lo.ast, hi := some hi.ast }, hi.pos,
                              lo.cost + hi.cost)]
          else
            out := out ++ [({ var, lo := some lo.ast }, lo.pos, lo.cost)]
      else if o.isOp ">=" || o.isOp ">" then
        for lo in ← bound (pos + 2) do
          out := out ++ [({ var, lo := some lo.ast, loStrict := o.isOp ">" }, lo.pos, lo.cost)]
      else if o.isOp "<=" || o.isOp "<" then
        for hi in ← bound (pos + 2) do
          out := out ++ [({ var, hi := some hi.ast, hiStrict := o.isOp "<" }, hi.pos, hi.cost)]
      else if o.isOp "|" then
        for n in ← bound (pos + 2) do
          out := out ++ [({ var, divisorOf := some n.ast }, n.pos, n.cost)]
  | _, _ => pure ()
  -- `lo <= k <= hi`
  for lo in ← bound pos do
    match ctx.tok? lo.pos, ctx.tok? (lo.pos + 1), ctx.tok? (lo.pos + 2) with
    | some r1, some mid, some r2 =>
      if (r1.isOp "<=" || r1.isOp "<") && mid.kind == .ident &&
          (r2.isOp "<=" || r2.isOp "<") then
        for hi in ← bound (lo.pos + 3) do
          out := out ++ [({ var := mid.text, lo := some lo.ast, hi := some hi.ast,
                            loStrict := r1.isOp "<", hiStrict := r2.isOp "<" }, hi.pos,
                          lo.cost + hi.cost)]
    | _, _, _ => pure ()
  return out

end

/-- All readings of an expression starting at token `pos`, one per end position. -/
def parseFrom (ctx : PCtx) (pos : Nat) : List Res :=
  (parseExpr ctx #[] pos 0).run' {}

/-- Convenience entry point for tests: parse a whole string as one expression. -/
def parseAll (cls : Classifier) (s : String) : Input × Array Token × List Res :=
  let inp := Input.ofString s
  let toks := Lexer.tokenize inp
  let cls := { cls with prescan := Prescan.run toks }
  let ctx : PCtx := { inp, toks, cls }
  (inp, toks, parseFrom ctx 0)

end
end GenExpr.Raw
