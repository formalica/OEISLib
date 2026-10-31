module
public import Scripts.Templates.LinearRecurrence.Programs
public meta import Scripts.Templates.LinearRecurrence.Programs

/-!
Recurrences in Python/Sage and Haskell programs:

* Python   `def a(n): if n < 2: return n` / `return a(n-1) + a(n-2)` (any `if`/`elif`/`else` ladder
           of returns, also `return x if c else y`), `a = lambda n: …`, and the list idiom
           `a = [1, 1]` followed by `for i in range(2, N): a.append(a[-1] + a[-2])`
* Haskell  clauses `a 0 = 1`, `a 1 = 2`, `a n = 3 * a (n-1) - a (n-2)`, and the stream
           `fibs = 0 : 1 : zipWith (+) fibs (tail fibs)`

The function bodies are read into the same branch trees as in `Programs`.
-/

namespace Oeis.Template.LinearRecurrence
public section

open Recognize

/-! ## Lines -/

structure Line where
  /-- Character offset of the line in the text. -/
  start : Nat
  chars : Array Char
  indent : Nat
  deriving Inhabited

def linesOf (text : String) : Array Line := Id.run do
  let mut out : Array Line := #[]
  let mut pos := 0
  for l in text.splitOn "\n" do
    let cs := chars l
    let indent := (cs.toList.takeWhile fun c => c == ' ' || c == '\t').length
    out := out.push { start := pos, chars := cs, indent }
    pos := pos + cs.size + 1
  return out

/-- The code of a line: without a trailing comment (`marker`) and trailing white space. -/
def Line.code (l : Line) (marker : String) : Array Char := Id.run do
  let cut := (List.range l.chars.size).find? (startsAt l.chars · marker)
  let cs := match cut with | some i => l.chars.extract 0 i | none => l.chars
  let mut n := cs.size
  while n > 0 && cs[n - 1]!.isWhitespace do n := n - 1
  return cs.extract 0 n

private def Line.blank (l : Line) (marker : String) : Bool := (l.code marker).all Char.isWhitespace

/-! ## Python -/

/-- `x`, or `x if c else y`, where `x` may be a list element `[1, 3][n-1]`. -/
partial def pyExpr (d : Dialect) (a : Array Char) (i : Nat) : Except String (BExpr × Nat) := do
  let (x, j) ← parseLeaf d #[] a i
  match identAt? a (skipWs a j) with
  | some ("if", k) =>
    let some (c, m) := parseCond d a k | throw "the condition is not a comparison of n"
    let m ← expectWord a m "else"
    let (e, n) ← pyExpr d a m
    return (.ite c x e, n)
  | _ => return (x, j)

/-- `return expr` filling the rest of the line. -/
private def pyReturn (d : Dialect) (a : Array Char) (i : Nat) : Except String BExpr := do
  let j ← expectWord a i "return"
  let (b, e) ← pyExpr d a j
  if skipWs a e < a.size then throw "something follows the returned expression"
  return b

/-- The returns of a function body as one tree: the `if`/`elif`/`else` ladder, then the final
`return`. `body` are the code lines, in order; indentation is not used, because the stored
programs have lost it. -/
private def pyLadder (d : Dialect) (body : Array (Array Char)) : Except String BExpr := do
  let mut branches : Array (Option Cond × BExpr) := #[]
  let mut i := 0
  while i < body.size do
    let code := body[i]!
    let k := skipWs code 0
    match identAt? code k with
    | some (kw, j) =>
      if kw == "if" || kw == "elif" then
        let some (c, m) := parseCond d code j | throw "the condition is not a comparison of n"
        let m ← expectChar code m ':'
        if skipWs code m < code.size then
          branches := branches.push (some c, ← pyReturn d code m)
        else
          let some next := body[i + 1]? | throw "the branch has no body"
          branches := branches.push (some c, ← pyReturn d next 0)
          i := i + 1
      else if kw == "else" then
        let m ← expectChar code j ':'
        if skipWs code m < code.size then
          branches := branches.push (none, ← pyReturn d code m)
        else
          let some next := body[i + 1]? | throw "the branch has no body"
          branches := branches.push (none, ← pyReturn d next 0)
          i := i + 1
        break
      else if kw == "return" then
        branches := branches.push (none, ← pyReturn d code k)
        break
      else throw s!"a statement `{kw}` that is not a return"
    | none => throw "a statement that is not a return"
    i := i + 1
  let some (none, last) := branches.back? | throw "the function does not end with an unconditional return"
  return branches.pop.foldr (init := last) fun (c, e) acc =>
    match c with
    | some c => .ite c e acc
    | none => acc

/-- `def name(var):` possibly followed by the first statement: `(name, var, where it starts)`. -/
private def pyHead (a : Array Char) : Option (String × String × Nat) := do
  let k := skipWs a 0
  let (kw, j) ← identAt? a k
  guard (kw == "def")
  let (name, e) ← identAt? a (skipWs a j)
  guard (a[e]? == some '(')
  let (var, v) ← identAt? a (skipWs a (e + 1))
  let v := skipWs a v
  guard (a[v]? == some ')')
  let v := skipWs a (v + 1)
  guard (a[v]? == some ':')
  return (name, var, v + 1)

private def pyDialect (name var : String) : Dialect :=
  { syn := { names := #[name], var, powers := #["**", "^"] }, listBase := 0, tuples := true }

/-- Does a line continue a function body: the statements of a branch ladder. -/
private def pyBodyLine (code : Array Char) : Bool :=
  match identAt? code (skipWs code 0) with
  | some (w, _) => w == "if" || w == "elif" || w == "else" || w == "return"
  | none => false

/-- `NAME = [1, 1]` -/
private def pyList (a : Array Char) : Option (String × Array Int) := do
  let (name, j) ← identAt? a (skipWs a 0)
  let k := skipWs a j
  guard (a[k]? == some '=' && a[k + 1]? != some '=')
  let m := skipWs a (k + 1)
  guard (a[m]? == some '[')
  let (vs, e) ← intListBr a (m + 1) #[]
  guard (skipWs a e ≥ a.size)
  return (name, vs)

/-- `for i in range(…):` with an optional body on the same line: where the body starts. -/
private def pyFor (a : Array Char) : Option (String × Nat) := do
  let (kw, j) ← identAt? a (skipWs a 0)
  guard (kw == "for")
  let (var, e) ← identAt? a (skipWs a j)
  let e ← (expectWord a e "in").toOption
  guard (startsAt a (skipWs a e) "range")
  let colon ← (List.range a.size).find? fun i => a[i]! == ':' && i > e
  return (var, colon + 1)

/-- `NAME.append(expr)` filling the line from `i`: the lags of the new element. -/
private def pyAppend (name var : String) (a : Array Char) (i : Nat) : Option Lin := do
  let (n, j) ← identAt? a (skipWs a i)
  guard (n == name && a[j]? == some '.')
  let (m, k) ← identAt? a (j + 1)
  guard (m == "append" && a[k]? == some '(')
  let syn : Syn := { names := #[name], openC := '[', closeC := ']', negIndex := true, var }
  let (l, e) ← (parseExpr syn a (k + 1)).toOption
  guard (a[skipWs a e]? == some ')' && skipWs a (e + 1) ≥ a.size)
  return l

def scanPython (offset : Int) (count : Nat) (text : String) : Array Raw × Array String := Id.run do
  let ls := linesOf text
  let mut found : Array Raw := #[]
  let mut why : Array String := #[]
  let mut li := 0
  while li < ls.size do
    let line := ls[li]!
    let code := line.code "#"
    if let some (name, var, rest) := pyHead code then
      -- the body: the rest of the line, then the lines that are branch statements or are
      -- indented deeper than the `def`
      let mut body : Array (Array Char) := #[]
      let mut last := li
      let inline := code.extract rest code.size
      unless inline.all Char.isWhitespace do body := body.push inline
      let mut k := li + 1
      while k < ls.size && (ls[k]!.blank "#" || ls[k]!.indent > line.indent ||
          pyBodyLine (ls[k]!.code "#")) do
        unless ls[k]!.blank "#" do
          body := body.push (ls[k]!.code "#")
          last := k
        k := k + 1
      let d := pyDialect name var
      match pyLadder d body with
      | .ok b =>
        match b.analyze offset offset count with
        | .ok (r, vals) =>
          found := found.push
            { recur := r, claim := if vals.isEmpty then .none else .values vals,
              start := line.start + line.indent,
              stop := ls[last]!.start + (ls[last]!.code "#").size, flavor := "python-def" }
        | .error e => why := why.push e
      | .error e => why := why.push e
      li := last + 1
      continue
    -- a = [1, 1] / for i in range(2, N): a.append(a[-1] + a[-2])
    if let some (name, init) := pyList code then
      let mut k := li + 1
      while k < ls.size && ls[k]!.blank "#" do k := k + 1
      if let some forLine := ls[k]? then
        let fc := forLine.code "#"
        if let some (var, after) := pyFor fc then
          let inline := !(fc.extract after fc.size).all Char.isWhitespace
          let appendIn : Option (Array Char × Nat × Nat) :=
            if inline then some (fc, after, k)
            else
              (List.range (ls.size - (k + 1))).findSome? fun d =>
                let l := ls[k + 1 + d]!
                if l.blank "#" then none else some (l.code "#", 0, k + 1 + d)
          if let some (ac, from_, lastLine) := appendIn then
            if let some l := pyAppend name var ac from_ then
              -- lags: `a[-j]` is shift `-j`, `a[i-j]` is shift `-j` of the new element
              match (({ terms := #[(0, 1)] } : Lin).sub l).toRec with
              | .ok r =>
                let vals := (init.mapIdx fun i v => (offset + i, v))
                found := found.push
                  { recur := r, claim := .values vals, start := line.start + line.indent,
                    stop := ls[lastLine]!.start + (ls[lastLine]!.code "#").size,
                    flavor := "python-list" }
                li := lastLine + 1
                continue
              | .error e => why := why.push e
    li := li + 1
  return (found, why)

/-! ## Haskell -/

/-- `a 0 = 1`: a base clause. -/
private def hsBase (name : String) (a : Array Char) : Option (Int × Int) := do
  let (n, j) ← identAt? a (skipWs a 0)
  guard (n == name)
  let (idx, k) ← intAt? a j
  let k := skipWs a k
  guard (a[k]? == some '=' && a[k + 1]? != some '=')
  let (v, e) ← intAt? a (k + 1)
  guard (skipWs a e ≥ a.size)
  return (idx, v)

/-- `a n = expr`: the variable and the linear form. -/
private def hsStep (name : String) (a : Array Char) : Option Lin := do
  let (n, j) ← identAt? a (skipWs a 0)
  guard (n == name)
  let (var, k) ← identAt? a (skipWs a j)
  let k := skipWs a k
  guard (a[k]? == some '=' && a[k + 1]? != some '=')
  let (l, e) ← (parseExpr { names := #[name], var } a (k + 1)).toOption
  guard (skipWs a e ≥ a.size)
  return l

/-- `fibs = 0 : 1 : zipWith (+) fibs (tail fibs)`. -/
private def hsStream (a : Array Char) : Option (String × Array Int) := do
  let (name, j) ← identAt? a (skipWs a 0)
  let k := skipWs a j
  guard (a[k]? == some '=')
  let mut vals : Array Int := #[]
  let mut at_ := k + 1
  for _ in [0:64] do
    match intAt? a at_ with
    | some (v, e) =>
      let e := skipWs a e
      if a[e]? == some ':' then
        vals := vals.push v
        at_ := e + 1
      else break
    | none => break
  let p ← (expectWord a at_ "zipWith").toOption
  let p ← (expectChar a p '(').toOption
  let p ← (expectChar a p '+').toOption
  let p ← (expectChar a p ')').toOption
  let p ← (expectWord a p name).toOption
  let rest := slice a (skipWs a p) a.size |>.trimAscii.toString
  guard (rest == s!"(tail {name})" || rest == s!"(tail  {name})" || rest == s!"(tail {name} )")
  guard (vals.size ≥ 2)
  return (name, vals)

def scanHaskell (offset : Int) (_count : Nat) (text : String) : Array Raw × Array String :=
  Id.run do
  let ls := linesOf text
  let mut found : Array Raw := #[]
  let mut li := 0
  while li < ls.size do
    let line := ls[li]!
    let code := line.code "--"
    if let some (_, vals) := hsStream code then
      let m := vals.size
      let coeffs := ((Array.replicate m (0 : Int)).set! (m - 1) 1).set! (m - 2) 1
      found := found.push
        { recur := ⟨coeffs⟩, claim := .values (vals.mapIdx fun i v => (offset + i, v)),
          start := line.start + line.indent, stop := line.start + code.size,
          flavor := "haskell-stream" }
    -- clauses: base cases, then the step; all for one name, one after the other
    if let some (name, _) := identAt? code (skipWs code 0) then
      if let some l := hsStep name code then
        -- the base clauses just above, directly adjacent
        let mut first := li
        let mut vals : Array (Int × Int) := #[]
        while first > 0 && (hsBase name ((ls[first - 1]!).code "--")).isSome do
          first := first - 1
          vals := vals.push (hsBase name ((ls[first]!).code "--")).get!
        match (({ terms := #[(0, 1)] } : Lin).sub l).toRec with
        | .ok r =>
          found := found.push
            { recur := r, claim := if vals.isEmpty then .none else .values vals,
              start := ls[first]!.start + ls[first]!.indent, stop := line.start + code.size,
              flavor := "haskell-clauses" }
        | .error _ => pure ()
    li := li + 1
  return (found, #[])

end
end Oeis.Template.LinearRecurrence
