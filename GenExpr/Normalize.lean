module
public import GenExpr.Typed
public meta import GenExpr.Typed

/-!
Rewrites applied to a typed expression before it is either evaluated or printed.

Keeping them here rather than in the printer is what makes "what we check" and "what we emit" the
same term: `GenExpr.Infer` normalises every typing it produces, so the interpreter and the
renderer never see different arithmetic.
-/

namespace GenExpr
public section

private def isKey (a : Alt) (k : String) : Bool := a.key == k

/-- Left-spine flatten of a `+`/`-` chain into positive and negative terms. Only the left spine,
because `a + (b - c)` is genuinely not `a + b - c` over `ℕ`. -/
private partial def signedTerms : TExpr → Array TExpr × Array TExpr
  | e@(.node a args) =>
    if args.size != 2 then (#[e], #[])
    else if isKey a "+" then
      let (p, n) := signedTerms args[0]!
      (p.push args[1]!, n)
    else if isKey a "-" then
      let (p, n) := signedTerms args[0]!
      (p, n.push args[1]!)
    else (#[e], #[])
  | e => (#[e], #[])

private partial def factors : TExpr → Array TExpr × Array TExpr
  | e@(.node a args) =>
    if args.size != 2 then (#[e], #[])
    else if isKey a "*" then
      let (n, d) := factors args[0]!
      (n.push args[1]!, d)
    else if isKey a "/" then
      let (n, d) := factors args[0]!
      (n, d.push args[1]!)
    else (#[e], #[])
  | e => (#[e], #[])

private def rebuild (op : Alt) (xs : Array TExpr) (init : TExpr) : TExpr :=
  xs.foldl (fun acc x => .node op #[acc, x]) init

/-- Additions before subtractions and multiplications before divisions, wherever the value is a
natural number. Over `ℕ`, `3*n^2 - 7*n + 6` is wrong at `n = 1` and `3*n^2 + 6 - 7*n` is not. -/
partial def normalizeNat (e : TExpr) : TExpr :=
  let e : TExpr := match e with
    | .node a args => .node a (args.map normalizeNat)
    | .cast s d x => .cast s d (normalizeNat x)
    | .agg k v lo hi dv ls hs b t =>
      .agg k v (lo.map normalizeNat) (hi.map normalizeNat) (dv.map normalizeNat) ls hs
        (normalizeNat b) t
    | x => x
  match e with
  | .node a _ =>
    if a.result != .nat then e
    else if isKey a "+" || isKey a "-" then
      let (pos, neg) := signedTerms e
      if neg.isEmpty || pos.isEmpty then e
      else
        let add := { a with key := "+", template := "{0} + {1}" }
        let sub := { a with key := "-", template := "{0} - {1}" }
        rebuild sub neg (rebuild add pos[1:].toArray pos[0]!)
    else if isKey a "*" || isKey a "/" then
      let (num, den) := factors e
      if den.isEmpty || num.isEmpty then e
      else
        let mul := { a with key := "*", template := "{0} * {1}" }
        let div := { a with key := "/", template := "{0} / {1}" }
        rebuild div den (rebuild mul num[1:].toArray num[0]!)
    else e
  | _ => e

/-- Replace a variable by an expression of the same type; used to shift an unbounded sum's index
so that `Sum_{k>=1} f(k)` becomes `∑' k, f (k+1)`. -/
partial def substVar (name : String) (repl : TExpr) : TExpr → TExpr
  | .var n t => if n == name && t == repl.ty then repl else .var n t
  | .cast s d e => .cast s d (substVar name repl e)
  | .node a args => .node a (args.map (substVar name repl))
  | .agg k v lo hi dv ls hs b t =>
    if v == name then .agg k v lo hi dv ls hs b t
    else
      .agg k v (lo.map (substVar name repl)) (hi.map (substVar name repl))
        (dv.map (substVar name repl)) ls hs (substVar name repl b) t
  | e => e

def natPlus (n : Nat) (e : TExpr) : TExpr :=
  .node { key := "+", template := "{0} + {1}", params := #[.nat, .nat], result := .nat,
          transparent := true, prec := 65, argPrec := #[65, 66] }
    #[e, .lit (toString n) .nat]

/-- `(n + k) - c` becomes `n + (k - c)`. Shifting a recursive definition past its base cases
produces such terms, and the arithmetic has to be done here rather than left to `omega`. -/
partial def simplifyOffsets (v : String) : TExpr → TExpr
  | .node sub args =>
    let args := args.map (simplifyOffsets v)
    let rebuilt := TExpr.node sub args
    if sub.key != "-" || args.size != 2 then rebuilt
    else
      match args[0]!, args[1]! with
      | .node add inner, .lit c _ =>
        if add.key != "+" || inner.size != 2 then rebuilt
        else
          match inner[0]!, inner[1]! with
          | .var n _, .lit k _ =>
            if n != v then rebuilt
            else
              let kk := k.toNat!
              let cc := c.toNat!
              if cc > kk then rebuilt
              else if cc == kk then .var v .nat
              else natPlus (kk - cc) (.var v .nat)
          | _, _ => rebuilt
      | _, _ => rebuilt
  | .cast s d e => .cast s d (simplifyOffsets v e)
  | .agg k b lo hi dv ls hs body t =>
    .agg k b (lo.map (simplifyOffsets v)) (hi.map (simplifyOffsets v))
      (dv.map (simplifyOffsets v)) ls hs (simplifyOffsets v body) t
  | e => e

end
end GenExpr
