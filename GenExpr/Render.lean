import GenExpr.Infer
import GenExpr.Normalize

/-!
Printing typed expressions as Lean source.

Two things happen here that are not simple traversal:

* **aggregator lowering.** A binder becomes a `Finset`, a `tsum` with a shifted index, or an
  interval integral, depending on its bounds;
* **cast placement.** A cast is written as an ascription, and a subtree of nothing but literals
  is ascribed once at its root so that Lean does not default it to `ℕ`.

The truncation-safe reordering that `ℕ` needs is *not* here: it is applied in `GenExpr.Infer`,
so that the interpreter and this printer always see the same term.

Bodies are emitted with `«self»` where the definition calls itself, so the same body can be
re-rendered under a different name.
-/

namespace GenExpr

/-- Placeholder standing for the name of the definition being built. -/
def selfToken : String := "«self»"

structure RenderStyle where
  /-- Emit `n !` (needs `open Nat`) instead of `Nat.factorial n`. -/
  postfixFactorial : Bool := false
deriving Inhabited

/-! ## Rendering -/

private def fill (template : String) (args : Array String) : String := Id.run do
  let mut out := template
  for i in [0:args.size] do
    out := out.replace s!"\{{i}}" args[i]!
  return out

private def paren (need : Bool) (s : String) : String := if need then "(" ++ s ++ ")" else s

/-- A subtree of nothing but numerals carries no type information of its own. -/
private partial def allLiterals : TExpr → Bool
  | .lit .. | .dec .. => true
  | .node a args => a.transparent && args.all allLiterals
  | _ => false

mutual

/-- `ctx` is the precedence of the position the term appears in. -/
partial def render (st : RenderStyle) (ctx : Nat) : TExpr → String
  | .lit t ty => paren (ty != .nat && ty.isNumeric && ctx > 1023) s!"{t}"
  | .dec w f ty => paren (ty != .rat) s!"{w}.{f}"
  | .var n _ => n
  | .cast _ d e => s!"({render st 0 e} : {d.render})"
  | e@(.node a args) =>
    -- One ascription pins an all-literal subtree that Lean would otherwise default to `ℕ`.
    if a.result != .nat && a.result.isNumeric && allLiterals e then
      s!"({fill a.template (renderArgs st a args)} : {a.result.render})"
    else paren (a.prec < ctx) (fill a.template (renderArgs st a args))
  | .agg kind v lo hi dv _ hiStrict body ty =>
    -- A big operator's body extends to the right, so an aggregator used as an operand always
    -- needs parentheses.
    paren (ctx > 0) (renderAgg st kind v lo hi dv hiStrict body ty)

partial def renderArgs (st : RenderStyle) (a : Alt) (args : Array TExpr) : Array String :=
  args.mapIdx fun i x => render st (a.argPrec[i]?.getD 1024) x

partial def renderAgg (st : RenderStyle) (kind : AggKind) (v : String) (lo hi dv : Option TExpr)
    (hiStrict : Bool) (body : TExpr) (ty : Ty) : String :=
  -- The body is the rightmost part, so it needs no precedence context of its own.
  match kind, dv, lo, hi with
  | _, some d, _, _ =>
    let sym := if kind == .prod then "∏" else "∑"
    s!"{sym} {v} ∈ Nat.divisors {render st 1024 d}, {render st 0 body}"
  | .integral, none, some l, some h =>
    s!"∫ {v} in ({render st 0 l} : ℝ)..{render st 0 h}, {render st 0 body}"
  | _, none, some l, some h =>
    let sym := if kind == .prod then "∏" else "∑"
    let set :=
      match l with
      | .lit "0" _ => if hiStrict then s!"Finset.range {render st 1024 h}"
                      else s!"Finset.range ({render st 65 h} + 1)"
      | _ => if hiStrict then s!"Finset.Ico {render st 1024 l} {render st 1024 h}"
             else s!"Finset.Icc {render st 1024 l} {render st 1024 h}"
    s!"{sym} {v} ∈ {set}, {render st 0 body}"
  | _, none, some l, none =>
    -- Unbounded: reindex from zero rather than guarding inside the body.
    let sym := if kind == .prod then "∏'" else "∑'"
    let shifted :=
      match l with
      | .lit "0" _ => body
      | .lit s _ => substVar v (natPlus (s.toNat!) (.var v .nat)) body
      | _ => body
    s!"{sym} {v} : ℕ, {render st 0 shifted}"
  | _, _, _, _ => s!"sorry -- unsupported {kind} over {ty.render}"

end

/-! ## Definitions -/

/-- Whether the body calls the definition being built. -/
partial def usesSelf : TExpr → Bool
  | .node a args => a.template.startsWith selfToken || args.any usesSelf
  | e => (TExpr.children e).any usesSelf

private def dedupStrings (xs : Array String) : Array String :=
  (xs.foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]).qsort (· < ·)

/-- Modules a term needs: those of its alternatives, of every type it mentions, and of the way
its aggregators are lowered. -/
def exprImports (e : TExpr) : Array String :=
  e.imports ++ (e.types.map Builtins.typeImports).flatten ++
    (e.aggregators.map fun (k, bounded, dv) => Builtins.aggImports k bounded dv).flatten

/-- Modules the declaration needs, sorted and without duplicates. -/
def typingImports (t : Typing) : Array String :=
  dedupStrings <|
    exprImports t.expr ++ (t.aux.map fun (_, ps, b) =>
      exprImports b ++ (ps.map fun (_, ty) => Builtins.typeImports ty).flatten).flatten ++
    (t.params.map fun (_, ty) => Builtins.typeImports ty).flatten ++ Builtins.typeImports t.ret

/-- The body alone, with `«self»` where the definition recurses. Stored as-is, so the same body
can later be re-rendered under a different name. -/
def renderBody (st : RenderStyle) (t : Typing) : String :=
  render st 0 t.expr

private def binders (t : Typing) : String :=
  String.join (t.params.toList.map fun (n, ty) => s!" ({n} : {ty.render})")

/-- A plain `def` for a name, used for auxiliary definitions found in the input. -/
def renderAux (st : RenderStyle) (name : String) (params : Array (String × Ty)) (body : TExpr) :
    String :=
  let bs := String.join (params.toList.map fun (n, ty) => s!" ({n} : {ty.render})")
  let kw := if body.computable then "def" else "noncomputable def"
  s!"{kw} {name}{bs} : {body.ty.render} :=\n  {render st 0 body}"

/-- A complete `def`. `patched` lists values supplied as base cases, keyed by their actual
arguments, so that data starting at index 1 is not mis-rendered as starting at 0. -/
def renderDef (st : RenderStyle) (t : Typing) (name : String)
    (patched : Array (Array Int × Int) := #[]) : String :=
  let body := (renderBody st t).replace selfToken name
  let sig := s!"{name}{binders t} : {t.ret.render}"
  let kw := if t.computable then "def" else "noncomputable def"
  let ty := String.intercalate " → " (t.params.toList.map (·.2.render) ++ [t.ret.render])
  let natArg := t.params.size == 1 && t.params[0]!.2 == .nat
  let v := (t.params[0]?.map (·.1)).getD "n"
  let lit (x : Int) : String := if x < 0 then s!"({x})" else toString x
  if patched.isEmpty then
    if usesSelf t.expr then
      s!"{kw} {sig} :=\n  {body}\ndecreasing_by all_goals simp_wf; omega"
    else s!"{kw} {sig} :=\n  {body}"
  else if natArg && usesSelf t.expr then
    -- Structural form: every index below the general case gets an arm, so the recursive call
    -- always lands on a smaller one. Indices outside the data get a junk value.
    let b := patched.foldl (fun m (a, _) => max m ((a[0]?.getD 0).toNat + 1)) 0
    let valueAt (i : Nat) : String :=
      match patched.find? fun (a, _) => a[0]? == some (i : Int) with
      | some (_, x) => lit x
      | none => "0"
    let arms := (List.range b).map fun i => s!"  | {i} => {valueAt i}"
    let shifted := simplifyOffsets v (substVar v (natPlus b (.var v .nat)) t.expr)
    let general := s!"  | {v} + {b} => " ++ (render st 0 shifted).replace selfToken name
    s!"{kw} {name} : {ty}\n" ++ String.intercalate "\n" (arms ++ [general])
  else if natArg then
    let arms := patched.toList.map fun (a, x) => s!"  | {a[0]!} => {lit x}"
    s!"{kw} {name} : {ty}\n" ++ String.intercalate "\n" (arms ++ [s!"  | {v} => {body}"])
  else
    let names := t.params.map (·.1)
    let cond (a : Array Int) : String :=
      String.intercalate " ∧ " ((Array.zip names a).toList.map fun (n, x) => s!"{n} = {lit x}")
    let chain := patched.foldr (fun (a, x) acc => s!"if {cond a} then {lit x} else {acc}") body
    s!"{kw} {sig} :=\n  {chain}"

end GenExpr
