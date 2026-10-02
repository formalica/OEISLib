import GenExpr.Registry
import GenExpr.Ast

/-!
Typed expressions.

Every node carries a concrete type and, where it stands for a Lean term, the `Alt` that was
chosen. Casts are explicit and — by the transparency rule in `GenExpr.Registry` — only ever wrap
a leaf or an opaque result.
-/

namespace GenExpr

inductive TExpr where
  /-- A numeral, elaborated directly at `ty` rather than cast into it. -/
  | lit (text : String) (ty : Ty)
  | dec (whole frac : String) (ty : Ty)
  | var (name : String) (ty : Ty)
  | cast (src dst : Ty) (e : TExpr)
  | node (alt : Alt) (args : Array TExpr)
  | agg (kind : AggKind) (var : String) (lo hi dv : Option TExpr) (loStrict hiStrict : Bool)
      (body : TExpr) (ty : Ty)
deriving Repr, BEq

instance : Inhabited TExpr := ⟨.lit "0" .nat⟩

namespace TExpr

def ty : TExpr → Ty
  | .lit _ t | .dec _ _ t | .var _ t => t
  | .cast _ d _ => d
  | .node a _ => a.result
  | .agg _ _ _ _ _ _ _ _ t => t

/-- Numerals elaborate at any numeric type, so casting one is never the cheaper reading. -/
def isLiteral : TExpr → Bool
  | .lit .. | .dec .. => true
  | _ => false

partial def children : TExpr → Array TExpr
  | .lit .. | .dec .. | .var .. => #[]
  | .cast _ _ e => #[e]
  | .node _ args => args
  | .agg _ _ lo hi dv _ _ body _ => (#[lo, hi, dv].filterMap id).push body

partial def alts : TExpr → Array Alt
  | .node a args => args.foldl (fun acc x => acc ++ alts x) #[a]
  | e => (children e).foldl (fun acc x => acc ++ alts x) #[]

private def dedup (xs : Array String) : Array String :=
  xs.foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]

def imports (e : TExpr) : Array String := dedup ((e.alts.map (·.imports)).flatten)

/-- Every type some node of the term has, cast sources included. -/
partial def types (e : TExpr) : Array Ty :=
  let here := match e with
    | .cast s d _ => #[s, d]
    | x => #[x.ty]
  (children e).foldl (fun acc x => acc ++ types x) here

/-- Each aggregator as `(kind, has an upper bound, ranges over divisors)`. -/
partial def aggregators : TExpr → Array (AggKind × Bool × Bool)
  | e@(.agg k _ _ hi dv _ _ _ _) =>
    (children e).foldl (fun acc x => acc ++ aggregators x) #[(k, hi.isSome, dv.isSome)]
  | e => (children e).foldl (fun acc x => acc ++ aggregators x) #[]

def opens (e : TExpr) : Array String := dedup ((e.alts.map (·.opens)).flatten)

/-- Whether the term can be evaluated, as opposed to merely elaborated. -/
partial def computable : TExpr → Bool
  | .lit _ t | .dec _ _ t | .var _ t => t.isComputable
  | .cast _ d e => d.isComputable && computable e
  | .node a args => a.computable && args.all computable
  -- An unbounded sum is a `tsum` and an integral has no upper bound of this shape; neither runs.
  | .agg _ _ lo hi dv _ _ body t =>
    t.isComputable && (hi.isSome || dv.isSome) &&
      ((#[lo, hi, dv].filterMap id).all computable) && computable body

partial def size : TExpr → Nat
  | e => (children e).foldl (fun acc x => acc + size x) 1

/-- Debug rendering; the Lean printer lives in `GenExpr.Render`. -/
partial def format : TExpr → String
  | .lit t ty => s!"{t}:{ty}"
  | .dec w f ty => s!"{w}.{f}:{ty}"
  | .var n ty => s!"{n}:{ty}"
  | .cast s d e => s!"({format e} : {s}→{d})"
  | .node a args =>
    if args.isEmpty then a.template
    else a.template ++ "[" ++ String.intercalate ", " (args.toList.map format) ++ "]"
  | .agg k v lo hi dv _ _ body ty =>
    let dom := match dv, lo, hi with
      | some d, _, _ => s!"{v}|{format d}"
      | none, some l, some h => s!"{v}={format l}..{format h}"
      | none, some l, none => s!"{v}>={format l}"
      | _, _, _ => v
    s!"{k}:{ty}\{{dom}}(" ++ format body ++ ")"

instance : ToString TExpr := ⟨format⟩

end TExpr

end GenExpr
