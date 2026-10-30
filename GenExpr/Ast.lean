module
public import GenExpr.Types
public meta import GenExpr.Types

/-!
Syntax-neutral abstract syntax tree.

Every frontend (raw OEIS text now; LaTeX and Wolfram later) produces this type, and every later
stage consumes it, so `Ast` is the extension point for new surface syntaxes.

Two deliberate absences:

* there is no ambiguity node — the parser returns a costed *list* of alternatives per token range
  instead, which is also what the segmentation DP needs;
* implicit multiplication is an ordinary `.mul`, since nothing downstream benefits from knowing
  that the `*` was not written out.
-/

namespace GenExpr
public section

inductive BinOp where
  | add | sub | mul | div | pow | mod
deriving DecidableEq, Repr, Inhabited, BEq, Hashable

namespace BinOp

def symbol : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .pow => "^" | .mod => "mod"

/-- Registry key of the operator; `mod` renders as Lean's `%`. -/
def key : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .pow => "^" | .mod => "%"

instance : ToString BinOp := ⟨symbol⟩

end BinOp

inductive UnOp where
  | neg | abs
deriving DecidableEq, Repr, Inhabited, BEq, Hashable

inductive RelOp where
  | eq | ne | lt | le | gt | ge | divides
deriving DecidableEq, Repr, Inhabited, BEq, Hashable

namespace RelOp

def symbol : RelOp → String
  | .eq => "=" | .ne => "<>" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .divides => "|"

def ofString : String → Option RelOp
  | "=" | "==" => some .eq
  | "!=" | "<>" => some .ne
  | "<" => some .lt
  | "<=" => some .le
  | ">" => some .gt
  | ">=" => some .ge
  | "|" => some .divides
  | _ => none

instance : ToString RelOp := ⟨symbol⟩

end RelOp

inductive AggKind where
  | sum | prod | integral
deriving DecidableEq, Repr, Inhabited, BEq, Hashable

namespace AggKind

def name : AggKind → String
  | .sum => "sum" | .prod => "prod" | .integral => "int"

instance : ToString AggKind := ⟨name⟩

end AggKind

/-- The binder of an aggregator is inlined into `Ast.agg` to keep `Ast` a single inductive;
`Ast.mkAgg` / `Ast.binder?` provide the record view. Several binders nest as several `agg` nodes. -/
inductive Ast where
  | num (value : Nat) (sp : Span)
  /-- `1.25`, kept as its digit groups so it can be rendered exactly at any type. -/
  | dec (whole frac : String) (sp : Span)
  | ident (name : String) (sp : Span)
  /-- `f(a, b)`. A subscript is desugared into the first argument: `log_2(n)` is `log(2, n)`. -/
  | app (head : String) (args : Array Ast) (sp : Span)
  | un (op : UnOp) (e : Ast) (sp : Span)
  | bin (op : BinOp) (l r : Ast) (sp : Span)
  /-- `n!` is `count = 1`, `n!!` is `count = 2`; which function that means is a registry choice. -/
  | fact (count : Nat) (e : Ast) (sp : Span)
  | agg (kind : AggKind) (var : String) (lo hi : Option Ast) (loStrict hiStrict : Bool)
      (divisorOf : Option Ast) (body : Ast) (sp : Span)
  /-- A relation chain: `a = b = c` is `rel a [(eq, b), (eq, c)]`. -/
  | rel (head : Ast) (rest : Array (RelOp × Ast)) (sp : Span)
deriving Repr, Inhabited, BEq

/-- Record view of an aggregator binder. -/
structure BinderSpec where
  var : String
  lo : Option Ast := none
  hi : Option Ast := none
  loStrict : Bool := false
  hiStrict : Bool := false
  divisorOf : Option Ast := none
deriving Repr, Inhabited, BEq

namespace Ast

def mkAgg (kind : AggKind) (b : BinderSpec) (body : Ast) (sp : Span) : Ast :=
  .agg kind b.var b.lo b.hi b.loStrict b.hiStrict b.divisorOf body sp

def binder? : Ast → Option BinderSpec
  | .agg _ var lo hi loStrict hiStrict divisorOf _ _ =>
      some { var, lo, hi, loStrict, hiStrict, divisorOf }
  | _ => none

def span : Ast → Span
  | .num _ sp | .dec _ _ sp | .ident _ sp | .app _ _ sp | .un _ _ sp | .bin _ _ _ sp
  | .fact _ _ sp | .agg _ _ _ _ _ _ _ _ sp | .rel _ _ sp => sp

def withSpan (sp : Span) : Ast → Ast
  | .num v _ => .num v sp
  | .dec w f _ => .dec w f sp
  | .ident n _ => .ident n sp
  | .app h args _ => .app h args sp
  | .un o e _ => .un o e sp
  | .bin o l r _ => .bin o l r sp
  | .fact k e _ => .fact k e sp
  | .agg k v lo hi ls hs dv b _ => .agg k v lo hi ls hs dv b sp
  | .rel h rest _ => .rel h rest sp

/-- Extends a relation chain, so that `a = b = c` is one node rather than nested ones. -/
def appendRel (lhs : Ast) (op : RelOp) (rhs : Ast) (sp : Span) : Ast :=
  match lhs with
  | .rel h rest _ => .rel h (rest.push (op, rhs)) sp
  | _ => .rel lhs #[(op, rhs)] sp

/-- A lone number or name carries no formula and is never worth reporting. -/
def isAtom : Ast → Bool
  | .num .. | .dec .. | .ident .. => true
  | _ => false

/-- Whether the tree contains an operator, relation or aggregator. A fragment without one — a
lone name, or a bare call like `A(x)` — states nothing, however well formed it is. -/
partial def hasStructure : Ast → Bool
  | .num .. | .dec .. | .ident .. => false
  | .un .. | .bin .. | .fact .. | .agg .. | .rel .. => true
  | .app _ args _ => args.any hasStructure

partial def children : Ast → Array Ast
  | .num .. | .dec .. | .ident .. => #[]
  | .app _ args _ => args
  | .un _ e _ | .fact _ e _ => #[e]
  | .bin _ l r _ => #[l, r]
  | .agg _ _ lo hi _ _ dv body _ => #[lo, hi, dv].filterMap id |>.push body
  | .rel h rest _ => rest.map (·.2) |>.insertIdx 0 h

/-- Fully parenthesised rendering, used as the golden form in parser tests. -/
partial def format : Ast → String
  | .num v _ => toString v
  | .dec w f _ => s!"{w}.{f}"
  | .ident n _ => n
  | .app h args _ => h ++ "(" ++ String.intercalate ", " (args.toList.map format) ++ ")"
  | .un .neg e _ => "(-" ++ format e ++ ")"
  | .un .abs e _ => "|" ++ format e ++ "|"
  | .fact k e _ => "(" ++ format e ++ String.ofList (List.replicate k '!') ++ ")"
  | .bin op l r _ => "(" ++ format l ++ " " ++ op.symbol ++ " " ++ format r ++ ")"
  | .agg k var lo hi loS hiS dv body _ =>
      let dom :=
        match dv, lo, hi with
        | some d, _, _ => s!"{var}|{format d}"
        | none, some l, some h =>
            let lop := if loS then "<" else "<="
            let hop := if hiS then "<" else "<="
            s!"{format l}{lop}{var}{hop}{format h}"
        | none, some l, none => s!"{var}>{if loS then "" else "="}{format l}"
        | none, none, some h => s!"{var}<{if hiS then "" else "="}{format h}"
        | none, none, none => var
      s!"{k}\{{dom}}(" ++ format body ++ ")"
  | .rel h rest _ =>
      "(" ++ format h ++
        String.join (rest.toList.map fun (op, e) => " " ++ op.symbol ++ " " ++ format e) ++ ")"

instance : ToString Ast := ⟨format⟩

end Ast

end
end GenExpr
