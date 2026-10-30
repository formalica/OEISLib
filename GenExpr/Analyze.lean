module
public import GenExpr.Ast
public meta import GenExpr.Ast
public import GenExpr.Frontend.Raw.Prescan
public meta import GenExpr.Frontend.Raw.Prescan

/-!
Name analysis of a parsed fragment.

The segmenter needs to know, before any typing happens, whether a reading can possibly become a
formalization. Three properties decide it:

* an applied name that resolves to nothing is a **function hole** and can never be filled, so the
  reading is dead;
* an unresolved bare name is a **free variable**, and only as many of those as the requested
  signature can bind are acceptable;
* a reading with no **ground** content — no literal, no known function, no known constant — is
  prose that happens to parse, such as `Jean - Christophe`.
-/

namespace GenExpr
public section

open GenExpr.Raw

structure NameInfo where
  /-- Names that resolve to nothing at all. -/
  freeVars : Array String := #[]
  /-- Names bound as a parameter of some definition in the input. They are free in any fragment
  that is not that definition. -/
  paramVars : Array String := #[]
  funcHoles : Array String := #[]
  hasGround : Bool := false
deriving Inhabited, Repr

namespace NameInfo

private def union (a b : Array String) : Array String :=
  b.foldl (fun acc n => if acc.contains n then acc else acc.push n) a

def merge (a b : NameInfo) : NameInfo :=
  { freeVars := union a.freeVars b.freeVars
    paramVars := union a.paramVars b.paramVars
    funcHoles := union a.funcHoles b.funcHoles
    hasGround := a.hasGround || b.hasGround }

/-- Every name that has to be bound by the requested signature. -/
def unbound (i : NameInfo) : Array String := union i.freeVars i.paramVars

def ground : NameInfo := { hasGround := true }

end NameInfo

/-- `locals` are binders introduced by enclosing aggregators. -/
partial def nameInfo (cls : Classifier) (locals : Array String) : Ast → NameInfo
  | .num .. | .dec .. => .ground
  | .ident name _ =>
    match cls.classify locals name with
    | .var =>
      if locals.contains name then {}
      else if cls.prescan.params.contains name then { paramVars := #[name] }
      -- A catalogue constant such as `pi` is ground; a parameter carries no information.
      else .ground
    | .func => .ground
    | .unknown =>
      if cls.prescan.applied.contains name && !cls.prescan.bare.contains name then
        { funcHoles := #[name] }
      else { freeVars := #[name] }
  | .app head args _ =>
    let here : NameInfo :=
      match cls.classify locals head with
      | .func => .ground
      | _ => { funcHoles := #[head] }
    args.foldl (fun acc a => acc.merge (nameInfo cls locals a)) here
  | .un _ e _ | .fact _ e _ => nameInfo cls locals e
  | .bin _ l r _ => (nameInfo cls locals l).merge (nameInfo cls locals r)
  | .agg _ var lo hi _ _ dv body _ =>
    let inner := locals.push var
    let bounds := #[lo, hi, dv].filterMap id
    let acc := bounds.foldl (fun acc e => acc.merge (nameInfo cls locals e)) NameInfo.ground
    acc.merge (nameInfo cls inner body)
  | .rel h rest _ =>
    rest.foldl (fun acc (_, e) => acc.merge (nameInfo cls locals e)) (nameInfo cls locals h)

/-- `f(x, y) = rhs` or `c = rhs`: the head name and its parameter names, when the left-hand side
of a relation chain has that shape. -/
def definitionHead? : Ast → Option (String × Array String)
  | .rel h _ _ =>
    match h with
    | .ident name _ => some (name, #[])
    | .app name args _ =>
      if args.all (fun a => a matches .ident ..) then
        some (name, args.filterMap fun | .ident v _ => some v | _ => none)
      else none
    | _ => none
  | _ => none

/-- Every name the expression mentions, whether applied or bare, in order of first occurrence. -/
partial def referencedNames (e : Ast) : Array String :=
  go #[] e
where
  go (acc : Array String) : Ast → Array String
    | .num .. | .dec .. => acc
    | .ident n _ => if acc.contains n then acc else acc.push n
    | .app h args _ =>
      let acc := if acc.contains h then acc else acc.push h
      args.foldl go acc
    | .un _ x _ | .fact _ x _ => go acc x
    | .bin _ l r _ => go (go acc l) r
    | .agg _ _ lo hi _ _ dv body _ =>
      let acc := (#[lo, hi, dv].filterMap id).foldl go acc
      go acc body
    | .rel h rest _ => rest.foldl (fun a (_, x) => go a x) (go acc h)

/-- An integer literal, possibly negated. -/
def intLit? : Ast → Option Int
  | .num k _ => some (Int.ofNat k)
  | .un .neg e _ => (intLit? e).map (fun k => -k)
  | _ => none

/-- Number of nodes; how "big" a member of a relation chain is. -/
partial def astSize (e : Ast) : Nat := e.children.foldl (fun acc c => acc + astSize c) 1

/-- Every name used as a call head. -/
partial def appliedHeads (e : Ast) : Array String :=
  let here := match e with
    | .app h _ _ => #[h]
    | _ => #[]
  e.children.foldl (fun acc c => (appliedHeads c).foldl
    (fun a n => if a.contains n then a else a.push n) acc) here

end
end GenExpr
