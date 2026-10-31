module
public import Scripts.Templates.LinearRecurrence.Mathematica
public meta import Scripts.Templates.LinearRecurrence.Mathematica

/-!
Recurrences in programs written as a function with base cases:

* PARI/GP   `a(n)=if(n<2, n, a(n-1)+a(n-2))`, and `a(n)=if(n==0,1,if(n==1,2, …))`
* Maple     `a := proc(n) option remember; if n<2 then n else … fi end proc`, `a := n -> …`,
            ``a := n -> `if`(n<2, n, …)``, and `a(0):=0: a(1):=1: a(n):=…`
* Magma     `[n le 2 select 1 else Self(n-1)+Self(n-2) : n in [1..30]]`, also `I[n]` for a list `I`

The function body is a tree of conditions on `n` (`BExpr`). It is evaluated at every index of the
published terms: the leaves without a call give the base cases (checked against the data as the
claim `values`), and the leaves with calls must all be the same linear form, which is the
recurrence.
-/

namespace Oeis.Template.LinearRecurrence
public section

open Recognize

/-! ## Branch trees -/

inductive Cmp where
  | lt | le | eq | ne | gt | ge
  deriving BEq

/-- A disjunction of comparisons of `n` with a constant. -/
structure Cond where
  alts : Array (Cmp × Int)

def Cond.holds (c : Cond) (n : Int) : Bool :=
  c.alts.any fun (op, k) =>
    match op with
    | .lt => n < k | .le => n ≤ k | .eq => n == k | .ne => n != k | .gt => n > k | .ge => n ≥ k

inductive Leaf where
  | lin (l : Lin)
  /-- `vals[idx(n)]`, the list indexed from `base`. -/
  | list (vals : Array Int) (idx : Lin) (base : Int)

inductive BExpr where
  | leaf (l : Leaf)
  | ite (c : Cond) (t e : BExpr)

instance : Inhabited BExpr := ⟨.leaf (.lin {})⟩

def BExpr.eval : BExpr → Int → Leaf
  | .leaf l, _ => l
  | .ite c t e, n => if c.holds n then t.eval n else e.eval n

/-- Evaluates the tree for the published terms, the first term having `n = origin` (and the OEIS
index `offset`): the recurrence of the recursive leaves and the base cases of the others. -/
def BExpr.analyze (b : BExpr) (offset origin : Int) (count : Nat) :
    Except String (Rec × Array (Int × Int)) := do
  let mut body : Option Lin := none
  let mut vals : Array (Int × Int) := #[]
  for t in [0:count] do
    let n := origin + t
    match b.eval n with
    | .lin l =>
      if l.terms.isEmpty then vals := vals.push (offset + t, l.c + l.nc * n)
      else
        match body with
        | none => body := some l
        | some p => if p != l then throw "the recursive branches differ"
    | .list vs idx base =>
      let i := idx.c + idx.nc * n - base
      if i < 0 || i.toNat ≥ vs.size then throw "a list index is out of range"
      vals := vals.push (offset + t, vs[i.toNat]!)
  let some l := body | throw "there is no recursive branch"
  unless l.terms.all (·.1 < 0) do throw "a branch calls the function at a later index"
  let r ← (({ terms := #[(0, 1)] } : Lin).sub l).toRec
  return (r, vals)

/-! ## Parsing the pieces -/

structure Dialect where
  syn : Syn
  /-- Magma compares with words: `n le 2`. -/
  words : Bool := false
  /-- The index of the first element of a list: 1 in PARI, Maple and Magma, 0 in Python. -/
  listBase : Int := 1
  /-- `(1, 2, 3)[n]` is a list too (Python tuples). -/
  tuples : Bool := false

private def symbolicCmps : List (String × Cmp) :=
  [("<=", .le), (">=", .ge), ("==", .eq), ("!=", .ne), ("<>", .ne), ("<", .lt), (">", .gt),
   ("=", .eq)]

private def wordCmps : List (String × Cmp) :=
  [("le", .le), ("lt", .lt), ("eq", .eq), ("ne", .ne), ("gt", .gt), ("ge", .ge)]

private def parseCmp (words : Bool) (a : Array Char) (i : Nat) : Option (Cmp × Nat) :=
  if words then
    match identAt? a i with
    | some (w, j) => (wordCmps.lookup w).map (·, j)
    | none => none
  else (symbolicCmps.find? (startsAt a i ·.1)).map fun (s, c) => (c, i + s.length)

/-- `1, 1, 2]` (or `)`): the integers up to the closing character. -/
partial def intListWith (close : Char) (a : Array Char) (i : Nat) (acc : Array Int) :
    Option (Array Int × Nat) :=
  match intAt? a i with
  | none => none
  | some (v, j) =>
    let j := skipWs a j
    match a[j]? with
    | some ',' => intListWith close a (j + 1) (acc.push v)
    | some c => if c == close then some (acc.push v, j + 1) else none
    | none => none

/-- `1, 1, 2]`. -/
def intListBr (a : Array Char) (i : Nat) (acc : Array Int) : Option (Array Int × Nat) :=
  intListWith ']' a i acc

/-- `n < 2`, or `n in [0, 1]`: the comparisons it stands for. -/
private def parseCondAtom (d : Dialect) (a : Array Char) (i : Nat) :
    Option (Array (Cmp × Int) × Nat) := do
  let (name, j) ← identAt? a (skipWs a i)
  guard (name == d.syn.var)
  let j := skipWs a j
  match identAt? a j with
  | some ("in", k) =>
    let k := skipWs a k
    let close := if a[k]? == some '[' then ']' else ')'
    guard (a[k]? == some '[' || a[k]? == some '(')
    let (vs, e) ← intListWith close a (k + 1) #[]
    return (vs.map (Cmp.eq, ·), e)
  | _ =>
    let (op, k) ← parseCmp d.words a j
    let (v, e) ← intAt? a k
    return (#[(op, v)], e)

/-- `n < 2`, `n = 0 or n = 1`, `n==0 || n==1`, `n in [0, 1]`, each possibly in parentheses. -/
partial def parseCond (d : Dialect) (a : Array Char) (i : Nat) : Option (Cond × Nat) :=
  let i := skipWs a i
  if a[i]? == some '(' then
    match parseCond d a (i + 1) with
    | some (c, e) =>
      let e := skipWs a e
      if a[e]? == some ')' then
        -- `(n<2) or (n==3)` continues after the parenthesis
        parseCondMore d a c (e + 1)
      else none
    | none => none
  else do
    let (alts, e) ← parseCondAtom d a i
    parseCondMore d a ⟨alts⟩ e

where
  parseCondMore (d : Dialect) (a : Array Char) (c : Cond) (e : Nat) : Option (Cond × Nat) :=
    let j := skipWs a e
    let more : Option (Cond × Nat) :=
      if startsAt a j "||" then parseCond d a (j + 2)
      else
        match identAt? a j with
        | some ("or", k) => parseCond d a k
        | _ => none
    match more with
    | some (c', k) => some (⟨c.alts ++ c'.alts⟩, k)
    | none => some (c, e)

/-- `[1,1,2][n+1]` or `L[n]` for a known list `L`: the value of a list at an affine index. -/
def parseListLeaf (d : Dialect) (lists : Array (String × Array Int)) (a : Array Char) (i : Nat) :
    Option (Leaf × Nat) := do
  let i := skipWs a i
  let (vals, j) ←
    if a[i]? == some '[' then intListBr a (i + 1) #[]
    else if a[i]? == some '(' && d.tuples then intListWith ')' a (i + 1) #[]
    else do
      let (name, j) ← identAt? a i
      let (_, vs) ← lists.find? (·.1 == name)
      pure (vs, j)
  let j := skipWs a j
  guard (a[j]? == some '[')
  let (idx, k) ← (parseExpr { d.syn with names := #[] } a (j + 1)).toOption
  let k := skipWs a k
  guard (a[k]? == some ']' && idx.terms.isEmpty)
  return (.list vals idx d.listBase, k + 1)

def parseLeaf (d : Dialect) (lists : Array (String × Array Int)) (a : Array Char) (i : Nat) :
    Except String (BExpr × Nat) :=
  match parseListLeaf d lists a i with
  | some (l, j) => .ok (.leaf l, j)
  | none => do
    let (l, j) ← parseExpr d.syn a i
    return (.leaf (.lin l), j)

def expectChar (a : Array Char) (i : Nat) (c : Char) : Except String Nat :=
  let j := skipWs a i
  if a[j]? == some c then .ok (j + 1) else .error s!"expected `{c}`"

def expectWord (a : Array Char) (i : Nat) (w : String) : Except String Nat :=
  match identAt? a (skipWs a i) with
  | some (x, j) => if x == w then .ok j else .error s!"expected `{w}`"
  | none => .error s!"expected `{w}`"

/-! ## PARI/GP: `if(cond, then, else)` -/

partial def pariBranch (d : Dialect) (lists : Array (String × Array Int)) (a : Array Char)
    (i : Nat) : Except String (BExpr × Nat) := do
  let i := skipWs a i
  match identAt? a i with
  | some ("if", j) =>
    let o ← expectChar a j '('
    let some (c, k) := parseCond d a o | throw "the condition is not a comparison of n"
    let k ← expectChar a k ','
    let (t, k) ← pariBranch d lists a k
    let k ← expectChar a k ','
    let (e, k) ← pariBranch d lists a k
    let k ← expectChar a k ')'
    return (.ite c t e, k)
  | _ => parseLeaf d lists a i

/-- `name(var) = body`: the end of the body. -/
private def functionHead (a : Array Char) (i : Nat) : Option (String × String × Nat) := do
  let (name, j) ← identAt? a i
  guard (a[j]? == some '(')
  let (var, k) ← identAt? a (skipWs a (j + 1))
  let k ← (expectChar a k ')').toOption
  let k := skipWs a k
  guard (a[k]? == some '=' && a[k + 1]? != some '=')
  return (name, var, k + 1)

def scanPari (offset : Int) (count : Nat) (text : String) : Array Raw × Array String := Id.run do
  let a := chars (maskCredits text)
  let mut found : Array Raw := #[]
  let mut why : Array String := #[]
  for i in [0:a.size] do
    if i == 0 || !isIdChar a[i - 1]! then
      if let some (name, var, k) := functionHead a i then
        let d : Dialect := { syn := { names := #[name], var } }
        match pariBranch d #[] a k with
        | .error e => if e != "the expression ends early" then why := why.push e
        | .ok (b, e) =>
          match b.analyze offset offset count with
          | .ok (r, vals) =>
            found := found.push { recur := r, claim := if vals.isEmpty then .none else .values vals,
                                  start := i, stop := e, flavor := "pari-function" }
          | .error e => why := why.push e
  return (found, why)

/-! ## Maple -/

mutual

/-- `if c then e (elif c then e)* else e fi`, `` `if`(c, t, e) ``, or an expression. -/
partial def mapleBranch (d : Dialect) (lists : Array (String × Array Int)) (a : Array Char)
    (i : Nat) : Except String (BExpr × Nat) := do
  let i := skipWs a i
  if startsAt a i "`if`" then
    let o ← expectChar a (i + 4) '('
    let some (c, k) := parseCond d a o | throw "the condition is not a comparison of n"
    let k ← expectChar a k ','
    let (t, k) ← mapleBranch d lists a k
    let k ← expectChar a k ','
    let (e, k) ← mapleBranch d lists a k
    let k ← expectChar a k ')'
    return (.ite c t e, k)
  else
    match identAt? a i with
    | some ("if", j) => mapleIf d lists a j
    | some ("return", j) => mapleBranch d lists a j
    | _ => parseLeaf d lists a i

/-- A `;` after a branch. -/
partial def mapleSemi (a : Array Char) (i : Nat) : Nat :=
  let j := skipWs a i
  if a[j]? == some ';' then j + 1 else i

/-- After `if` or `elif`: `cond then expr` and the rest of the chain. -/
partial def mapleIf (d : Dialect) (lists : Array (String × Array Int)) (a : Array Char)
    (i : Nat) : Except String (BExpr × Nat) := do
  let some (c, k) := parseCond d a i | throw "the condition is not a comparison of n"
  let k ← expectWord a k "then"
  let (t, k) ← mapleBranch d lists a k
  let k := mapleSemi a k
  match identAt? a (skipWs a k) with
  | some ("elif", j) =>
    let (e, m) ← mapleIf d lists a j
    return (.ite c t e, m)
  | some ("else", j) =>
    let (e, m) ← mapleBranch d lists a j
    let m ← mapleEnd a (mapleSemi a m)
    return (.ite c t e, m)
  | _ => throw "an `if` without `else`"

/-- `fi` or `end if`. -/
partial def mapleEnd (a : Array Char) (i : Nat) : Except String Nat :=
  match identAt? a (skipWs a i) with
  | some ("fi", j) => .ok j
  | some ("end", j) => expectWord a j "if"
  | _ => .error "expected `fi`"

end

/-- `local x, y;` `option remember;` and a memoizing `name(var) :=` before the body. -/
private partial def mapleSkipPrelude (a : Array Char) (i : Nat) (name var : String) : Nat :=
  let j := skipWs a i
  match identAt? a j with
  | some (w, e) =>
    if w == "local" || w == "global" || w == "option" || w == "options" || w == "description" then
      match (List.range (a.size - e)).find? (fun k => a[e + k]! == ';') with
      | some k => mapleSkipPrelude a (e + k + 1) name var
      | none => j
    else if w == name then
      match expectChar a e '(' with
      | .ok o =>
        match identAt? a (skipWs a o) with
        | some (v, k) =>
          match expectChar a k ')' with
          | .ok k =>
            let k := skipWs a k
            if v == var && startsAt a k ":=" then k + 2 else j
          | .error _ => j
        | none => j
      | .error _ => j
    else j
  | none => j

/-- The end of `proc … end proc` / `end`. -/
private def mapleProcEnd (a : Array Char) (i : Nat) : Except String Nat := do
  let k := skipWs a i
  let k := if a[k]? == some ';' then k + 1 else k
  let j ← expectWord a k "end"
  match identAt? a (skipWs a j) with
  | some ("proc", e) => return e
  | _ => return j

def scanMapleFunctions (offset : Int) (count : Nat) (text : String) :
    Array Raw × Array String := Id.run do
  let a := chars (maskCredits text)
  let mut found : Array Raw := #[]
  let mut why : Array String := #[]
  for i in [0:a.size] do
    if i == 0 || !isIdChar a[i - 1]! then
      if let some (name, j) := identAt? a i then
        let k := skipWs a j
        if startsAt a k ":=" then
          let m := skipWs a (k + 2)
          -- `proc(var) … end proc`  or  `var -> …`
          let parsed : Except String (BExpr × Nat × String) := do
            match identAt? a m with
            | some ("proc", e) =>
              let o ← expectChar a e '('
              let some (var, v) := identAt? a (skipWs a o) | throw "no parameter"
              let v ← expectChar a v ')'
              let body := mapleSkipPrelude a v name var
              let d : Dialect := { syn := { names := #[name, "procname"], var } }
              let (b, e) ← mapleBranch d #[] a body
              let e ← mapleProcEnd a e
              return (b, e, var)
            | some (var, e) =>
              let e := skipWs a e
              unless startsAt a e "->" do throw "not a function"
              let d : Dialect := { syn := { names := #[name, "procname"], var } }
              let (b, e) ← mapleBranch d #[] a (e + 2)
              return (b, e, var)
            | none => throw "not a function"
          match parsed with
          | .error e =>
            unless e == "not a function" || e == "the expression ends early" do why := why.push e
          | .ok (b, e, _) =>
            match b.analyze offset offset count with
            | .ok (r, vals) =>
              found := found.push { recur := r, claim := if vals.isEmpty then .none else .values vals,
                                    start := i, stop := e, flavor := "maple-function" }
            | .error e => why := why.push e
  return (found, why)

/-- `(name, variable)` of every `name(var) :=` head: the functions defined by assignment. -/
def assignedNames (a : Array Char) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for i in [0:a.size] do
    if i == 0 || !isIdChar a[i - 1]! then
      if let some (name, j) := identAt? a i then
        if a[j]? == some '(' then
          if let some (v, k) := identAt? a (skipWs a (j + 1)) then
            let k := skipWs a k
            if a[k]? == some ')' && startsAt a (skipWs a (k + 1)) ":=" &&
                !out.contains (name, v) then out := out.push (name, v)
  return out

/-- Everything recognized in a Maple block. -/
def scanMaple (offset : Int) (count : Nat) (text : String) : Array Raw × Array String := Id.run do
  let (fs, why) := scanMapleFunctions offset count text
  let mut found := fs
  let mut why := why
  for (name, var) in assignedNames (chars text) do
    let (rs, ws) := scanText { names := #[name], var, juxt := true } #[":=", "="]
      "maple-assignment" text
    found := found ++ rs
    why := why ++ ws
  return (found, why)

/-! ## Magma: `[cond select e else e : n in [1..N]]` -/

mutual

partial def magmaBranch (d : Dialect) (lists : Array (String × Array Int)) (a : Array Char)
    (i : Nat) : Except String (BExpr × Nat) := do
  match parseCond d a i with
  | some (c, j) =>
    let j ← expectWord a j "select"
    let (t, k) ← magmaBranch d lists a j
    let k ← expectWord a k "else"
    let (e, m) ← magmaBranch d lists a k
    return (.ite c t e, m)
  | none => parseLeaf d lists a i

end

/-- `NAME := [1, 1];` definitions of lists, with where they start. -/
def listDefinitions (a : Array Char) : Array (String × Array Int × Nat) := Id.run do
  let mut out := #[]
  for i in [0:a.size] do
    if i == 0 || !isIdChar a[i - 1]! then
      if let some (name, j) := identAt? a i then
        let k := skipWs a j
        if startsAt a k ":=" then
          let m := skipWs a (k + 2)
          if a[m]? == some '[' then
            if let some (vs, _) := intListBr a (m + 1) #[] then out := out.push (name, vs, i)
  return out

def scanMagma (offset : Int) (count : Nat) (text : String) : Array Raw × Array String := Id.run do
  let a := chars (maskCredits text)
  let defs := listDefinitions a
  let lists := defs.map fun (n, vs, _) => (n, vs)
  let mut found : Array Raw := #[]
  let mut why : Array String := #[]
  for i in [0:a.size] do
    if a[i]? == some '[' && (i == 0 || !isIdChar a[i - 1]!) then
      let d : Dialect := { syn := { names := #["Self"] }, words := true }
      -- the comprehension needs its variable first: `[ … : n in [1..N]]`
      match (matching a i) with
      | none => pure ()
      | some close =>
        let parts := (List.range (close - i)).filter (fun k => a[i + 1 + k]? == some ':')
        -- the last top-level `:` splits the body from the range
        match parts.getLast? with
        | none => pure ()
        | some k =>
          let colon := i + 1 + k
          match identAt? a (skipWs a (colon + 1)) with
          | none => pure ()
          | some (var, e) =>
            let e := skipWs a e
            let rng := skipWs a (e + 2)
            if startsAt a e "in" && a[rng]? == some '[' then
              match intAt? a (rng + 1) with
              | some (lo, _) =>
                if lo == 1 then
                  let d := { d with syn := { d.syn with var } }
                  match magmaBranch d lists a (i + 1) with
                  | .ok (b, _) =>
                    match b.analyze offset 1 count with
                    | .ok (r, vals) =>
                      -- the list definition the body indexes belongs to the text
                      let from_ := defs.foldl (init := i) fun m (_, _, s) => if s < m then s else m
                      let usesList := defs.any fun (n, _, _) =>
                        (List.range (colon - i)).any fun k => startsAt a (i + k) (n ++ "[")
                      found := found.push
                        { recur := r, claim := if vals.isEmpty then .none else .values vals,
                          start := if usesList then from_ else i, stop := close + 1,
                          flavor := "magma-select" }
                    | .error w => why := why.push w
                  | .error w => if w != "the expression ends early" then why := why.push w
                else pure ()
              | none => pure ()
            else pure ()
  return (found, why)

end
end Oeis.Template.LinearRecurrence
