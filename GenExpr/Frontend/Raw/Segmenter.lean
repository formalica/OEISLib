module
public import GenExpr.Analyze
public meta import GenExpr.Analyze
public import GenExpr.Frontend.Raw.Parser
public meta import GenExpr.Frontend.Raw.Parser

/-!
Segmentation: finding the formulas inside a line of prose.

The parser is run from *every* start position and the results are grouped by end position, giving
a set of candidate fragments. A weighted-interval DP then picks a non-overlapping cover of maximum
weight, where a fragment that cannot become a formalization has weight zero.

Greedy leftmost-longest matching is not enough. In

    another words (1+2*x^4)/((1-x^3)*(1-x-x^2))

the longest parse from `words` is a call `words(1+2*x^4)` — perfectly well formed, but it has a
function hole. It gets weight zero, and the cover starting one token later wins on its own merits
rather than by any special-casing of prose.

Fragments that score zero are kept as diagnostics with the reason they were rejected.
-/

namespace GenExpr.Raw
public section

structure SegConfig where
  /-- How many distinct unbound variables a reading may have; normally the target's arity. -/
  maxFreeVars : Nat := 1
deriving Inhabited

/-- A candidate stretch of tokens together with every reading of it. -/
structure Segment where
  startTok : Nat
  stopTok : Nat
  span : Span
  text : String
  alts : List Res
  weight : Nat
  reasons : List Reject
deriving Inhabited

namespace Segment

def best? (s : Segment) : Option Res :=
  (s.alts.toArray.qsort fun a b => a.cost < b.cost)[0]?

end Segment

/-- Why a reading is not worth carrying forward, or `[]` if it is. -/
private def rejectReasons (cls : Classifier) (cfg : SegConfig) (e : Ast) : List Reject :=
  if !e.hasStructure then [.bareAtom]
  else
    let info := nameInfo cls #[] e
    let ownParams := (definitionHead? e).map (·.2) |>.getD #[]
    let free := info.unbound.filter fun v => !ownParams.contains v
    let holes := info.funcHoles.toList.map Reject.hole
    let tooMany :=
      if free.size > cfg.maxFreeVars then [Reject.tooManyFreeVars free.toList] else []
    let ungrounded :=
      if info.hasGround || (definitionHead? e).isSome then []
      else [Reject.unsupported "no ground content"]
    holes ++ tooMany ++ ungrounded

/-- Every reading of every token range, grouped by range. One memo is shared across all start
positions, so the whole scan costs about as much as a single parse. -/
def candidates (ctx : PCtx) (cfg : SegConfig) : Array Segment := Id.run do
  let byStart : Array (List Res) :=
    StateT.run' (m := Id) (do
      let mut acc : Array (List Res) := #[]
      for s in [0:ctx.toks.size] do
        acc := acc.push (← parseExpr ctx #[] s 0)
      return acc) {}
  let mut out : Array Segment := #[]
  for s in [0:ctx.toks.size] do
    let rs := byStart[s]!
    let mut stops : Array Nat := #[]
    for r in rs do
      if r.pos > s && !stops.contains r.pos then stops := stops.push r.pos
    for stop in stops do
      let alts := (rs.filter (·.pos == stop)).toArray.qsort (fun a b => a.cost < b.cost) |>.toList
      let viable := alts.filter fun r => (rejectReasons ctx.cls cfg r.ast).isEmpty
      let reasons :=
        if !viable.isEmpty then []
        else match alts with
          | [] => [Reject.bareAtom]
          | r :: _ => rejectReasons ctx.cls cfg r.ast
      out := out.push
        { startTok := s, stopTok := stop
          span := ctx.range s stop
          text := ctx.inp.extract ctx.toks[s]!.start ctx.toks[stop - 1]!.stop
          alts := if viable.isEmpty then alts else viable
          weight := if viable.isEmpty then 0 else stop - s
          reasons }
  return out

/-- Non-overlapping cover of maximum total weight; ties go to fewer fragments, then to the
cheaper parse. -/
def cover (segs : Array Segment) (nToks : Nat) : Array Segment := Id.run do
  let mut byStart : Array (Array Segment) := Array.replicate (nToks + 1) #[]
  for g in segs do
    if g.weight > 0 then byStart := byStart.modify g.startTok (·.push g)
  let mut best : Array (Nat × Nat × List Segment) := Array.replicate (nToks + 1) (0, 0, [])
  for k in [0:nToks] do
    let i := nToks - 1 - k
    let mut cur := best[i + 1]!
    for g in byStart[i]! do
      let (w, c, tail) := best[g.stopTok]!
      let cand := (w + g.weight, c + 1, g :: tail)
      if cand.1 > cur.1 || (cand.1 == cur.1 && cand.2.1 < cur.2.1) then cur := cand
    best := best.set! i cur
  return (best[0]!.2.2).toArray

/-- Result of scanning one input. -/
structure Scan where
  input : Input
  toks : Array Token
  cls : Classifier
  /-- The chosen non-overlapping fragments, left to right. -/
  chosen : Array Segment
  /-- Every candidate range, including the rejected ones and their reasons. -/
  all : Array Segment
deriving Inhabited

/-- Tokenize, prescan, parse from every position, and pick the best cover. -/
def scan (cls : Classifier) (cfg : SegConfig) (s : String) : Scan :=
  let input := Input.ofString s
  let toks := Lexer.tokenize input
  let cls := { cls with prescan := Prescan.run toks }
  let ctx : PCtx := { inp := input, toks, cls }
  let all := candidates ctx cfg
  { input, toks, cls, chosen := cover all toks.size, all }

end
end GenExpr.Raw
