module
public import Scripts.OeisTemplate.Recognize
public meta import Scripts.OeisTemplate.Recognize
public import OEISLib.Common.Coxeter
public meta import OEISLib.Common.Coxeter

/-!
# Template `coxeter`

> Number of reduced words of length n in Coxeter group on g generators
> S_i with relations (S_i)^2 = (S_i S_j)^r = I

~2302 sequences, `g ∈ [3,60]`, `r ∈ [3,60]`; the shared math is `OEISLib.Common.Coxeter`.

* `maindef`      the title, formalized as `fun n => coxSeq g r n`
* `formula`      `G.f.: (t^r+2t^{r-1}+…+1)/(C(g-1,2) t^r-(g-2)(t^{r-1}+…+t)+1)`, its factored
                 variant, and the order-`r` recurrence
* `mathematica`  `coxG[{r, C, -(g-2)}]` and `CoefficientList[Series[…],{x,0,K}]`
* `pari`         `Vec((…)/(…)+O(x^K))`
* `magma`        `PowerSeriesRing` / `Coefficients`

Every snippet becomes a truncated coefficient list `coeffsUpTo g r K`, equal to the main
definition pointwise. Private flag: `--check-cap=K` (compare only the first `K` terms).
-/

namespace Oeis.Template.Coxeter
public section

open Recognize

private abbrev lib : String := "OEISLib.Common.Coxeter"

structure Params where
  g : Nat
  r : Nat

/-! ## 1. Title -/

def parseTitle (title : String) : Option Params := do
  let pref := "Number of reduced words of length n in Coxeter group on "
  guard (title.startsWith pref)
  let rest := (title.drop pref.length).toString
  let parts := rest.splitOn " generators S_i with relations (S_i)^2 = (S_i S_j)^"
  guard (parts.length == 2)
  let g ← parts[0]!.trimAscii.toString.toNat?
  let r ← ((parts[1]!.splitOn " = I.")[0]!).trimAscii.toString.toNat?
  guard (3 ≤ g && g ≤ 60)
  guard (3 ≤ r && r ≤ 60)
  return ⟨g, r⟩

/-! ## 2. Recognition

Each recognizer returns the end position of the code it recognizes at the start of its text;
the template quotes exactly that prefix. -/

private def mentions (text : String) (n : Nat) : Bool := text.contains (toString n)

/-- Wolfram `coxG[{r, C, -(g-2)}]`. -/
def recogCoxG (p : Params) (text : String) : Option Nat := do
  guard (text.contains "coxG")
  guard (mentions text p.r)
  guard (mentions text (OEISLib.Common.Coxeter.c1 p.g))
  guard (mentions text (OEISLib.Common.Coxeter.c2 p.g) ||
    text.contains s!"-{OEISLib.Common.Coxeter.c2 p.g}")
  match text.splitOn "}]" with
  | head :: _ :: _ => some (head.length + 2)
  | _ => some text.length

/-- Wolfram `CoefficientList[Series[…]]`. -/
def recogSeries (p : Params) (text : String) : Option Nat := do
  guard (text.contains "CoefficientList" && text.contains "Series")
  guard (mentions text p.r || text.contains "Range")
  guard (mentions text (OEISLib.Common.Coxeter.c1 p.g) || mentions text (p.g - 1))
  return codeEnd text

/-- The `K` of a `{t, 0, K}` series bound. -/
def seriesK (text : String) : Option Nat :=
  let a := chars text
  let needle := ", 0,"
  Id.run do
    for i in [0:a.size] do
      if slice a i (i + needle.length) == needle then
        if let some (k, _) := digitsFrom a (i + needle.length) then
          return some k
    return none

/-- The optional fourth entry `K` of `coxG[{r, C, -(g-2), K}]`. -/
def coxGK (text : String) : Option Nat :=
  match (text.splitOn "coxG[{") with
  | _ :: rest :: _ =>
    match ((rest.splitOn "}").head!.splitOn ",") with
    | [_, _, _, k] => k.trimAscii.toString.toNat?
    | _ => none
  | _ => none

/-- `G.f.: P/Q` with the exponent `r` and the constants `C(g-1,2)`, `g-2`. -/
def recogGfRational (p : Params) (text : String) : Option Nat := do
  guard (text.toLower.contains "g.f")
  guard (text.contains "/")
  guard (text.contains s!"^{p.r}")
  guard (mentions text (OEISLib.Common.Coxeter.c1 p.g))
  guard (mentions text (OEISLib.Common.Coxeter.c2 p.g))
  return codeEnd text

/-- Greubel's factored g.f. -/
def recogGfFactored (p : Params) (text : String) : Option Nat := do
  guard (text.toLower.contains "g.f")
  guard (text.contains "(1+x)" || text.contains "(1+t)" || text.contains "(1-x" ||
    text.contains "1-x^")
  guard (mentions text p.r)
  guard (mentions text (OEISLib.Common.Coxeter.c1 p.g) || mentions text (p.g - 1))
  return codeEnd text

/-- `a(n) = … a(n-k) …` recurrence. -/
def recogRecurrence (p : Params) (text : String) : Option Nat := do
  guard (text.contains "a(n)" || text.contains "a(n+")
  guard (text.contains "a(n-" || text.contains "a(n -")
  guard (mentions text (OEISLib.Common.Coxeter.c1 p.g) ||
    mentions text (OEISLib.Common.Coxeter.c2 p.g))
  return codeEnd text

/-- PARI `Vec((…)/(…)+O(x^K))`; the block is already known to be PARI. -/
def recogPari (p : Params) (text : String) : Option Nat := do
  guard (mentions text (OEISLib.Common.Coxeter.c1 p.g) || mentions text (p.g - 1))
  guard (mentions text p.r || text.contains "x^")
  return codeEnd text

/-- Magma `PowerSeriesRing` / `Coefficients`; the block is already known to be Magma. -/
def recogMagma (p : Params) (text : String) : Option Nat := do
  guard (text.contains "Coefficients" || text.contains "PowerSeries")
  guard (mentions text (OEISLib.Common.Coxeter.c1 p.g) || mentions text (p.g - 1) ||
    mentions text p.r)
  return codeEnd text

/-- The `(language, recognizers)` pairs scanned for a sequence, in order. -/
def sections (p : Params) : List (String × List LineRecognizer) :=
  [("formula", [("gf-rational", recogGfRational p), ("gf-factored", recogGfFactored p),
                ("recurrence", recogRecurrence p)]),
   ("mathematica", [("wolfram-coxG", recogCoxG p), ("wolfram-series", recogSeries p)]),
   ("pari", [("pari-vec", recogPari p)]),
   ("magma", [("magma-series", recogMagma p)])]

/-! ## 3. Candidates -/

private def paramsJson (p : Params) (extra : String := "") : String :=
  s!"\{\"g\":{p.g},\"r\":{p.r}{extra}}"

def mainDefinition (p : Params) (title : String) (verified : Nat) : Candidate where
  sources := #[{ language := Section.maindef, originalText := title }]
  argKind := "Nat"
  leanType := "Nat → Nat"
  leanCode := s!"fun n => {lib}.coxSeq {p.g} {p.r} n"
  imports := #[lib]
  verifiedUpto := verified
  params := paramsJson p

/-- `formula = coeffsUpTo g r k` and its pointwise agreement with the main definition. -/
def snippet (p : Params) (h : Hit) (k verified : Nat) : Candidate where
  sources := #[h.source]
  argKind := "Nat"
  leanType := "List Nat"
  leanCode := s!"{lib}.coeffsUpTo {p.g} {p.r} {k}"
  imports := #[lib]
  eqStatement := "∀ (n : Nat) (h : n < «self».length), «self»[n]'h = «main» n"
  eqProof := s!"intro n h\n\
    have h' : n < ({lib}.coeffsUpTo {p.g} {p.r} {k}).length := by simpa [«self»] using h\n\
    have h1 := {lib}.coeffsUpTo_getElem {p.g} {p.r} {k} n h'\n\
    have h2 : «main» n = {lib}.coxSeq {p.g} {p.r} n := rfl\n\
    rw [h2]\n\
    simpa [«self»] using h1"
  verifiedUpto := verified
  params := paramsJson p s!",\"flavor\":\"{h.flavor}\",\"K\":{k}"
  notes := h.flavor

/-! ## 4. The template -/

/-- The truncation bound the snippet states, or the number of verified terms minus one. -/
private def boundOf (h : Hit) (verified : Nat) : Nat :=
  (match h.flavor with
    | "wolfram-series" => seriesK h.text
    | "wolfram-coxG" => coxGK h.text
    | _ => none).getD (verified - 1)

def formalize (extras : List String) (src : SeqSource) : Verdict :=
  match parseTitle src.title with
  | none => .skip "title does not match the coxeter template"
  | some p =>
    if src.offset != 0 then .skip s!"unsupported offset {src.offset} (template expects 0)"
    else if src.terms.size < 2 then .skip "fewer than two published terms"
    else match termsNat src.terms with
      | .error e => .fail e
      | .ok terms =>
        let count := (flagNat? extras "--check-cap").elim terms.size (min terms.size ·)
        let computed := (Array.range count).map (OEISLib.Common.Coxeter.coxSeq p.g p.r)
        match checkPrefix computed (terms.extract 0 count) with
        | .error e => .fail s!"verification failed: {e}"
        | .ok verified =>
          let found := (sections p).foldl (init := (#[] : Array Hit)) fun acc (lang, recs) =>
            acc ++ hits src lang recs (maxLines := if lang == "formula" then 4 else 1)
          let snippets := found.map fun h => snippet p h (boundOf h verified) verified
          .items (#[mainDefinition p src.title verified] ++ snippets)

def template : Template where
  name := "coxeter"
  descr := "reduced words in the Coxeter group on g generators with (S_i S_j)^r = I (~2302 seqs)"
  selectWhere := "title LIKE 'Number of reduced words of length n in Coxeter group on %'"
  flags := #["--check-cap"]
  formalize := formalize

end
end Oeis.Template.Coxeter
