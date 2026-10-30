module
public import Scripts.OeisTemplate.Recognize
public meta import Scripts.OeisTemplate.Recognize
public import OEISLib.Common.Residue
public meta import OEISLib.Common.Residue

/-!
# Template `primeCongruent`

> Primes congruent to `a` mod `m`.

~980 sequences (single-residue titles; the `{…} mod m` variants are their own templates). The
shared math is `OEISLib.Common.Residue`; the bound is the largest published term, so the data
itself guarantees that enough members exist below it.

* `maindef`      the title, as the `n`-th member of the class up to the bound
* `mathematica`  `Select[Prime[Range[K]], MemberQ[{a}, Mod[#, m]] &]` and
                 `Select[Range[s, e, m], PrimeQ]`
* `pari`         `is(n)=isprime(n) && n%m==a`
* `magma`        `[p: p in PrimesUpTo(B) | p mod m eq a]`

Private flag: `--check-cap=K` (compare only the first `K` terms).
-/

namespace Oeis.Template.PrimeCongruent
public section

open Recognize

private abbrev lib : String := "OEISLib.Common.Residue"

structure Params where
  a : Nat
  m : Nat

/-! ## 1. Title -/

def parseTitle (title : String) : Option Params := do
  guard (title.startsWith "Primes congruent to ")
  let parts := (title.drop "Primes congruent to ".length).toString.splitOn " mod "
  guard (parts.length == 2)
  let a ← parts[0]!.trimAscii.toString.toNat?
  let tail := parts[1]!.trimAscii.toString
  guard (tail.endsWith ".")
  let m ← (tail.dropEnd 1).toString.toNat?
  guard (2 ≤ m && a < m)
  return ⟨a, m⟩

/-! ## 2. Recognition

Each recognizer returns the end position of the code it recognizes at the start of its text;
the template quotes exactly that prefix. -/

/-- `Select[Prime[Range[K]], MemberQ[{a}, Mod[#, m]] &]`; also yields `K`. -/
def parseFirstPrimes (p : Params) (text : String) : Option (Nat × Nat) := do
  let c := chars text
  let i ← eatLit c 0 "Select[Prime[Range["
  let (k, i) ← digitsFrom c i
  let i ← eatLit c i "]],MemberQ[{"
  let (a', i) ← digitsFrom c i
  guard (a' == p.a)
  let i ← eatLit c i "},Mod[#,"
  let (m', i) ← digitsFrom c i
  guard (m' == p.m)
  let i ← eatLit c i "]]&]"
  return (k, endAfterSemicolon c i)

/-- `Select[Range[s, e, m], PrimeQ]`: a progression through the residue class. -/
def recogProgression (p : Params) (text : String) : Option Nat := do
  let c := chars text
  let i ← eatLit c 0 "Select[Range["
  let (s, i) ← digitsFrom c i
  let i ← eatLit c i ","
  let (_, i) ← digitsFrom c i
  let i ← eatLit c i ","
  let (step, i) ← digitsFrom c i
  guard (step == p.m)
  guard (s % p.m == p.a % p.m)
  let i ← eatLit c i "],PrimeQ]"
  return endAfterSemicolon c i

/-- `is(n)=isprime(n) && n%m==a`; the block is already known to be PARI. -/
def recogPari (p : Params) (text : String) : Option Nat := do
  let c := chars text
  let i ← eatLit c 0 "is(n)=isprime(n)&&n%"
  let (m', i) ← digitsFrom c i
  guard (m' == p.m)
  let i ← eatLit c i "=="
  let (a', i) ← digitsFrom c i
  guard (a' == p.a)
  return endAfterSemicolon c i

/-- `[p: p in PrimesUpTo(B) | p mod m eq a]`, in its many spacings; the block is already
known to be Magma. -/
def recogMagma (p : Params) (text : String) : Option Nat := do
  let c := chars text
  let i ← eatLit c 0 "[p:pinPrimesUpTo("
  let (_, i) ← digitsFrom c i
  let i ← eatLit c i ")|pmod"
  let (m', i) ← digitsFrom c i
  guard (m' == p.m)
  let i ← eatLit c i "eq"
  let (a', i) ← digitsFrom c i
  guard (a' == p.a)
  let i ← eatLit c i "]"
  return endAfterSemicolon c i

/-- The `(language, recognizers)` pairs scanned for a sequence, in order. -/
def sections (p : Params) : List (String × List LineRecognizer) :=
  [("mathematica", [("wolfram-first-primes", fun t => (parseFirstPrimes p t).map (·.2)),
                    ("wolfram-progression", recogProgression p)]),
   ("pari", [("pari-characteristic-function", recogPari p)]),
   ("magma", [("magma-list", recogMagma p)])]

/-! ## 3. Candidates -/

private def paramsJson (p : Params) (bound : Nat) (extra : String := "") : String :=
  s!"\{\"a\":{p.a},\"m\":{p.m},\"bound\":{bound}{extra}}"

def mainDefinition (p : Params) (title : String) (bound verified : Nat) : Candidate where
  language := Section.maindef
  originalText := title
  argKind := "PNat"
  leanType := "PNat → Nat"
  leanCode := s!"fun n => {lib}.nthIn {p.a} {p.m} (n.val - 1) {bound}"
  imports := #[lib]
  verifiedUpto := verified
  params := paramsJson p bound

private def base (p : Params) (h : Hit) (bound verified : Nat) : Candidate where
  language := h.language
  blockIndex := h.blockIndex
  originalText := h.text
  argKind := "PNat"
  imports := #[lib]
  verifiedUpto := verified
  params := paramsJson p bound s!",\"flavor\":\"{h.flavor}\""
  notes := h.flavor

/-- The bounded enumeration of the class, equal to the main definition position by position. -/
def enumeration (p : Params) (h : Hit) (bound verified : Nat) : Candidate :=
  let ap := s!"{p.a} {p.m}"
  { base p h bound verified with
    leanType := "List Nat"
    leanCode := s!"{lib}.membersUpTo {ap} {bound}"
    eqStatement :=
      "∀ (i : Nat) (h : i < «self».length), «self»[i]? = some («main» ⟨i + 1, by omega⟩)"
    eqProof := s!"intro i h\n\
      have h1 : «self»[i]? = ({lib}.membersUpTo {ap} {bound})[i]? := rfl\n\
      have h2 : «main» ⟨i + 1, by omega⟩ = {lib}.nthIn {ap} i {bound} := rfl\n\
      have h' : i < ({lib}.membersUpTo {ap} {bound}).length := h\n\
      rw [h1, h2]\n\
      rcases {lib}.getElem?_nthIn {ap} i {bound} with hs | hz\n\
      · exact hs\n\
      · exact absurd ({lib}.nthIn_pos h') (by rw [hz]; simp)" }

/-- The PARI membership test decides `Nat.Prime n ∧ n % m = a`. -/
def characteristic (p : Params) (h : Hit) (bound verified : Nat) : Candidate :=
  { base p h bound verified with
    leanType := "Nat → Bool"
    leanCode := s!"{lib}.isMember {p.a} {p.m}"
    eqStatement := s!"∀ n : Nat, «self» n = true ↔ Nat.Prime n ∧ n % {p.m} = {p.a}"
    eqProof := s!"intro n\nexact {lib}.isMember_iff" }

/-- Members among the first `k` primes; equal to the whole enumeration once the lengths agree. -/
def firstPrimes (p : Params) (h : Hit) (k bound verified : Nat) : Candidate :=
  let members := s!"{lib}.membersUpTo {p.a} {p.m} {bound}"
  { base p h bound verified with
    leanType := "List Nat"
    leanCode := s!"{lib}.selectFrom (({lib}.primesUpTo {bound}).take {k}) {p.a} {p.m}"
    eqStatement := s!"«self».length = ({members}).length → «self» = {members}"
    eqProof := "intro h\n" ++
      s!"have hsub : List.Sublist «self» ({members}) := by\n" ++
      "  unfold «self»\n" ++
      s!"  exact {lib}.selectFrom_take_sub ..\n" ++
      s!"exact {lib}.eq_of_sub_of_length hsub h"
    params := paramsJson p bound s!",\"flavor\":\"{h.flavor}\",\"K\":{k}" }

/-! ## 4. The template -/

def formalize (extras : List String) (src : SeqSource) : Verdict :=
  match parseTitle src.title with
  | none => .skip "title does not match the primeCongruent template"
  | some p =>
    if src.offset != 1 then .skip s!"unsupported offset {src.offset} (template emits a PNat API)"
    else match termsNat src.terms with
      | .error e => .fail e
      | .ok terms =>
        if terms.isEmpty then .skip "sequence publishes no terms"
        else
          let bound := terms[terms.size - 1]!
          let count := (flagNat? extras "--check-cap").elim terms.size (min terms.size ·)
          let members := (OEISLib.Common.Residue.membersUpTo p.a p.m bound).toArray
          if members.size < count then
            .fail s!"enumeration produced only {members.size} members up to {bound}, but the \
              sequence publishes {count} terms"
          else match checkPrefix (members.extract 0 count) (terms.extract 0 count) with
            | .error e => .fail s!"verification failed: {e}"
            | .ok verified =>
              let found := (sections p).foldl (init := (#[] : Array Hit)) fun acc (lang, recs) =>
                acc ++ hits src lang recs
              let snippets := found.map fun h =>
                match h.flavor with
                | "wolfram-first-primes" =>
                  match parseFirstPrimes p h.text with
                  | some (k, _) => firstPrimes p h k bound verified
                  | none => enumeration p h bound verified
                | "pari-characteristic-function" => characteristic p h bound verified
                | _ => enumeration p h bound verified
              .items (#[mainDefinition p src.title bound verified] ++ snippets)

def template : Template where
  name := "primeCongruent"
  descr := "primes congruent to a mod m (~980 sequences; %t Select / %o PARI+Magma programs)"
  selectWhere := "title LIKE 'Primes congruent to % mod %.' AND title NOT LIKE '%{%'"
  flags := #["--check-cap"]
  formalize := formalize

end
end Oeis.Template.PrimeCongruent
