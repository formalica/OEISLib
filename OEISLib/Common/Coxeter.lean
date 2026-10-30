module
public import Mathlib.Tactic

/-!
# Coxeter growth series — complete-graph diagram

Generic parameterized library behind the OEIS template

> Number of reduced words of length n in Coxeter group on g generators
> S_i with relations (S_i)^2 = (S_i S_j)^r = I

(~2302 sequences, g∈[3,50], r∈[3,50], (S_i)^2 always exponent 2).

Each sequence is the growth series of the Coxeter group whose diagram is
the complete graph on g vertices with every edge labelled r. Its
Poincaré series is rational:

  G(t) = (t^r + 2 t^{r-1} + … + 2 t + 1)
         / (C(g-1,2) t^r - (g-2)(t^{r-1}+…+t) + 1)

       = (1+t)(1-t^r)/(1-x)  /  same denominator

       = (1+t)(1-t^r) / (1-(g-1)t + (C(g-1,2)+(g-2)) t^r - C(g-1,2) t^{r+1})

The coefficients satisfy the linear recurrence of order r

  a(n) = (g-2) Σ_{k=1}^{r-1} a(n-k) - C(g-1,2) a(n-r)    (n ≥ r)

with a(0)=1.
The library provides a single computable definition `coxSeq g r`
via power-series division. Every concrete sequence delegates to it;
`Equiv_*.lean` files are thin instantiations.

Wolfram `coxG[{r, C(g-1,2), -(g-2)}]`, `CoefficientList[Series[…]]`,
PARI `Vec` and Magma `PowerSeriesRing` all transcribe to `coeffsUpTo`.
-/

namespace OEISLib.Common.Coxeter
public section

/-! ## Parameters -/

/-- `C(g-1,2) = (g-1)(g-2)/2` — leading coefficient of the denominator. -/
def c1 (g : Nat) : Nat := (g - 1) * (g - 2) / 2

/-- `g-2` — repeated coefficient of the denominator. -/
def c2 (g : Nat) : Nat := g - 2

/-! ## Numerator / denominator coefficient lists -/

/-- Numerator `1 + 2t + … + 2t^{r-1} + t^r` as coefficient list. -/
def numCoeffs (r : Nat) : List Int :=
  List.range (r + 1) |>.map fun i => if i = 0 || i = r then (1 : Int) else 2

/-- Denominator `1 - (g-2)(t+…+t^{r-1}) + C(g-1,2) t^r` as coefficient list. -/
def denCoeffs (g r : Nat) : List Int :=
  List.range (r + 1) |>.map fun i =>
    if i = 0 then (1 : Int)
    else if i = r then (c1 g : Int)
    else -((c2 g : Int))

/-! ## Power-series division -/

/-- Auxiliary: list of `G(0)…G(n)` as `Int`s via `G = num/den`.
`den[0]=1` so `G[n] = num[n] - Σ_{k=1}^{min(n,r)} den[k]·G[n-k]`. -/
def coxSeqAux (g r : Nat) : Nat → List Int
  | 0 => [1]
  | n + 1 =>
    let prev := coxSeqAux g r n
    let num := numCoeffs r
    let den := denCoeffs g r
    let num_n : Int := num.getD (n + 1) 0
    let s : Int := ((List.range (min (n + 1) r) |>.map fun k =>
      let k1 := k + 1
      let dk := den.getD k1 0
      let ak := prev.getD (n + 1 - k1) 0
      dk * ak)).sum
    let v : Int := num_n - s
    prev ++ [v]

/-- Main sequence as `Nat` (values are positive for valid `g r`; clipped at 0 otherwise). -/
def coxSeq (g r : Nat) (n : Nat) : Nat :=
  let v := (coxSeqAux g r n).getD n 0
  if v < 0 then 0 else v.toNat

theorem coxSeqAux_length (g r n : Nat) : (coxSeqAux g r n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coxSeqAux, ih]

theorem coxSeq_zero (g r : Nat) : coxSeq g r 0 = 1 := by
  simp [coxSeq, coxSeqAux]

/-- The `K`-truncated coefficient list `a(0)…a(K)` — transcription of
`CoefficientList[Series[num/den,{t,0,K}],t]` / `Vec` / `PowerSeriesRing`. -/
def coeffsUpTo (g r K : Nat) : List Nat :=
  List.range (K + 1) |>.map (coxSeq g r)

theorem coeffsUpTo_length (g r K : Nat) : (coeffsUpTo g r K).length = K + 1 := by
  simp [coeffsUpTo]

/-- `coeffsUpTo` agrees with `coxSeq` pointwise (by definition). -/
theorem coeffsUpTo_getElem (g r K n : Nat) (h : n < (coeffsUpTo g r K).length) :
    (coeffsUpTo g r K)[n]'h = coxSeq g r n := by
  simp [coeffsUpTo]

/-- Membership in the truncated list. -/
theorem mem_coeffsUpTo {g r K x : Nat} :
    x ∈ coeffsUpTo g r K ↔ ∃ n ≤ K, x = coxSeq g r n := by
  simp [coeffsUpTo, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by omega, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by omega, rfl⟩

end
end OEISLib.Common.Coxeter
