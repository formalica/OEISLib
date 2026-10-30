module
public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Square-root continued-fraction numerators

The mathematical specification uses Mathlib's continued fraction of `Real.sqrt d`.
The integer algorithm below is independently executable. Agreement with the specification
is proved for every nonsquare radicand by `relation_nonsquare`, using an integer-state
invariant to identify the entire coefficient stream. Numerical tests are supplementary.
-/

namespace OEISLib.Common.SqrtContinuedFraction
public section

/-- A numerator of the actual continued fraction, with the first convergent at index zero. -/
def relation (d n p : Nat) : Prop :=
  (p : ℝ) = (GenContFract.of (Real.sqrt d)).nums n

/-- Integer state representing the complete quotient `(sqrt d + m) / q`.
Only nonsquare radicands are intended; the total algorithm has junk behavior otherwise. -/
structure State where
  m : Nat
  q : Nat
  a : Nat
  deriving DecidableEq, Repr

/-- Initial complete quotient `sqrt d`. -/
def initial (d : Nat) : State := ⟨0, 1, Nat.sqrt d⟩

/-- The standard exact integer square-root continued-fraction update. -/
def step (d : Nat) (s : State) : State :=
  let m := s.q * s.a - s.m
  let q := (d - m * m) / s.q
  ⟨m, q, (Nat.sqrt d + m) / q⟩

/-- The state at the requested zero-based partial quotient. -/
def state (d : Nat) : Nat → State
  | 0 => initial d
  | n + 1 => step d (state d n)

/-- Integer partial quotients produced by the algorithm. -/
def coefficient (d n : Nat) : Nat := (state d n).a

/-- Continuants of any sequence of integer partial quotients. -/
def numerator (a : Nat → Nat) : Nat → Nat
  | 0 => a 0
  | 1 => a 1 * a 0 + 1
  | n + 2 => a (n + 2) * numerator a (n + 1) + numerator a n

/-- Continuants agree with Mathlib whenever the head and all partial quotients agree.
This separates the elementary numerator recurrence from the square-root algorithm invariant. -/
theorem numerator_eq_nums (a : Nat → Nat) (g : GenContFract ℝ)
    (head_eq : g.h = (a 0 : ℝ))
    (coeff_eq : ∀ n, g.s.get? n = some ⟨1, (a (n + 1) : ℝ)⟩) (n : Nat) :
    (numerator a n : ℝ) = g.nums n := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [numerator] using head_eq.symm
  | one =>
    rw [GenContFract.first_num_eq (coeff_eq 0), head_eq]
    simp [numerator]
  | more n ih₀ ih₁ =>
    rw [GenContFract.nums_recurrence (coeff_eq (n + 1)) ih₀.symm ih₁.symm]
    simp [numerator]

/-- Paired recurrence, keeping the previous numerator to avoid branching recursion. -/
def numeratorPair (a : Nat → Nat) : Nat → Nat × Nat
  | 0 => (1, a 0)
  | n + 1 =>
    let p := numeratorPair a n
    (p.2, a (n + 1) * p.2 + p.1)

theorem numeratorPair_snd (a : Nat → Nat) (n : Nat) :
    (numeratorPair a n).2 = numerator a n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih₀ ih₁ =>
    change a (n + 2) * (numeratorPair a (n + 1)).2 +
      (numeratorPair a n).2 = numerator a (n + 2)
    rw [ih₁, ih₀]
    rfl

/-- Computable sequence; `relation_nonsquare` proves correctness for nonsquare radicands. -/
def computed (d n : Nat) : Nat := (numeratorPair (coefficient d) n).2

theorem computed_eq_numerator (d n : Nat) :
    computed d n = numerator (coefficient d) n :=
  numeratorPair_snd _ _

/-- The initial integer coefficient is the actual floor of the real square root. -/
theorem head_eq_coefficient (d : Nat) :
    (GenContFract.of (Real.sqrt d)).h = (coefficient d 0 : ℝ) := by
  have : (GenContFract.of (Real.sqrt d)).h = (⌊Real.sqrt (d : ℝ)⌋ : ℤ) := rfl
  rw [this, Real.floor_real_sqrt_eq_nat_sqrt]
  simp [coefficient, state, initial]

/-- The remaining obligation is agreement of the entire coefficient stream.
No caller may replace this universal hypothesis with finite term checks. -/
theorem relation_computed_of_coefficients (d : Nat)
    (coeff_eq : ∀ n, (GenContFract.of (Real.sqrt d)).s.get? n =
      some ⟨1, (coefficient d (n + 1) : ℝ)⟩) (n : Nat) :
    relation d n (computed d n) := by
  unfold relation
  rw [computed_eq_numerator]
  exact numerator_eq_nums _ _ (head_eq_coefficient d) coeff_eq n

/-! ### The `d = 2` bridge

The complete quotients of `√2` are constant from the first step: `x₀ = √2` and
`xₙ = √2 + 1` for `n ≥ 1`, because `(√2 − 1)⁻¹ = √2 + 1`. This makes the full
coefficient-stream agreement provable here, giving one complete, kernel-checked instance
of the bridge. The general nonsquare proof below uses an invariant on the integer state. -/

private theorem sqrt_two_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_two_sub_one_mul_add_one :
    (Real.sqrt 2 - 1 : ℝ) * (Real.sqrt 2 + 1) = 1 := by
  linear_combination sqrt_two_sq

private theorem sqrt_two_sub_one_ne_zero : (Real.sqrt 2 - 1 : ℝ) ≠ 0 := by
  intro h
  have hc := sqrt_two_sub_one_mul_add_one
  rw [h] at hc
  norm_num at hc

private theorem floor_sqrt_two : ⌊(Real.sqrt 2 : ℝ)⌋ = 1 := by
  simpa using (Real.floor_real_sqrt_eq_nat_sqrt (a := 2))

private theorem floor_sqrt_two_add_one : ⌊(Real.sqrt 2 + 1 : ℝ)⌋ = 2 := by
  rw [Int.floor_add_one, floor_sqrt_two]
  norm_num

private theorem of_sqrt_two :
    GenContFract.IntFractPair.of (Real.sqrt 2 : ℝ) = ⟨(1 : ℤ), Real.sqrt 2 - 1⟩ := by
  simp [GenContFract.IntFractPair.of, Int.fract, floor_sqrt_two]

private theorem of_sqrt_two_add_one :
    GenContFract.IntFractPair.of (Real.sqrt 2 + 1 : ℝ) = ⟨(2 : ℤ), Real.sqrt 2 - 1⟩ := by
  simp only [GenContFract.IntFractPair.of, Int.fract, floor_sqrt_two_add_one,
    Int.cast_ofNat]
  congr 1
  ring

private theorem inv_sqrt_two_sub_one : ((Real.sqrt 2 : ℝ) - 1)⁻¹ = Real.sqrt 2 + 1 :=
  (eq_inv_of_mul_eq_one_left (by
    rw [mul_comm]
    exact sqrt_two_sub_one_mul_add_one)).symm

/-- Explicit formula: every stream entry of `√2` from index one on is `⟨2, √2 − 1⟩`. -/
private theorem stream_sqrt_two_succ (n : ℕ) :
    GenContFract.IntFractPair.stream (Real.sqrt 2 : ℝ) (n + 1)
      = some ⟨(2 : ℤ), Real.sqrt 2 - 1⟩ := by
  induction n with
  | zero =>
    refine GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mpr
      ⟨GenContFract.IntFractPair.of (Real.sqrt 2 : ℝ),
        GenContFract.IntFractPair.stream_zero (Real.sqrt 2 : ℝ), ?_, ?_⟩
    · simpa [GenContFract.IntFractPair.of, Int.fract, floor_sqrt_two] using
        sqrt_two_sub_one_ne_zero
    · simpa [GenContFract.IntFractPair.of, Int.fract, floor_sqrt_two, floor_sqrt_two_add_one,
        inv_sqrt_two_sub_one] using of_sqrt_two_add_one
  | succ n ih =>
    refine GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mpr
      ⟨⟨(2 : ℤ), Real.sqrt 2 - 1⟩, ih, sqrt_two_sub_one_ne_zero, ?_⟩
    change GenContFract.IntFractPair.of ((Real.sqrt 2 - 1 : ℝ)⁻¹) = _
    rw [inv_sqrt_two_sub_one]
    exact of_sqrt_two_add_one

/-- Every coefficient entry of `GenContFract.of v` is the `b` component of the corresponding
stream entry, one index later. -/
theorem of_s_get? (v : ℝ) (n : ℕ) :
    (GenContFract.of v).s.get? n =
      (GenContFract.IntFractPair.stream v (n + 1)).bind (some ∘ fun p => ⟨(1 : ℝ), ↑p.b⟩) := by
  change (GenContFract.IntFractPair.stream v (n + 1)).map
    (fun p => (⟨(1 : ℝ), ↑p.b⟩ : GenContFract.Pair ℝ)) = _
  cases GenContFract.IntFractPair.stream v (n + 1) <;> rfl

theorem of_sqrt_two_s_get? (n : ℕ) :
    (GenContFract.of (Real.sqrt 2 : ℝ)).s.get? n = some ⟨(1 : ℝ), 2⟩ := by
  rw [of_s_get?, stream_sqrt_two_succ n]
  simp

private theorem state_two_succ (n : ℕ) : state 2 (n + 1) = ⟨1, 1, 2⟩ := by
  induction n with
  | zero => simp [state, step, initial]
  | succ n ih =>
    change step 2 (state 2 (n + 1)) = _
    rw [ih]
    simp [step]

theorem coefficient_two_succ (n : ℕ) : coefficient 2 (n + 1) = 2 := by
  simp [coefficient, state_two_succ n]

theorem coeff_eq_sqrt_two (n : ℕ) :
    (GenContFract.of (Real.sqrt 2 : ℝ)).s.get? n = some ⟨(1 : ℝ), (coefficient 2 (n + 1) : ℝ)⟩ := by
  rw [of_sqrt_two_s_get?, coefficient_two_succ]
  norm_num

/-- **The complete bridge for `d = 2`**: `computed 2 n` is exactly the `n`-th numerator of the
continued fraction convergents to `√2`. -/
theorem relation_sqrt_two (n : ℕ) : relation 2 n (computed 2 n) :=
  relation_computed_of_coefficients 2 coeff_eq_sqrt_two n

/-! ### The general nonsquare bridge

For nonsquare `d` the complete quotients never terminate, and the integer state
`(m, q, a)` exactly mirrors them: `x = (√d + m) / q` has floor `a` and positive
fractional part. Three elementary facts carry the argument. -/

private theorem nonsquare_cast_ne {d : ℕ} (hd : Nat.sqrt d * Nat.sqrt d ≠ d) (j : ℕ) :
    Real.sqrt (d : ℝ) ≠ (j : ℝ) := by
  intro h
  have hj : (j : ℝ) * (j : ℝ) = (d : ℝ) := by
    rw [← h]
    exact Real.mul_self_sqrt (by exact_mod_cast Nat.zero_le d)
  have hjnat : j * j = d := by
    rw [← Nat.cast_mul] at hj
    exact Nat.cast_injective hj
  have hsq : Nat.sqrt (j * j) = j := Nat.sqrt_eq j
  rw [hjnat] at hsq
  refine hd ?_
  rw [hsq]
  exact hjnat

private theorem sqrt_sub_mul_add {d M : ℕ} (hM : M * M ≤ d) :
    (Real.sqrt (d : ℝ) - (M : ℝ)) * (Real.sqrt (d : ℝ) + (M : ℝ))
      = ((d - M * M : ℕ) : ℝ) := by
  have h1 : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
    Real.mul_self_sqrt (by exact_mod_cast Nat.zero_le d)
  rw [Nat.cast_sub hM]
  push_cast
  linear_combination h1

private theorem floor_complete_quotient (d m q : ℕ) (hq : 0 < q) :
    ⌊(Real.sqrt (d : ℝ) + (m : ℝ)) / (q : ℝ)⌋ = (((Nat.sqrt d + m) / q : ℕ) : ℤ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdmNat : q * ((Nat.sqrt d + m) / q) + (Nat.sqrt d + m) % q = Nat.sqrt d + m :=
    Nat.div_add_mod (Nat.sqrt d + m) q
  have hrlt : (Nat.sqrt d + m) % q < q := Nat.mod_lt _ hq
  have hfloor : (⌊Real.sqrt (d : ℝ)⌋ : ℤ) = ((Nat.sqrt d : ℕ) : ℤ) :=
    Real.floor_real_sqrt_eq_nat_sqrt (a := d)
  have hlo : ((Nat.sqrt d : ℕ) : ℝ) ≤ Real.sqrt (d : ℝ) := by
    have h := Int.floor_le (Real.sqrt (d : ℝ))
    rw [hfloor] at h
    exact_mod_cast h
  have hhi : Real.sqrt (d : ℝ) < ((Nat.sqrt d : ℕ) : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (Real.sqrt (d : ℝ))
    rw [hfloor] at h
    simpa using h
  have hr0 : (0 : ℝ) ≤ (((Nat.sqrt d + m) % q : ℕ) : ℝ) :=
    by exact_mod_cast Nat.zero_le ((Nat.sqrt d + m) % q)
  have hrq : (((Nat.sqrt d + m) % q : ℕ) : ℝ) + 1 ≤ (q : ℝ) :=
    by exact_mod_cast Nat.succ_le_of_lt hrlt
  have hdm : ((q : ℕ) : ℝ) * (((Nat.sqrt d + m) / q : ℕ) : ℝ)
      + (((Nat.sqrt d + m) % q : ℕ) : ℝ) = ((Nat.sqrt d : ℕ) : ℝ) + (m : ℝ) := by
    exact_mod_cast hdmNat
  have hlow : (((Nat.sqrt d + m) / q : ℕ) : ℝ) ≤ (Real.sqrt (d : ℝ) + (m : ℝ)) / (q : ℝ) := by
    rw [le_div_iff₀ hq0]
    linarith [hdm, hlo, hr0]
  have hup : (Real.sqrt (d : ℝ) + (m : ℝ)) / (q : ℝ) < (((Nat.sqrt d + m) / q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hq0]
    have e1 : ((((Nat.sqrt d + m) / q : ℕ) : ℝ) + 1) * (q : ℝ)
        = ((Nat.sqrt d : ℕ) : ℝ) + (m : ℝ) + (q : ℝ) - (((Nat.sqrt d + m) % q : ℕ) : ℝ) := by
      linear_combination hdm
    linarith [e1, hhi, hrq]
  have hz : ((((Nat.sqrt d + m) / q : ℕ) : ℤ) : ℝ) = (((Nat.sqrt d + m) / q : ℕ) : ℝ) :=
    Int.cast_natCast _
  rw [← hz] at hlow hup
  exact Int.floor_eq_iff.mpr ⟨hlow, hup⟩

/-- The complete quotient `x = (√d + m) / q` of a nonsquare radicand, stated in terms of the
integer state. The last two components tie the real quantity to the state, and the fourth
records that `d − m²` is divisible by `q`. -/
def StateInv (d : ℕ) (n : ℕ) (s : State) : Prop :=
  0 < s.q ∧
  s.m ≤ Nat.sqrt d ∧
  (∃ W, s.q * W = d - s.m * s.m) ∧
  s.a * s.q ≥ s.m ∧
  s.a = (Nat.sqrt d + s.m) / s.q ∧
  (Real.sqrt (d : ℝ) + (s.m : ℝ)) / (s.q : ℝ) - (s.a : ℝ) ≠ 0 ∧
  GenContFract.IntFractPair.stream (Real.sqrt (d : ℝ)) n
    = some ⟨(s.a : ℤ), (Real.sqrt (d : ℝ) + (s.m : ℝ)) / (s.q : ℝ) - (s.a : ℝ)⟩

/-- The base state: the initial complete quotient is `√d` itself, whose floor is the
integer square root and whose fractional part is nonzero exactly when `d` is a nonsquare. -/
theorem state_inv_zero (d : ℕ) (hd : Nat.sqrt d * Nat.sqrt d ≠ d) :
    StateInv d 0 (initial d) := by
  have hne := nonsquare_cast_ne hd (Nat.sqrt d)
  refine ⟨Nat.one_pos, Nat.zero_le _, ⟨d, by simp [initial]⟩, Nat.zero_le _,
    by simp [initial], ?_, ?_⟩
  · simpa [initial, sub_eq_zero] using hne
  · rw [GenContFract.IntFractPair.stream_zero]
    simp [GenContFract.IntFractPair.of, Int.fract,
      Real.floor_real_sqrt_eq_nat_sqrt, initial]

private theorem step_m_le_sqrt (d : ℕ) (s : State)
    (ha : s.a = (Nat.sqrt d + s.m) / s.q) :
    (step d s).m ≤ Nat.sqrt d := by
  have h := Nat.div_mul_le_self (Nat.sqrt d + s.m) s.q
  rw [← ha, Nat.mul_comm s.a s.q] at h
  change s.q * s.a - s.m ≤ Nat.sqrt d
  omega

private theorem step_divisible (d : ℕ) (s : State)
    (hm : s.m ≤ Nat.sqrt d) (ham : s.m ≤ s.a * s.q)
    (ha : s.a = (Nat.sqrt d + s.m) / s.q)
    (hw : ∃ W, s.q * W = d - s.m * s.m) :
    s.q ∣ d - (step d s).m * (step d s).m := by
  obtain ⟨W, hW⟩ := hw
  have hm2 : s.m * s.m ≤ d := Nat.le_sqrt.mp hm
  have hm'2 : (step d s).m * (step d s).m ≤ d :=
    Nat.le_sqrt.mp (step_m_le_sqrt d s ha)
  have hWz : (s.q : ℤ) * W = (d : ℤ) - (s.m : ℤ) * s.m := by
    have h := congrArg (fun x : ℕ => (x : ℤ)) hW
    simpa only [Nat.cast_sub hm2, Nat.cast_mul] using h
  have hmz : ((step d s).m : ℤ) = (s.q : ℤ) * s.a - s.m := by
    change ((s.q * s.a - s.m : ℕ) : ℤ) = _
    rw [Nat.cast_sub (by simpa [Nat.mul_comm] using ham), Nat.cast_mul]
  apply Int.natCast_dvd_natCast.mp
  refine ⟨(W : ℤ) + 2 * s.a * s.m - (s.a : ℤ) * s.a * s.q, ?_⟩
  rw [Nat.cast_sub hm'2, Nat.cast_mul, hmz]
  linear_combination -hWz

private theorem step_q_pos_mul (d : ℕ) (hd : Nat.sqrt d * Nat.sqrt d ≠ d)
    (s : State) (hq : 0 < s.q) (hm : s.m ≤ Nat.sqrt d)
    (ham : s.m ≤ s.a * s.q) (ha : s.a = (Nat.sqrt d + s.m) / s.q)
    (hw : ∃ W, s.q * W = d - s.m * s.m) :
    0 < (step d s).q ∧
      (step d s).q * s.q = d - (step d s).m * (step d s).m := by
  have hdiv := step_divisible d s hm ham ha hw
  have hsq : Nat.sqrt d * Nat.sqrt d < d :=
    lt_of_le_of_ne (Nat.le_sqrt.mp le_rfl) hd
  have hm' := step_m_le_sqrt d s ha
  have hlt : (step d s).m * (step d s).m < d :=
    lt_of_le_of_lt (Nat.mul_le_mul hm' hm') hsq
  have hpos : 0 < d - (step d s).m * (step d s).m := by omega
  exact ⟨Nat.div_pos (Nat.le_of_dvd hpos hdiv) hq, Nat.div_mul_cancel hdiv⟩

private theorem step_reciprocal (d : ℕ) (s : State)
    (hq : 0 < s.q) (ham : s.m ≤ s.a * s.q)
    (hm' : (step d s).m ≤ Nat.sqrt d)
    (hq' : 0 < (step d s).q)
    (he : (step d s).q * s.q = d - (step d s).m * (step d s).m) :
    ((Real.sqrt (d : ℝ) + s.m) / s.q - s.a)⁻¹ =
      (Real.sqrt (d : ℝ) + (step d s).m) / (step d s).q := by
  have hq0 : (s.q : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.q ≠ 0)
  have hq'0 : ((step d s).q : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : (step d s).q ≠ 0)
  have hmz : ((step d s).m : ℝ) = (s.q : ℝ) * s.a - s.m := by
    change ((s.q * s.a - s.m : ℕ) : ℝ) = _
    rw [Nat.cast_sub (by simpa [Nat.mul_comm] using ham), Nat.cast_mul]
  have he' : ((step d s).q : ℝ) * s.q =
      ((d - (step d s).m * (step d s).m : ℕ) : ℝ) := by
    exact_mod_cast he
  have hprod := sqrt_sub_mul_add (Nat.le_sqrt.mp hm')
  rw [← he', hmz] at hprod
  symm
  apply eq_inv_of_mul_eq_one_left
  field_simp
  rw [hmz]
  linear_combination hprod

private theorem complete_quotient_mul_ge (d m q a : ℕ) (hq : 0 < q)
    (hm : m ≤ Nat.sqrt d) (ha : a = (Nat.sqrt d + m) / q)
    (hx : 1 < (Real.sqrt (d : ℝ) + m) / q) : m ≤ a * q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hf := floor_complete_quotient d m q hq
  rw [← ha] at hf
  have hb := Int.floor_eq_iff.mp hf
  simp only [Int.cast_natCast] at hb
  have ha1 : 1 ≤ a := by
    by_contra h
    have : a = 0 := by omega
    simp only [this, Nat.cast_zero, zero_add] at hb
    linarith [hb.2]
  have hmR : (m : ℝ) ≤ Real.sqrt (d : ℝ) := by
    have hf0 := Int.floor_le (Real.sqrt (d : ℝ))
    rw [Real.floor_real_sqrt_eq_nat_sqrt] at hf0
    have : (m : ℝ) ≤ Nat.sqrt d := by exact_mod_cast hm
    simpa only [Int.cast_natCast] using le_trans this hf0
  have hu := (div_lt_iff₀ hqR).mp hb.2
  by_contra h
  have halt : a * q < m := by omega
  have haltR : (a : ℝ) * q < m := by exact_mod_cast halt
  have haq : q ≤ a * q := by nlinarith
  have haqR : (q : ℝ) ≤ (a : ℝ) * q := by exact_mod_cast haq
  nlinarith

private theorem complete_quotient_fr_ne (d m q a : ℕ)
    (hd : Nat.sqrt d * Nat.sqrt d ≠ d) (hq : 0 < q) (ham : m ≤ a * q) :
    (Real.sqrt (d : ℝ) + m) / q - a ≠ 0 := by
  intro h
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have he := sub_eq_zero.mp h
  field_simp at he
  apply nonsquare_cast_ne hd (a * q - m)
  rw [Nat.cast_sub ham, Nat.cast_mul]
  linarith

/-- The exact integer update preserves the complete-quotient invariant. -/
theorem state_inv_step (d : ℕ) (hd : Nat.sqrt d * Nat.sqrt d ≠ d)
    (n : ℕ) (s : State) (h : StateInv d n s) :
    StateInv d (n + 1) (step d s) := by
  obtain ⟨hq, hm, hw, ham, ha, hfr, hs⟩ := h
  have hm' := step_m_le_sqrt d s ha
  obtain ⟨hq', he⟩ := step_q_pos_mul d hd s hq hm ham ha hw
  have hinv := step_reciprocal d s hq ham hm' hq' he
  have ha' : (step d s).a = (Nat.sqrt d + (step d s).m) / (step d s).q := rfl
  have hf := floor_complete_quotient d s.m s.q hq
  rw [← ha] at hf
  have hfract : Int.fract ((Real.sqrt (d : ℝ) + s.m) / s.q) =
      (Real.sqrt (d : ℝ) + s.m) / s.q - s.a := by
    simp only [Int.fract, hf, Int.cast_natCast]
  have hnonneg := Int.fract_nonneg ((Real.sqrt (d : ℝ) + s.m) / s.q)
  have hlt := Int.fract_lt_one ((Real.sqrt (d : ℝ) + s.m) / s.q)
  rw [hfract] at hnonneg hlt
  have hpos : 0 < (Real.sqrt (d : ℝ) + s.m) / s.q - s.a := by
    exact lt_of_le_of_ne hnonneg (Ne.symm hfr)
  have hx' : 1 < (Real.sqrt (d : ℝ) + (step d s).m) / (step d s).q := by
    rw [← hinv]
    exact (one_lt_inv₀ hpos).mpr hlt
  have ham' := complete_quotient_mul_ge d _ _ _ hq' hm' ha' hx'
  have hfr' := complete_quotient_fr_ne d _ _ _ hd hq' ham'
  refine ⟨hq', hm', ⟨s.q, he⟩, ham', ha', hfr', ?_⟩
  refine GenContFract.IntFractPair.succ_nth_stream_eq_some_iff.mpr
    ⟨⟨(s.a : ℤ), (Real.sqrt (d : ℝ) + s.m) / s.q - s.a⟩, hs, hfr, ?_⟩
  change GenContFract.IntFractPair.of
    (((Real.sqrt (d : ℝ) + s.m) / s.q - s.a)⁻¹) = _
  rw [hinv]
  have hf' := floor_complete_quotient d (step d s).m (step d s).q hq'
  rw [← ha'] at hf'
  simp only [GenContFract.IntFractPair.of, Int.fract, hf', Int.cast_natCast]

/-- Every integer state represents the corresponding real complete quotient. -/
theorem general_inv (d : ℕ) (hd : Nat.sqrt d * Nat.sqrt d ≠ d) (n : ℕ) :
    StateInv d n (state d n) := by
  induction n with
  | zero => exact state_inv_zero d hd
  | succ n ih => exact state_inv_step d hd n (state d n) ih

/-- All coefficients agree with Mathlib, not merely a finite prefix. -/
theorem coeff_eq_nonsquare (d : ℕ) (hd : Nat.sqrt d * Nat.sqrt d ≠ d) (n : ℕ) :
    (GenContFract.of (Real.sqrt (d : ℝ))).s.get? n =
      some ⟨1, (coefficient d (n + 1) : ℝ)⟩ := by
  obtain ⟨_, _, _, _, _, _, hs⟩ := general_inv d hd (n + 1)
  rw [of_s_get?, hs]
  simp [coefficient]

/-- The integer algorithm computes the actual convergent numerators for every nonsquare. -/
theorem relation_nonsquare (d : ℕ) (hd : Nat.sqrt d * Nat.sqrt d ≠ d) (n : ℕ) :
    relation d n (computed d n) :=
  relation_computed_of_coefficients d (coeff_eq_nonsquare d hd) n

/-- The mathematical specification uniquely determines the executable numerator. -/
theorem relation_iff_eq_computed (d : ℕ) (hd : Nat.sqrt d * Nat.sqrt d ≠ d)
    (n p : ℕ) : relation d n p ↔ p = computed d n := by
  have hc := relation_nonsquare d hd n
  constructor
  · intro h
    exact Nat.cast_injective (h.trans hc.symm)
  · rintro rfl
    exact hc

/-- Finite source-program output. `prependOne` preserves the exceptional sqrt(5)/sqrt(10)
convention without changing the requested count of convergents. -/
def program (d count : Nat) (prependOne : Bool := false) : List Nat :=
  let values := (List.range count).map (computed d)
  if prependOne then 1 :: values else values

/-- Indexing preserves the source's finite convergent count. -/
theorem program_getElem? (d count i : ℕ) (h : i < count) :
    (program d count false)[i]? = some (computed d i) := by
  simp [program, List.getElem?_range h]

/-- The exceptional convention adds one element, rather than replacing a convergent. -/
theorem program_prepend_getElem? (d count i : ℕ) (h : i < count + 1) :
    (program d count true)[i]? = some (if i = 0 then 1 else computed d (i - 1)) := by
  cases i with
  | zero => simp [program]
  | succ i =>
    have hi : i < count := by omega
    simp [program, List.getElem?_range hi]

theorem program_length (d count : ℕ) (prependOne : Bool) :
    (program d count prependOne).length = count + (if prependOne then 1 else 0) := by
  cases prependOne <;> simp [program]

end
end OEISLib.Common.SqrtContinuedFraction
