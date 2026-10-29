import OEISLib.Common.SqrtContinuedFraction

/-! Kernel-checked applications of the general bridge, separate from finite value tests. -/

namespace OEISLib.Common.SqrtContinuedFraction.Test

private theorem six_nonsquare : Nat.sqrt 6 * Nat.sqrt 6 ≠ 6 := by decide +kernel

private theorem thirteen_nonsquare : Nat.sqrt 13 * Nat.sqrt 13 ≠ 13 := by decide +kernel

theorem invariant_six (n : ℕ) : StateInv 6 n (state 6 n) := by
  induction n with
  | zero => exact state_inv_zero 6 six_nonsquare
  | succ n ih => exact state_inv_step 6 six_nonsquare n (state 6 n) ih

theorem relation_six (n : ℕ) : relation 6 n (computed 6 n) :=
  relation_nonsquare 6 six_nonsquare n

theorem relation_thirteen (n : ℕ) : relation 13 n (computed 13 n) :=
  relation_nonsquare 13 thirteen_nonsquare n

/-- A concrete numeral is connected to Mathlib, not just to the integer evaluator. -/
theorem numerator_six_three : (GenContFract.of (Real.sqrt (6 : ℝ))).nums 3 = 49 := by
  have h := relation_six 3
  have hc : computed 6 3 = 49 := by decide +kernel
  unfold relation at h
  rw [hc] at h
  exact h.symm

end OEISLib.Common.SqrtContinuedFraction.Test
