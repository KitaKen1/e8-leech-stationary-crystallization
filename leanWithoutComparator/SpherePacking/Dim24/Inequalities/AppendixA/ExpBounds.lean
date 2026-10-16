-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Real.Basic


/-!
Elementary exponential bounds used in Appendix A truncation arguments.

This file provides a certified rational upper bound for `q(t) = exp(-2πt)` when `t ≥ 1`.
-/


open scoped BigOperators Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

private def x0Q : ℚ := (6283184 : ℚ) / 1000000

private def x0 : ℝ := (x0Q : ℝ)

private lemma x0_eq_two_mul_piLower : x0 = 2 * (3.141592 : ℝ) := by
  norm_num [x0, x0Q]

private lemma x0_nonneg : 0 ≤ x0 := by
  norm_num [x0, x0Q]

/--
Lower bound for `Real.exp x` by truncating its power series.

This is the inequality `∑_{n=0}^N x^n / n! ≤ exp(x)` for `x ≥ 0`.
-/
public lemma exp_lower_bound_range (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (Finset.sum (Finset.range (N + 1)) (fun n => x ^ n / (Nat.factorial n))) ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx (N + 1)

private lemma exp_x0_gt_535 : (535 : ℝ) < Real.exp x0 := by
  have hle' :
      Finset.sum (Finset.range 16) (fun n => x0 ^ n / (Nat.factorial n)) ≤ Real.exp x0 := by
    simpa using! exp_lower_bound_range (x := x0) x0_nonneg 15
  -- The partial sum is rational, so we prove the comparison in `ℚ` and cast.
  have hsum_gt :
      (535 : ℝ) < Finset.sum (Finset.range 16) (fun n => x0 ^ n / (Nat.factorial n)) := by
    set sQ : ℚ :=
        Finset.sum (Finset.range 16) (fun n => x0Q ^ n / (Nat.factorial n)) with hsQ
    have hsQ_gt : (535 : ℚ) < sQ := by
      rw [hsQ]
      -- `decide` does not reduce comparisons on `ℚ` (it gets stuck at `Rat.blt`), so we expand the
      -- finite sum and let `norm_num` clear denominators and discharge the resulting arithmetic
      -- goal.
      set_option maxRecDepth 6000 in
      simp [Finset.sum_range_succ, x0Q, div_eq_mul_inv, Nat.factorial]
      norm_num
    have hsQ_gtR : (535 : ℝ) < (sQ : ℝ) := by
      exact_mod_cast hsQ_gt
    simpa [hsQ, x0, x0Q, div_eq_mul_inv] using! hsQ_gtR
  exact lt_of_lt_of_le hsum_gt hle'

private lemma exp_two_pi_gt_535 : (535 : ℝ) < Real.exp (2 * Real.pi) := by
  have hx0_lt : x0 < 2 * Real.pi := by
    simpa [x0_eq_two_mul_piLower] using!
      (mul_lt_mul_of_pos_left Real.pi_gt_d6 (by norm_num : (0 : ℝ) < 2))
  exact lt_trans exp_x0_gt_535 (Real.exp_lt_exp.2 hx0_lt)

/-- Numeric bound used in Appendix A: `exp(-2π) < 1/535`. -/
public lemma exp_neg_two_pi_lt_one_div_535 : Real.exp (-2 * Real.pi) < (1 : ℝ) / 535 := by
  -- `exp(-x) = 1/exp(x)`.
  simpa [Real.exp_neg, one_div] using!
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < (535 : ℝ)) exp_two_pi_gt_535)

/-- For `t ≥ 1`, the value `exp(-2πt)` is at most `1/535`. -/
public lemma q_le_one_div_535_of_one_le (t : ℝ) (ht : 1 ≤ t) :
    Real.exp (-2 * Real.pi * t) ≤ (1 : ℝ) / 535 := by
  have hmul : (-2 * Real.pi * t) ≤ (-2 * Real.pi) := by
    -- Multiply `1 ≤ t` by the nonpositive constant `-2π`.
    have hneg : (-2 * Real.pi) ≤ 0 := by nlinarith [Real.pi_pos]
    simpa [mul_assoc] using! (mul_le_mul_of_nonpos_left ht hneg)
  exact (Real.exp_le_exp.2 hmul).trans (le_of_lt exp_neg_two_pi_lt_one_div_535)

end

end SpherePacking.Dim24.AppendixA
