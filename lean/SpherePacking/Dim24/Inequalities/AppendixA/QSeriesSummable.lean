-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum


/-!
Summability helpers for Appendix A `q`-series on the imaginary axis.

These are extracted from the truncation arguments in Appendix A (see `appendix.txt`), where one
needs to justify Cauchy products and tail estimates for series of the form
`∑ aₙ q(t)^n` with polynomially bounded coefficients.
-/


open scoped BigOperators
open UpperHalfPlane

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- For `t ≥ 1`, `q t = exp(-2πt)` is bounded by `exp(-2π)`. -/
public lemma q_le_exp_neg_two_pi (t : ℝ) (ht : 1 ≤ t) : q t ≤ Real.exp (-2 * Real.pi) := by
  simpa [q] using! Real.exp_le_exp.2 (by nlinarith [ht, Real.pi_pos.le])

/-- The base ratio `exp(-2π)` is strictly less than `1`. -/
public lemma exp_neg_two_pi_lt_one : Real.exp (-2 * Real.pi) < 1 :=
  Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])

/--
A generic summability criterion for `qseries`-terms at `z = it t` using a polynomial coefficient
bound.
-/
public lemma summable_norm_qseries_of_coeffBound (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t)
    (a : ℕ → ℚ) (C : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    Summable (fun n : ℕ => ‖(a n : ℂ) * qterm (it t ht0) n‖) := by
  -- Compare to `C * (n+1)^k * r0^n` with `r0 = exp(-2π)` and `q t ≤ r0`.
  set r0 : ℝ := Real.exp (-2 * Real.pi)
  have hr0_nonneg : 0 ≤ r0 := (Real.exp_pos _).le
  have hr0_lt_one : r0 < 1 := by simpa [r0] using! exp_neg_two_pi_lt_one
  have hr0_norm : ‖r0‖ < 1 := by simpa [Real.norm_of_nonneg hr0_nonneg] using! hr0_lt_one
  have hq_le : q t ≤ r0 := by simpa [r0] using! q_le_exp_neg_two_pi t ht
  have hq0 : 0 ≤ q t := (Real.exp_pos _).le
  have hqpow_le : ∀ n : ℕ, (q t) ^ n ≤ r0 ^ n := fun n => pow_le_pow_left₀ hq0 hq_le n
  have hC0 : 0 ≤ C := by
    refine le_trans (abs_nonneg (a := (a 0 : ℝ))) ?_
    simpa using! (ha 0)
  have hs_pow : Summable (fun n : ℕ => ((n : ℝ) ^ k : ℝ) * r0 ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hr0_norm
  have hs_shift :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * r0 ^ (n + 1)) := by
    simpa [Nat.cast_add, Nat.cast_one] using!
      (summable_nat_add_iff 1 (f := fun n : ℕ => ((n : ℝ) ^ k : ℝ) * r0 ^ n)).2 hs_pow
  have hr0_pos : 0 < r0 := Real.exp_pos _
  have hs_shift' :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * r0 ^ n) := by
    have hs1 :
        Summable (fun n : ℕ => (1 / r0) * (((n + 1 : ℕ) : ℝ) ^ k * r0 ^ (n + 1))) :=
      hs_shift.mul_left (1 / r0)
    refine hs1.congr ?_
    intro n
    field_simp [hr0_pos.ne']
    simp [pow_succ, mul_comm]
  have hs_major : Summable (fun n : ℕ => C * (((n + 1 : ℕ) : ℝ) ^ k * r0 ^ n)) :=
    hs_shift'.mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hs_major
  intro n
  have hnorm_q : ‖qterm (it t ht0) n‖ = (q t) ^ n := by
    simpa using! norm_qterm_it (t := t) (ht := ht0) (n := n)
  calc
    ‖(a n : ℂ) * qterm (it t ht0) n‖
        = ‖(a n : ℂ)‖ * ‖qterm (it t ht0) n‖ := by simp
    _ = |(a n : ℝ)| * (q t) ^ n := by simp [hnorm_q]
    _ ≤ (C * (((n + 1 : ℕ) : ℝ) ^ k)) * (q t) ^ n := by
          exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hq0 _)
    _ ≤ (C * (((n + 1 : ℕ) : ℝ) ^ k)) * r0 ^ n := by
          have hCn : 0 ≤ C * (((n + 1 : ℕ) : ℝ) ^ k) := mul_nonneg hC0 (by positivity)
          exact mul_le_mul_of_nonneg_left (hqpow_le n) hCn
    _ = C * (((n + 1 : ℕ) : ℝ) ^ k * r0 ^ n) := by ring

end

end SpherePacking.Dim24.AppendixA
