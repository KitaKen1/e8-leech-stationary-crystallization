-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds

/-!
### Reducing the tail bound to a numerator estimate

Appendix A's tail bound is phrased in terms of `BKernel - leading`. This file defines the explicit
leading term `BleadingLeadingTerm` and the numerator
`BleadingNum = (BKernel - BleadingLeadingTerm) * Δ(it)^2`, and shows that a lower bound on
`(BleadingNum t ht).re` yields a lower bound on `(BKernel t ht).re - BleadingLeadingTerm t`.
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

/-- The explicit leading term subtracted from `BKernel` in Appendix A. -/
@[expose]
public def BleadingLeadingTerm (t : ℝ) : ℝ :=
  (1 / 39 : ℝ) * t * Real.exp (2 * Real.pi * t) -
    (10 / (117 * Real.pi) : ℝ) * Real.exp (2 * Real.pi * t)

/-- The numerator `(BKernel - BleadingLeadingTerm) * Δ(it)^2` used to control the tail bound. -/
@[expose]
public def BleadingNum (t : ℝ) (ht : 0 < t) : ℂ :=
  (BKernel t ht - (BleadingLeadingTerm t : ℂ)) * (Δ (it t ht)) ^ (2 : ℕ)

private lemma BleadingNum_re (t : ℝ) (ht : 0 < t) :
    (BleadingNum t ht).re = ((BKernel t ht).re - BleadingLeadingTerm t) * (Δ (it t ht)).re ^ 2 := by
  have hΔim : (Δ (it t ht)).im = 0 := Delta_it_im (t := t) ht
  simp [BleadingNum, BleadingNum, pow_two, Complex.mul_re, Complex.mul_im, hΔim,
    sub_eq_add_neg]

private lemma Bleading_re_div_Delta_sq (t : ℝ) (ht : 0 < t) :
    (BKernel t ht).re - BleadingLeadingTerm t = (BleadingNum t ht).re / (Δ (it t ht)).re ^ 2 := by
  have hpos : 0 < (Δ (it t ht)).re := Delta_it_re_pos (t := t) ht
  have hΔne : (Δ (it t ht)).re ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hpos)
  have h := BleadingNum_re (t := t) ht
  exact Eq.symm (div_eq_of_eq_mul hΔne h)

/--
If `L` is a nonnegative lower bound for `(BleadingNum t ht).re`, then it is also a lower bound for
`(BKernel t ht).re - BleadingLeadingTerm t`.
-/
public theorem Bleading_lowerBound_of_num {t : ℝ} (ht : 0 < t) {L : ℝ}
    (hL : 0 ≤ L)
    (hnum : L ≤ (BleadingNum t ht).re) :
    L ≤ (BKernel t ht).re - BleadingLeadingTerm t := by
  have hpos : 0 < (Δ (it t ht)).re := Delta_it_re_pos (t := t) ht
  have hsq_le_one : (Δ (it t ht)).re ^ 2 ≤ 1 := Delta_it_re_sq_le_one (t := t) ht
  have hinv_ge_one : (1 : ℝ) ≤ 1 / ((Δ (it t ht)).re ^ 2) := by
    have : (1 : ℝ) / 1 ≤ (1 : ℝ) / ((Δ (it t ht)).re ^ 2) :=
      one_div_le_one_div_of_le (pow_pos hpos 2) hsq_le_one
    simpa using! this
  calc
    L ≤ L * (1 / ((Δ (it t ht)).re ^ 2)) := by
          simpa [mul_one] using! (mul_le_mul_of_nonneg_left hinv_ge_one hL)
    _ ≤ (BleadingNum t ht).re * (1 / ((Δ (it t ht)).re ^ 2)) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = (BleadingNum t ht).re / (Δ (it t ht)).re ^ 2 := by
          simp [div_eq_mul_inv]
    _ = (BKernel t ht).re - BleadingLeadingTerm t := by
          simp [Bleading_re_div_Delta_sq (t := t) ht]

end SpherePacking.Dim24
