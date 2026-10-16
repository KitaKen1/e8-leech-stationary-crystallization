-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
public import Mathlib.Analysis.Real.Pi.Bounds
import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
import SpherePacking.Dim24.ModularForms.Psi.Relations
import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
import Mathlib.Tactic.Ring


/-!
# Clearing denominators via `Δ(it)^2`

Appendix A works with the numerators `varphi_num` and `psiS_num` obtained after clearing the factor
`Δ(z)^2` in `varphi` and `ψS`. This file records the corresponding algebraic rewrites and the
"real-on-the-imaginary-axis" facts needed to pass from numerator bounds to real-part inequalities.

## Main definitions
* `varphi_num`
* `psiS_num`

## Main statements
* `psiS_eq_psiS_num_div_Delta_sq`
* `varphi_num_it_im`, `psiS_num_it_im`
* `ineq2_num_it_re_eq`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

open AppendixA


/-- Numerator of `varphi z` after clearing the factor `Δ z ^ 2`. -/
@[expose] public def varphi_num (z : ℍ) : ℂ :=
  (25 * (E₄ z) ^ 4 - 49 * (E₆ z) ^ 2 * (E₄ z))
      + 48 * (E₆ z) * (E₄ z) ^ 2 * (E₂ z)
      + ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2) * (E₂ z) ^ 2

/-- Numerator of `ψS z` after clearing the factor `Δ z ^ 2`. -/
@[expose] public def psiS_num (z : ℍ) : ℂ :=
  -((7 : ℂ) * (H₂ z) ^ 5 * (H₄ z) ^ 2 + (7 : ℂ) * (H₂ z) ^ 6 * (H₄ z) + (2 : ℂ) * (H₂ z) ^ 7)

/-- Rewrite `ψS` as `psiS_num / Δ^2`. -/
public lemma psiS_eq_psiS_num_div_Delta_sq (z : ℍ) :
    ψS z = psiS_num z / (Δ z) ^ 2 := by
  set expr : ℂ :=
    (7 : ℂ) * (H₂ z) ^ 5 * (H₄ z) ^ 2 + (7 : ℂ) * (H₂ z) ^ 6 * (H₄ z) + (2 : ℂ) * (H₂ z) ^ 7
  have h : ψS z = -(expr / (Δ z) ^ 2) := by
    simpa [expr, add_assoc, add_left_comm, add_comm] using! (ψS_apply z)
  calc
    ψS z = -(expr / (Δ z) ^ 2) := h
    _ = (-expr) / (Δ z) ^ 2 := by simp [div_eq_mul_inv]
    _ = psiS_num z / (Δ z) ^ 2 := by simp [psiS_num, expr]

/-- On the imaginary axis, `varphi_num (it t)` has vanishing imaginary part. -/
public lemma varphi_num_it_im (t : ℝ) (ht0 : 0 < t) : (varphi_num (it t ht0)).im = 0 := by
  have hE4 : (E₄ (it t ht0)).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using! (E₄_imag_axis_real t ht0)
  have hE6 : (E₆ (it t ht0)).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using! (E₆_imag_axis_real t ht0)
  have hE2 : (E₂ (it t ht0)).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using! (E₂_imag_axis_real t ht0)
  have hE4_2 : ((E₄ (it t ht0)) ^ 2).im = 0 := Complex.im_pow_eq_zero_of_im_eq_zero hE4 2
  have hE4_3 : ((E₄ (it t ht0)) ^ 3).im = 0 := Complex.im_pow_eq_zero_of_im_eq_zero hE4 3
  have hE4_4 : ((E₄ (it t ht0)) ^ 4).im = 0 := Complex.im_pow_eq_zero_of_im_eq_zero hE4 4
  have hE6_2 : ((E₆ (it t ht0)) ^ 2).im = 0 := Complex.im_pow_eq_zero_of_im_eq_zero hE6 2
  have hE2_2 : ((E₂ (it t ht0)) ^ 2).im = 0 := Complex.im_pow_eq_zero_of_im_eq_zero hE2 2
  simp [varphi_num, Complex.add_im, Complex.sub_im, Complex.mul_im, hE4, hE6, hE2, hE4_2, hE4_3,
    hE4_4, hE6_2, hE2_2, -E4_apply, -E6_apply]

/-- On the imaginary axis, `psiS_num (it t)` has vanishing imaginary part. -/
public lemma psiS_num_it_im (t : ℝ) (ht0 : 0 < t) : (psiS_num (it t ht0)).im = 0 := by
  have hH2 : (H₂ (it t ht0)).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using! (H₂_imag_axis_real t ht0)
  have hH4 : (H₄ (it t ht0)).im = 0 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using! (H₄_imag_axis_real t ht0)
  have hH2_5 : ((H₂ (it t ht0)) ^ 5).im = 0 := Complex.im_pow_eq_zero_of_im_eq_zero hH2 5
  have hH2_6 : ((H₂ (it t ht0)) ^ 6).im = 0 := Complex.im_pow_eq_zero_of_im_eq_zero hH2 6
  have hH2_7 : ((H₂ (it t ht0)) ^ 7).im = 0 := Complex.im_pow_eq_zero_of_im_eq_zero hH2 7
  have hH4_2 : ((H₄ (it t ht0)) ^ 2).im = 0 := Complex.im_pow_eq_zero_of_im_eq_zero hH4 2
  simp [psiS_num, Complex.add_im, Complex.mul_im, hH4, hH2_5, hH2_6, hH2_7, hH4_2]

/--
Real-part identity used in the denominator reduction step.

It expresses `(varphi - (432/π^2) * ψS).re` at `z = it t` in terms of the numerator real part
divided by `((Δ (it t)).re)^2`.
-/
public lemma ineq2_num_it_re_eq (t : ℝ) (ht0 : 0 < t) :
    (varphi (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * ψS (it t ht0)).re =
      ((varphi_num (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * psiS_num (it t ht0)).re) /
        ((Δ (it t ht0)).re ^ 2) := by
  set z : ℍ := it t ht0
  have hvarphi : varphi z = varphi_num z / (Δ z) ^ 2 := by
    simp [Dim24.varphi, varphi_num]
  have hpsiS : ψS z = psiS_num z / (Δ z) ^ 2 :=
    psiS_eq_psiS_num_div_Delta_sq (z := z)
  have hmain :
      varphi z - (432 / (Real.pi ^ 2) : ℂ) * ψS z =
        (varphi_num z - (432 / (Real.pi ^ 2) : ℂ) * psiS_num z) / (Δ z) ^ 2 := by
    simp [hvarphi, hpsiS, div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_comm]
    ring
  have hΔim : (Δ z).im = 0 := Delta_it_im (t := t) ht0
  set d : ℝ := (Δ z).re ^ 2
  have hΔ2 : (Δ z) ^ 2 = (d : ℂ) := by
    refine Complex.ext ?_ ?_
    · rw [pow_two]
      simp [d, Complex.mul_re, hΔim, pow_two]
    · have hleft : ((Δ z) ^ 2).im = 0 := Complex.im_pow_eq_zero_of_im_eq_zero hΔim 2
      simp [hleft]
  have hdiv (w : ℂ) (d : ℝ) : (w / (d : ℂ)).re = w.re / d :=
    Complex.div_ofReal_re w d
  -- Put everything over the real denominator `((Δ(it)).re)^2` and take real parts.
  grind only


end SpherePacking.Dim24
