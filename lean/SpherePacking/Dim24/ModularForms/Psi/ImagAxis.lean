-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.ModularForms.Psi.Defs
import SpherePacking.Tactic.NormNumI
import SpherePacking.Dim24.ModularForms.Psi.Relations


/-!
# Imaginary axis facts for `ψ`

Paper reference: used in `dim_24.tex`, Section 4 and Appendix A.
-/

namespace SpherePacking.Dim24

noncomputable section

open scoped Real ModularForm
open UpperHalfPlane Complex ModularGroup MatrixGroups

/-- Evaluate `ResToImagAxis F t` on the positive imaginary axis as `F (it t ht)`. -/
public lemma resToImagAxis_eq_it (F : ℍ → ℂ) (t : ℝ) (ht : 0 < t) :
    ResToImagAxis F t = F (it t ht) := by
  have hit :
      (⟨Complex.I * (t : ℂ), by simp [ht]⟩ : ℍ) = it t ht := by
    ext
    rfl
  unfold ResToImagAxis
  rw [dif_pos ht]
  simp [hit]

/-- The imaginary part of `it t ht` is `t`. -/
public lemma it_im (t : ℝ) (ht : 0 < t) : (it t ht).im = t := by
  simp [Dim24.it, UpperHalfPlane.im, Complex.mul_im]

private lemma Complex.eq_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext <;> simp [hz]

/-- On the positive imaginary axis, the real part of `ψI` is nonnegative. -/
public lemma ψI_imagAxis_re_nonneg (t : ℝ) (ht : 0 < t) : 0 ≤ (ψI (it t ht)).re := by
  set z : ℍ := it t ht
  have hH2im : (H₂ z).im = 0 := by
    simpa [z, resToImagAxis_eq_it (F := H₂) (t := t) ht] using! (H₂_imag_axis_pos.1 t ht)
  have hH4im : (H₄ z).im = 0 := by
    simpa [z, resToImagAxis_eq_it (F := H₄) (t := t) ht] using! (H₄_imag_axis_pos.1 t ht)
  have hΔim : (Δ z).im = 0 := by
    simpa [z, resToImagAxis_eq_it (F := Δ) (t := t) ht] using! (Delta_imag_axis_pos.1 t ht)
  have hH2pos : 0 < (H₂ z).re := by
    simpa [z, resToImagAxis_eq_it (F := H₂) (t := t) ht] using! (H₂_imag_axis_pos.2 t ht)
  have hH4pos : 0 < (H₄ z).re := by
    simpa [z, resToImagAxis_eq_it (F := H₄) (t := t) ht] using! (H₄_imag_axis_pos.2 t ht)
  have hΔpos : 0 < (Δ z).re := by
    simpa [z, resToImagAxis_eq_it (F := Δ) (t := t) ht] using! (Delta_imag_axis_pos.2 t ht)
  let h2 : ℝ := (H₂ z).re
  let h4 : ℝ := (H₄ z).re
  let d : ℝ := (Δ z).re
  have h2pos : 0 < h2 := by simpa [h2] using! hH2pos
  have h4pos : 0 < h4 := by simpa [h4] using! hH4pos
  have dpos : 0 < d := by simpa [d] using! hΔpos
  have hH2 : H₂ z = (h2 : ℂ) := by
    simpa [h2] using! (Complex.eq_of_im_eq_zero (z := H₂ z) hH2im)
  have hH4 : H₄ z = (h4 : ℂ) := by
    simpa [h4] using! (Complex.eq_of_im_eq_zero (z := H₄ z) hH4im)
  have hΔ : Δ z = (d : ℂ) := by
    simpa [d] using! (Complex.eq_of_im_eq_zero (z := Δ z) hΔim)
  have hre :
      (ψI z).re =
        (7 * h4 ^ 5 * h2 ^ 2 + 7 * h4 ^ 6 * h2 + 2 * h4 ^ 7) / (d ^ 2) := by
    rw [ψI_eq_H (z := z), hH2, hH4, hΔ]
    simp_rw [← Complex.ofReal_pow]
    -- Convert complex powers of real numbers to `ofReal` powers, then simplify.
    -- After simplification, we get a cancellation goal with an `Or`; we prove the main branch.
    simp only [div_eq_mul_inv, mul_re, add_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
      sub_zero, mul_im, zero_mul, add_zero, inv_re, normSq_ofReal, mul_inv_rev, add_im, inv_im,
      neg_zero, mul_eq_mul_left_iff]
    refine Or.inl ?_
    have hdne : d ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt dpos)
    rw [← mul_assoc, mul_inv_cancel₀ hdne]
    simp only [one_mul]
  have hd0 : 0 ≤ d ^ 2 := pow_nonneg (le_of_lt dpos) 2
  have hnum0 : 0 ≤ 7 * h4 ^ 5 * h2 ^ 2 + 7 * h4 ^ 6 * h2 + 2 * h4 ^ 7 := by
    positivity
  -- Now `re(ψI(it))` is a quotient of nonnegative reals.
  simpa [z, h2, h4, d, hre] using! (div_nonneg hnum0 hd0)

/-- On the positive imaginary axis, `ψI(it)` is real-valued. -/
public theorem ψI_imagAxis_real (t : ℝ) (ht : 0 < t) : (ψI (it t ht)).im = 0 := by
  /- Proof sketch:
  Same style as `ψS_imagAxis_nonpos`: each theta value is real on the imaginary axis, so the
  rational expression for `ψI` has zero imaginary part. -/
  set z : ℍ := it t ht
  have hH2im : (H₂ z).im = 0 := by
    simpa [z, resToImagAxis_eq_it (F := H₂) (t := t) ht] using! (H₂_imag_axis_real t ht)
  have hH4im : (H₄ z).im = 0 := by
    simpa [z, resToImagAxis_eq_it (F := H₄) (t := t) ht] using! (H₄_imag_axis_real t ht)
  have hΔim : (Δ z).im = 0 := by
    simpa [z, resToImagAxis_eq_it (F := Δ) (t := t) ht] using! (Delta_imag_axis_real t ht)
  have hH2 : H₂ z = ((H₂ z).re : ℂ) := Complex.eq_of_im_eq_zero (z := H₂ z) hH2im
  have hH4 : H₄ z = ((H₄ z).re : ℂ) := Complex.eq_of_im_eq_zero (z := H₄ z) hH4im
  have hΔ : Δ z = ((Δ z).re : ℂ) := Complex.eq_of_im_eq_zero (z := Δ z) hΔim
  -- After rewriting everything as `ofReal`, the expression has zero imaginary part.
  rw [ψI_eq_H (z := z), hH2, hH4, hΔ]
  simp_rw [← Complex.ofReal_pow]
  simp [div_eq_mul_inv, -Complex.ofReal_pow, -Complex.ofReal_zpow]

/-- On the positive imaginary axis, `ψS(it)` is real and nonpositive
(by its theta-series formula). -/
public theorem ψS_imagAxis_nonpos (t : ℝ) (ht : 0 < t) : (ψS (it t ht)).re ≤ 0 := by
  /- Proof sketch:
  Rewrite `ψS` using the explicit theta expression from the paper (after expanding the slash
  action), then use that `Θ₂(it),Θ₃(it),Θ₄(it)` are real and nonnegative for `t>0`,
  and `Δ(it)>0`.
  -/
  have hψS : ψS (it t ht) = ResToImagAxis ψS t := by
    simpa using! (resToImagAxis_eq_it (F := ψS) (t := t) ht).symm
  rw [hψS]
  have hSlash' :
      ResToImagAxis ψS t =
        (Complex.I : ℂ) ^ (10 : ℤ) * (t : ℂ) ^ (10 : ℤ) * ResToImagAxis ψI (1 / t) := by
    -- `ResToImagAxis ψS t` is definitionaly `ψS.resToImagAxis t`.
    change ψS.resToImagAxis t = _
    simpa [ψS] using!
      (ResToImagAxis.SlashActionS (F := ψI) (k := (-10 : ℤ)) (t := t) ht)
  rw [hSlash']
  have hI10 : (Complex.I : ℂ) ^ (10 : ℤ) = (-1 : ℂ) := by
    norm_num1
  rw [hI10]
  -- Reduce to the nonnegativity of `re(ψI(i/t))`.
  set s : ℝ := 1 / t
  have hs : 0 < s := by simpa [s] using! (one_div_pos.2 ht)
  have hψIim : (ResToImagAxis ψI s).im = 0 := by
    have h : (ψI (it s hs)).im = 0 := ψI_imagAxis_real (t := s) hs
    have hres := resToImagAxis_eq_it (F := ψI) (t := s) hs
    simpa [hres] using! h
  have hψIre : 0 ≤ (ResToImagAxis ψI s).re := by
    have h : 0 ≤ (ψI (it s hs)).re := ψI_imagAxis_re_nonneg (t := s) hs
    have hres := resToImagAxis_eq_it (F := ψI) (t := s) hs
    simpa [hres] using! h
  let a : ℂ := (t : ℂ) ^ (10 : ℤ)
  have ha : a = ((t ^ (10 : ℤ) : ℝ) : ℂ) := by
    dsimp [a]
    exact (Complex.ofReal_zpow t (10 : ℤ)).symm
  let x : ℂ := a * ResToImagAxis ψI s
  have hx : 0 ≤ x.re := by
    have htPow0 : 0 ≤ t ^ (10 : ℤ) := (zpow_pos ht (10 : ℤ)).le
    have hxa : x.re = t ^ (10 : ℤ) * (ResToImagAxis ψI s).re := by
      -- Rewrite `a` as an `ofReal` to simplify real/imag parts.
      simp [x, ha, Complex.mul_re, hψIim, -Complex.ofReal_zpow, -Complex.ofReal_pow]
    -- `x.re` is a product of two nonnegative reals.
    simpa [hxa] using! mul_nonneg htPow0 hψIre
  -- `(-1 : ℂ) * x = -x`, so the real part is `-(x.re) ≤ 0`.
  have : ((-x).re) ≤ 0 := by
    simpa using! (neg_nonpos.2 hx)
  -- Unfold `x`; the goal is exactly `(-x).re ≤ 0`.
  simpa [x, a, s, mul_assoc] using! this

end

end SpherePacking.Dim24
