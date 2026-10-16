-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.SpecialValuesExpU
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
public import SpherePacking.Dim24.ModularForms.Psi.Relations


/-!
# Rectangle identity for `ψI'` and `expU`

This file proves a finite-rectangle contour identity for the integrand `ψI' z * expU u z`. This is
the main analytic input for the limit `TopEdge(u,T) → Bfun(u)` as `T → ∞`.

## Main statements
* `ψI_rect_integral_eq_top_sub_vertical`
-/

open scoped Real
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter Set MeasureTheory intervalIntegral
open scoped Interval

namespace Deriv

/-- Relation between the `ψ`-functions on the upper half-plane:
`ψI' z - ψI' (z + 1) = ψS' z`. -/
public lemma ψI'_sub_ψI'_add_one_eq_ψS' (z : ℂ) (hz : 0 < z.im) :
    ψI' z - ψI' (z + 1) = ψS' z := by
  have hT : ψT' z = ψI' (z + 1) :=
    SpherePacking.Dim24.ψT'_eq_ψI'_add_one (z := z)
  have hsum :
      ψS' z + ψT' z = ψI' z := by
    have h := congrArg (fun F : ℍ → ℂ => F (UpperHalfPlane.mk z hz)) ψS_add_ψT_eq_ψI
    simpa [ψI', ψS', ψT', hz, UpperHalfPlane.mk, add_comm, add_left_comm, add_assoc] using! h
  -- Rearrange and replace `ψT' z` with `ψI'(z+1)`.
  calc
    ψI' z - ψI' (z + 1) = ψI' z - ψT' z := by simp [hT]
    _ = (ψS' z + ψT' z) - ψT' z := by simp [hsum.symm]
    _ = ψS' z := by ring_nf

/-- Rectangle identity comparing the bottom and top horizontal integrals to the vertical integral
of `ψS'`, for the integrand `ψI' z * expU u z`. -/
public lemma ψI_rect_integral_eq_top_sub_vertical (u : ℝ) (hu : expU u 1 = 1) {T : ℝ}
    (hT : (1 : ℝ) ≤ T) :
    (∫ x in (0 : ℝ)..1,
          ψI' ((x : ℂ) + Complex.I) * expU u ((x : ℂ) + Complex.I)) -
        (∫ x in (0 : ℝ)..1,
              ψI' ((x : ℂ) + (T : ℂ) * Complex.I) *
                expU u ((x : ℂ) + (T : ℂ) * Complex.I)) =
      (Complex.I : ℂ) •
        ∫ t in (1 : ℝ)..T, ψS' (t * Complex.I) * expU u (t * Complex.I) := by
  let f : ℂ → ℂ := fun z : ℂ => ψI' z * expU u z
  have hdiffOn_ψI_ofComplex :
      DifferentiableOn ℂ (fun z : ℂ => ψI (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
    differentiableOn_ψI_ofComplex
  have hdiffOn_ψI' : DifferentiableOn ℂ ψI' {z : ℂ | 0 < z.im} := by
    refine hdiffOn_ψI_ofComplex.congr ?_
    intro z hz
    have hz' : 0 < z.im := by simpa [Set.mem_setOf_eq] using! hz
    simp [ψI', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  have hdiffOn_exp : DifferentiableOn ℂ (fun z : ℂ => expU u z) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hlin :
        DifferentiableAt ℂ (fun z : ℂ => (Real.pi * Complex.I * (u : ℂ)) * z) z := by
      fun_prop
    have hexp :
        DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((Real.pi * Complex.I * (u : ℂ)) * z)) z :=
      hlin.cexp
    simpa [expU, mul_assoc, mul_left_comm, mul_comm] using! hexp.differentiableWithinAt
  have hdiffOn_f : DifferentiableOn ℂ f {z : ℂ | 0 < z.im} := hdiffOn_ψI'.mul hdiffOn_exp
  have hcontRect : ContinuousOn f ([[0, (1 : ℝ)]] ×ℂ [[(1 : ℝ), T]]) := by
    have hcont : ContinuousOn f {z : ℂ | 0 < z.im} := hdiffOn_f.continuousOn
    have hsubset : ([[0, (1 : ℝ)]] ×ℂ [[(1 : ℝ), T]]) ⊆ {z : ℂ | 0 < z.im} := by
      intro z hz
      have hzIm : z.im ∈ [[(1 : ℝ), T]] := (Complex.mem_reProdIm.1 hz).2
      have hzImIcc : z.im ∈ Set.Icc (1 : ℝ) T := by
        simpa [uIcc_of_le hT] using! hzIm
      have hzIm' : (1 : ℝ) ≤ z.im := hzImIcc.1
      exact lt_of_lt_of_le (by norm_num) hzIm'
    exact hcont.mono hsubset
  have hdiffRect :
      DifferentiableOn ℂ f (Ioo (0 : ℝ) 1 ×ℂ Ioo (1 : ℝ) T) := by
    refine hdiffOn_f.mono ?_
    intro z hz
    have hzIm : z.im ∈ Ioo (1 : ℝ) T := (Complex.mem_reProdIm.1 hz).2
    have : (1 : ℝ) < z.im := (mem_Ioo.1 hzIm).1
    exact lt_trans (by norm_num) this
  have hrect0 :
      (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), f (x + (1 : ℝ) * Complex.I)) -
          (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), f (x + T * Complex.I)) +
            (Complex.I : ℂ) • (∫ t : ℝ in (1 : ℝ)..T, f ((1 : ℂ) + t * Complex.I)) -
              (Complex.I : ℂ) • (∫ t : ℝ in (1 : ℝ)..T, f ((0 : ℂ) + t * Complex.I)) = 0 := by
    let z0 : ℂ := (0 : ℂ) + (1 : ℝ) * Complex.I
    let w0 : ℂ := (1 : ℂ) + T * Complex.I
    have hcontRect' : ContinuousOn f ([[z0.re, w0.re]] ×ℂ [[z0.im, w0.im]]) := by
      simpa [z0, w0, Complex.add_re, Complex.add_im, uIcc_of_le hT, mul_assoc, add_assoc, add_comm,
        add_left_comm] using! hcontRect
    have hdiffRect' :
        DifferentiableOn ℂ f
          (Ioo (min z0.re w0.re) (max z0.re w0.re) ×ℂ Ioo (min z0.im w0.im) (max z0.im w0.im)) := by
      simpa [z0, w0, Complex.add_re, Complex.add_im, min_eq_left (zero_le_one : (0 : ℝ) ≤ 1),
        max_eq_right (zero_le_one : (0 : ℝ) ≤ 1), min_eq_left hT, max_eq_right hT,
        mul_assoc, add_assoc, add_comm, add_left_comm] using! hdiffRect
    have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (f := f) (z := z0) (w := w0) hcontRect' hdiffRect'
    simpa
      [z0, w0, Complex.add_re, Complex.add_im, mul_assoc, add_assoc, add_left_comm, add_comm]
      using! h
  have hfcont : ContinuousOn f {z : ℂ | 0 < z.im} := hdiffOn_f.continuousOn
  let γ1 : ℝ → ℂ := fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I
  have hγ1 : ContinuousOn γ1 ([[ (1 : ℝ), T ]]) := by
    have : Continuous γ1 := by
      simpa [γ1] using! (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    exact this.continuousOn
  have hmap1 : MapsTo γ1 ([[ (1 : ℝ), T ]]) {z : ℂ | 0 < z.im} := by
    intro t ht
    have htIcc : t ∈ Set.Icc (1 : ℝ) T := by simpa [uIcc_of_le hT] using! ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htIcc.1
    simpa [γ1, Complex.add_im] using! ht0
  have hInt1 : IntervalIntegrable (fun t : ℝ => f (γ1 t)) MeasureTheory.volume (1 : ℝ) T := by
    have hcont1 : ContinuousOn (fun t : ℝ => f (γ1 t)) ([[ (1 : ℝ), T ]]) := hfcont.comp hγ1 hmap1
    simpa [γ1] using! hcont1.intervalIntegrable (μ := MeasureTheory.volume) (a := (1 : ℝ)) (b := T)
  let γ0 : ℝ → ℂ := fun t : ℝ => (0 : ℂ) + (t : ℂ) * Complex.I
  have hγ0 : ContinuousOn γ0 ([[ (1 : ℝ), T ]]) := by
    have : Continuous γ0 := by
      simpa [γ0] using! (Complex.continuous_ofReal.mul continuous_const)
    exact this.continuousOn
  have hmap0 : MapsTo γ0 ([[ (1 : ℝ), T ]]) {z : ℂ | 0 < z.im} := by
    assumption
  have hInt0 : IntervalIntegrable (fun t : ℝ => f (γ0 t)) MeasureTheory.volume (1 : ℝ) T := by
    have hcont0 : ContinuousOn (fun t : ℝ => f (γ0 t)) ([[ (1 : ℝ), T ]]) := hfcont.comp hγ0 hmap0
    simpa [γ0] using! hcont0.intervalIntegrable (μ := MeasureTheory.volume) (a := (1 : ℝ)) (b := T)
  have hvert :
      (∫ t : ℝ in (1 : ℝ)..T, f ((1 : ℂ) + t * Complex.I)) -
          (∫ t : ℝ in (1 : ℝ)..T, f ((0 : ℂ) + t * Complex.I)) =
        ∫ t : ℝ in (1 : ℝ)..T, -ψS' (t * Complex.I) * expU u (t * Complex.I) := by
    have hsub :
        (∫ t : ℝ in (1 : ℝ)..T, f ((1 : ℂ) + t * Complex.I) - f ((0 : ℂ) + t * Complex.I)) =
          (∫ t : ℝ in (1 : ℝ)..T, f ((1 : ℂ) + t * Complex.I)) -
            (∫ t : ℝ in (1 : ℝ)..T, f ((0 : ℂ) + t * Complex.I)) :=
      intervalIntegral.integral_sub hInt1 hInt0
    have hcongr :
        (∫ t : ℝ in (1 : ℝ)..T, f ((1 : ℂ) + t * Complex.I) - f ((0 : ℂ) + t * Complex.I)) =
          ∫ t : ℝ in (1 : ℝ)..T, -ψS' (t * Complex.I) * expU u (t * Complex.I) := by
      refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
      intro t ht
      have htIcc : t ∈ Set.Icc (1 : ℝ) T := by
        simpa [uIcc_of_le hT] using! ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) htIcc.1
      have hψ :
          ψI' (t * Complex.I) - ψI' (t * Complex.I + 1) = ψS' (t * Complex.I) :=
        ψI'_sub_ψI'_add_one_eq_ψS' (z := (t : ℂ) * Complex.I) (by simpa using! ht0)
      have hshift : expU u ((1 : ℂ) + t * Complex.I) = expU u (t * Complex.I) := by
        have := expU_add_one (u := u) hu (z := (t : ℂ) * Complex.I)
        simpa [add_comm, add_left_comm, add_assoc] using! this
      grind only
    lia
  have hvertSmul :
      (Complex.I : ℂ) • (∫ t : ℝ in (1 : ℝ)..T, f ((1 : ℂ) + t * Complex.I)) -
          (Complex.I : ℂ) • (∫ t : ℝ in (1 : ℝ)..T, f ((0 : ℂ) + t * Complex.I)) =
        -(Complex.I : ℂ) • ∫ t : ℝ in (1 : ℝ)..T, ψS' (t * Complex.I) * expU u (t * Complex.I) := by
    have h0 : (Complex.I : ℂ) •
        ((∫ t : ℝ in (1 : ℝ)..T, f ((1 : ℂ) + t * Complex.I)) -
            (∫ t : ℝ in (1 : ℝ)..T, f ((0 : ℂ) + t * Complex.I))) =
        (Complex.I : ℂ) • ∫ t : ℝ in (1 : ℝ)..T, -ψS' (t * Complex.I) * expU u (t * Complex.I) := by
      simpa using! congrArg (fun z : ℂ => (Complex.I : ℂ) • z) hvert
    have h1 :
        (Complex.I : ℂ) • (∫ t : ℝ in (1 : ℝ)..T, f ((1 : ℂ) + t * Complex.I)) -
            (Complex.I : ℂ) • (∫ t : ℝ in (1 : ℝ)..T, f ((0 : ℂ) + t * Complex.I)) =
          (Complex.I : ℂ) •
            ∫ t : ℝ in (1 : ℝ)..T, -ψS' (t * Complex.I) * expU u (t * Complex.I) := by
      simpa [smul_eq_mul, mul_sub] using! h0
    simpa
      [intervalIntegral.integral_neg, smul_neg, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      using! h1
  have hrect1 :
      (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), f (x + (1 : ℝ) * Complex.I)) -
          (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), f (x + T * Complex.I)) -
            (Complex.I : ℂ) •
              ∫ t : ℝ in (1 : ℝ)..T, ψS' (t * Complex.I) * expU u (t * Complex.I) = 0 := by
    have hrect0' :
        ((∫ x : ℝ in (0 : ℝ)..(1 : ℝ), f (x + (1 : ℝ) * Complex.I)) -
              (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), f (x + T * Complex.I))) +
            ((Complex.I : ℂ) • (∫ t : ℝ in (1 : ℝ)..T, f ((1 : ℂ) + t * Complex.I)) -
                (Complex.I : ℂ) • (∫ t : ℝ in (1 : ℝ)..T, f ((0 : ℂ) + t * Complex.I))) = 0 := by
      simpa [add_sub_assoc, add_assoc] using! hrect0
    have : ((∫ x : ℝ in (0 : ℝ)..(1 : ℝ), f (x + (1 : ℝ) * Complex.I)) -
                (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), f (x + T * Complex.I))) +
              (-(Complex.I : ℂ) •
                  ∫ t : ℝ in (1 : ℝ)..T,
                    ψS' (t * Complex.I) * expU u (t * Complex.I)) = 0 := by
      have h := hrect0'
      rw [hvertSmul] at h
      exact h
    simpa [sub_eq_add_neg, add_assoc] using! this
  have hbottom :
      (∫ x : ℝ in (0 : ℝ)..(1 : ℝ), f (x + (1 : ℝ) * Complex.I)) =
        ∫ x in (0 : ℝ)..1, ψI' ((x : ℂ) + Complex.I) * expU u ((x : ℂ) + Complex.I) := by
    simp [f]
  grind only

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
