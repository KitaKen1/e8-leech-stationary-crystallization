-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
import Mathlib.Init
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSRectAnalytic
public import SpherePacking.Dim24.MagicFunction.SpecialValuesExpU
public import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims

/-!
# Rectangle integral identity for `ψS'`

This file proves a rectangle-domain integral identity for `ψS'` with the exponential factor
`expU`. The result is used both in the `b` special-value development and in the Laplace-profile
development.

## Main statements
* `ψS_rect_integral_eq_one_add_expU_one_mul_vertical`
-/

noncomputable section

namespace SpherePacking.Dim24.SpecialValuesAux

open Set
open MeasureTheory
open intervalIntegral
open Complex
open scoped Interval

/-- A rectangle-domain integral identity for `ψS'` with exponential twist `expU`. -/
public lemma ψS_rect_integral_eq_one_add_expU_one_mul_vertical (u : ℝ) (hu0 : 0 ≤ u) :
    (∫ x in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I) * expU u ((x : ℂ) + Complex.I)) =
      (1 + expU u 1) *
        (Complex.I • ∫ t in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)) := by
  let fU : ℂ → ℂ := fun z : ℂ => ψS' z * expU u z
  have hcont :
      ContinuousOn fU (Set.uIcc (0 : ℝ) 1 ×ℂ (Set.Ici (1 : ℝ))) := by
    refine (continuousOn_ψS'_rect.mul ?_)
    have hcontE : Continuous fun z : ℂ => expU u z := continuous_expU (u := u)
    exact hcontE.continuousOn
  have hdiff :
      ∀ x ∈ ((Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) ×ℂ (Set.Ioi (1 : ℝ))) \ (∅ : Set ℂ),
        DifferentiableAt ℂ fU x := by
    intro z hz
    have hzIm1 : z.im ∈ Set.Ioi (1 : ℝ) := (Complex.mem_reProdIm.1 (by simpa using! hz.1)).2
    have hzIm : 0 < z.im := lt_of_lt_of_le (by norm_num) (le_of_lt hzIm1)
    have hψ : DifferentiableAt ℂ ψS' z := differentiableAt_ψS'_of_im_pos z hzIm
    have hE : DifferentiableAt ℂ (fun w : ℂ => expU u w) z := by
      simpa using! (differentiableAt_expU (u := u) (z := z))
    simpa [fU] using! hψ.mul hE
  have hint₁ :
      MeasureTheory.IntegrableOn (fun t : ℝ => fU ((0 : ℂ) + t * Complex.I)) (Set.Ioi (1 : ℝ))
        MeasureTheory.volume := by
    have hf :
        MeasureTheory.Integrable (fun t : ℝ => ψS' (t * Complex.I))
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using!
        SpherePacking.Dim24.PsiSPrelims.integrableOn_ψS'_vertical_left
    have hg :
        MeasureTheory.AEStronglyMeasurable (fun t : ℝ => expU u (t * Complex.I))
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      have : Continuous fun t : ℝ => expU u (t * Complex.I) := by
        have : Continuous fun t : ℝ => Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I) := by
          fun_prop
        simpa [expU, mul_assoc] using! this.cexp
      exact this.aestronglyMeasurable
    have hbound :
        ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)),
          ‖expU u (t * Complex.I)‖ ≤ 1 := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 ≤ (t * Complex.I).im := by
        have : 0 ≤ t := le_of_lt (lt_of_lt_of_le (by norm_num) (le_of_lt ht))
        simpa using! this
      exact norm_expU_le_one (u := u) hu0 (z := t * Complex.I) ht0
    have hmul :
        MeasureTheory.Integrable (fun t : ℝ => ψS' (t * Complex.I) * expU u (t * Complex.I))
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
      hf.mul_bdd hg hbound
    simpa [fU, MeasureTheory.IntegrableOn, add_comm, add_left_comm, add_assoc, mul_assoc] using! hmul
  have hint₂ :
      MeasureTheory.IntegrableOn (fun t : ℝ => fU ((1 : ℂ) + t * Complex.I)) (Set.Ioi (1 : ℝ))
        MeasureTheory.volume := by
    have hf :
        MeasureTheory.Integrable (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I))
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using!
        SpherePacking.Dim24.PsiSPrelims.integrableOn_ψS'_vertical_right
    have hg :
        MeasureTheory.AEStronglyMeasurable (fun t : ℝ => expU u ((1 : ℂ) + t * Complex.I))
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      have : Continuous fun t : ℝ => expU u ((1 : ℂ) + t * Complex.I) := by
        have : Continuous fun t : ℝ =>
            Real.pi * Complex.I * (u : ℂ) * ((1 : ℂ) + (t : ℂ) * Complex.I) := by
          fun_prop
        simpa [expU, mul_assoc] using! this.cexp
      exact this.aestronglyMeasurable
    have hbound :
        ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))),
          ‖expU u ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (1 : ℝ) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le (by norm_num) (le_of_lt ht))
      exact norm_expU_le_one (u := u) hu0 (z := (1 : ℂ) + (t : ℂ) * Complex.I) (by simpa using! ht0)
    have hmul :
        MeasureTheory.Integrable
          (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I) * expU u ((1 : ℂ) + t * Complex.I))
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
      hf.mul_bdd hg hbound
    simpa [fU, MeasureTheory.IntegrableOn] using! hmul
  have htendsto_fU :
      ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖fU z‖ < ε := by
    intro ε hε
    rcases SpherePacking.Dim24.PsiSPrelims.htendsto_ψS' ε hε with ⟨M0, hM0⟩
    refine ⟨max M0 0, ?_⟩
    intro z hzM
    have hzM0 : M0 ≤ z.im := le_trans (le_max_left _ _) hzM
    have hz0 : 0 ≤ z.im := le_trans (le_max_right _ _) hzM
    have hnorm : ‖expU u z‖ ≤ 1 := norm_expU_le_one (u := u) hu0 (z := z) hz0
    have h' : ‖fU z‖ ≤ ‖ψS' z‖ := by
      have := mul_le_mul_of_nonneg_left hnorm (norm_nonneg (ψS' z))
      simpa [fU, norm_mul, mul_one] using! this
    exact lt_of_le_of_lt h' (hM0 z hzM0)
  have hrect :
      (∫ (x : ℝ) in (0 : ℝ)..1, fU (x + (1 : ℝ) * Complex.I)) +
          (Complex.I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU ((1 : ℂ) + t * Complex.I)) -
            (Complex.I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU ((0 : ℂ) + t * Complex.I)) = 0 := by
    have hrect0 :=
      integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ))
        (f := fU)
        (x₁ := (0 : ℝ))
        (x₂ := (1 : ℝ))
        hcont
        (s := (∅ : Set ℂ))
        (by simp)
        hdiff
        hint₁
        hint₂
        htendsto_fU
    simpa [min_eq_left (zero_le_one : (0 : ℝ) ≤ 1), max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] using!
      hrect0
  have hright :
      (∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU ((1 : ℂ) + t * Complex.I)) =
        -((∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU (t * Complex.I)) * (expU u 1)) := by
    have hEq :
        (fun t : ℝ => fU ((1 : ℂ) + t * Complex.I)) =ᵐ[
            MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))
          ] fun t : ℝ => -(fU (t * Complex.I) * (expU u 1)) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
      have hψ : ψS' ((1 : ℂ) + t * Complex.I) = -ψS' (t * Complex.I) :=
        SpherePacking.Dim24.PsiSPrelims.ψS'_add_one t ht0
      have hexp : expU u ((1 : ℂ) + t * Complex.I) = expU u (t * Complex.I) * expU u 1 := by
        simpa [expU, add_assoc, add_left_comm, add_comm, mul_assoc] using!
          (expU_add_one_mul (u := u) (z := (t : ℂ) * Complex.I))
      calc
        fU ((1 : ℂ) + t * Complex.I) =
            ψS' ((1 : ℂ) + t * Complex.I) * expU u ((1 : ℂ) + t * Complex.I) := rfl
        _ = (-ψS' (t * Complex.I)) * (expU u (t * Complex.I) * expU u 1) := by
            simp [hψ, hexp]
        _ = -(ψS' (t * Complex.I) * (expU u (t * Complex.I) * expU u 1)) := by
            simp [neg_mul]
        _ = -(fU (t * Complex.I) * expU u 1) := by
            simp [fU, mul_assoc]
    have hEqInt :
        (∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU ((1 : ℂ) + t * Complex.I)) =
          ∫ (t : ℝ) in Set.Ioi (1 : ℝ), -(fU (t * Complex.I) * (expU u 1)) := by
      simpa using! (MeasureTheory.integral_congr_ae hEq)
    have :
        ∫ (t : ℝ) in Set.Ioi (1 : ℝ), -(fU (t * Complex.I) * (expU u 1)) =
          -((∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU (t * Complex.I)) * (expU u 1)) := by
      simp [MeasureTheory.integral_neg, MeasureTheory.integral_mul_const]
    simpa [hEqInt] using! this
  have hleft :
      (∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU ((0 : ℂ) + t * Complex.I)) =
        ∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU (t * Complex.I) := by
    simp
  have hhor :
      (∫ (x : ℝ) in (0 : ℝ)..1, fU (x + (1 : ℝ) * Complex.I)) =
        (1 + expU u 1) * (Complex.I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU (t * Complex.I)) := by
    have hrect' :
        (∫ (x : ℝ) in (0 : ℝ)..1, fU (x + (1 : ℝ) * Complex.I)) +
            (Complex.I • (-(∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU (t * Complex.I)) * expU u 1)) -
              (Complex.I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU (t * Complex.I)) = 0 := by
      simpa [hright, hleft] using! hrect
    have hEq :
        (∫ (x : ℝ) in (0 : ℝ)..1, fU (x + (1 : ℝ) * Complex.I)) =
          (Complex.I • (∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU (t * Complex.I)) * expU u 1) +
            (Complex.I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU (t * Complex.I)) := by
      have :
          (∫ (x : ℝ) in (0 : ℝ)..1, fU (x + (1 : ℝ) * Complex.I)) -
              ((Complex.I • (∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU (t * Complex.I)) * expU u 1) +
                (Complex.I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ), fU (t * Complex.I))) = 0 := by
        simpa
            [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_neg,
              mul_assoc, mul_left_comm, mul_comm]
          using! hrect'
      exact sub_eq_zero.mp this
    grind only
  simpa [fU, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using! hhor

end SpherePacking.Dim24.SpecialValuesAux

end
