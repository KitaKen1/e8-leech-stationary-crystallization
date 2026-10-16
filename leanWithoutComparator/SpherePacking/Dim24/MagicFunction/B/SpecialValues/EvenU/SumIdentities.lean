-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.EvenU.J135Factor
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims
import SpherePacking.Dim24.MagicFunction.B.Defs.J3Smooth
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.TopEdge.J6


/-!
# Cancellation identities at `expU u 1 = 1`

This file proves that the two sub-sums `J₁' + J₃' + J₅'` and `J₂' + J₄' + J₆'` vanish whenever
`expU u 1 = 1`. The first identity follows immediately from the factorization in
`EvenU.J135Factor`; the second uses the same open-rectangle deformation argument as in the
special-value computation for `b`.

## Main statements
* `J₁'_J₃'_J₅'_zero_sum_of`
* `J₂'_J₄'_J₆'_zero_sum_of`
-/


open scoped Real
open scoped Interval

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Set intervalIntegral
open RealIntegrals

/-- If `expU u 1 = 1`, then the sum `J₁' u + J₃' u + J₅' u` vanishes. -/
public lemma J₁'_J₃'_J₅'_zero_sum_of (u : ℝ) (hu : expU u 1 = 1) :
    J₁' u + J₃' u + J₅' u = 0 := by
  -- This is immediate from the exact factorization of `J₁'+J₃'+J₅'`.
  have hfac : (expU u 1)⁻¹ + expU u 1 - 2 = (0 : ℂ) := by
    simp [hu]
    norm_num
  simp [J₁'_J₃'_J₅'_factor (u := u), hfac]

/-- Integrability of `t ↦ ψS' (t * I) * expU u (t * I)` on the vertical ray `t>1` when `0 ≤ u`. -/
public lemma integrableOn_ψS'_mul_expU_vertical_left (u : ℝ) (hu0 : 0 ≤ u) :
    MeasureTheory.IntegrableOn (fun t : ℝ => ψS' (t * Complex.I) * expU u (t * Complex.I))
      (Ioi (1 : ℝ)) MeasureTheory.volume := by
  have hf :
      MeasureTheory.Integrable (fun t : ℝ => ψS' (t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn] using!
      SpherePacking.Dim24.PsiSPrelims.integrableOn_ψS'_vertical_left
  have hg :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => expU u (t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    have harg : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by fun_prop
    exact ((continuous_expU (u := u)).comp harg).aestronglyMeasurable
  have hg_bound :
      ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ‖expU u (t * Complex.I)‖ ≤ 1 := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le (by norm_num) (le_of_lt ht))
    exact norm_expU_le_one (u := u) hu0 (z := (t : ℂ) * Complex.I) (by simpa using! ht0)
  have hmul :
      MeasureTheory.Integrable (fun t : ℝ => ψS' (t * Complex.I) * expU u (t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
    hf.mul_bdd hg hg_bound
  simpa [MeasureTheory.IntegrableOn] using! hmul

/-- Integrability of `t ↦ ψS' ((1:ℂ) + t * I) * expU u ((1:ℂ) + t * I)` on `t>1` when `0 ≤ u`. -/
public lemma integrableOn_ψS'_mul_expU_vertical_right (u : ℝ) (hu0 : 0 ≤ u) :
    MeasureTheory.IntegrableOn
        (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I) * expU u ((1 : ℂ) + t * Complex.I))
        (Ioi (1 : ℝ)) MeasureTheory.volume := by
  have hf :
      MeasureTheory.Integrable (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn] using!
      SpherePacking.Dim24.PsiSPrelims.integrableOn_ψS'_vertical_right
  have hg :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => expU u ((1 : ℂ) + t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    have harg : Continuous fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I := by fun_prop
    exact ((continuous_expU (u := u)).comp harg).aestronglyMeasurable
  have hg_bound :
      ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ‖expU u ((1 : ℂ) + t * Complex.I)‖ ≤ 1 := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le (by norm_num) (le_of_lt ht))
    have : 0 ≤ ((1 : ℂ) + (t : ℂ) * Complex.I).im := by simpa using! ht0
    exact norm_expU_le_one (u := u) hu0 (z := (1 : ℂ) + (t : ℂ) * Complex.I) this
  have hmul :
      MeasureTheory.Integrable
          (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I) * expU u ((1 : ℂ) + t * Complex.I))
          (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
    hf.mul_bdd hg hg_bound
  simpa [MeasureTheory.IntegrableOn] using! hmul

/-- The boundary integral of `ψS' z * expU u z` on the open rectangle with corners
`0 + I`, `1 + I`, and vertical edges extending to `im → ∞` is zero. -/
public lemma integral_boundary_open_rect_ψS'_mul_expU_eq_zero (u : ℝ) (hu0 : 0 ≤ u) :
    (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I) * expU u (x + (1 : ℝ) * Complex.I)) +
          (Complex.I •
            ∫ (t : ℝ) in Ioi (1 : ℝ),
              ψS' ((1 : ℂ) + t * Complex.I) * expU u ((1 : ℂ) + t * Complex.I)) -
            (Complex.I •
              ∫ (t : ℝ) in Ioi (1 : ℝ),
                ψS' ((0 : ℂ) + t * Complex.I) * expU u ((0 : ℂ) + t * Complex.I)) =
      0 := by
  let fU : ℂ → ℂ := fun z : ℂ => ψS' z * expU u z
  have hcont : ContinuousOn fU (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) := by
    refine (continuousOn_ψS'_rect.mul ?_)
    exact (continuous_expU (u := u)).continuousOn
  have hdiff :
      ∀ x ∈ ((Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) ×ℂ (Ioi (1 : ℝ))) \ (∅ : Set ℂ),
        DifferentiableAt ℂ fU x := by
    intro z hz
    have hzIm1 : z.im ∈ Ioi (1 : ℝ) := (Complex.mem_reProdIm.1 (by simpa using! hz.1)).2
    have hzIm : 0 < z.im := lt_of_lt_of_le (by norm_num) (le_of_lt hzIm1)
    have hψ : DifferentiableAt ℂ ψS' z := differentiableAt_ψS'_of_im_pos z hzIm
    have hE : DifferentiableAt ℂ (fun w : ℂ => expU u w) z := by
      simpa using! (differentiableAt_expU (u := u) (z := z))
    simpa [fU] using! hψ.mul hE
  have hint₁ :
      MeasureTheory.IntegrableOn (fun t : ℝ => fU ((0 : ℂ) + t * Complex.I)) (Ioi (1 : ℝ))
        MeasureTheory.volume := by
    simpa [fU, zero_add] using! integrableOn_ψS'_mul_expU_vertical_left (u := u) hu0
  have hint₂ :
      MeasureTheory.IntegrableOn (fun t : ℝ => fU ((1 : ℂ) + t * Complex.I)) (Ioi (1 : ℝ))
        MeasureTheory.volume := by
    simpa [fU] using! integrableOn_ψS'_mul_expU_vertical_right (u := u) hu0
  have htendsto_fU :
      ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖fU z‖ < ε := by
    intro ε hε
    rcases SpherePacking.Dim24.PsiSPrelims.htendsto_ψS' ε hε with ⟨M0, hM0⟩
    refine ⟨max M0 0, ?_⟩
    intro z hz
    have hzM0 : M0 ≤ z.im := le_trans (le_max_left _ _) hz
    have hz0 : 0 ≤ z.im := le_trans (le_max_right _ _) hz
    have hle : ‖expU u z‖ ≤ 1 := norm_expU_le_one (u := u) hu0 (z := z) hz0
    have hnorm : ‖fU z‖ ≤ ‖ψS' z‖ := by
      have h' : ‖ψS' z‖ * ‖expU u z‖ ≤ ‖ψS' z‖ := by
        have := mul_le_mul_of_nonneg_left hle (norm_nonneg (ψS' z))
        simpa using! (this.trans (by simp))
      simpa [fU, norm_mul] using! h'
    exact lt_of_le_of_lt hnorm (hM0 z hzM0)
  have hrect :=
    Complex.integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
      (y := (1 : ℝ)) (f := fU) (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ)) hcont (s := (∅ : Set ℂ)) (by simp)
      hdiff hint₁ hint₂ htendsto_fU
  simpa [fU, min_eq_left (zero_le_one : (0 : ℝ) ≤ 1), max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)]
    using! hrect

/-- If `expU u 1 = 1` and `0 ≤ u`, then the sum `J₂' u + J₄' u + J₆' u` vanishes. -/
public lemma J₂'_J₄'_J₆'_zero_sum_of (u : ℝ) (hu : expU u 1 = 1) (hu0 : 0 ≤ u) :
    J₂' u + J₄' u + J₆' u = 0 := by
  -- Rewrite `J₂'(u)+J₄'(u)` as the horizontal integral of `ψS' * expU`.
  have hJ24 :
      J₂' u + J₄' u =
        ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) :=
    Deriv.J₂'_J₄_as_ψS_horizontal_of (u := u) hu
  -- Apply the open-rectangle deformation to `z ↦ ψS' z * expU u z`.
  let fU : ℂ → ℂ := fun z : ℂ => ψS' z * expU u z
  have hrect :
      (∫ (x : ℝ) in (0 : ℝ)..1, fU (x + (1 : ℝ) * Complex.I)) +
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU ((1 : ℂ) + t * Complex.I)) -
            (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU ((0 : ℂ) + t * Complex.I)) = 0 := by
    simpa [fU] using! integral_boundary_open_rect_ψS'_mul_expU_eq_zero (u := u) hu0
  have hright :
      (∫ (t : ℝ) in Ioi (1 : ℝ), fU ((1 : ℂ) + t * Complex.I)) =
        -∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I) := by
    have hEq :
        (fun t : ℝ => fU ((1 : ℂ) + t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Ioi (1 : ℝ))]
          fun t : ℝ => -fU (t * Complex.I) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
      have hψ : ψS' ((1 : ℂ) + t * Complex.I) = -ψS' (t * Complex.I) :=
        SpherePacking.Dim24.PsiSPrelims.ψS'_add_one (t := t) ht0
      have hexp : expU u ((1 : ℂ) + t * Complex.I) = expU u (t * Complex.I) := by
        simpa [add_assoc, add_left_comm, add_comm] using!
          (expU_add_one (u := u) hu (z := (t : ℂ) * Complex.I))
      simp [fU, hψ, hexp]
    have hEqInt :
        (∫ (t : ℝ) in Ioi (1 : ℝ), fU ((1 : ℂ) + t * Complex.I)) =
          ∫ (t : ℝ) in Ioi (1 : ℝ), -fU (t * Complex.I) := by
      simpa using! (MeasureTheory.integral_congr_ae hEq)
    simpa [MeasureTheory.integral_neg] using! hEqInt
  have hhor :
      (∫ (x : ℝ) in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) -
          (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) = 0 := by
    have h' :
        (∫ (x : ℝ) in (0 : ℝ)..1, fU (x + (1 : ℝ) * Complex.I)) +
            (Complex.I • (-∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I))) -
              (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU ((0 : ℂ) + t * Complex.I)) = 0 := by
      simpa [hright] using! hrect
    simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_neg] using! h'
  have hJ6 :
      J₆' u = (-2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) := by
    simpa [fU] using! (Deriv.J₆'_eq_vertical_Ioi (u := u))
  grind only


end SpecialValuesAux.EvenU
end

end SpherePacking.Dim24
