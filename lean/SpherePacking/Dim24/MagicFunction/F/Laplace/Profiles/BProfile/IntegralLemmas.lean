-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Profiles.BProfile.TailDifference
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims
import SpherePacking.Dim24.MagicFunction.B.Defs.J5Smooth


/-!
# Rewriting the `ψI'` Laplace integral

This file provides helper lemmas for rewriting the `ψI'` integral in the convergent range
`u > 4`, splitting the integral at `t = 1` and replacing `expU` by the real exponential on the
imaginary axis.

## Main statements
* `integral_Ioi_psiI'_expU_eq_interval_add_Ioi_one`
* `integral_Ioi_psiI'_expU_eq_real_exp`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped UpperHalfPlane Interval Topology

open Complex Filter MeasureTheory Real SchwartzMap Set
open UpperHalfPlane
open MagicFunction.Parametrisations RealIntegrals SpecialValuesAux

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Split the `ψI'` Laplace integral at `t = 1` into an interval integral and a tail integral. -/
public lemma integral_Ioi_psiI'_expU_eq_interval_add_Ioi_one (u : ℝ) (hu0 : 0 ≤ u) (hu : 4 < u) :
    (∫ t in Set.Ioi (0 : ℝ), ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) =
      (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) +
        (∫ t in Set.Ioi (1 : ℝ), ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) := by
  let V0 : ℂ := ∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)
  let Itail : ℂ := ∫ t in Set.Ioi (1 : ℝ), ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)
  let fI : ℝ → ℂ := fun t : ℝ => ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)
  have hcontExpU : Continuous fun z : ℂ => expU u z := by
    simpa using! (continuous_expU (u := u))
  have hcontγ : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by
    simpa using! (continuous_ofReal.mul continuous_const)
  have hV0set : V0 = ∫ t in Set.Ioc (0 : ℝ) 1, fI t := by
    exact Eq.symm (Integration.integral_restrict_Ioc01_eq_intervalIntegral fI)
  have hIntIoi1 : Integrable (fun t : ℝ => fI t) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    -- Reduce to integrability of `ψS'` and `ψT'` on the tail, then use `ψS + ψT = ψI`.
    have hIntS :
        Integrable (fun t : ℝ => ψS' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I))
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
      have hf :
          Integrable (fun t : ℝ => ψS' (t * Complex.I)) (volume.restrict (Set.Ioi (1 : ℝ))) := by
        simpa [IntegrableOn] using! SpherePacking.Dim24.PsiSPrelims.integrableOn_ψS'_vertical_left
      have hg :
          AEStronglyMeasurable (fun t : ℝ => expU u (t * Complex.I)) (volume.restrict (Set.Ioi (1 :
          ℝ)))
            := by
        have : Continuous fun t : ℝ => expU u (t * Complex.I) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using! hcontExpU.comp hcontγ
        exact this.aestronglyMeasurable
      have hbound :
          ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi (1 : ℝ))), ‖expU u (t * Complex.I)‖ ≤ 1 := by
        refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        have ht0 : 0 ≤ (t * Complex.I).im := by
          have : 0 ≤ t := le_of_lt (lt_of_lt_of_le (by norm_num) (le_of_lt ht))
          simpa using! this
        exact norm_expU_le_one (u := u) hu0 (z := t * Complex.I) ht0
      simpa [mul_assoc, mul_left_comm, mul_comm] using! (hf.mul_bdd hg hbound)
    have hIntT :
        Integrable (fun t : ℝ => ψT' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I))
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [IntegrableOn] using! (integrableOn_ψT'_vertical_left_mul_expU (u := u) hu)
    have hEq :
        (fun t : ℝ => fI t) =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
          fun t : ℝ =>
            (ψS' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) +
              (ψT' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
      have hsum' : ψI' ((t : ℂ) * Complex.I) = ψS' ((t : ℂ) * Complex.I) + ψT' ((t : ℂ) * Complex.I)
        := ψI'_eq_ψS'_add_ψT' (t := t) ht0
      calc
        fI t = ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I) := rfl
        _ = (ψS' ((t : ℂ) * Complex.I) + ψT' ((t : ℂ) * Complex.I)) * expU u ((t : ℂ) * Complex.I)
          := by
              simp [hsum']
        _ =
            (ψS' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) +
              (ψT' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) := by
              simp [add_mul]
    have hIntSum :
        Integrable
          (fun t : ℝ =>
            (ψS' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) +
              (ψT' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)))
          (volume.restrict (Set.Ioi (1 : ℝ))) :=
      hIntS.add hIntT
    exact hIntSum.congr hEq.symm
  have hIntIoc : IntegrableOn fI (Set.Ioc (0 : ℝ) 1) := by
    rcases SpherePacking.Dim24.Schwartz.J5Smooth.exists_bound_norm_ψI'_z₅' with ⟨M, hM⟩
    have hAe : Set.Ioo (0 : ℝ) 1 =ᵐ[volume] Set.Ioc (0 : ℝ) 1 :=
      Ioo_ae_eq_Ioc' (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) (measure_singleton (1 : ℝ))
    have hμ :
        volume.restrict (Set.Ioo (0 : ℝ) 1) = volume.restrict (Set.Ioc (0 : ℝ) 1) := by
      simpa using! (Measure.restrict_congr_set (μ := volume) hAe)
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by infer_instance
    have hmeas_oo : AEStronglyMeasurable fI (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have hcontψ :
          ContinuousOn (fun t : ℝ => ψI' ((t : ℂ) * Complex.I)) (Set.Ioo (0 : ℝ) 1) := by
        have hcont := SpherePacking.Dim24.Schwartz.J5Smooth.continuousOn_ψI'_z₅'
        refine hcont.congr ?_
        intro t ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₅'_eq_of_mem (t := t) htIcc)
        simp [hz5, mul_comm]
      have hcontExp : Continuous fun t : ℝ => expU u ((t : ℂ) * Complex.I) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! hcontExpU.comp hcontγ
      have hψ :
          AEStronglyMeasurable (fun t : ℝ => ψI' ((t : ℂ) * Complex.I))
            (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
        (hcontψ.aestronglyMeasurable measurableSet_Ioo)
      have hexp :
          AEStronglyMeasurable (fun t : ℝ => expU u ((t : ℂ) * Complex.I))
            (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
        hcontExp.aestronglyMeasurable
      simpa [fI, mul_assoc] using! hψ.mul hexp
    have hfinite_oo : HasFiniteIntegral fI (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have hbound_oo :
          ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), ‖fI t‖ ≤ M := by
        refine ae_restrict_of_forall_mem measurableSet_Ioo ?_
        intro t ht
        have htIm : 0 ≤ (((t : ℂ) * Complex.I).im) := by
          have : 0 ≤ t := le_of_lt ht.1
          simpa using! this
        have hexpU : ‖expU u ((t : ℂ) * Complex.I)‖ ≤ 1 :=
          norm_expU_le_one (u := u) hu0 (z := (t : ℂ) * Complex.I) htIm
        have hψI' : ‖ψI' ((t : ℂ) * Complex.I)‖ ≤ M := by
          have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
          have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₅'_eq_of_mem (t := t) htIcc)
          simpa [hz5, mul_assoc, mul_left_comm, mul_comm] using! hM t ht
        calc
          ‖fI t‖ = ‖ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)‖ := by rfl
          _ ≤ ‖ψI' ((t : ℂ) * Complex.I)‖ * ‖expU u ((t : ℂ) * Complex.I)‖ :=
                norm_mul_le _ _
          _ ≤ ‖ψI' ((t : ℂ) * Complex.I)‖ * 1 := by
                exact mul_le_mul_of_nonneg_left hexpU (norm_nonneg _)
          _ = ‖ψI' ((t : ℂ) * Complex.I)‖ := by simp
          _ ≤ M := hψI'
      exact HasFiniteIntegral.of_bounded hbound_oo
    have hInt_oo : Integrable fI (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      ⟨hmeas_oo, hfinite_oo⟩
    have hInt_oc : Integrable fI (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      simpa [hμ] using! hInt_oo
    exact hInt_oc
  have hUnion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
    norm_num
  have hIall : (∫ t in Set.Ioi (0 : ℝ), fI t) = V0 + Itail := by
    have hItail : (∫ t in Set.Ioi (1 : ℝ), fI t) = Itail := by
      simp [Itail, fI]
    have hsplit :
        (∫ t in Set.Ioi (0 : ℝ), fI t) = (∫ t in Set.Ioc (0 : ℝ) 1, fI t) + (∫ t in Set.Ioi (1 : ℝ),
        fI t)
          := by
      -- split the `Ioi 0` integral at `1`
      have hdis : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := by
        exact Ioc_disjoint_Ioi_same
      have hmeasIoi : MeasurableSet (Set.Ioi (1 : ℝ)) := measurableSet_Ioi
      have h :=
        (MeasureTheory.setIntegral_union (μ := volume) (f := fI)
          hdis hmeasIoi hIntIoc (by simpa [IntegrableOn] using! hIntIoi1))
      -- Rewrite the union as `Ioi 0`.
      simpa [hUnion] using! h
    -- Substitute `V0` and `Itail`.
    simpa [hV0set, hItail, add_assoc, add_left_comm, add_comm] using! hsplit
  -- Finish by unfolding the `V0`/`Itail` abbreviations.
  simpa [fI, V0, Itail, add_assoc, add_left_comm, add_comm] using! hIall

/-- Replace `expU u (t * I)` by `Real.exp (-π * u * t)` in the `ψI'` Laplace integral. -/
public lemma integral_Ioi_psiI'_expU_eq_real_exp (u : ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) =
      ∫ t in Set.Ioi (0 : ℝ), ψI' ((t : ℂ) * Complex.I) * Real.exp (-Real.pi * u * t) := by
  refine MeasureTheory.integral_congr_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro t ht
  have hexp : expU u ((t : ℂ) * Complex.I) = (Real.exp (-Real.pi * u * t) : ℂ) := by
    have h1 : expU u ((t : ℂ) * Complex.I) = Complex.exp (-Real.pi * u * t : ℂ) := by
      simpa [expU] using! (LaplaceA.exp_pi_I_mul_mul_I_eq_real_exp (u := u) (t := t))
    simp_all
  simp [hexp, mul_assoc]

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile
