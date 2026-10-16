import E8Leech.LatticePhaseLawUniqueness
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Measurable rotating fundamental-domain windows

The inverse orthogonal action is jointly continuous, via the adjoint.
A rotated phase window therefore has a measurable density against volume,
unit mass at covolume one, and the same averaging law as uniform lattice phase.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

theorem continuous_orientation_inverse_apply {d : ℕ} :
    Continuous (fun p : LatticeOrientation d × Ambient d => p.1.isometry.symm p.2) := by
  have hmap : Continuous (fun Q : LatticeOrientation d => Q.isometry.toContinuousLinearMap) :=
    continuous_induced_dom
  have hsym : Continuous (fun Q : LatticeOrientation d => Q.isometry.symm.toContinuousLinearMap) := by
    have hh : Continuous (fun Q : LatticeOrientation d =>
        ContinuousLinearMap.adjoint Q.isometry.toContinuousLinearMap) :=
      (ContinuousLinearMap.adjoint :
      (Ambient d →L[ℝ] Ambient d) ≃ₗᵢ⋆[ℝ] (Ambient d →L[ℝ] Ambient d)).continuous.comp hmap
    have he (Q : LatticeOrientation d) :
        ContinuousLinearMap.adjoint Q.isometry.toContinuousLinearMap =
          Q.isometry.symm.toContinuousLinearMap := by
      have hleft : Q.isometry.toContinuousLinearMap = (Q.isometry : Ambient d →L[ℝ] Ambient d) := by
        ext x
        rfl
      have hright : Q.isometry.symm.toContinuousLinearMap =
          (Q.isometry.symm : Ambient d →L[ℝ] Ambient d) := by
        ext x
        rfl
      rw [hleft, Q.isometry.adjoint_eq_symm, hright]
    simpa only [he] using hh
  exact (hsym.comp continuous_fst).clm_apply continuous_snd

def orientationPhaseDensity {d : ℕ} (D : Set (Ambient d))
    (Q : LatticeOrientation d) (a : Ambient d) : ℝ≥0∞ :=
  D.indicator (1 : Ambient d → ℝ≥0∞) (Q.isometry.symm a)

theorem measurable_orientationPhaseDensity {d : ℕ} {D : Set (Ambient d)}
    (hD : MeasurableSet D) :
    Measurable (fun p : LatticeOrientation d × Ambient d => orientationPhaseDensity D p.1 p.2) :=
  (measurable_one.indicator hD).comp continuous_orientation_inverse_apply.measurable

theorem lintegral_orientationPhaseDensity {d : ℕ} {D : Set (Ambient d)}
    (hD : MeasurableSet D) (Q : LatticeOrientation d) :
    (∫⁻ a, orientationPhaseDensity D Q a) = volume D := by
  exact (Q.isometry.symm.measurePreserving.lintegral_comp (measurable_one.indicator hD)).trans
    (lintegral_indicator_one hD)

theorem lintegral_orientationPhaseDensity_mul {d : ℕ} {D : Set (Ambient d)}
    (hD : MeasurableSet D) (Q : LatticeOrientation d)
    (f : Ambient d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ a, orientationPhaseDensity D Q a * f a) = ∫⁻ u in D, f (Q.isometry u) := by
  have hdens : Measurable (fun a => orientationPhaseDensity D Q a) :=
    (measurable_orientationPhaseDensity hD).comp (measurable_const.prodMk measurable_id)
  have hg : Measurable (fun a => orientationPhaseDensity D Q a * f a) := hdens.mul hf
  calc
    _ = ∫⁻ u, orientationPhaseDensity D Q (Q.isometry u) * f (Q.isometry u) :=
      (Q.isometry.measurePreserving.lintegral_comp hg).symm
    _ = ∫⁻ u, D.indicator (fun u => f (Q.isometry u)) u := by
      apply lintegral_congr
      intro u
      simp only [orientationPhaseDensity, Q.isometry.symm_apply_apply]
      by_cases hu : u ∈ D <;> simp [hu]
    _ = _ := lintegral_indicator hD _

theorem lintegral_phaseDensity_translate_rotatedLatticeShift {d : ℕ}
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume) (hDm : MeasurableSet D)
    (Q : LatticeOrientation d) (u : Ambient d)
    (F : Configuration (Ambient d) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ a, orientationPhaseDensity D Q a * F (translate a (rotatedLatticeShift Λ Q u))) =
      ∫⁻ c, F c ∂rotatedLatticeShiftLaw Λ D Q := by
  have hf : Measurable (fun a => F (translate a (rotatedLatticeShift Λ Q u))) :=
    hF.comp (measurable_translate_param (fun _ : Ambient d => rotatedLatticeShift Λ Q u)
      id measurable_const measurable_id)
  rw [lintegral_orientationPhaseDensity_mul hDm Q _ hf]
  exact lintegral_translate_rotatedLatticeShift Λ hD Q F hF u

end E8Leech
