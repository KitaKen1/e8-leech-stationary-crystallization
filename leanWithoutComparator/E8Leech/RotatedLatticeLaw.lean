import E8Leech.IsometricLatticeEnergy
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Orthogonal images of the uniformly shifted lattice

An orthogonal image preserves stationarity and intensity. The orientation
parameter carries the Borel structure induced by its continuous linear map.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Classical

structure LatticeOrientation (d : ℕ) where
  isometry : Ambient d ≃ₗᵢ[ℝ] Ambient d

instance {d : ℕ} : TopologicalSpace (LatticeOrientation d) :=
  TopologicalSpace.induced (fun Q : LatticeOrientation d => Q.isometry.toContinuousLinearMap)
    inferInstance

instance {d : ℕ} : SecondCountableTopology (LatticeOrientation d) :=
  TopologicalSpace.secondCountableTopology_induced _ _ _

instance {d : ℕ} : MeasurableSpace (LatticeOrientation d) := borel _

instance {d : ℕ} : BorelSpace (LatticeOrientation d) := ⟨rfl⟩

theorem continuous_orientation_apply {d : ℕ} :
    Continuous (fun p : LatticeOrientation d × Ambient d => p.1.isometry p.2) := by
  have hmap : Continuous (fun Q : LatticeOrientation d =>
      Q.isometry.toContinuousLinearMap) := by
    exact continuous_induced_dom
  have hQ : Continuous (fun p : LatticeOrientation d × Ambient d =>
      p.1.isometry.toContinuousLinearMap) := hmap.comp continuous_fst
  exact hQ.clm_apply continuous_snd

def rotateConfiguration {d : ℕ} (Q : Ambient d ≃ₗᵢ[ℝ] Ambient d)
    (c : Configuration (Ambient d)) : Configuration (Ambient d) :=
  c.mapHomeomorph Q.toHomeomorph

theorem measurable_rotateConfiguration {d : ℕ} (Q : Ambient d ≃ₗᵢ[ℝ] Ambient d) :
    Measurable (rotateConfiguration Q) := Configuration.measurable_mapHomeomorph _

theorem translate_rotateConfiguration {d : ℕ} (Q : Ambient d ≃ₗᵢ[ℝ] Ambient d)
    (a : Ambient d) (c : Configuration (Ambient d)) :
    translate a (rotateConfiguration Q c) =
      rotateConfiguration Q (translate (Q.symm a) c) := by
  apply Configuration.ext
  change (fun x => a + x) '' (Q '' c.support) =
    Q '' ((fun x => Q.symm a + x) '' c.support)
  rw [image_image, image_image]
  congr 1
  funext x
  simp only [map_add, Q.apply_symm_apply]

theorem isStationary_rotateConfiguration {d : ℕ} (Q : Ambient d ≃ₗᵢ[ℝ] Ambient d)
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ) :
    IsStationary (μ.map (rotateConfiguration Q)) := by
  intro a
  refine ⟨measurable_translate a, ?_⟩
  rw [Measure.map_map (measurable_translate a) (measurable_rotateConfiguration Q)]
  have he : translate a ∘ rotateConfiguration Q =
      rotateConfiguration Q ∘ translate (Q.symm a) :=
    funext (translate_rotateConfiguration Q a)
  rw [he, ← Measure.map_map (measurable_rotateConfiguration Q)
    (measurable_translate (Q.symm a)), (hμ (Q.symm a)).map_eq]

theorem hasIntensity_rotateConfiguration {d : ℕ} (Q : Ambient d ≃ₗᵢ[ℝ] Ambient d)
    (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) (hρ : HasIntensity μ ρ) :
    HasIntensity (μ.map (rotateConfiguration Q)) ρ := by
  intro W hW
  rw [lintegral_map (Configuration.measurable_count hW) (measurable_rotateConfiguration Q)]
  change (∫⁻ c, (c.mapHomeomorph Q.toHomeomorph).count W ∂μ) = _
  simp_rw [Configuration.count_mapHomeomorph]
  change (∫⁻ c, c.count (Q ⁻¹' W) ∂μ) = _
  rw [hρ _ (Q.continuous.measurable hW),
    Q.measurePreserving.measure_preimage hW.nullMeasurableSet]

def rotatedLatticeShift {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (Q : LatticeOrientation d) (u : Ambient d) : Configuration (Ambient d) :=
  rotateConfiguration Q.isometry (latticeShift Λ u)

theorem rotatedLatticeShift_eq_isometry {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] (Q : LatticeOrientation d) (u : Ambient d) :
    rotatedLatticeShift Λ Q u = latticeIsometryConfiguration Λ
      ((IsometryEquiv.addLeft u).trans Q.isometry.toIsometryEquiv) := by
  apply Configuration.ext
  change Q.isometry '' ((fun x => u + x) '' (Λ : Set (Ambient d))) = _
  rw [image_image]
  rfl

theorem count_rotatedLatticeShift {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] (Q : LatticeOrientation d) (u : Ambient d)
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (rotatedLatticeShift Λ Q u).count W =
      ∑' ℓ : Λ, W.indicator (1 : Ambient d → ℝ≥0∞) (Q.isometry (u + ℓ)) := by
  rw [rotatedLatticeShift, rotateConfiguration, Configuration.count_mapHomeomorph]
  change (latticeShift Λ u).count (Q.isometry ⁻¹' W) = _
  rw [count_latticeShift Λ u (Q.isometry.continuous.measurable hW)]
  rfl

theorem measurable_rotatedLatticeShift {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Measurable (fun p : LatticeOrientation d × Ambient d => rotatedLatticeShift Λ p.1 p.2) := by
  refine Configuration.measurable_of_counts fun W hW => ?_
  simp_rw [count_rotatedLatticeShift Λ _ _ hW]
  apply Measurable.tsum
  intro ℓ
  apply (measurable_one.indicator hW).comp
  exact continuous_orientation_apply.measurable.comp
    (measurable_fst.prodMk (measurable_snd.add_const (ℓ : Ambient d)))

def rotatedLatticeShiftLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (D : Set (Ambient d)) (Q : LatticeOrientation d) : Measure (Configuration (Ambient d)) :=
  (latticeShiftLaw Λ D).map (rotateConfiguration Q.isometry)

theorem rotatedLatticeShiftLaw_eq_map {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (D : Set (Ambient d)) (Q : LatticeOrientation d) :
    rotatedLatticeShiftLaw Λ D Q = (volume.restrict D).map (rotatedLatticeShift Λ Q) := by
  exact Measure.map_map (measurable_rotateConfiguration Q.isometry) (measurable_latticeShift Λ)

theorem isProbabilityMeasure_rotatedLatticeShiftLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (Q : LatticeOrientation d) : IsProbabilityMeasure (rotatedLatticeShiftLaw Λ D Q) := by
  let := isProbabilityMeasure_latticeShiftLaw Λ hD hcov
  exact Measure.isProbabilityMeasure_map (measurable_rotateConfiguration Q.isometry).aemeasurable

theorem isStationary_rotatedLatticeShiftLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (Q : LatticeOrientation d) :
    IsStationary (rotatedLatticeShiftLaw Λ D Q) :=
  isStationary_rotateConfiguration Q.isometry _ (isStationary_latticeShiftLaw Λ hD)

theorem hasIntensity_rotatedLatticeShiftLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (Q : LatticeOrientation d) :
    HasIntensity (rotatedLatticeShiftLaw Λ D Q) 1 :=
  hasIntensity_rotateConfiguration Q.isometry _ 1 (hasIntensity_latticeShiftLaw Λ hD)

theorem potentialEnergy_rotatedLatticeShiftLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (Q : LatticeOrientation d)
    (P : Ambient d → Ambient d → ℝ≥0∞) (hP : IsometryInvariantPotential P)
    (hPm : Measurable (Function.uncurry P)) :
    potentialEnergy P (rotatedLatticeShiftLaw Λ D Q) =
      latticePotentialEnergy (Λ : Set (Ambient d)) P := by
  have hF : Measurable (rotatedLatticeShift Λ Q) :=
    (measurable_rotateConfiguration Q.isometry).comp (measurable_latticeShift Λ)
  have hc := hasIntensity_rotatedLatticeShiftLaw Λ hD Q
  have hexp := expected_count_unitWindow _ 1 hc
  rw [rotatedLatticeShiftLaw_eq_map,
    lintegral_map (Configuration.measurable_count (measurable_unitWindow d)) hF] at hexp
  unfold potentialEnergy
  rw [rotatedLatticeShiftLaw_eq_map,
    lintegral_map (measurable_orderedWindowEnergy hPm (measurable_unitWindow d)) hF]
  have he (u : Ambient d) : orderedWindowEnergy P (rotatedLatticeShift Λ Q u) (unitWindow d) =
      latticePotentialEnergy (Λ : Set (Ambient d)) P *
        (rotatedLatticeShift Λ Q u).count (unitWindow d) := by
    apply orderedWindowEnergy_eq_lattice_mul_count Λ P hP _
      ((IsometryEquiv.addLeft u).trans Q.isometry.toIsometryEquiv)
    · rw [rotatedLatticeShift_eq_isometry]
      rfl
    · exact measurable_unitWindow d
  simp_rw [he]
  have hcount : Measurable (fun u : Ambient d =>
      (rotatedLatticeShift Λ Q u).count (unitWindow d)) :=
    (Configuration.measurable_count (measurable_unitWindow d)).comp hF
  rw [lintegral_const_mul _ hcount, hexp, mul_one]

end E8Leech
