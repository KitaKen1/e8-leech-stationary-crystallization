import E8Leech.RotatedLatticeLaw
import E8Leech.StationaryLawMixture
import E8Leech.GaussianMixtureFiniteMeasure

/-!
# Arbitrary mixtures of lattice orientations with uniform phase

For every Borel probability distribution on orthogonal orientations, choose
Lebesgue-uniform phase in a lattice fundamental domain. The resulting law is
stationary, has intensity one, and attains every measurable invariant lattice
energy. This is the constructive direction of the phase/orientation law
classification; the representation of every stationary lattice law is separate.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

theorem measurable_rotatedLatticeShiftLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (D : Set (Ambient d)) :
    Measurable (rotatedLatticeShiftLaw Λ D) := by
  apply Measure.measurable_of_measurable_coe
  intro H hH
  have hm := measurable_rotatedLatticeShift Λ
  have hs (Q : LatticeOrientation d) : Measurable (rotatedLatticeShift Λ Q) :=
    (measurable_rotateConfiguration Q.isometry).comp (measurable_latticeShift Λ)
  simp_rw [rotatedLatticeShiftLaw_eq_map Λ D,
    Measure.map_apply (hs _) hH]
  exact measurable_measure_prodMk_left (ν := volume.restrict D) (hm hH)

def orientationMixtureLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (D : Set (Ambient d)) (σ : Measure (LatticeOrientation d)) :
    Measure (Configuration (Ambient d)) := σ.bind (rotatedLatticeShiftLaw Λ D)

theorem isProbabilityMeasure_orientationMixtureLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (σ : Measure (LatticeOrientation d)) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (orientationMixtureLaw Λ D σ) :=
  isProbabilityMeasure_bind_laws σ _ (measurable_rotatedLatticeShiftLaw Λ D)
    (isProbabilityMeasure_rotatedLatticeShiftLaw Λ hD hcov)

theorem isStationary_orientationMixtureLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (σ : Measure (LatticeOrientation d)) :
    IsStationary (orientationMixtureLaw Λ D σ) :=
  isStationary_bind_laws σ _ (measurable_rotatedLatticeShiftLaw Λ D)
    (isStationary_rotatedLatticeShiftLaw Λ hD)

theorem hasIntensity_orientationMixtureLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (σ : Measure (LatticeOrientation d))
    [IsProbabilityMeasure σ] : HasIntensity (orientationMixtureLaw Λ D σ) 1 :=
  hasIntensity_bind_laws σ _ (measurable_rotatedLatticeShiftLaw Λ D) 1
    (hasIntensity_rotatedLatticeShiftLaw Λ hD)

theorem potentialEnergy_orientationMixtureLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (σ : Measure (LatticeOrientation d))
    [IsProbabilityMeasure σ] (P : Ambient d → Ambient d → ℝ≥0∞)
    (hP : IsometryInvariantPotential P) (hPm : Measurable (Function.uncurry P)) :
    potentialEnergy P (orientationMixtureLaw Λ D σ) =
      latticePotentialEnergy (Λ : Set (Ambient d)) P :=
  potentialEnergy_bind_laws σ _ (measurable_rotatedLatticeShiftLaw Λ D) P hPm _
    (fun Q => potentialEnergy_rotatedLatticeShiftLaw Λ hD Q P hP hPm)

def e8OrientationMixtureLaw (σ : Measure (LatticeOrientation 8)) :
    Measure (Configuration (Ambient 8)) :=
  orientationMixtureLaw e8Lattice (ZSpan.fundamentalDomain e8EuclideanBasis) σ

def leechOrientationMixtureLaw (σ : Measure (LatticeOrientation 24)) :
    Measure (Configuration (Ambient 24)) :=
  orientationMixtureLaw leechLattice (ZSpan.fundamentalDomain leechEuclideanBasis) σ

theorem e8_orientationMixture_stationary_probability_intensity
    (σ : Measure (LatticeOrientation 8)) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (e8OrientationMixtureLaw σ) ∧
      IsStationary (e8OrientationMixtureLaw σ) ∧ HasIntensity (e8OrientationMixtureLaw σ) 1 := by
  have hD : IsAddFundamentalDomain e8Lattice
      (ZSpan.fundamentalDomain e8EuclideanBasis) volume :=
    ZSpan.isAddFundamentalDomain e8EuclideanBasis volume
  exact ⟨isProbabilityMeasure_orientationMixtureLaw e8Lattice hD e8Lattice_covolume σ,
    isStationary_orientationMixtureLaw e8Lattice hD σ,
    hasIntensity_orientationMixtureLaw e8Lattice hD σ⟩

theorem leech_orientationMixture_stationary_probability_intensity
    (σ : Measure (LatticeOrientation 24)) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (leechOrientationMixtureLaw σ) ∧
      IsStationary (leechOrientationMixtureLaw σ) ∧ HasIntensity (leechOrientationMixtureLaw σ) 1 := by
  have hD : IsAddFundamentalDomain leechLattice
      (ZSpan.fundamentalDomain leechEuclideanBasis) volume := by
    rw [leechLattice_eq_span]
    exact ZSpan.isAddFundamentalDomain leechEuclideanBasis volume
  exact ⟨isProbabilityMeasure_orientationMixtureLaw leechLattice hD leechLattice_covolume σ,
    isStationary_orientationMixtureLaw leechLattice hD σ,
    hasIntensity_orientationMixtureLaw leechLattice hD σ⟩

theorem e8_potentialEnergy_orientationMixture (σ : Measure (LatticeOrientation 8))
    [IsProbabilityMeasure σ] (P : Ambient 8 → Ambient 8 → ℝ≥0∞)
    (hP : IsometryInvariantPotential P) (hPm : Measurable (Function.uncurry P)) :
    potentialEnergy P (e8OrientationMixtureLaw σ) = latticePotentialEnergy e8Set P := by
  rw [← coe_e8Lattice]
  exact potentialEnergy_orientationMixtureLaw e8Lattice
    (ZSpan.isAddFundamentalDomain e8EuclideanBasis volume) σ P hP hPm

theorem leech_potentialEnergy_orientationMixture (σ : Measure (LatticeOrientation 24))
    [IsProbabilityMeasure σ] (P : Ambient 24 → Ambient 24 → ℝ≥0∞)
    (hP : IsometryInvariantPotential P) (hPm : Measurable (Function.uncurry P)) :
    potentialEnergy P (leechOrientationMixtureLaw σ) = latticePotentialEnergy leechSet P := by
  have hD : IsAddFundamentalDomain leechLattice
      (ZSpan.fundamentalDomain leechEuclideanBasis) volume := by
    rw [leechLattice_eq_span]
    exact ZSpan.isAddFundamentalDomain leechEuclideanBasis volume
  rw [← coe_leechLattice]
  exact potentialEnergy_orientationMixtureLaw leechLattice hD σ P hP hPm

theorem e8_rieszEnergy_orientationMixture (σ : Measure (LatticeOrientation 8))
    [IsProbabilityMeasure σ] (s : ℝ) :
    rieszEnergy s (e8OrientationMixtureLaw σ) = latticeRieszEnergy e8Set s :=
  e8_potentialEnergy_orientationMixture σ _ (rieszPotential_isometryInvariant s)
    (measurable_rieszPotential s)

theorem leech_rieszEnergy_orientationMixture (σ : Measure (LatticeOrientation 24))
    [IsProbabilityMeasure σ] (s : ℝ) :
    rieszEnergy s (leechOrientationMixtureLaw σ) = latticeRieszEnergy leechSet s :=
  leech_potentialEnergy_orientationMixture σ _ (rieszPotential_isometryInvariant s)
    (measurable_rieszPotential s)

theorem e8_gaussianEnergy_orientationMixture (σ : Measure (LatticeOrientation 8))
    [IsProbabilityMeasure σ] (α : ℝ) :
    potentialEnergy (gaussianPotential α) (e8OrientationMixtureLaw σ) =
      latticePotentialEnergy e8Set (gaussianPotential α) :=
  e8_potentialEnergy_orientationMixture σ _ (gaussianPotential_isometryInvariant α)
    ((measurable_gaussianPotential_joint 8).comp (measurable_const.prodMk measurable_id))

theorem leech_gaussianEnergy_orientationMixture (σ : Measure (LatticeOrientation 24))
    [IsProbabilityMeasure σ] (α : ℝ) :
    potentialEnergy (gaussianPotential α) (leechOrientationMixtureLaw σ) =
      latticePotentialEnergy leechSet (gaussianPotential α) :=
  leech_potentialEnergy_orientationMixture σ _ (gaussianPotential_isometryInvariant α)
    ((measurable_gaussianPotential_joint 24).comp (measurable_const.prodMk measurable_id))

theorem e8_positiveGaussianMixtureEnergy_orientationMixture
    (σ : Measure (LatticeOrientation 8)) [IsProbabilityMeasure σ] (ν : Measure ℝ)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞) :
    potentialEnergy (positiveGaussianMixturePotential ν) (e8OrientationMixtureLaw σ) =
      latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) :=
  e8_potentialEnergy_orientationMixture σ _ (positiveGaussianMixturePotential_isometryInvariant ν)
    (e8_measurable_positiveGaussianMixturePotential_of_finite_lattice_energy ν hbase)

theorem leech_positiveGaussianMixtureEnergy_orientationMixture
    (σ : Measure (LatticeOrientation 24)) [IsProbabilityMeasure σ] (ν : Measure ℝ)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞) :
    potentialEnergy (positiveGaussianMixturePotential ν) (leechOrientationMixtureLaw σ) =
      latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) :=
  leech_potentialEnergy_orientationMixture σ _ (positiveGaussianMixturePotential_isometryInvariant ν)
    (leech_measurable_positiveGaussianMixturePotential_of_finite_lattice_energy ν hbase)

end E8Leech
