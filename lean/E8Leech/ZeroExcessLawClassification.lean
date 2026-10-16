import E8Leech.ExactLatticeLawClassification
import E8Leech.ZeroExcessLatticeEquivalence

/-! # Zero excess is exactly an arbitrary orientation mixture with uniform phase -/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

theorem e8_riesz_zero_excess_iff_orientationMixture {s : ℝ} (hs : (8 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    rieszEnergy s μ = latticeRieszEnergy e8Set s ↔
      ∃ σ : Measure (LatticeOrientation 8), IsProbabilityMeasure σ ∧ μ = e8OrientationMixtureLaw σ := by
  constructor
  · intro he
    exact e8_exists_orientationMixtureLaw_of_ae_isometric_lattice μ hμ
      ((e8_riesz_zero_excess_iff_ae_isometric_lattice hs μ hμ hρ).mp he)
  · rintro ⟨σ, hσ, he⟩
    let := hσ
    rw [he]
    exact e8_rieszEnergy_orientationMixture σ s

theorem e8_gaussian_zero_excess_iff_orientationMixture {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy e8Set (gaussianPotential α) ↔
      ∃ σ : Measure (LatticeOrientation 8), IsProbabilityMeasure σ ∧ μ = e8OrientationMixtureLaw σ := by
  constructor
  · intro he
    exact e8_exists_orientationMixtureLaw_of_ae_isometric_lattice μ hμ
      ((e8_gaussian_zero_excess_iff_ae_isometric_lattice hα μ hμ hρ).mp he)
  · rintro ⟨σ, hσ, he⟩
    let := hσ
    rw [he]
    exact e8_gaussianEnergy_orientationMixture σ α

theorem e8_positiveGaussianMixture_zero_excess_iff_orientationMixture (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (positiveGaussianMixturePotential ν) μ = latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ↔
      ∃ σ : Measure (LatticeOrientation 8), IsProbabilityMeasure σ ∧ μ = e8OrientationMixtureLaw σ := by
  constructor
  · intro he
    exact e8_exists_orientationMixtureLaw_of_ae_isometric_lattice μ hμ
      ((e8_positiveGaussianMixture_zero_excess_iff_ae_isometric_lattice ν hν hbase μ hμ hρ).mp he)
  · rintro ⟨σ, hσ, he⟩
    let := hσ
    rw [he]
    exact e8_positiveGaussianMixtureEnergy_orientationMixture σ ν hbase

theorem leech_riesz_zero_excess_iff_orientationMixture {s : ℝ} (hs : (24 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    rieszEnergy s μ = latticeRieszEnergy leechSet s ↔
      ∃ σ : Measure (LatticeOrientation 24), IsProbabilityMeasure σ ∧ μ = leechOrientationMixtureLaw σ := by
  constructor
  · intro he
    exact leech_exists_orientationMixtureLaw_of_ae_isometric_lattice μ hμ
      ((leech_riesz_zero_excess_iff_ae_isometric_lattice hs μ hμ hρ).mp he)
  · rintro ⟨σ, hσ, he⟩
    let := hσ
    rw [he]
    exact leech_rieszEnergy_orientationMixture σ s

theorem leech_gaussian_zero_excess_iff_orientationMixture {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy leechSet (gaussianPotential α) ↔
      ∃ σ : Measure (LatticeOrientation 24), IsProbabilityMeasure σ ∧ μ = leechOrientationMixtureLaw σ := by
  constructor
  · intro he
    exact leech_exists_orientationMixtureLaw_of_ae_isometric_lattice μ hμ
      ((leech_gaussian_zero_excess_iff_ae_isometric_lattice hα μ hμ hρ).mp he)
  · rintro ⟨σ, hσ, he⟩
    let := hσ
    rw [he]
    exact leech_gaussianEnergy_orientationMixture σ α

theorem leech_positiveGaussianMixture_zero_excess_iff_orientationMixture (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (positiveGaussianMixturePotential ν) μ = latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ↔
      ∃ σ : Measure (LatticeOrientation 24), IsProbabilityMeasure σ ∧ μ = leechOrientationMixtureLaw σ := by
  constructor
  · intro he
    exact leech_exists_orientationMixtureLaw_of_ae_isometric_lattice μ hμ
      ((leech_positiveGaussianMixture_zero_excess_iff_ae_isometric_lattice ν hν hbase μ hμ hρ).mp he)
  · rintro ⟨σ, hσ, he⟩
    let := hσ
    rw [he]
    exact leech_positiveGaussianMixtureEnergy_orientationMixture σ ν hbase

end E8Leech
