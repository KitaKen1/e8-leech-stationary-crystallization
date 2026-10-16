import E8Leech.LatticeContainerUniqueness

/-!
# Zero-excess configurations have a unique containing lattice

Upgrade the measurable probability-one event of Z1 to uniqueness of the
containing lattice as a set. This does not assert a measurable choice of
the lattice, equality of the configuration with the lattice, or a Haar law.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

/-- Uniqueness of the lattice set, rather than of an isometry parameter.
No measurability of this predicate is asserted. -/
def UniqueLatticeContainment {d : ℕ} (Λ : Set (Ambient d))
    (c : Configuration (Ambient d)) : Prop :=
  ∃! Γ : Set (Ambient d), (∃ Φ : Ambient d ≃ᵢ Ambient d, Γ = Φ '' Λ) ∧ c.support ⊆ Γ

theorem e8_unique_lattice_container_of_fullDensity (c : Configuration (Ambient 8))
    (hc : FullDensityLatticeContainment e8Set c) : UniqueLatticeContainment e8Set c := by
  have hc' : FullDensityLatticeContainment (e8Lattice : Set (Ambient 8)) c := by
    simpa only [coe_e8Lattice] using hc
  simpa only [UniqueLatticeContainment, coe_e8Lattice] using
    exists_unique_lattice_container_of_fullDensity e8EuclideanBasis e8Lattice le_rfl
      e8Lattice_covolume c hc'

theorem leech_unique_lattice_container_of_fullDensity (c : Configuration (Ambient 24))
    (hc : FullDensityLatticeContainment leechSet c) : UniqueLatticeContainment leechSet c := by
  have hc' : FullDensityLatticeContainment (leechLattice : Set (Ambient 24)) c := by
    simpa only [coe_leechLattice] using hc
  have hle : Submodule.span ℤ (Set.range leechEuclideanBasis) ≤ leechLattice := by
    rw [leechLattice_eq_span]
  simpa only [UniqueLatticeContainment, coe_leechLattice] using
    exists_unique_lattice_container_of_fullDensity leechEuclideanBasis leechLattice hle
      leechLattice_covolume c hc'

theorem unique_lattice_container_event_of_fullDensity_event {d : ℕ}
    {Λ : Set (Ambient d)} (μ : Measure (Configuration (Ambient d)))
    (hunique : ∀ c, FullDensityLatticeContainment Λ c → UniqueLatticeContainment Λ c)
    (hgood : ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment Λ c) :
    ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment Λ c ∧ UniqueLatticeContainment Λ c := by
  obtain ⟨H, hH, hp, hc⟩ := hgood
  exact ⟨H, hH, hp, fun c h => ⟨hc c h, hunique c (hc c h)⟩⟩

theorem e8_zero_excess_riesz_unique_lattice_container {s : ℝ} (hs : (8 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : rieszEnergy s μ = latticeRieszEnergy e8Set s) :
    ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment e8Set c ∧ UniqueLatticeContainment e8Set c :=
  unique_lattice_container_event_of_fullDensity_event μ e8_unique_lattice_container_of_fullDensity
    (e8_zero_excess_riesz_lattice_containment hs μ hμ hρ henergy)

theorem leech_zero_excess_riesz_unique_lattice_container {s : ℝ} (hs : (24 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : rieszEnergy s μ = latticeRieszEnergy leechSet s) :
    ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment leechSet c ∧ UniqueLatticeContainment leechSet c :=
  unique_lattice_container_event_of_fullDensity_event μ leech_unique_lattice_container_of_fullDensity
    (leech_zero_excess_riesz_lattice_containment hs μ hμ hρ henergy)

theorem e8_zero_excess_positiveGaussianMixture_unique_lattice_container
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν)) :
    ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment e8Set c ∧ UniqueLatticeContainment e8Set c :=
  unique_lattice_container_event_of_fullDensity_event μ e8_unique_lattice_container_of_fullDensity
    (e8_zero_excess_positiveGaussianMixture_lattice_containment ν hν hbase μ hμ hρ henergy)

theorem leech_zero_excess_positiveGaussianMixture_unique_lattice_container
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν)) :
    ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment leechSet c ∧ UniqueLatticeContainment leechSet c :=
  unique_lattice_container_event_of_fullDensity_event μ leech_unique_lattice_container_of_fullDensity
    (leech_zero_excess_positiveGaussianMixture_lattice_containment ν hν hbase μ hμ hρ henergy)

theorem e8_zero_excess_gaussian_unique_lattice_container {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy e8Set (gaussianPotential α)) :
    ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment e8Set c ∧ UniqueLatticeContainment e8Set c :=
  unique_lattice_container_event_of_fullDensity_event μ e8_unique_lattice_container_of_fullDensity
    (e8_zero_excess_gaussian_lattice_containment hα μ hμ hρ henergy)

theorem leech_zero_excess_gaussian_unique_lattice_container {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy leechSet (gaussianPotential α)) :
    ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment leechSet c ∧ UniqueLatticeContainment leechSet c :=
  unique_lattice_container_event_of_fullDensity_event μ leech_unique_lattice_container_of_fullDensity
    (leech_zero_excess_gaussian_lattice_containment hα μ hμ hρ henergy)

end E8Leech
