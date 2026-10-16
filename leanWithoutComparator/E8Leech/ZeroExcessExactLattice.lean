import E8Leech.StationaryLatticeIntensity

/-!
# At zero excess the configuration is an entire isometric lattice

The stationary reconstructed lattice has intensity one. Equal intensities and
containment remove every missing point. This completes Z3 for E8 and Leech,
for Riesz and all positive Gaussian mixtures, but not the Haar law classification.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

/-- Exact lattice configurations on a measurable probability-one event, with no missing points.
The law is fixed by the canonical measurable reconstruction. Haar phase is not asserted. -/
def ExactLatticeRealization {d : ℕ} (Λ : Set (Ambient d))
    (μ : Measure (Configuration (Ambient d))) : Prop :=
  HasIntensity (μ.map ternaryReconstruction) 1 ∧ μ.map ternaryReconstruction = μ ∧
    ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, c = ternaryReconstruction c ∧
        ∃ Φ : Ambient d ≃ᵢ Ambient d, c.support = Φ '' Λ

theorem exact_lattice_event_of_reconstructed_event {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (hgood : ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, ReconstructedLatticeContainer (Λ : Set (Ambient d)) c) :
    ExactLatticeRealization (Λ : Set (Ambient d)) μ := by
  obtain ⟨H, hH, hp, hc⟩ := hgood
  have hae : ∀ᵐ c ∂μ, ReconstructedLatticeContainer (Λ : Set (Ambient d)) c := by
    have hh : ∀ᵐ c ∂μ, c ∈ H := (mem_ae_iff_prob_eq_one hH).mpr hp
    filter_upwards [hh] with c h
    exact hc c h
  have hsub : ∀ᵐ c ∂μ, c.support ⊆ (ternaryReconstruction c).support := hae.mono fun _ h => h.1
  have hρF := hasIntensity_one_of_stationary_affine_lattice_container b Λ hle hcov μ hρ
    ternaryReconstruction measurable_ternaryReconstruction
    (isStationary_map_ternaryReconstruction μ hμ) (hae.mono fun c h =>
      ⟨h.1, by obtain ⟨Φ, hΦ⟩ := h.2; exact ⟨Φ, hΦ.subset⟩⟩)
  have heq := ae_eq_of_support_subset_of_equal_intensity μ ternaryReconstruction
    measurable_ternaryReconstruction hsub (by simp : (1 : ℝ≥0∞) ≠ ∞) hρ hρF
  have hmap : μ.map ternaryReconstruction = μ := by
    calc
      μ.map ternaryReconstruction = μ.map id :=
        Measure.map_congr (heq.mono fun _ h => h.symm)
      _ = μ := Measure.map_id
  have hexact : ∀ᵐ c ∂μ, c = ternaryReconstruction c ∧
      ∃ Φ : Ambient d ≃ᵢ Ambient d, c.support = Φ '' (Λ : Set (Ambient d)) := by
    filter_upwards [heq, hae] with c he hc
    obtain ⟨Φ, hΦ⟩ := hc.2
    exact ⟨he, Φ, (congrArg Configuration.support he).trans hΦ⟩
  exact ⟨hρF, hmap, exists_measurable_probability_one_of_ae μ hexact⟩

theorem e8_exact_lattice_event_of_reconstructed_event
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (hgood : ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment e8Set c ∧ ReconstructedLatticeContainer e8Set c) :
    ExactLatticeRealization e8Set μ := by
  obtain ⟨H, hH, hp, hc⟩ := hgood
  have hh : ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, ReconstructedLatticeContainer (e8Lattice : Set (Ambient 8)) c := by
    refine ⟨H, hH, hp, fun c h => ?_⟩
    simpa only [coe_e8Lattice] using (hc c h).2
  simpa only [coe_e8Lattice] using exact_lattice_event_of_reconstructed_event
    e8EuclideanBasis e8Lattice le_rfl e8Lattice_covolume μ hμ hρ hh

theorem leech_exact_lattice_event_of_reconstructed_event
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (hgood : ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment leechSet c ∧ ReconstructedLatticeContainer leechSet c) :
    ExactLatticeRealization leechSet μ := by
  obtain ⟨H, hH, hp, hc⟩ := hgood
  have hh : ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, ReconstructedLatticeContainer (leechLattice : Set (Ambient 24)) c := by
    refine ⟨H, hH, hp, fun c h => ?_⟩
    simpa only [coe_leechLattice] using (hc c h).2
  have hle : Submodule.span ℤ (Set.range leechEuclideanBasis) ≤ leechLattice := by
    rw [leechLattice_eq_span]
  simpa only [coe_leechLattice] using exact_lattice_event_of_reconstructed_event
    leechEuclideanBasis leechLattice hle leechLattice_covolume μ hμ hρ hh

theorem e8_zero_excess_riesz_exact_lattice {s : ℝ} (hs : (8 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : rieszEnergy s μ = latticeRieszEnergy e8Set s) : ExactLatticeRealization e8Set μ :=
  e8_exact_lattice_event_of_reconstructed_event μ hμ hρ
    (e8_zero_excess_riesz_measurable_container hs μ hμ hρ henergy).2

theorem leech_zero_excess_riesz_exact_lattice {s : ℝ} (hs : (24 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : rieszEnergy s μ = latticeRieszEnergy leechSet s) : ExactLatticeRealization leechSet μ :=
  leech_exact_lattice_event_of_reconstructed_event μ hμ hρ
    (leech_zero_excess_riesz_measurable_container hs μ hμ hρ henergy).2

theorem e8_zero_excess_positiveGaussianMixture_exact_lattice
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν)) : ExactLatticeRealization e8Set μ :=
  e8_exact_lattice_event_of_reconstructed_event μ hμ hρ
    (e8_zero_excess_positiveGaussianMixture_measurable_container ν hν hbase μ hμ hρ henergy).2

theorem leech_zero_excess_positiveGaussianMixture_exact_lattice
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν)) : ExactLatticeRealization leechSet μ :=
  leech_exact_lattice_event_of_reconstructed_event μ hμ hρ
    (leech_zero_excess_positiveGaussianMixture_measurable_container ν hν hbase μ hμ hρ henergy).2

theorem e8_zero_excess_gaussian_exact_lattice {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy e8Set (gaussianPotential α)) :
    ExactLatticeRealization e8Set μ :=
  e8_exact_lattice_event_of_reconstructed_event μ hμ hρ
    (e8_zero_excess_gaussian_measurable_container hα μ hμ hρ henergy).2

theorem leech_zero_excess_gaussian_exact_lattice {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy leechSet (gaussianPotential α)) :
    ExactLatticeRealization leechSet μ :=
  leech_exact_lattice_event_of_reconstructed_event μ hμ hρ
    (leech_zero_excess_gaussian_measurable_container hα μ hμ hρ henergy).2

end E8Leech
