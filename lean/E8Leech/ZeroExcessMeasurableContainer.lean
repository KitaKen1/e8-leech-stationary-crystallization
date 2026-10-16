import E8Leech.MeasurableTernaryReconstruction

/-!
# A measurable equivariant containing-lattice map at zero excess

The universal ternary reconstruction equals the unique containing lattice on
the full-density event. Its pushforward of any stationary law is stationary.
For the actual zero-excess laws this completes Z2, without a parameter selector
or a Borel description of the whole existential containment predicate.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

theorem ternaryLocallyFinite_of_isometry_image {d : ℕ}
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (c : Configuration (Ambient d)) (Φ : Ambient d ≃ᵢ Ambient d)
    (hΦ : ternarySupport c = Φ '' (Λ : Set (Ambient d))) : TernaryLocallyFinite c := by
  intro K hK
  rw [hΦ]
  exact ((latticeConfiguration Λ).mapHomeomorph Φ.toHomeomorph).finite_on_compacts K hK

theorem ternaryReconstruction_isometry_image_of_fullDensity {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (c : Configuration (Ambient d)) (hc : FullDensityLatticeContainment (Λ : Set (Ambient d)) c) :
    ∃ Φ : Ambient d ≃ᵢ Ambient d,
      (ternaryReconstruction c).support = Φ '' (Λ : Set (Ambient d)) := by
  obtain ⟨Φ, hΦ⟩ := ternarySupport_isometry_image_of_fullDensity b Λ hle hcov c hc
  have hf := ternaryLocallyFinite_of_isometry_image Λ c Φ hΦ
  exact ⟨Φ, by simp only [ternaryReconstruction_support, if_pos hf, hΦ]⟩

theorem isStationary_map_ternaryReconstruction {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ) :
    IsStationary (μ.map ternaryReconstruction) := by
  intro a
  refine ⟨measurable_translate a, ?_⟩
  rw [Measure.map_map (measurable_translate a) measurable_ternaryReconstruction]
  have he : translate a ∘ ternaryReconstruction = ternaryReconstruction ∘ translate a := by
    funext c
    exact (ternaryReconstruction_translate a c).symm
  rw [he, ← Measure.map_map measurable_ternaryReconstruction (measurable_translate a),
    (hμ a).map_eq]

theorem isProbabilityMeasure_map_ternaryReconstruction {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.map ternaryReconstruction) := by
  constructor
  rw [Measure.map_apply measurable_ternaryReconstruction MeasurableSet.univ,
    preimage_univ, measure_univ]

/-- The universal measurable reconstruction is an actual containing reference lattice. -/
def ReconstructedLatticeContainer {d : ℕ} (Λ : Set (Ambient d))
    (c : Configuration (Ambient d)) : Prop :=
  c.support ⊆ (ternaryReconstruction c).support ∧
    ∃ Φ : Ambient d ≃ᵢ Ambient d, (ternaryReconstruction c).support = Φ '' Λ

theorem reconstructedLatticeContainer_of_fullDensity {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (c : Configuration (Ambient d)) (hc : FullDensityLatticeContainment (Λ : Set (Ambient d)) c) :
    ReconstructedLatticeContainer (Λ : Set (Ambient d)) c := by
  obtain ⟨Φ, hΦ⟩ := ternarySupport_isometry_image_of_fullDensity b Λ hle hcov c hc
  have hf := ternaryLocallyFinite_of_isometry_image Λ c Φ hΦ
  refine ⟨?_, Φ, ?_⟩
  · simpa only [ternaryReconstruction_support, if_pos hf] using support_subset_ternarySupport c
  · simpa only [ternaryReconstruction_support, if_pos hf] using hΦ

theorem e8_reconstructedLatticeContainer_of_fullDensity (c : Configuration (Ambient 8))
    (hc : FullDensityLatticeContainment e8Set c) : ReconstructedLatticeContainer e8Set c := by
  have hc' : FullDensityLatticeContainment (e8Lattice : Set (Ambient 8)) c := by
    simpa only [coe_e8Lattice] using hc
  simpa only [coe_e8Lattice] using reconstructedLatticeContainer_of_fullDensity
    e8EuclideanBasis e8Lattice le_rfl e8Lattice_covolume c hc'

theorem leech_reconstructedLatticeContainer_of_fullDensity (c : Configuration (Ambient 24))
    (hc : FullDensityLatticeContainment leechSet c) : ReconstructedLatticeContainer leechSet c := by
  have hc' : FullDensityLatticeContainment (leechLattice : Set (Ambient 24)) c := by
    simpa only [coe_leechLattice] using hc
  have hle : Submodule.span ℤ (Set.range leechEuclideanBasis) ≤ leechLattice := by
    rw [leechLattice_eq_span]
  simpa only [coe_leechLattice] using reconstructedLatticeContainer_of_fullDensity
    leechEuclideanBasis leechLattice hle leechLattice_covolume c hc'

theorem measurable_container_event_of_fullDensity_event {d : ℕ} {Λ : Set (Ambient d)}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    (hrec : ∀ c, FullDensityLatticeContainment Λ c → ReconstructedLatticeContainer Λ c)
    (hgood : ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment Λ c) :
    IsStationary (μ.map ternaryReconstruction) ∧
    ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment Λ c ∧ ReconstructedLatticeContainer Λ c := by
  obtain ⟨H, hH, hp, hc⟩ := hgood
  exact ⟨isStationary_map_ternaryReconstruction μ hμ, H, hH, hp,
    fun c h => ⟨hc c h, hrec c (hc c h)⟩⟩

theorem e8_zero_excess_riesz_measurable_container {s : ℝ} (hs : (8 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : rieszEnergy s μ = latticeRieszEnergy e8Set s) :
    IsStationary (μ.map ternaryReconstruction) ∧
    ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment e8Set c ∧ ReconstructedLatticeContainer e8Set c :=
  measurable_container_event_of_fullDensity_event μ hμ e8_reconstructedLatticeContainer_of_fullDensity
    (e8_zero_excess_riesz_lattice_containment hs μ hμ hρ henergy)

theorem leech_zero_excess_riesz_measurable_container {s : ℝ} (hs : (24 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : rieszEnergy s μ = latticeRieszEnergy leechSet s) :
    IsStationary (μ.map ternaryReconstruction) ∧
    ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment leechSet c ∧ ReconstructedLatticeContainer leechSet c :=
  measurable_container_event_of_fullDensity_event μ hμ leech_reconstructedLatticeContainer_of_fullDensity
    (leech_zero_excess_riesz_lattice_containment hs μ hμ hρ henergy)

theorem e8_zero_excess_positiveGaussianMixture_measurable_container
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν)) :
    IsStationary (μ.map ternaryReconstruction) ∧
    ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment e8Set c ∧ ReconstructedLatticeContainer e8Set c :=
  measurable_container_event_of_fullDensity_event μ hμ e8_reconstructedLatticeContainer_of_fullDensity
    (e8_zero_excess_positiveGaussianMixture_lattice_containment ν hν hbase μ hμ hρ henergy)

theorem leech_zero_excess_positiveGaussianMixture_measurable_container
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν)) :
    IsStationary (μ.map ternaryReconstruction) ∧
    ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment leechSet c ∧ ReconstructedLatticeContainer leechSet c :=
  measurable_container_event_of_fullDensity_event μ hμ leech_reconstructedLatticeContainer_of_fullDensity
    (leech_zero_excess_positiveGaussianMixture_lattice_containment ν hν hbase μ hμ hρ henergy)

theorem e8_zero_excess_gaussian_measurable_container {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy e8Set (gaussianPotential α)) :
    IsStationary (μ.map ternaryReconstruction) ∧
    ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment e8Set c ∧ ReconstructedLatticeContainer e8Set c :=
  measurable_container_event_of_fullDensity_event μ hμ e8_reconstructedLatticeContainer_of_fullDensity
    (e8_zero_excess_gaussian_lattice_containment hα μ hμ hρ henergy)

theorem leech_zero_excess_gaussian_measurable_container {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy leechSet (gaussianPotential α)) :
    IsStationary (μ.map ternaryReconstruction) ∧
    ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment leechSet c ∧ ReconstructedLatticeContainer leechSet c :=
  measurable_container_event_of_fullDensity_event μ hμ leech_reconstructedLatticeContainer_of_fullDensity
    (leech_zero_excess_gaussian_lattice_containment hα μ hμ hρ henergy)

end E8Leech
