import FCTargetDefinitions

noncomputable section
namespace E8LeechFC
open E8Leech Set MeasureTheory
open scoped ENNReal

theorem e8_quantitative_crystallization {s γ : ℝ} (hs : (8 : ℝ) < s) (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient 8)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          rieszEnergy s μ ≤ latticeRieszEnergy e8Set s + ENNReal.ofReal δ →
          ∃ G : Set (Configuration (Ambient 8)), MeasurableSet G ∧
            G ⊆ {c | LocalCrystal e8Set c (observationRadius δ)
              (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G := by
  sorry

theorem e8_gaussian_crystallization {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent e8Set (gaussianPotential α) γ := by
  sorry

theorem e8_positiveGaussianMixture_crystallization (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    {γ : ℝ} (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent e8Set (positiveGaussianMixturePotential ν) γ := by
  sorry

theorem e8_riesz_zero_excess_iff_ae_isometric_lattice {s : ℝ} (hs : (8 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    rieszEnergy s μ = latticeRieszEnergy e8Set s ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set := by
  sorry

theorem e8_gaussian_zero_excess_iff_ae_isometric_lattice {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy e8Set (gaussianPotential α) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set := by
  sorry

theorem e8_positiveGaussianMixture_zero_excess_iff_ae_isometric_lattice
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set := by
  sorry

theorem leech_quantitative_crystallization {s γ : ℝ} (hs : (24 : ℝ) < s) (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient 24)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          rieszEnergy s μ ≤ latticeRieszEnergy leechSet s + ENNReal.ofReal δ →
          ∃ G : Set (Configuration (Ambient 24)), MeasurableSet G ∧
            G ⊆ {c | LocalCrystal leechSet c (observationRadius δ)
              (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G := by
  sorry

theorem leech_gaussian_crystallization {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent leechSet (gaussianPotential α) γ := by
  sorry

theorem leech_positiveGaussianMixture_crystallization (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    {γ : ℝ} (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent leechSet (positiveGaussianMixturePotential ν) γ := by
  sorry

theorem leech_riesz_zero_excess_iff_ae_isometric_lattice {s : ℝ} (hs : (24 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    rieszEnergy s μ = latticeRieszEnergy leechSet s ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet := by
  sorry

theorem leech_gaussian_zero_excess_iff_ae_isometric_lattice {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy leechSet (gaussianPotential α) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet := by
  sorry

theorem leech_positiveGaussianMixture_zero_excess_iff_ae_isometric_lattice
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet := by
  sorry

theorem stationary_exact_lattice_law {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hb : Λ = Submodule.span ℤ (Set.range b))
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient d ≃ᵢ Ambient d, c.support = Φ '' (Λ : Set (Ambient d))) :
    ∃ σ : Measure (LatticeOrientation d), IsProbabilityMeasure σ ∧ μ = orientationMixtureLaw Λ D σ := by
  sorry

end E8LeechFC
