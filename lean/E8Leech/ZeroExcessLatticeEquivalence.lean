import E8Leech.IsometricLatticeEnergy

/-! # Zero excess if and only if the configurations are entire isometric lattices -/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

theorem ae_isometric_lattice_of_exactLatticeRealization {d : ℕ} {Λ : Set (Ambient d)}
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (h : ExactLatticeRealization Λ μ) :
    ∀ᵐ c ∂μ, ∃ Φ : Ambient d ≃ᵢ Ambient d, c.support = Φ '' Λ := by
  obtain ⟨_, _, H, hH, hp, hc⟩ := h
  have hh : ∀ᵐ c ∂μ, c ∈ H := (mem_ae_iff_prob_eq_one hH).mpr hp
  exact hh.mono fun c h => (hc c h).2

theorem e8_potentialEnergy_eq_of_ae_isometric_lattice
    (P : Ambient 8 → Ambient 8 → ℝ≥0∞) (hP : IsometryInvariantPotential P)
    (μ : Measure (Configuration (Ambient 8))) (hρ : HasIntensity μ 1)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set) :
    potentialEnergy P μ = latticePotentialEnergy e8Set P := by
  rw [← coe_e8Lattice] at hgood ⊢
  exact potentialEnergy_eq_lattice_of_ae_isometric_lattice e8Lattice P hP μ hρ hgood

theorem leech_potentialEnergy_eq_of_ae_isometric_lattice
    (P : Ambient 24 → Ambient 24 → ℝ≥0∞) (hP : IsometryInvariantPotential P)
    (μ : Measure (Configuration (Ambient 24))) (hρ : HasIntensity μ 1)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet) :
    potentialEnergy P μ = latticePotentialEnergy leechSet P := by
  rw [← coe_leechLattice] at hgood ⊢
  exact potentialEnergy_eq_lattice_of_ae_isometric_lattice leechLattice P hP μ hρ hgood

theorem e8_riesz_zero_excess_iff_ae_isometric_lattice {s : ℝ} (hs : (8 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    rieszEnergy s μ = latticeRieszEnergy e8Set s ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set := by
  constructor
  · intro he
    exact ae_isometric_lattice_of_exactLatticeRealization μ (e8_zero_excess_riesz_exact_lattice hs μ hμ hρ he)
  · intro h
    exact e8_potentialEnergy_eq_of_ae_isometric_lattice (rieszPotential s)
      (rieszPotential_isometryInvariant s) μ hρ h

theorem leech_riesz_zero_excess_iff_ae_isometric_lattice {s : ℝ} (hs : (24 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    rieszEnergy s μ = latticeRieszEnergy leechSet s ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet := by
  constructor
  · intro he
    exact ae_isometric_lattice_of_exactLatticeRealization μ (leech_zero_excess_riesz_exact_lattice hs μ hμ hρ he)
  · intro h
    exact leech_potentialEnergy_eq_of_ae_isometric_lattice (rieszPotential s)
      (rieszPotential_isometryInvariant s) μ hρ h

theorem e8_positiveGaussianMixture_zero_excess_iff_ae_isometric_lattice
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set := by
  constructor
  · intro he
    exact ae_isometric_lattice_of_exactLatticeRealization μ
      (e8_zero_excess_positiveGaussianMixture_exact_lattice ν hν hbase μ hμ hρ he)
  · intro h
    exact e8_potentialEnergy_eq_of_ae_isometric_lattice _
      (positiveGaussianMixturePotential_isometryInvariant ν) μ hρ h

theorem leech_positiveGaussianMixture_zero_excess_iff_ae_isometric_lattice
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet := by
  constructor
  · intro he
    exact ae_isometric_lattice_of_exactLatticeRealization μ
      (leech_zero_excess_positiveGaussianMixture_exact_lattice ν hν hbase μ hμ hρ he)
  · intro h
    exact leech_potentialEnergy_eq_of_ae_isometric_lattice _
      (positiveGaussianMixturePotential_isometryInvariant ν) μ hρ h

theorem e8_gaussian_zero_excess_iff_ae_isometric_lattice {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy e8Set (gaussianPotential α) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set := by
  constructor
  · intro he
    exact ae_isometric_lattice_of_exactLatticeRealization μ (e8_zero_excess_gaussian_exact_lattice hα μ hμ hρ he)
  · intro h
    exact e8_potentialEnergy_eq_of_ae_isometric_lattice _ (gaussianPotential_isometryInvariant α) μ hρ h

theorem leech_gaussian_zero_excess_iff_ae_isometric_lattice {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy leechSet (gaussianPotential α) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet := by
  constructor
  · intro he
    exact ae_isometric_lattice_of_exactLatticeRealization μ (leech_zero_excess_gaussian_exact_lattice hα μ hμ hρ he)
  · intro h
    exact leech_potentialEnergy_eq_of_ae_isometric_lattice _ (gaussianPotential_isometryInvariant α) μ hρ h

end E8Leech
