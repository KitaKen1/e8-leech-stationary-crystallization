import E8Leech.GeneralGammaTransfer
import E8Leech.LeechCrystallization

/-!
# The E8 and Leech theorems for every exponent `0 < γ < 1/12`

The existing unconditional analytic and periodic stability inputs are reused.
The target is the original-point quantitative conclusion with a measurable
high-probability subevent. This does not assert Borelness of the full success
event or the endpoint `γ = 1/12`.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory

/-- Stationary E8 crystallization at every exponent below `1/12`. -/
theorem e8CrystallizationAllExponents_holds : StationaryCrystallizationForAllExponents e8Set := by
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, h⟩ := e8_sectionwisePeriodicStabilityInput
  exact stationaryCrystallizationForAllExponents_of_sectionwise_inputs e8Set isClosed_e8Set
    ⟨0, zero_mem_e8⟩ (fun _ hx _ hy => e8Set_sub hx hy) (Real.sqrt 2) E B c η₀
    (Real.sqrt_pos.mpr (by norm_num)) hE hB hc hη₀ h e8_analyticUnitCostInput_gt

/-- Stationary Leech crystallization at every exponent below `1/12`. -/
theorem leechCrystallizationAllExponents_holds :
    StationaryCrystallizationForAllExponents leechSet := by
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, h⟩ := leech_sectionwisePeriodicStabilityInput_holds
  exact stationaryCrystallizationForAllExponents_of_sectionwise_inputs leechSet isClosed_leechSet
    ⟨0, zero_mem_leechSet⟩ (fun _ hx _ hy => leechSet_sub hx hy) 2 E B c η₀
    (by norm_num) hE hB hc hη₀ h (fun s hs => by
      have hs0 : 0 < s := lt_trans (by norm_num) hs
      obtain ⟨C, hC, hinput⟩ := leech_analyticUnitCostInput_of_ckmrv hs0
        leechKernelInequalities leechFourierIdentities leechBlockBounds
      exact ⟨C⁻¹, 1 / 8, (inv_pos.mpr hC).le, by norm_num, hinput⟩)

/-- The two unconditional general-exponent targets together. -/
theorem e8LeechCrystallizationAllExponents_holds :
    StationaryCrystallizationForAllExponents e8Set ∧
      StationaryCrystallizationForAllExponents leechSet :=
  ⟨e8CrystallizationAllExponents_holds, leechCrystallizationAllExponents_holds⟩

/-- The E8 general-exponent theorem with the manuscript's energy inequality. -/
theorem e8_crystallization_of_energy_le_general {s γ : ℝ} (hs : (8 : ℝ) < s) (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient 8)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          rieszEnergy s μ ≤ latticeRieszEnergy e8Set s + ENNReal.ofReal δ →
          ∃ G : Set (Configuration (Ambient 8)), MeasurableSet G ∧
            G ⊆ {c | LocalCrystal e8Set c (observationRadius δ)
              (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G := by
  obtain ⟨C, hC, δ₀, hδ₀, hδ₀e, h⟩ := e8CrystallizationAllExponents_holds γ hγ hγlt s (by exact_mod_cast hs)
  exact ⟨C, hC, δ₀, hδ₀, hδ₀e, fun μ hP hS hI δ hδ hδ' hE =>
    h μ hP hS hI δ hδ hδ' ⟨e8_latticeRieszEnergy_ne_top hs, hE⟩⟩

/-- **The Leech theorem in the form of the manuscript** (`s > 24`; see
`e8_crystallization_of_energy_le_general`). -/
theorem leech_crystallization_of_energy_le_general {s γ : ℝ} (hs : (24 : ℝ) < s) (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient 24)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          rieszEnergy s μ ≤ latticeRieszEnergy leechSet s + ENNReal.ofReal δ →
          ∃ G : Set (Configuration (Ambient 24)), MeasurableSet G ∧
            G ⊆ {c | LocalCrystal leechSet c (observationRadius δ)
              (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G := by
  obtain ⟨C, hC, δ₀, hδ₀, hδ₀e, h⟩ := leechCrystallizationAllExponents_holds γ hγ hγlt s (by exact_mod_cast hs)
  exact ⟨C, hC, δ₀, hδ₀, hδ₀e, fun μ hP hS hI δ hδ hδ' hE =>
    h μ hP hS hI δ hδ hδ' ⟨leech_latticeRieszEnergy_ne_top hs, hE⟩⟩

end E8Leech
