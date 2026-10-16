import E8Leech.LeechPeriodicStability
import E8Leech.LeechCharacterizationProof

/-!
# The periodic stability input for the Leech lattice, without hypotheses

`LeechPeriodicStability` proves the periodic stability input for the Leech lattice from
`LeechCharacterization`, and `LeechCharacterizationProof` proves `LeechCharacterization`. This
file combines the two. What remains for the stationary crystallization target of the Leech lattice
is the analytic unit-cost input alone.
-/

namespace E8Leech

/-- **The periodic stability input for the Leech lattice.** -/
theorem leech_sectionwisePeriodicStabilityInput_holds :
    ∃ E B c η₀ : ℝ, 0 ≤ E ∧ 0 ≤ B ∧ 0 ≤ c ∧ 0 < η₀ ∧
      SectionwisePeriodicStabilityInput leechSet 2 E B c η₀ :=
  leech_sectionwisePeriodicStabilityInput leechCharacterization

/-- **What remains for the Leech lattice.** The stationary crystallization target for the Leech
lattice follows from the analytic unit-cost input of the Leech lattice. -/
theorem leech_stationaryCrystallization_of_analyticInput
    (hanalytic : ∀ s : ℝ, ((24 : ℕ) : ℝ) < s → ∃ A δA : ℝ,
      0 ≤ A ∧ 0 < δA ∧ AnalyticUnitCostInput leechSet s 2 A δA) :
    leechCrystallizationTarget :=
  leech_stationaryCrystallization_of_inputs leechCharacterization hanalytic

end E8Leech
