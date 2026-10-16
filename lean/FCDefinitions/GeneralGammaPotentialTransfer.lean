import FCDefinitions.PotentialCrystallization

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def PotentialCrystallizationTargetForExponent {d : ℕ} (Λ : Set (Ambient d))
    (P : Ambient d → Ambient d → ℝ≥0∞) (γ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
    ∀ μ : Measure (Configuration (Ambient d)),
      IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        HasPotentialExcessAtMost P μ (latticePotentialEnergy Λ P) (ENNReal.ofReal δ) →
        ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
          G ⊆ {z | LocalCrystal Λ z (observationRadius δ)
            (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
          ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G

end E8Leech
