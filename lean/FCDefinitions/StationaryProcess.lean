import FCDefinitions.Configuration

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

def translate {d : ℕ} (a : Ambient d) : Configuration (Ambient d) → Configuration (Ambient d) :=
  Configuration.mapHomeomorph (Homeomorph.addLeft a)

def IsStationary {d : ℕ} (μ : Measure (Configuration (Ambient d))) : Prop :=
  ∀ a : Ambient d, MeasurePreserving (translate a) μ μ

def HasIntensity {d : ℕ} (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) : Prop :=
  ∀ W : Set (Ambient d), MeasurableSet W →
    (∫⁻ c, c.count W ∂μ) = ρ * volume W

end E8Leech
