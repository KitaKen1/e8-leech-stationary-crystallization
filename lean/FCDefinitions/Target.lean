import FCDefinitions.LeechCoordinates

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def observationRadius (δ : ℝ) : ℝ :=
  Real.log (1 / δ) / Real.log (Real.log (1 / δ))

def latticeRieszEnergy {d : ℕ} (Λ : Set (Ambient d)) (s : ℝ) : ℝ≥0∞ :=
  ∑' y : Λ, if (y : Ambient d) = 0 then 0 else rieszPotential s 0 (y : Ambient d)

def LocalCrystal {d : ℕ} (Λ : Set (Ambient d))
    (c : Configuration (Ambient d)) (R error loss : ℝ) : Prop :=
  (∃ Φ : Ambient d ≃ᵢ Ambient d, ∃ Z : Finset (Ambient d),
    (↑Z : Set (Ambient d)) ⊆ Λ ∧
    (∀ x ∈ c.support ∩ Metric.closedBall 0 R, ∃ z ∈ Z, dist x (Φ z) ≤ error) ∧
    (∀ z ∈ Z, ∃ x ∈ c.support ∩ Metric.closedBall 0 R, dist (Φ z) x ≤ error)) ∧
  ENNReal.ofReal (1 - loss) * volume (Metric.closedBall (0 : Ambient d) R) ≤
    c.count (Metric.closedBall 0 R)

end E8Leech
