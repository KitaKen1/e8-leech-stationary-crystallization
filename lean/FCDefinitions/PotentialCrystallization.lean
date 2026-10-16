import FCDefinitions.GaussianPotentialMixtures

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def potentialEnergy {d : ℕ} (P : Ambient d → Ambient d → ℝ≥0∞)
    (μ : Measure (Configuration (Ambient d))) : ℝ≥0∞ :=
  ∫⁻ z, orderedWindowEnergy P z (unitWindow d) ∂μ

def HasPotentialExcessAtMost {d : ℕ} (P : Ambient d → Ambient d → ℝ≥0∞)
    (μ : Measure (Configuration (Ambient d))) (L δ : ℝ≥0∞) : Prop :=
  L ≠ ∞ ∧ potentialEnergy P μ ≤ L + δ

end E8Leech
