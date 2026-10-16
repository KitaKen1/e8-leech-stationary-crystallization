import FCDefinitions.Target

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def potentialMixture {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) (V : Θ → Ambient d → Ambient d → ℝ≥0∞)
    (x y : Ambient d) : ℝ≥0∞ := ∫⁻ θ, V θ x y ∂ν

def latticePotentialEnergy {d : ℕ} (Λ : Set (Ambient d))
    (V : Ambient d → Ambient d → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' y : Λ, if (y : Ambient d) = 0 then 0 else V 0 y

end E8Leech
