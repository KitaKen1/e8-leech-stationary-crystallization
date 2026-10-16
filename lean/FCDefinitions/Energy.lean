import FCDefinitions.StationaryProcess

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def orderedWindowEnergy {X : Type*} [TopologicalSpace X]
    (V : X → X → ℝ≥0∞) (c : Configuration X) (W : Set X) : ℝ≥0∞ :=
  ∑' x : c.support, if (x : X) ∈ W then
    ∑' y : c.support, if (y : X) = (x : X) then 0 else V x y
    else 0

def rieszPotential {d : ℕ} (s : ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  ENNReal.ofReal (dist x y) ^ (-s)

def unitWindow (d : ℕ) : Set (Ambient d) :=
  {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}

def rieszEnergy {d : ℕ} (s : ℝ) (μ : Measure (Configuration (Ambient d))) : ℝ≥0∞ :=
  ∫⁻ c, orderedWindowEnergy (rieszPotential s) c (unitWindow d) ∂μ

def HasRieszExcessAtMost {d : ℕ} (s : ℝ)
    (μ : Measure (Configuration (Ambient d))) (latticeEnergy δ : ℝ≥0∞) : Prop :=
  latticeEnergy ≠ ∞ ∧ rieszEnergy s μ ≤ latticeEnergy + δ

end E8Leech
