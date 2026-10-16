import FCDefinitions.PotentialMixtures

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def gaussianKernel {d : ℕ} (α : ℝ) (x : Ambient d) : ℝ :=
  Real.exp (-α * ‖x‖ ^ 2)

end E8Leech
