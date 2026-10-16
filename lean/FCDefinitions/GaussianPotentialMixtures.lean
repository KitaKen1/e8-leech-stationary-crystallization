import FCDefinitions.GaussianPairIntegrals

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def gaussianPotential {d : ℕ} (α : ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianKernel α (x - y))

def positiveGaussianMixturePotential {d : ℕ} (ν : Measure ℝ)
    (x y : Ambient d) : ℝ≥0∞ :=
  potentialMixture (ν.restrict (Ioi 0)) (gaussianPotential (d := d)) x y

end E8Leech
