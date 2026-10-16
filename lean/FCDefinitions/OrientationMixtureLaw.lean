import FCDefinitions.RotatedLatticeLaw

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def orientationMixtureLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (D : Set (Ambient d)) (σ : Measure (LatticeOrientation d)) :
    Measure (Configuration (Ambient d)) := σ.bind (rotatedLatticeShiftLaw Λ D)

end E8Leech
