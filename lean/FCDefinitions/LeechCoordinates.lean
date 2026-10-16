import FCDefinitions.Golay

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def leechResidue (z : Fin 24 → ℤ) (m : ℤ) : Fin 24 → ZMod 2 :=
  fun i => ((z i - m) / 2 : ℤ)

def leechNumerators : Set (Fin 24 → ℤ) :=
  {z | ∃ m : ℤ, (∀ i, (2 : ℤ) ∣ z i - m) ∧
    (8 : ℤ) ∣ (∑ i, z i) - 4 * m ∧ leechResidue z m ∈ golayCode}

def leechCoordinates (z : Fin 24 → ℤ) : Ambient 24 :=
  WithLp.toLp 2 (fun i => (z i : ℝ) / Real.sqrt 8)

def leechSet : Set (Ambient 24) := leechCoordinates '' leechNumerators

end E8Leech
