import FCDefinitions.Energy

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def e8Numerators : Set (Fin 8 → ℤ) :=
  {z | (∀ i, (2 : ℤ) ∣ z i - z 0) ∧ (4 : ℤ) ∣ ∑ i, z i}

def halfCoordinates (z : Fin 8 → ℤ) : Ambient 8 :=
  WithLp.toLp 2 (fun i => (z i : ℝ) / 2)

def e8Set : Set (Ambient 8) := halfCoordinates '' e8Numerators

end E8Leech
