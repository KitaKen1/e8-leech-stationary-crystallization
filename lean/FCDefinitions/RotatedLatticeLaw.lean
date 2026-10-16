import FCDefinitions.LatticeShiftLaw

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

structure LatticeOrientation (d : ℕ) where
  isometry : Ambient d ≃ₗᵢ[ℝ] Ambient d

instance {d : ℕ} : TopologicalSpace (LatticeOrientation d) :=
  TopologicalSpace.induced (fun Q : LatticeOrientation d => Q.isometry.toContinuousLinearMap)
    inferInstance

instance {d : ℕ} : SecondCountableTopology (LatticeOrientation d) :=
  TopologicalSpace.secondCountableTopology_induced _ _ _

instance {d : ℕ} : MeasurableSpace (LatticeOrientation d) := borel _

instance {d : ℕ} : BorelSpace (LatticeOrientation d) := ⟨rfl⟩

def rotateConfiguration {d : ℕ} (Q : Ambient d ≃ₗᵢ[ℝ] Ambient d)
    (c : Configuration (Ambient d)) : Configuration (Ambient d) :=
  c.mapHomeomorph Q.toHomeomorph

def rotatedLatticeShift {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (Q : LatticeOrientation d) (u : Ambient d) : Configuration (Ambient d) :=
  rotateConfiguration Q.isometry (latticeShift Λ u)

def rotatedLatticeShiftLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (D : Set (Ambient d)) (Q : LatticeOrientation d) : Measure (Configuration (Ambient d)) :=
  (latticeShiftLaw Λ D).map (rotateConfiguration Q.isometry)

end E8Leech
