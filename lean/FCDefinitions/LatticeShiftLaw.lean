import FCDefinitions.GeneralGammaPotentialTransfer

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

section
variable {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
def latticeConfiguration : Configuration (Ambient d) where
  support := (Λ : Set (Ambient d))
  finite_on_compacts K hK := by
    have h : (K ∩ (Λ.toAddSubgroup : Set (Ambient d))).Finite := by
      have : DiscreteTopology Λ.toAddSubgroup := (inferInstance : DiscreteTopology Λ)
      exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hK.isBounded
        AddSubgroup.isClosed_of_discrete
    rw [Set.inter_comm]
    exact h

def latticeShift (u : Ambient d) : Configuration (Ambient d) :=
  translate u (latticeConfiguration Λ)

variable [IsZLattice ℝ Λ]

def latticeShiftLaw (D : Set (Ambient d)) : Measure (Configuration (Ambient d)) :=
  (volume.restrict D).map (latticeShift Λ)

end
end E8Leech
