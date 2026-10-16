import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

variable {X : Type*} [TopologicalSpace X]
structure Configuration (X : Type*) [TopologicalSpace X] where
  support : Set X
  finite_on_compacts : ∀ K : Set X, IsCompact K → (support ∩ K).Finite

namespace Configuration
instance : Coe (Configuration X) (Set X) := ⟨Configuration.support⟩

def mapHomeomorph (e : X ≃ₜ X) (c : Configuration X) : Configuration X where
  support := e '' c.support
  finite_on_compacts K hK := by
    have hpre : IsCompact (e ⁻¹' K) := by
      have heq : e ⁻¹' K = e.symm '' K := by
        ext x
        constructor
        · intro hx
          exact ⟨e x, hx, e.symm_apply_apply x⟩
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
      rw [heq]
      exact hK.image e.symm.continuous
    have hfinite := (c.finite_on_compacts (e ⁻¹' K) hpre).image e
    have heq : e '' (c.support ∩ e ⁻¹' K) = e '' c.support ∩ K := by
      exact Set.image_inter_preimage e c.support K
    rwa [heq] at hfinite

section
variable [MeasurableSpace X] [MeasurableSingletonClass X]
def count (c : Configuration X) (A : Set X) : ℝ≥0∞ :=
  Measure.count (c.support ∩ A)

instance : MeasurableSpace (Configuration X) :=
  ⨆ A : {A : Set X // MeasurableSet A},
    MeasurableSpace.comap (fun c : Configuration X => c.count A.1) inferInstance
end
end Configuration
end E8Leech
