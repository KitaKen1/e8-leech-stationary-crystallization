-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.DualCovolume
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.Setup

/-!
# Self-duality from integrality and unimodularity

For a full `ℤ`-lattice `L` in `ℝ²⁴`, integrality implies `L ≤ L*` (where `L*` is the dual lattice).
If moreover the covolume is `1`, then the discriminant group `L*/L` is trivial, hence `L = L*`.

This is one of the standard structural inputs in the theory of even unimodular lattices.

## Main statements
* `le_dualLattice_of_integral`
* `dualLattice_eq_of_integral_unimodular`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

open scoped RealInnerProductSpace
open MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
/-- An integral lattice is contained in its dual lattice. -/
public theorem le_dualLattice_of_integral (L : Submodule ℤ ℝ²⁴) (hInt : Integral L) :
    L ≤ DualLattice L := by
  intro x hx
  -- `x ∈ DualLattice L` iff `∀ y ∈ L, ⟪x,y⟫` is an integer.
  refine (LinearMap.BilinForm.mem_dualSubmodule (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴))
      (N := L) (x := x)).2 ?_
  intro y hy
  rcases hInt x y hx hy with ⟨m, hm⟩
  refine (Submodule.mem_one).2 ⟨m, ?_⟩
  simpa [innerₗ_apply_apply] using! hm.symm

/-- An integral unimodular lattice is self-dual. -/
public theorem dualLattice_eq_of_integral_unimodular (L : Submodule ℤ ℝ²⁴)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hInt : Integral L) (hUnimod : Unimodular L) :
    DualLattice L = L := by
  have hLdual : L ≤ DualLattice L := le_dualLattice_of_integral (L := L) hInt
  have hcov : ZLattice.covolume L volume = 1 := by
    simpa [Unimodular] using! hUnimod
  have hcard :
      (Nat.card (DiscriminantGroup L) : ℝ) = (ZLattice.covolume L volume) ^ 2 :=
    card_discriminantGroup_eq_covolume_sq (L := L) hLdual
  have hcard1 : (Nat.card (DiscriminantGroup L) : ℝ) = (1 : ℝ) := by
    simpa [hcov] using! hcard
  have hcardNat : Nat.card (DiscriminantGroup L) = 1 := by
    exact_mod_cast hcard1
  have hrel :
      L.toAddSubgroup.relIndex (DualLattice L).toAddSubgroup = 1 := by
    -- `relIndex` is the cardinality of the discriminant group.
    simpa [hcardNat] using! (relIndex_eq_card_discriminantGroup (L := L))
  have hdual_le' :
      (DualLattice L).toAddSubgroup ≤ L.toAddSubgroup :=
    (AddSubgroup.relIndex_eq_one.mp hrel)
  have hdual_le : DualLattice L ≤ L := by
    assumption
  exact le_antisymm hdual_le hLdual

end SpherePacking.Dim24.Uniqueness.RigidityClassify
