-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.BiplaneParams
import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneUniqueness.Extract

/-!
# Setup for biplane uniqueness

We pick a distinguished block `B₀ ∈ D.blocks` and define its complement `U = univ \\ B₀`.
This corresponds to the first line of the proof of Theorem `thm:biplane_unique` in the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Aux

noncomputable section

variable (D : Biplane.Structure)

/-- A biplane has at least one block. -/
lemma blocks_card_pos : 0 < D.blocks.card := by simp [D.blocks_card]

/-- A distinguished block in a biplane structure (chosen nonconstructively). -/
public def chooseBlock : Biplane.Block :=
  Classical.choose <| Finset.card_pos.1 (blocks_card_pos D)

/-- The chosen block is indeed a member of `D.blocks`. -/
public lemma chooseBlock_mem : chooseBlock D ∈ D.blocks :=
  (Classical.choose_spec <| Finset.card_pos.1 (blocks_card_pos D))

lemma chooseBlock_card : (chooseBlock D).card = 5 :=
  D.block_card _ (chooseBlock_mem D)

/-- The complement of the chosen block, viewed as a finset of points. -/
def U : Finset Biplane.Point := U0 (B0 := chooseBlock D)

lemma mem_U_iff {x : Biplane.Point} : x ∈ U D ↔ x ∉ chooseBlock D := by
  simpa [U] using! (mem_U0_iff (B0 := chooseBlock D) (x := x))

attribute [grind =] mem_U_iff

lemma U_card : (U D).card = 6 := by
  simpa [U] using! U0_card (D := D) (B0 := chooseBlock D) (chooseBlock_mem D)

lemma union_chooseBlock_U : chooseBlock D ∪ U D = (Finset.univ : Finset Biplane.Point) := by
  ext x
  by_cases hx : x ∈ chooseBlock D <;> simp [Finset.mem_union, mem_U_iff (D := D), hx]

lemma disjoint_chooseBlock_U : Disjoint (chooseBlock D) (U D) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxB hxU
  exact (mem_U_iff (D := D) (x := x)).1 hxU hxB

end

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Aux

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
