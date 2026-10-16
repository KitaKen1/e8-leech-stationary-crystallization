-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.BiplaneParams

/-!
# Indexing blocks by pairs in a distinguished block

Fix a biplane structure `D` and a distinguished block `B₀ ∈ D.blocks`. For any distinct points
`x, y ∈ B₀`, the biplane axiom `lam(x,y) = 2` implies there is a unique block `B ≠ B₀`
containing both `x` and `y`. This file packages the resulting indexing function
`otherBlockThroughPair` together with its specification lemma.

This corresponds to Step 1 in the proof of Theorem `thm:biplane_unique` in the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Aux

noncomputable section

variable (D : Biplane.Structure) {B0 : Biplane.Block}

/-- For `x ≠ y` in `B0`, there is a unique other block through `{x,y}` besides `B0`. -/
public lemma exists_unique_other_block_through_pair
    (hB0 : B0 ∈ D.blocks) {x y : Biplane.Point} (hx : x ∈ B0) (hy : y ∈ B0) (hxy : x ≠ y) :
    ∃! B : Biplane.Block, B ∈ D.blocks ∧ x ∈ B ∧ y ∈ B ∧ B ≠ B0 := by
  let S : Finset Biplane.Block := D.blocks.filter (fun B => x ∈ B ∧ y ∈ B)
  have hcard : S.card = 2 := by
    -- `lam(x,y) = 2` (Lemma `biplane_from_intersections` in the note).
    simpa [S, Biplane.Structure.lam] using!
      (Biplane.Structure.lam_eq_two (D := D) (x := x) (y := y) hxy)
  have hB0S : B0 ∈ S := by
    simp [S, hB0, hx, hy]
  have hcard_erase : (S.erase B0).card = 1 := by
    simpa [hcard] using! (Finset.card_erase_of_mem (s := S) (a := B0) hB0S)
  rcases Finset.card_eq_one.1 hcard_erase with ⟨B1, hErase⟩
  refine ⟨B1, ?_, ?_⟩
  · have hB1_erase : B1 ∈ S.erase B0 := by simp [hErase]
    have hB1S : B1 ∈ S := (Finset.mem_erase.1 hB1_erase).2
    have hB1_ne : B1 ≠ B0 := (Finset.mem_erase.1 hB1_erase).1
    have hmemS : B1 ∈ D.blocks ∧ x ∈ B1 ∧ y ∈ B1 := by
      simpa [S] using! hB1S
    exact ⟨hmemS.1, hmemS.2.1, hmemS.2.2, hB1_ne⟩
  · intro B hB
    have hBS : B ∈ S := by
      simp [S, hB.1, hB.2.1, hB.2.2.1]
    have hB_erase : B ∈ S.erase B0 :=
      (Finset.mem_erase.2 ⟨hB.2.2.2, hBS⟩)
    have : B ∈ ({B1} : Finset Biplane.Block) := by simpa [hErase] using! hB_erase
    simpa using! (Finset.mem_singleton.1 this)

/-- The unique non-`B0` block containing the pair `{x,y} ⊆ B0`. -/
public def otherBlockThroughPair
    (hB0 : B0 ∈ D.blocks) {x y : Biplane.Point} (hx : x ∈ B0) (hy : y ∈ B0) (hxy : x ≠ y) :
    Biplane.Block :=
  Classical.choose (exists_unique_other_block_through_pair (D := D) (B0 := B0) hB0 hx hy hxy).exists

/-- The defining properties of `otherBlockThroughPair`. -/
public lemma otherBlockThroughPair_spec
    (hB0 : B0 ∈ D.blocks) {x y : Biplane.Point} (hx : x ∈ B0) (hy : y ∈ B0) (hxy : x ≠ y) :
    otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy ∈ D.blocks ∧
      x ∈ otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy ∧
      y ∈ otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy ∧
      otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy ≠ B0 := by
  -- unpack the `∃!` witness
  have hExU := (exists_unique_other_block_through_pair (D := D) (B0 := B0) hB0 hx hy hxy)
  have hEx := hExU.exists
  have hspec := Classical.choose_spec hEx
  exact hspec

end

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Aux

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
