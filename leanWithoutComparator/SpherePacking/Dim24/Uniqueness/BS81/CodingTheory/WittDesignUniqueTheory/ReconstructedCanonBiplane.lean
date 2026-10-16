-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.BiplaneBasic

/-!
# A canonical biplane on `Fin 11`

This file defines an explicit `2-(11,5,2)` biplane structure on `Fin 11`, used as a fixed target
for reconstruction and uniqueness arguments. The distinguished block is
`{0,1,2,3,4}`, and the remaining ten blocks each contain exactly two points from this block and
three points from `{5,6,7,8,9,10}`.

The particular choice of explicit model is not important: any fixed biplane would serve as a
canonical target once uniqueness up to isomorphism is established.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

noncomputable section

namespace GolayUniquenessSteps.WittDesignUniqueTheory.ReconstructedCanonicalBiplane

open Biplane

/-- The distinguished block `{0,1,2,3,4}`. -/
@[expose] public def B0 : Block := ({(0 : Point), 1, 2, 3, 4} : Block)
/-- The block containing `0,1` and the triple `{5,6,7}`. -/
@[expose] public def B01 : Block := ({(0 : Point), 1, 5, 6, 7} : Block)
/-- The block containing `0,2` and the triple `{7,9,10}`. -/
@[expose] public def B02 : Block := ({(0 : Point), 2, 7, 9, 10} : Block)
/-- The block containing `0,3` and the triple `{5,8,10}`. -/
@[expose] public def B03 : Block := ({(0 : Point), 3, 5, 8, 10} : Block)
/-- The block containing `0,4` and the triple `{6,8,9}`. -/
@[expose] public def B04 : Block := ({(0 : Point), 4, 6, 8, 9} : Block)
/-- The block containing `1,2` and the triple `{6,8,10}`. -/
@[expose] public def B12 : Block := ({(1 : Point), 2, 6, 8, 10} : Block)
/-- The block containing `1,3` and the triple `{7,8,9}`. -/
@[expose] public def B13 : Block := ({(1 : Point), 3, 7, 8, 9} : Block)
/-- The block containing `1,4` and the triple `{5,9,10}`. -/
@[expose] public def B14 : Block := ({(1 : Point), 4, 5, 9, 10} : Block)
/-- The block containing `2,3` and the triple `{5,6,9}`. -/
@[expose] public def B23 : Block := ({(2 : Point), 3, 5, 6, 9} : Block)
/-- The block containing `2,4` and the triple `{5,7,8}`. -/
@[expose] public def B24 : Block := ({(2 : Point), 4, 5, 7, 8} : Block)
/-- The block containing `3,4` and the triple `{6,7,10}`. -/
@[expose] public def B34 : Block := ({(3 : Point), 4, 6, 7, 10} : Block)

/-- The list of all blocks of the canonical biplane. -/
@[expose] public def canonBlocks : Finset Block :=
  {B0, B01, B02, B03, B04, B12, B13, B14, B23, B24, B34}

/-- The canonical biplane has `11` blocks. -/
public lemma canonBlocks_card : canonBlocks.card = 11 := by decide

/-- Every canonical block has cardinality `5`. -/
public lemma block_card (B : Block) (hB : B ∈ canonBlocks) : B.card = 5 := by
  rcases (by simpa [canonBlocks] using! hB) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl
    <;> decide

/-- Any two distinct canonical blocks intersect in exactly `2` points. -/
public lemma inter_card
    {B B' : Block} (hB : B ∈ canonBlocks) (hB' : B' ∈ canonBlocks) (hne : B ≠ B') :
    (B ∩ B').card = 2 := by
  rcases (by simpa [canonBlocks] using! hB) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl <;>
    rcases (by simpa [canonBlocks] using! hB') with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    <;> first | cases hne rfl | decide

/-- The canonical biplane structure on `Fin 11` with block set `canonBlocks`. -/
@[expose] public def canonicalStructure : Biplane.Structure where
  blocks := canonBlocks
  blocks_card := canonBlocks_card
  block_card := block_card
  inter_card := by
    intro B B' hB hB' hne
    exact inter_card (hB := hB) (hB' := hB') hne

/-- The block finset `canonBlocks` is definitionally `canonicalStructure.blocks`. -/
public lemma canonBlocks_eq_blocks : canonBlocks = canonicalStructure.blocks := rfl

end GolayUniquenessSteps.WittDesignUniqueTheory.ReconstructedCanonicalBiplane

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
