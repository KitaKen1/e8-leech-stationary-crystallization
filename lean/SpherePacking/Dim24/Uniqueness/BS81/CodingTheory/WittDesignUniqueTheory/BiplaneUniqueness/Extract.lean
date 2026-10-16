-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.BiplaneParams

/-!
# Extracting a `2-(6,3,2)` design from a biplane

Fix a biplane structure `D` and a distinguished block `B₀ ∈ D.blocks`. Let `U₀ = univ \ B₀`.
For any other block `B`, the finset `outside B = B \ B₀` is a triple of points in `U₀`. This file
packages these triples into `tripleSystem` and records the basic cardinality lemmas needed in the
later relabelling step of the biplane uniqueness argument.

This corresponds to Step 2 in the proof of Theorem `thm:biplane_unique` in the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Aux

noncomputable section

variable (D : Biplane.Structure) {B0 : Biplane.Block}

/-- The complement of the distinguished block `B0`. -/
public def U0 : Finset Biplane.Point :=
  (Finset.univ : Finset Biplane.Point) \ B0

/-- Membership in `U0` is equivalent to non-membership in `B0`. -/
public lemma mem_U0_iff {x : Biplane.Point} : x ∈ U0 (B0 := B0) ↔ x ∉ B0 := by simp [U0]

attribute [grind =] mem_U0_iff

/-- The ambient point type has 11 elements. -/
lemma card_univ_point : (Finset.univ : Finset Biplane.Point).card = 11 := by
  -- `simp` can be brittle here under changes to what is re-exported; use a direct computation.
  simpa [Biplane.Point] using! (by decide : (Finset.univ : Finset (Fin 11)).card = 11)

/-- The complement `U0 = univ \\ B0` has 6 points. -/
public lemma U0_card (hB0 : B0 ∈ D.blocks) : (U0 (B0 := B0)).card = 6 := by
  have hB0card : B0.card = 5 := D.block_card B0 hB0
  simpa [U0, card_univ_point, hB0card] using!
    (Finset.card_sdiff_of_subset (s := B0) (t := (Finset.univ : Finset Biplane.Point))
      (Finset.subset_univ B0))

/-- The outside part of a block relative to `B0`: `B \\ B0`. -/
@[expose] public def outside (B : Biplane.Block) : Finset Biplane.Point :=
  B \ B0

/-- Membership in `outside B` means membership in `B` and not in `B0`. -/
public lemma mem_outside_iff {B : Biplane.Block} {x : Biplane.Point} :
    x ∈ outside (B0 := B0) B ↔ x ∈ B ∧ x ∉ B0 := by simp [outside, Finset.mem_sdiff]

attribute [grind =] mem_outside_iff

/-- If `B` is a block distinct from `B0`, then `outside B` has cardinality `3`. -/
public lemma outside_card_eq_three {B : Biplane.Block}
    (hB0 : B0 ∈ D.blocks) (hB : B ∈ D.blocks) (hne : B ≠ B0) :
    (outside (B0 := B0) B).card = 3 := by
  have hBcard : B.card = 5 := D.block_card B hB
  have hinter : (B ∩ B0).card = 2 := by
    -- use symmetry of `inter_card` to match the argument order
    simpa [Finset.inter_comm] using! D.inter_card (B := B0) (B' := B) hB0 hB (Ne.symm hne)
  have hsum := Finset.card_sdiff_add_card_inter B B0
  -- `card (B \\ B0) + card (B ∩ B0) = card B`.
  have hsdiff : (B \ B0).card = B.card - (B ∩ B0).card :=
    Nat.eq_sub_of_add_eq hsum
  -- evaluate numerically
  simpa [outside, hBcard, hinter] using! hsdiff

/-- The outside part of any block is contained in the complement `U0 = univ \\ B0`. -/
public lemma outside_subset_U0 {B : Biplane.Block} :
    outside (B0 := B0) B ⊆ U0 (B0 := B0) := by
  intro x hx; exact (mem_U0_iff (B0 := B0) (x := x)).2 (Finset.mem_sdiff.1 hx).2

/-- The extracted triple system on `U` coming from the ten blocks other than `B0`. -/
public def tripleSystem : Finset (Finset Biplane.Point) :=
  (D.blocks.erase B0).image (fun B => outside (B0 := B0) B)

end

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Aux
end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
