-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerDefs

/-!
# Pairwise intersection bound in `S(5,8,24)`

This file records the basic fact that two distinct blocks in a Steiner system `S(5,8,24)` meet in
at most four points. It is a purely Steiner-system consequence (no coding theory yet).
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads

noncomputable section

open SteinerSystem

/-- Two distinct blocks in `S(5,8,24)` intersect in at most four points. -/
public lemma inter_card_le_four_of_ne
    (S : SteinerSystem 24 8 5)
    {B B' : Finset (Fin 24)}
    (hB : B ∈ S.blocks) (hB' : B' ∈ S.blocks) (hne : B ≠ B') :
    (B ∩ B').card ≤ 4 := by
  -- Otherwise a 5-subset of the intersection would lie in two distinct blocks.
  by_contra hle
  have h5 : 5 ≤ (B ∩ B').card := Nat.lt_of_not_ge hle
  rcases Finset.exists_subset_card_eq (s := B ∩ B') h5 with ⟨T, hTsub, hTcard⟩
  -- Uniqueness of the block containing `T`.
  rcases S.cover_unique T (by simpa using! hTcard) with ⟨B0, hB0, huniq⟩
  have hBeq : B = B0 := huniq B ⟨hB, fun x hx => (Finset.mem_inter.1 (hTsub hx)).1⟩
  have hB'eq : B' = B0 := huniq B' ⟨hB', fun x hx => (Finset.mem_inter.1 (hTsub hx)).2⟩
  exact hne (hBeq.trans hB'eq.symm)

private lemma inter_card_eq_eight_iff_eq
    (S : SteinerSystem 24 8 5)
    {B B' : Finset (Fin 24)}
    (hB : B ∈ S.blocks) (hB' : B' ∈ S.blocks) :
    (B ∩ B').card = 8 ↔ B = B' := by
  constructor
  · intro hcard
    have hBcard : B.card = 8 := S.block_card B hB
    have hB'card : B'.card = 8 := S.block_card B' hB'
    have hBB' : B ∩ B' = B := by
      refine Finset.eq_of_subset_of_card_le (Finset.inter_subset_left) ?_
      simpa [hBcard] using! le_of_eq hcard.symm
    have hB'B : B ∩ B' = B' := by
      have hcard' : (B' ∩ B).card = 8 := by simpa [Finset.inter_comm] using! hcard
      have hB'B' : B' ∩ B = B' := by
        refine Finset.eq_of_subset_of_card_le (Finset.inter_subset_left) ?_
        simpa [hB'card] using! le_of_eq hcard'.symm
      simpa [Finset.inter_comm] using! hB'B'
    exact hBB'.symm.trans hB'B
  · intro hEq
    subst hEq
    have hBcard : B.card = 8 := S.block_card B hB
    simp [hBcard]

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads
