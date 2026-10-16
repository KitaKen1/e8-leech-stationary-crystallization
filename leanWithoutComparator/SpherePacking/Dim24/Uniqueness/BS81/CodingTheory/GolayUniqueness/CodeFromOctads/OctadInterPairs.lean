-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.OctadInterSums
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittParams

/-!
# Counting pairs inside intersections

We double-count pairs contained in `B ∩ B'` for a fixed block `B` in a Steiner system `S(5,8,24)`.

This is one of the counting identities used in
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`, Lemma `octad_intersections`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads

noncomputable section

open scoped BigOperators

open SteinerSystem

private lemma card_filter_erase_eq_76
    (S : SteinerSystem 24 8 5) {B : Finset (Fin 24)} (hB : B ∈ S.blocks)
    {T : Finset (Fin 24)} (hT : T.card = 2) (hTB : T ⊆ B) :
    ((S.blocksFinset.erase B).filter (fun B' => T ⊆ B')).card = 76 := by
  have hB_mem : B ∈ S.blocksContaining T :=
    (mem_blocksContaining S).2 ⟨hB, hTB⟩
  have hEq :
      (S.blocksFinset.erase B).filter (fun B' => T ⊆ B') = (S.blocksContaining T).erase B := by
    ext B'
    simp [SteinerSystem.blocksContaining, and_left_comm, and_comm]
  have hcard77 : (S.blocksContaining T).card = 77 := by
    simpa using! WittParams.card_blocksContaining_two (S := S) T hT
  simp_all

/--
For a fixed block `B`, the sum of `choose |B ∩ B'| 2` over all other blocks `B' ≠ B` equals `2128`.
-/
public lemma sum_choose_intersections_erase_eq_2128
    (S : SteinerSystem 24 8 5)
    {B : Finset (Fin 24)} (hB : B ∈ S.blocks) :
    (∑ B' ∈ S.blocksFinset.erase B, Nat.choose (B ∩ B').card 2) = 2128 := by
  have hBcard : B.card = 8 := S.block_card B hB
  -- `choose ((B ∩ B').card) 2` counts the 2-subsets of `B ∩ B'`.
  have hchoose (B' : Finset (Fin 24)) :
      Nat.choose (B ∩ B').card 2 = ((B ∩ B').powersetCard 2).card := by
    simp [Finset.card_powersetCard]
  have hpow (B' : Finset (Fin 24)) :
      ((B ∩ B').powersetCard 2).card = ∑ T ∈ B.powersetCard 2, (if T ⊆ B' then 1 else 0) := by
    -- A 2-subset of `B ∩ B'` is the same as a 2-subset of `B` contained in `B'`.
    -- Turn the card into a filtered sum over `B.powersetCard 2`.
    have hFinset :
        (B ∩ B').powersetCard 2 =
          (B.powersetCard 2).filter (fun T => T ⊆ B') := by
      ext T
      simp [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff, and_assoc,
        and_comm]
    calc
      ((B ∩ B').powersetCard 2).card
          = ((B.powersetCard 2).filter (fun T => T ⊆ B')).card := by simp [hFinset]
      _ = ∑ T ∈ B.powersetCard 2, (if T ⊆ B' then (1 : ℕ) else 0) := by
            simpa using!
              (Finset.card_filter (s := B.powersetCard 2) (p := fun T => T ⊆ B'))
  -- swap the two sums
  calc
    (∑ B' ∈ S.blocksFinset.erase B, Nat.choose (B ∩ B').card 2)
        = ∑ B' ∈ S.blocksFinset.erase B, ((B ∩ B').powersetCard 2).card := by
            refine Finset.sum_congr rfl ?_
            intro B' _hB'
            exact hchoose B'
    _ = ∑ B' ∈ S.blocksFinset.erase B, ∑ T ∈ B.powersetCard 2, (if T ⊆ B' then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro B' _hB'
          exact hpow B'
    _ = ∑ T ∈ B.powersetCard 2, ∑ B' ∈ S.blocksFinset.erase B, (if T ⊆ B' then 1 else 0) := by
          exact Finset.sum_comm
    _ = ∑ T ∈ B.powersetCard 2, ((S.blocksFinset.erase B).filter (fun B' => T ⊆ B')).card := by
          refine Finset.sum_congr rfl ?_
          intro T _hT
          exact (Finset.card_filter (s := S.blocksFinset.erase B) (p := fun B' => T ⊆ B')).symm
    _ = ∑ _T ∈ B.powersetCard 2, 76 := by
          refine Finset.sum_congr rfl ?_
          intro T hT
          have hTcard : T.card = 2 := (Finset.mem_powersetCard.1 hT).2
          have hTB : T ⊆ B := (Finset.mem_powersetCard.1 hT).1
          simp [card_filter_erase_eq_76 (S := S) (B := B) hB hTcard hTB]
    _ = (B.powersetCard 2).card * 76 := by simp
    _ = 2128 := by
          -- `card (powersetCard 2 B) = choose 8 2 = 28`
          have hch : Nat.choose 8 2 = 28 := by decide
          have hcard28 : (B.powersetCard 2).card = 28 := by
            simp [Finset.card_powersetCard, hBcard, hch]
          -- arithmetic
          simp [hcard28]

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads
