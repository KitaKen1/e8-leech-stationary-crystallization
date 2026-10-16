-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.OctadIntersections
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerParams
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittParams

/-!
# Counting intersection sizes

We double-count the sum of intersection cardinalities `|(B ∩ B')|` against a fixed block `B` in a
Steiner system `S(5,8,24)`.

These lemmas are part of the biplane reduction path in
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads

noncomputable section

open scoped BigOperators

open SteinerSystem

private lemma card_filter_erase_eq_252
    (S : SteinerSystem 24 8 5) {B : Finset (Fin 24)} (hB : B ∈ S.blocks)
    {x : Fin 24} (hx : x ∈ B) :
    ((S.blocksFinset.erase B).filter (fun B' => x ∈ B')).card = 252 := by
  have hB_mem :
      B ∈ S.blocksContaining ({x} : Finset (Fin 24)) :=
    (mem_blocksContaining S).2 ⟨hB, by simpa [Finset.singleton_subset_iff]⟩
  -- rewrite `blocksContaining {x}` as a filter by membership
  have hEq :
      (S.blocksFinset.erase B).filter (fun B' => x ∈ B') =
        (S.blocksContaining ({x} : Finset (Fin 24))).erase B := by
    ext B'
    simp [SteinerSystem.blocksContaining, Finset.singleton_subset_iff, and_left_comm, and_comm]
  have hcard253 :
      (S.blocksContaining ({x} : Finset (Fin 24))).card = 253 := by
    -- use `WittParams`
    simpa using! WittParams.card_blocksContaining_one (S := S) ({x} : Finset (Fin 24)) (by simp)
  simp_all

/-- For a fixed block `B`, the sum of `|(B ∩ B')|` over all other blocks `B' ≠ B` equals `2016`. -/
public lemma sum_intersections_erase_eq_2016
    (S : SteinerSystem 24 8 5)
    {B : Finset (Fin 24)} (hB : B ∈ S.blocks) :
    (∑ B' ∈ S.blocksFinset.erase B, (B ∩ B').card) = 2016 := by
  have hBcard : B.card = 8 := S.block_card B hB
  -- rewrite each intersection cardinality as a sum over points of `B`
  have hinter (B' : Finset (Fin 24)) :
      (B ∩ B').card = ∑ x ∈ B, (if x ∈ B' then 1 else 0) := by
    simp
  have hsum_filter (x : Fin 24) :
      (∑ B' ∈ S.blocksFinset.erase B, (if x ∈ B' then (1 : ℕ) else 0)) =
        ((S.blocksFinset.erase B).filter (fun B' => x ∈ B')).card :=
    (Finset.card_filter (s := S.blocksFinset.erase B) (p := fun B' => x ∈ B')).symm
  -- swap sums
  calc
    (∑ B' ∈ S.blocksFinset.erase B, (B ∩ B').card)
        = ∑ B' ∈ S.blocksFinset.erase B, ∑ x ∈ B, (if x ∈ B' then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro B' _hB'
            exact hinter B'
    _ = ∑ x ∈ B, ∑ B' ∈ S.blocksFinset.erase B, (if x ∈ B' then 1 else 0) := by
          -- `Finset.sum_comm` swaps the order of summation.
          exact Finset.sum_comm
    _ = ∑ x ∈ B, ((S.blocksFinset.erase B).filter (fun B' => x ∈ B')).card := by
          exact Finset.sum_congr rfl fun x a => hsum_filter x
    _ = ∑ _x ∈ B, 252 := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [card_filter_erase_eq_252 (S := S) (B := B) hB hx]
    _ = B.card * 252 := by simp
    _ = 2016 := by simp [hBcard]

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads
