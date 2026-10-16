-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
import Mathlib.Algebra.BigOperators.Ring.Finset
public import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.OctadInterPairs
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittParams

/-!
# Intersection numbers in `S(5,8,24)`

This file proves numerical identities in a Steiner system `S(5,8,24)` by double counting subsets
inside intersections with a fixed block. These identities are used to rule out intersection sizes
`1` and `3` in the biplane-based uniqueness argument for the Golay code.

This is the quantitative part of `paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`,
Lemma `octad_intersections`, and does not assume self-orthogonality.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads

noncomputable section

open scoped BigOperators

open SteinerSystem

variable {S : SteinerSystem 24 8 5}

/-- If `n ≤ 4`, then `Nat.choose n 4` is the indicator of `n = 4`. -/
public lemma choose4_of_le4 {n : ℕ} (hn : n ≤ 4) :
    Nat.choose n 4 = (if n = 4 then (1 : ℕ) else 0) := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by grind only
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> decide

/-- If `n ≤ 4`, then `Nat.choose n 3` splits into the `n = 3` and `n = 4` cases. -/
public lemma choose3_of_le4 {n : ℕ} (hn : n ≤ 4) :
    Nat.choose n 3 =
      (if n = 3 then (1 : ℕ) else 0) + (if n = 4 then (4 : ℕ) else 0) := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> decide

/-- If `n ≤ 4`, then `Nat.choose n 2` splits into the `n = 2`, `n = 3`, and `n = 4` cases. -/
public lemma choose2_of_le4 {n : ℕ} (hn : n ≤ 4) :
    Nat.choose n 2 =
      (if n = 2 then (1 : ℕ) else 0) +
        (if n = 3 then (3 : ℕ) else 0) +
          (if n = 4 then (6 : ℕ) else 0) := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Summing indicators over a `Finset` equals the cardinality of the filtered set. -/
@[simp] public lemma sum_ite_eq_card_filter {α : Type} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (∑ x ∈ s, (if p x then (1 : ℕ) else 0)) = (s.filter p).card :=
  (Finset.card_filter (s := s) (p := p)).symm

/-- Summing a constant `a` over `x ∈ s` satisfying `p` gives `a * card (s.filter p)`. -/
public lemma sum_ite_eq_mul_card_filter {α : Type} (a : ℕ) (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (∑ x ∈ s, (if p x then a else 0)) = a * (s.filter p).card := by
  rw [← Finset.sum_filter (s := s) (p := p) (f := fun _ => a)]
  calc
    (∑ _x ∈ s.filter p, a) = (s.filter p).card * a := by simp
    _ = a * (s.filter p).card := by simp [Nat.mul_comm]

private lemma powersetCard_filter_subset_eq_powersetCard_inter
    (B B' : Finset (Fin 24)) (m : ℕ) :
    (B.powersetCard m).filter (fun T => T ⊆ B') = (B ∩ B').powersetCard m := by
  ext T
  grind (splits := 2) only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff]

private lemma sum_choose4_intersections_eq
    (B : Finset (Fin 24)) :
    (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 4) = (B.powersetCard 4).card * 5 := by
  -- Rewrite the `choose` sum as a sum of cardinals of `powersetCard 4`.
  have hchoose :
      (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 4) =
        ∑ B' ∈ S.blocksFinset, ((B ∩ B').powersetCard 4).card := by
    refine Finset.sum_congr rfl ?_
    intro B' _hB'
    simp [Finset.card_powersetCard]
  -- Double count `4`-subsets of `B` contained in blocks.
  have hswap :
      (∑ B' ∈ S.blocksFinset, ((B ∩ B').powersetCard 4).card) =
        ∑ T ∈ B.powersetCard 4, (S.blocksContaining T).card := by
    -- Expand each `card` as a sum of indicators, swap sums, and repackage as `blocksContaining`.
    calc
          (∑ B' ∈ S.blocksFinset, ((B ∩ B').powersetCard 4).card)
          = ∑ B' ∈ S.blocksFinset, ((B.powersetCard 4).filter fun T => T ⊆ B').card := by
              refine Finset.sum_congr rfl ?_
              intro B' _hB'
              simp [powersetCard_filter_subset_eq_powersetCard_inter (B := B) (B' := B') (m := 4)]
    _ = ∑ B' ∈ S.blocksFinset, ∑ T ∈ B.powersetCard 4, (if T ⊆ B' then (1 : ℕ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro B' _hB'
          -- Rewrite `card (filter ...)` as a sum of indicators.
          exact (Finset.card_filter (s := B.powersetCard 4) (p := fun T => T ⊆ B'))
    _ = ∑ T ∈ B.powersetCard 4, ∑ B' ∈ S.blocksFinset, (if T ⊆ B' then (1 : ℕ) else 0) := by
          -- `Finset.sum_comm` swaps the order of summation.
          exact Finset.sum_comm
    _ = ∑ T ∈ B.powersetCard 4, ((S.blocksFinset.filter fun B' => T ⊆ B').card) := by
          refine Finset.sum_congr rfl ?_
          intro T _hT
          exact (Finset.card_filter (s := S.blocksFinset) (p := fun B' => T ⊆ B')).symm
    _ = ∑ T ∈ B.powersetCard 4, (S.blocksContaining T).card := by
          rfl
  -- Each `4`-subset of `B` lies in exactly `5` blocks.
  have hconst : ∀ T ∈ B.powersetCard 4, (S.blocksContaining T).card = 5 := by
    intro T hT
    have hTcard : T.card = 4 := (Finset.mem_powersetCard.1 hT).2
    simpa using! WittParams.card_blocksContaining_four (S := S) T hTcard
  calc
    (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 4)
        = ∑ T ∈ B.powersetCard 4, (S.blocksContaining T).card := by
            simpa [hchoose] using! hswap
    _ = ∑ _T ∈ B.powersetCard 4, 5 :=
          Finset.sum_congr rfl hconst
    _ = (B.powersetCard 4).card * 5 := by simp

/-- For a fixed block `B`, the sum of `choose |B ∩ B'| 4` over `B' ≠ B` equals `280`. -/
public lemma sum_choose4_intersections_erase_eq_280
    (B : Finset (Fin 24))
    (hB : B ∈ S.blocks) :
    (∑ B' ∈ S.blocksFinset.erase B, Nat.choose ((B ∩ B').card) 4) = 280 := by
  have hBcard : B.card = 8 := S.block_card B hB
  -- First compute the sum over all blocks.
  have hall :
      (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 4) = (B.powersetCard 4).card * 5 :=
    sum_choose4_intersections_eq (S := S) (B := B)
  have hPcard : (B.powersetCard 4).card = 70 := by
    have : Nat.choose 8 4 = 70 := by decide
    simpa [Finset.card_powersetCard, hBcard] using! this
  have hall' : (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 4) = 350 := by
    calc
      (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 4)
          = (B.powersetCard 4).card * 5 := hall
      _ = 70 * 5 := by simp [hPcard]
      _ = 350 := by decide
  -- Split off the `B' = B` term.
  have hsplit :
      (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 4) =
        Nat.choose ((B ∩ B).card) 4 +
          (∑ B' ∈ S.blocksFinset.erase B, Nat.choose ((B ∩ B').card) 4) := by
    have hmem : B ∈ S.blocksFinset := (SteinerSystem.mem_blocksFinset _ _).2 hB
    simpa [add_comm, add_left_comm, add_assoc] using!
      (S.blocksFinset.add_sum_erase (a := B)
        (f := fun B' => Nat.choose ((B ∩ B').card) 4) hmem).symm
  have hBB : Nat.choose ((B ∩ B).card) 4 = 70 := by
    -- `choose 8 4 = 70`
    have : Nat.choose 8 4 = 70 := by decide
    simpa [Finset.inter_self, hBcard] using! this
  -- Conclude.
  grind only

/-- For a fixed block `B`, the sum of `choose |B ∩ B'| 3` over `B' ≠ B` equals `1120`. -/
public lemma sum_choose3_intersections_erase_eq_1120
    (B : Finset (Fin 24))
    (hB : B ∈ S.blocks) :
    (∑ B' ∈ S.blocksFinset.erase B, Nat.choose ((B ∩ B').card) 3) = 1120 := by
  have hBcard : B.card = 8 := S.block_card B hB
  -- Analogous to `sum_choose4_intersections_eq`, with `3`-subsets.
  have hall :
      (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 3) = (B.powersetCard 3).card * 21 := by
    -- This proof mirrors `sum_choose4_intersections_eq` with `m=3` and `λ=21`.
    have hchoose :
        (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 3) =
          ∑ B' ∈ S.blocksFinset, ((B ∩ B').powersetCard 3).card := by
      refine Finset.sum_congr rfl ?_
      intro B' _hB'
      simp [Finset.card_powersetCard]
    have hswap :
        (∑ B' ∈ S.blocksFinset, ((B ∩ B').powersetCard 3).card) =
          ∑ T ∈ B.powersetCard 3, (S.blocksContaining T).card := by
      calc
        (∑ B' ∈ S.blocksFinset, ((B ∩ B').powersetCard 3).card)
            = ∑ B' ∈ S.blocksFinset, ((B.powersetCard 3).filter fun T => T ⊆ B').card := by
                refine Finset.sum_congr rfl ?_
                intro B' _hB'
                simp [powersetCard_filter_subset_eq_powersetCard_inter (B := B) (B' := B') (m := 3)]
        _ = ∑ B' ∈ S.blocksFinset, ∑ T ∈ B.powersetCard 3, (if T ⊆ B' then (1 : ℕ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro B' _hB'
              exact (Finset.card_filter (s := B.powersetCard 3) (p := fun T => T ⊆ B'))
        _ = ∑ T ∈ B.powersetCard 3, ∑ B' ∈ S.blocksFinset, (if T ⊆ B' then (1 : ℕ) else 0) := by
              exact Finset.sum_comm
        _ = ∑ T ∈ B.powersetCard 3, ((S.blocksFinset.filter fun B' => T ⊆ B').card) := by
              refine Finset.sum_congr rfl ?_
              intro T _hT
              exact (Finset.card_filter (s := S.blocksFinset) (p := fun B' => T ⊆ B')).symm
        _ = ∑ T ∈ B.powersetCard 3, (S.blocksContaining T).card := by
              rfl
    have hconst : ∀ T ∈ B.powersetCard 3, (S.blocksContaining T).card = 21 := by
      intro T hT
      have hTcard : T.card = 3 := (Finset.mem_powersetCard.1 hT).2
      simpa using! WittParams.card_blocksContaining_three (S := S) T hTcard
    calc
      (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 3)
          = ∑ T ∈ B.powersetCard 3, (S.blocksContaining T).card := by
              simpa [hchoose] using! hswap
      _ = ∑ _T ∈ B.powersetCard 3, 21 := by
            exact Finset.sum_congr rfl hconst
      _ = (B.powersetCard 3).card * 21 := by simp
  have hPcard : (B.powersetCard 3).card = 56 := by
    have : Nat.choose 8 3 = 56 := by decide
    simpa [Finset.card_powersetCard, hBcard] using! this
  have hall' : (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 3) = 1176 := by
    calc
      (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 3)
          = (B.powersetCard 3).card * 21 := hall
      _ = 56 * 21 := by simp [hPcard]
      _ = 1176 := by decide
  have hsplit :
      (∑ B' ∈ S.blocksFinset, Nat.choose ((B ∩ B').card) 3) =
        Nat.choose ((B ∩ B).card) 3 +
          (∑ B' ∈ S.blocksFinset.erase B, Nat.choose ((B ∩ B').card) 3) := by
    have hmem : B ∈ S.blocksFinset := (SteinerSystem.mem_blocksFinset _ _).2 hB
    simpa [add_comm, add_left_comm, add_assoc] using!
      (S.blocksFinset.add_sum_erase (a := B)
        (f := fun B' => Nat.choose ((B ∩ B').card) 3) hmem).symm
  have hBB : Nat.choose ((B ∩ B).card) 3 = 56 := by
    have : Nat.choose 8 3 = 56 := by decide
    simpa [Finset.inter_self, hBcard] using! this
  grind only

/-- In `S(5,8,24)`, every block meets some other block in exactly `2` points. -/
public lemma exists_inter_card_eq_two_of_mem
    (B : Finset (Fin 24)) (hB : B ∈ S.blocks) :
    ∃ B' ∈ S.blocks, B' ≠ B ∧ (B ∩ B').card = 2 := by
  -- Let `n2` be the number of other blocks meeting `B` in exactly `2` points.
  let blocksOther : Finset (Finset (Fin 24)) := S.blocksFinset.erase B
  let n2 : ℕ := (blocksOther.filter fun B' => (B ∩ B').card = 2).card
  let n3 : ℕ := (blocksOther.filter fun B' => (B ∩ B').card = 3).card
  let n4 : ℕ := (blocksOther.filter fun B' => (B ∩ B').card = 4).card
  have hBmem : B ∈ S.blocksFinset := (SteinerSystem.mem_blocksFinset _ _).2 hB
  have hBcard : B.card = 8 := S.block_card B hB
  have hle4 : ∀ {B' : Finset (Fin 24)}, B' ∈ blocksOther → (B ∩ B').card ≤ 4 := by
    intro B' hB'
    have hB'mem : B' ∈ S.blocks := by
      refine (SteinerSystem.mem_blocksFinset _ _).1 ?_
      exact (Finset.mem_erase.1 hB' |>.2)
    have hne : B ≠ B' := (Finset.mem_erase.1 hB' |>.1).symm
    exact inter_card_le_four_of_ne (S := S) (B := B) (B' := B') hB hB'mem hne
  -- First compute `n4` from the `choose 4` sum.
  have hsum4 : (∑ B' ∈ blocksOther, Nat.choose ((B ∩ B').card) 4) = 280 :=
    sum_choose4_intersections_erase_eq_280 (S := S) (B := B) hB
  have hterm4 :
      (∑ B' ∈ blocksOther, Nat.choose ((B ∩ B').card) 4) = n4 := by
    -- For `card ≤ 4`, `choose card 4` is the `card=4` indicator.
    calc
      (∑ B' ∈ blocksOther, Nat.choose ((B ∩ B').card) 4)
          = ∑ B' ∈ blocksOther, (if (B ∩ B').card = 4 then (1 : ℕ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro B' hB'
              simp [choose4_of_le4 (hn := hle4 hB')]
      _ = n4 := by
            exact sum_ite_eq_card_filter blocksOther fun x => (B ∩ x).card = 4
  have hn4 : n4 = 280 := by simpa [hterm4] using! hsum4
  -- Next compute `n3` from the `choose 3` sum.
  have hsum3 : (∑ B' ∈ blocksOther, Nat.choose ((B ∩ B').card) 3) = 1120 :=
    sum_choose3_intersections_erase_eq_1120 (S := S) (B := B) hB
  have hterm3 :
      (∑ B' ∈ blocksOther, Nat.choose ((B ∩ B').card) 3) = n3 + 4 * n4 := by
    have hsum3ind :
        (∑ B' ∈ blocksOther, (if (B ∩ B').card = 3 then (1 : ℕ) else 0)) = n3 := by
      dsimp [n3]
      exact (sum_ite_eq_card_filter (s := blocksOther) (p := fun B' => (B ∩ B').card = 3))
    have hsum4ind :
        (∑ B' ∈ blocksOther, (if (B ∩ B').card = 4 then (4 : ℕ) else 0)) = 4 * n4 := by
      simp [n4, sum_ite_eq_mul_card_filter]
    calc
      (∑ B' ∈ blocksOther, Nat.choose ((B ∩ B').card) 3)
          = ∑ B' ∈ blocksOther,
              ((if (B ∩ B').card = 3 then (1 : ℕ) else 0) +
                (if (B ∩ B').card = 4 then (4 : ℕ) else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro B' hB'
              simp [choose3_of_le4 (hn := hle4 hB')]
      _ = (∑ B' ∈ blocksOther, (if (B ∩ B').card = 3 then (1 : ℕ) else 0)) +
            (∑ B' ∈ blocksOther, (if (B ∩ B').card = 4 then (4 : ℕ) else 0)) := by
              simp [Finset.sum_add_distrib]
      _ = n3 + 4 * n4 := by
            simp [hsum3ind, hsum4ind]
  have hn3 : n3 = 0 := by
    -- `1120 = n3 + 4*n4 = n3 + 1120`
    have : n3 + 4 * n4 = 1120 := by
      simpa [hterm3] using! hsum3
    have : n3 + 1120 = 1120 := by simpa [hn4] using! this
    have : n3 + 1120 = 0 + 1120 := by simpa using! this
    exact Nat.add_right_cancel this
  -- Now compute `n2` from the `choose 2` sum (already available).
  have hsum2 : (∑ B' ∈ blocksOther, Nat.choose ((B ∩ B').card) 2) = 2128 :=
    sum_choose_intersections_erase_eq_2128 (S := S) (B := B) hB
  have hterm2 :
      (∑ B' ∈ blocksOther, Nat.choose ((B ∩ B').card) 2) = n2 + 3 * n3 + 6 * n4 := by
    have hsum2ind :
        (∑ B' ∈ blocksOther, (if (B ∩ B').card = 2 then (1 : ℕ) else 0)) = n2 := by
      dsimp [n2]
      exact (sum_ite_eq_card_filter (s := blocksOther) (p := fun B' => (B ∩ B').card = 2))
    have hsum3ind :
        (∑ B' ∈ blocksOther, (if (B ∩ B').card = 3 then (3 : ℕ) else 0)) = 3 * n3 := by
      simp [n3, sum_ite_eq_mul_card_filter]
    have hsum4ind :
        (∑ B' ∈ blocksOther, (if (B ∩ B').card = 4 then (6 : ℕ) else 0)) = 6 * n4 := by
      simp [n4, sum_ite_eq_mul_card_filter]
    calc
      (∑ B' ∈ blocksOther, Nat.choose ((B ∩ B').card) 2)
          = ∑ B' ∈ blocksOther,
              ((if (B ∩ B').card = 2 then (1 : ℕ) else 0) +
                (if (B ∩ B').card = 3 then (3 : ℕ) else 0) +
                  (if (B ∩ B').card = 4 then (6 : ℕ) else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro B' hB'
              simp [choose2_of_le4 (hn := hle4 hB'), add_assoc]
      _ = (∑ B' ∈ blocksOther, (if (B ∩ B').card = 2 then (1 : ℕ) else 0)) +
            (∑ B' ∈ blocksOther, (if (B ∩ B').card = 3 then (3 : ℕ) else 0)) +
              (∑ B' ∈ blocksOther, (if (B ∩ B').card = 4 then (6 : ℕ) else 0)) := by
              simp [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
      _ = n2 + 3 * n3 + 6 * n4 := by
            simp [hsum2ind, hsum3ind, hsum4ind, add_assoc]
  have hn2 : n2 = 448 := by
    lia
  -- Conclude existence from `n2 = 448`.
  have hn2pos : 0 < (blocksOther.filter fun B' => (B ∩ B').card = 2).card := by
    simp [n2, hn2]
  rcases Finset.card_pos.1 hn2pos with ⟨B', hB'⟩
  have hB'blocksOther : B' ∈ blocksOther := (Finset.mem_filter.1 hB').1
  have hB'blocks : B' ∈ S.blocks := by
    refine (SteinerSystem.mem_blocksFinset _ _).1 ?_
    exact (Finset.mem_erase.1 hB'blocksOther |>.2)
  have hne : B' ≠ B := (Finset.mem_erase.1 hB'blocksOther |>.1)
  have hcard : (B ∩ B').card = 2 := (Finset.mem_filter.1 hB').2
  exact ⟨B', hB'blocks, hne, hcard⟩

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads
