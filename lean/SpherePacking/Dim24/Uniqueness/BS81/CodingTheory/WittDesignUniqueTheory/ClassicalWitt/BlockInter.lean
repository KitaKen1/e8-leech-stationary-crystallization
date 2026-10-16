-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.OctadInterNumbers

/-!
# Even intersection sizes in a Witt design

For a Steiner system `S(5,8,24)`, this file proves that any two distinct blocks intersect in an
even number of points. The proof is a design-only double-counting argument, reusing the
intersection-number lemmas from `CodeFromOctads/OctadInterNumbers.lean`.

This parity statement is a key input for the classical route to Witt design uniqueness.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.ClassicalWitt.BlockIntersections

noncomputable section
open scoped BigOperators

open GolayUniquenessSteps.CodeFromOctads
open SteinerSystem

variable {S : SteinerSystem 24 8 5}

/-- The finset of blocks of `S` other than the given block `B`. -/
public def blocksOther (B : Finset (Fin 24)) : Finset (Finset (Fin 24)) :=
  S.blocksFinset.erase B

/-- Any block other than `B` meets `B` in at most `4` points. -/
public lemma inter_card_le_four_of_mem_other
    {B B' : Finset (Fin 24)} (hB : B ∈ S.blocks) (hB' : B' ∈ blocksOther (S := S) B) :
    (B ∩ B').card ≤ 4 := by
  have hB'blocks : B' ∈ S.blocks := by
    have : B' ∈ S.blocksFinset := (Finset.mem_erase.1 hB').2
    simpa [SteinerSystem.mem_blocksFinset] using! this
  have hne : B ≠ B' := (Finset.mem_erase.1 hB').1.symm
  exact inter_card_le_four_of_ne (S := S) (B := B) (B' := B') hB hB'blocks hne

/-- The `choose 4` intersection sum counts blocks meeting `B` in `4` points. -/
public lemma sum_choose4_eq_card_filter
    {B : Finset (Fin 24)} (hB : B ∈ S.blocks) :
    (∑ B' ∈ blocksOther (S := S) B, Nat.choose ((B ∩ B').card) 4)
      =
    ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 4).card := by
  calc
    (∑ B' ∈ blocksOther (S := S) B, Nat.choose ((B ∩ B').card) 4)
        = ∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 4 then (1 : ℕ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro B' hB'
            have hle : (B ∩ B').card ≤ 4 :=
              inter_card_le_four_of_mem_other (S := S) (B := B) hB hB'
            simp [GolayUniquenessSteps.CodeFromOctads.choose4_of_le4 (hn := hle)]
    _ = ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 4).card := by
          exact
            (GolayUniquenessSteps.CodeFromOctads.sum_ite_eq_card_filter
              (s := blocksOther (S := S) B) (p := fun B' => (B ∩ B').card = 4))

/-- There are exactly `280` blocks meeting a fixed block in `4` points. -/
public lemma n4_eq_280
    {B : Finset (Fin 24)} (hB : B ∈ S.blocks) :
    ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 4).card = 280 := by
  have hsum :
      (∑ B' ∈ blocksOther (S := S) B, Nat.choose ((B ∩ B').card) 4) = 280 := by
    simpa [blocksOther] using!
      (sum_choose4_intersections_erase_eq_280 (S := S) (B := B) hB)
  have hEq :
      (∑ B' ∈ blocksOther (S := S) B, Nat.choose ((B ∩ B').card) 4)
        =
      ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 4).card :=
    sum_choose4_eq_card_filter (S := S) (B := B) hB
  simpa [hEq] using! hsum

/-- No block other than `B` meets `B` in exactly `3` points. -/
public lemma n3_eq_0
    {B : Finset (Fin 24)} (hB : B ∈ S.blocks) :
    ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 3).card = 0 := by
  -- Use the `choose 3` sum: it equals `n3 + 4*n4`, with `n4 = 280`.
  let n3 : ℕ := ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 3).card
  let n4 : ℕ := ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 4).card
  have hn4 : n4 = 280 := by
    simpa [n4] using! n4_eq_280 (S := S) (B := B) hB
  have hsum :
      (∑ B' ∈ blocksOther (S := S) B, Nat.choose ((B ∩ B').card) 3) = 1120 := by
    simpa [blocksOther] using!
      (sum_choose3_intersections_erase_eq_1120 (S := S) (B := B) hB)
  have hterm :
      (∑ B' ∈ blocksOther (S := S) B, Nat.choose ((B ∩ B').card) 3) = n3 + 4 * n4 := by
    have hn3ind :
        (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 3 then (1 : ℕ) else 0)) = n3 := by
      simp [n3]
    have hn4ind :
        (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 4 then (4 : ℕ) else 0)) = 4 * n4 := by
      simp [n4, GolayUniquenessSteps.CodeFromOctads.sum_ite_eq_mul_card_filter]
    calc
      (∑ B' ∈ blocksOther (S := S) B, Nat.choose ((B ∩ B').card) 3)
          = ∑ B' ∈ blocksOther (S := S) B,
              ((if (B ∩ B').card = 3 then (1 : ℕ) else 0) +
                (if (B ∩ B').card = 4 then (4 : ℕ) else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro B' hB'
              have hle : (B ∩ B').card ≤ 4 :=
                inter_card_le_four_of_mem_other (S := S) (B := B) hB hB'
              simp [GolayUniquenessSteps.CodeFromOctads.choose3_of_le4 (hn := hle)]
      _ = (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 3 then (1 : ℕ) else 0)) +
            (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 4 then (4 : ℕ) else 0)) := by
              simp [Finset.sum_add_distrib]
      _ = n3 + 4 * n4 := by simp [hn3ind, hn4ind]
  lia

/-- No block other than `B` meets `B` in exactly `1` point. -/
public lemma n1_eq_0
    {B : Finset (Fin 24)} (hB : B ∈ S.blocks) :
    ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 1).card = 0 := by
  -- Use the intersection-size sum: it equals `n1 + 2*n2 + 3*n3 + 4*n4`.
  let n1 : ℕ := ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 1).card
  let n2 : ℕ := ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 2).card
  let n3 : ℕ := ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 3).card
  let n4 : ℕ := ((blocksOther (S := S) B).filter fun B' => (B ∩ B').card = 4).card
  have hn4 : n4 = 280 := by
    simpa [n4] using! n4_eq_280 (S := S) (B := B) hB
  have hn3 : n3 = 0 := by
    dsimp [n3]
    exact n3_eq_0 (S := S) (B := B) hB
  have hn2 : n2 = 448 := by
    -- Use the `choose 2` sum: `n2 + 3*n3 + 6*n4 = 2128`.
    have hsum :
        (∑ B' ∈ blocksOther (S := S) B, Nat.choose ((B ∩ B').card) 2) = 2128 := by
      simpa [blocksOther] using!
        (sum_choose_intersections_erase_eq_2128 (S := S) (B := B) hB)
    have hterm :
        (∑ B' ∈ blocksOther (S := S) B, Nat.choose ((B ∩ B').card) 2) =
          n2 + 3 * n3 + 6 * n4 := by
      have hn2ind :
          (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 2 then (1 : ℕ) else 0)) = n2 :=
        Eq.symm (Finset.card_filter (fun i => (B ∩ i).card = 2) (blocksOther B))
      have hn3ind :
          (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 3 then (3 : ℕ) else 0)) = 3 * n3 :=
        sum_ite_eq_mul_card_filter 3 (blocksOther B) fun x => (B ∩ x).card = 3
      have hn4ind :
          (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 4 then (6 : ℕ) else 0)) = 6 * n4 :=
        sum_ite_eq_mul_card_filter 6 (blocksOther B) fun x => (B ∩ x).card = 4
      calc
        (∑ B' ∈ blocksOther (S := S) B, Nat.choose ((B ∩ B').card) 2)
            = ∑ B' ∈ blocksOther (S := S) B,
                ((if (B ∩ B').card = 2 then (1 : ℕ) else 0) +
                  (if (B ∩ B').card = 3 then (3 : ℕ) else 0) +
                  (if (B ∩ B').card = 4 then (6 : ℕ) else 0)) := by
                refine Finset.sum_congr rfl ?_
                intro B' hB'
                have hle : (B ∩ B').card ≤ 4 :=
                  inter_card_le_four_of_mem_other (S := S) (B := B) hB hB'
                simp [GolayUniquenessSteps.CodeFromOctads.choose2_of_le4 (hn := hle), add_assoc]
        _ =
            (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 2 then (1 : ℕ) else 0)) +
              (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 3 then (3 : ℕ) else 0)) +
                (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 4 then (6 : ℕ) else 0)) := by
                simp [Finset.sum_add_distrib, add_assoc]
        _ = n2 + 3 * n3 + 6 * n4 := by
              simp [hn2ind, hn3ind, hn4ind, add_assoc]
    simp_all
  -- Now use the plain sum of intersection sizes to solve for `n1`.
  have hsum :
      (∑ B' ∈ blocksOther (S := S) B, (B ∩ B').card) = 2016 := by
    simpa [blocksOther] using!
      (sum_intersections_erase_eq_2016 (S := S) (B := B) hB)
  have hterm :
      (∑ B' ∈ blocksOther (S := S) B, (B ∩ B').card) = n1 + 2 * n2 + 3 * n3 + 4 * n4 := by
    -- Expand each intersection card by cases `0..4` (since `≤ 4` for `B' ≠ B`).
    have hrewrite :
        (∑ B' ∈ blocksOther (S := S) B, (B ∩ B').card)
          =
        ∑ B' ∈ blocksOther (S := S) B,
          ((if (B ∩ B').card = 1 then (1 : ℕ) else 0) +
            (if (B ∩ B').card = 2 then (2 : ℕ) else 0) +
            (if (B ∩ B').card = 3 then (3 : ℕ) else 0) +
            (if (B ∩ B').card = 4 then (4 : ℕ) else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro B' hB'
      have hle : (B ∩ B').card ≤ 4 := inter_card_le_four_of_mem_other (S := S) (B := B) hB hB'
      have hcases :
          (B ∩ B').card = 0 ∨ (B ∩ B').card = 1 ∨ (B ∩ B').card = 2 ∨
            (B ∩ B').card = 3 ∨ (B ∩ B').card = 4 := by
        omega
      rcases hcases with h0 | h1 | h2 | h3 | h4
      · simp [h0]
      · simp [h1]
      · simp [h2]
      · simp [h3]
      · simp [h4]
    have hn1ind :
        (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 1 then (1 : ℕ) else 0)) = n1 :=
      Eq.symm (Finset.card_filter (fun i => (B ∩ i).card = 1) (blocksOther B))
    have hn2ind :
        (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 2 then (2 : ℕ) else 0)) = 2 * n2 :=
      sum_ite_eq_mul_card_filter 2 (blocksOther B) fun x => (B ∩ x).card = 2
    have hn3ind :
        (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 3 then (3 : ℕ) else 0)) = 3 * n3 :=
      sum_ite_eq_mul_card_filter 3 (blocksOther B) fun x => (B ∩ x).card = 3
    have hn4ind :
        (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 4 then (4 : ℕ) else 0)) = 4 * n4 :=
      sum_ite_eq_mul_card_filter 4 (blocksOther B) fun x => (B ∩ x).card = 4
    calc
      (∑ B' ∈ blocksOther (S := S) B, (B ∩ B').card)
          =
          (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 1 then (1 : ℕ) else 0)) +
            (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 2 then (2 : ℕ) else 0)) +
            (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 3 then (3 : ℕ) else 0)) +
            (∑ B' ∈ blocksOther (S := S) B, (if (B ∩ B').card = 4 then (4 : ℕ) else 0)) := by
              simp [hrewrite, Finset.sum_add_distrib, add_assoc]
      _ = n1 + 2 * n2 + 3 * n3 + 4 * n4 := by
            simp [hn1ind, hn2ind, hn3ind, hn4ind, add_assoc]
  grind only

/-- Distinct blocks in a Steiner system `S(5,8,24)` intersect in an even number of points. -/
public theorem even_inter_card_of_ne
    {B B' : Finset (Fin 24)} (hB : B ∈ S.blocks) (hB' : B' ∈ S.blocks) (hne : B ≠ B') :
    Even (B ∩ B').card := by
  -- Reduce to a contradiction if the intersection has odd size `1` or `3`.
  have hB'_fin : B' ∈ blocksOther (S := S) B := by
    refine Finset.mem_erase.2 ?_
    refine ⟨hne.symm, ?_⟩
    simpa [SteinerSystem.mem_blocksFinset] using! hB'
  have hcases :
      (B ∩ B').card = 0 ∨ (B ∩ B').card = 1 ∨ (B ∩ B').card = 2 ∨
        (B ∩ B').card = 3 ∨ (B ∩ B').card = 4 := by
    have hle : (B ∩ B').card ≤ 4 :=
      inter_card_le_four_of_ne (S := S) (B := B) (B' := B') hB hB' hne
    omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · simp [h0]
  · -- rule out size `1`
    have hn1 : ((blocksOther (S := S) B).filter fun B'' => (B ∩ B'').card = 1).card = 0 :=
      n1_eq_0 (S := S) (B := B) hB
    have hEmpty : (blocksOther (S := S) B).filter (fun B'' => (B ∩ B'').card = 1) = ∅ := by
      exact Finset.card_eq_zero.mp hn1
    have hmem : B' ∈ (blocksOther (S := S) B).filter fun B'' => (B ∩ B'').card = 1 :=
      Finset.mem_filter.2 ⟨hB'_fin, h1⟩
    have : False := by simp [hEmpty] at hmem
    exact this.elim
  · simp [h2]
  · -- rule out size `3`
    have hn3 : ((blocksOther (S := S) B).filter fun B'' => (B ∩ B'').card = 3).card = 0 :=
      n3_eq_0 (S := S) (B := B) hB
    have hEmpty : (blocksOther (S := S) B).filter (fun B'' => (B ∩ B'').card = 3) = ∅ := by
      exact Finset.card_eq_zero.mp hn3
    have hmem : B' ∈ (blocksOther (S := S) B).filter fun B'' => (B ∩ B'').card = 3 :=
      Finset.mem_filter.2 ⟨hB'_fin, h3⟩
    have : False := by simp [hEmpty] at hmem
    exact this.elim
  · simpa [h4] using! (by decide : Even (4 : ℕ))

end

end GolayUniquenessSteps.WittDesignUniqueTheory.ClassicalWitt.BlockIntersections

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
