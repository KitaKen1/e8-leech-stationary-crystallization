-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerDerived

/-!
# Deriving `S(3,6,22)` from `S(5,8,24)`

This is the standard "derived design" construction: given a Steiner system `S(5,8,24)` and fixed
points `0,1`, consider the blocks containing both points and delete these two points, obtaining a
family of `6`-subsets of `Fin 22`. This family forms a Steiner system `S(3,6,22)`.

## Main definitions
* `DerivedS3622.derivedBlocks`
* `DerivedS3622.derivedSteinerSystem`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

namespace DerivedS3622

/-- The blocks of the derived `S(3,6,22)` design, obtained from blocks of `S` containing `0,1`. -/
@[expose] public def derivedBlocks (S : SteinerSystem 24 8 5) : Set (Finset (Fin 22)) :=
  {B22 | ∃ B24 : Finset (Fin 24),
      B24 ∈ S.blocks ∧ (0 : Fin 24) ∈ B24 ∧ (1 : Fin 24) ∈ B24 ∧ B22 = drop2 B24}

/-- The derived Steiner system `S(3,6,22)` obtained from a Steiner system `S(5,8,24)` by fixing
the points `0,1`. -/
@[expose] public def derivedSteinerSystem (S : SteinerSystem 24 8 5) :
    SteinerSystem 22 6 3 := by
  refine
    { blocks := derivedBlocks S
      block_card := ?_
      cover_unique := ?_ }
  · intro B22 hB22
    rcases hB22 with ⟨B24, hB24, h0, h1, rfl⟩
    have hcard : B24.card = 8 := S.block_card B24 hB24
    simp [card_drop2_of_card_eq_eight (B := B24) hcard h0 h1]
  · intro T hTcard
    let T24 : Finset (Fin 24) := insert (0 : Fin 24) (insert (1 : Fin 24) (T.map (Fin.addNatEmb 2)))
    have hT24card : T24.card = 5 := by
      have hmap : (T.map (Fin.addNatEmb 2)).card = 3 := by simp [hTcard]
      have h0 : (0 : Fin 24) ∉ T.map (Fin.addNatEmb 2) := by
        intro hmem
        rcases Finset.mem_map.1 hmem with ⟨i, _, hi0⟩
        exact emb22_ne_zero i hi0
      have h1 : (1 : Fin 24) ∉ T.map (Fin.addNatEmb 2) := by
        intro hmem
        rcases Finset.mem_map.1 hmem with ⟨i, _, hi1⟩
        exact emb22_ne_one i hi1
      grind only [= Finset.card_insert_of_notMem, = Finset.mem_insert]
    -- unique block of the 24-design containing `T24`
    rcases S.cover_unique T24 hT24card with ⟨B24, hB24, huniq⟩
    have hT24sub : T24 ⊆ B24 := hB24.2
    refine ⟨drop2 B24, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨B24, hB24.1, ?_, ?_, rfl⟩
        · have : (0 : Fin 24) ∈ T24 := by simp [T24]
          exact hT24sub this
        · have : (1 : Fin 24) ∈ T24 := by simp [T24]
          exact hT24sub this
      · intro i hi
        have him : (Fin.addNatEmb 2 i : Fin 24) ∈ T.map (Fin.addNatEmb 2) := by
          refine Finset.mem_map.2 ?_
          exact ⟨i, hi, rfl⟩
        have : (Fin.addNatEmb 2 i : Fin 24) ∈ T24 := by
          apply Finset.mem_insert.2
          right
          exact Finset.mem_insert_of_mem him
        have : (Fin.addNatEmb 2 i : Fin 24) ∈ B24 := hT24sub this
        exact (mem_drop2 B24 i).2 this
    · intro B22' hB22'
      rcases hB22' with ⟨hB22'blocks, hTsubB22'⟩
      rcases hB22'blocks with ⟨B24', hB24', h0', h1', rfl⟩
      have hT24sub' : T24 ⊆ B24' := by
        intro j hj
        rcases Finset.mem_insert.1 hj with hj0 | hjRest
        · subst hj0; exact h0'
        rcases Finset.mem_insert.1 hjRest with hj1 | hjMap
        · subst hj1; exact h1'
        -- `j` comes from the map, hence from some `i ∈ T`
        rcases Finset.mem_map.1 hjMap with ⟨i, hiT, rfl⟩
        have : (Fin.addNatEmb 2 i : Fin 24) ∈ B24' :=
          (mem_drop2 B24' i).1 (hTsubB22' hiT)
        simpa using! this
      -- uniqueness in `S` forces `B24' = B24`
      have hB24eq : B24' = B24 := by
        exact huniq _ ⟨hB24', hT24sub'⟩
      subst hB24eq
      rfl

end DerivedS3622

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
