-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.Weight8CountAux

/-!
# Counting weight-8 codewords in a Golay code

This step file derives the exact number `759` of weight-8 codewords from the invariants packaged
as `IsExtendedBinaryGolayCode`.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps

noncomputable section

open scoped BigOperators

/-- In an extended binary Golay code, the set of weight-8 codewords has cardinality `759`. -/
public theorem weight8Words_card_eq_759_of_isExtendedBinaryGolayCode_step
    (C : Code 24) (hC : IsExtendedBinaryGolayCode C) :
    Set.ncard (weight8Words C) = 759 := by
  -- Upper bound from the minimum distance argument.
  have hle : Set.ncard (weight8Words C) ≤ 759 :=
    weight8_codewords_le_759 (C := C) hC
  -- Lower bound: every 5-subset is contained in a weight-8 codeword, and each weight-8 codeword
  -- contains exactly `56` distinct 5-subsets of its support.
  set S : Set (BinWord 24) := weight8Words C
  letI : DecidablePred (fun w : BinWord 24 => w ∈ S) := Classical.decPred _
  have hS_card : Set.ncard S = S.toFinset.card := by
    simpa using! (Set.ncard_eq_toFinset_card S)
  let f : BinWord 24 → Finset (Finset (Fin 24)) := fun w => (support w).powersetCard 5
  have hcover :
      ((Finset.univ : Finset (Fin 24)).powersetCard 5) ⊆ S.toFinset.biUnion f := by
    intro T hT
    rcases Weight8CountAux.exists_weight8Word_of_mem_powersetCard5 (C := C) hC T hT with
      ⟨w, hwC, hw8, hTsub⟩
    have hwS : w ∈ S.toFinset := by
      refine (Set.mem_toFinset).2 ?_
      simpa [S] using! And.intro hwC hw8
    have hTcard : T.card = 5 := (Finset.mem_powersetCard.1 hT).2
    have hTmem : T ∈ f w :=
      Finset.mem_powersetCard.2 ⟨hTsub, hTcard⟩
    exact Finset.mem_biUnion.2 ⟨w, hwS, hTmem⟩
  have hcard_cover :
      ((Finset.univ : Finset (Fin 24)).powersetCard 5).card ≤ (S.toFinset.biUnion f).card :=
    Finset.card_le_card hcover
  have hbiUnion_le :
      (S.toFinset.biUnion f).card ≤ ∑ w ∈ S.toFinset, (f w).card :=
    Finset.card_biUnion_le
  have hchoose : ((Finset.univ : Finset (Fin 24)).powersetCard 5).card = 759 * 56 :=
    card_powersetCard5_univ_fin24_eq_759_mul_56
  have hconst :
      (∑ w ∈ S.toFinset, (f w).card) = S.toFinset.card * 56 := by
    have hwt : ∀ w ∈ S.toFinset, weight w = 8 := by
      intro w hw
      have hwS : w ∈ S := by
        simpa using! (Set.mem_toFinset.1 hw)
      exact hwS.2
    simpa [f] using! (sum_card_powersetCard5_support_eq_mul_56 (S := S.toFinset) hwt)
  grind only

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps
