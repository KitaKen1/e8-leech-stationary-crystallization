-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.OctadInterNumbers
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.WordFinset
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpInput

/-!
# Dodecads exist

From the Steiner-system intersection numbers, there are two octads meeting in exactly `2` points,
and their sum is a weight-`12` word.

This corresponds to Corollary `dodecad_exists` in
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory

noncomputable section

open scoped symmDiff

open GolayUniquenessSteps.CodeFromOctads

/-- In a sharp code, there exist two distinct octads meeting in exactly `2` points. -/
public theorem exists_octad_pair_inter_card_eq_two_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C) :
    ∃ B B' : Finset (Fin 24),
      B ∈ octadsFromCode C ∧
      B' ∈ octadsFromCode C ∧
      B ≠ B' ∧
      (B ∩ B').card = 2 := by
  rcases steiner_S_5_8_24_of_sharp (C := C) hC with ⟨S, hS⟩
  -- pick some octad using the Steiner cover property, e.g. the one covering `{0,1,2,3,4}`
  let T : Finset (Fin 24) := ({0, 1, 2, 3, 4} : Finset (Fin 24))
  have hTcard : T.card = 5 := by decide
  rcases S.cover_unique T hTcard with ⟨B, hB, _huniq⟩
  have hBmem : B ∈ S.blocks := hB.1
  rcases exists_inter_card_eq_two_of_mem (S := S) (B := B) hBmem with ⟨B', hB', hne, hcard⟩
  refine ⟨B, B', ?_, ?_, Ne.symm hne, hcard⟩
  · simpa [hS] using! hBmem
  · simpa [hS] using! hB'

/-- In a sharp code, there exists a codeword of weight `12`. -/
public theorem exists_weight12_word_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C) :
    ∃ u : BinWord 24, u ∈ C ∧ weight u = 12 := by
  rcases exists_octad_pair_inter_card_eq_two_of_sharp (C := C) hC with
    ⟨B, B', hB, hB', hne, hcard⟩
  rcases hB with ⟨w, hwC, hw8, rfl⟩
  rcases hB' with ⟨w', hw'C, hw'8, rfl⟩
  let u : BinWord 24 := w + w'
  have huC : u ∈ C := hC.linear.2 w w' hwC hw'C
  have hcardw : (support w).card = 8 := by
    simpa [GolayBounds.weight_eq_card_support] using! hw8
  have hcardw' : (support w').card = 8 := by
    simpa [GolayBounds.weight_eq_card_support] using! hw'8
  have hinter : (support w ∩ support w').card = 2 := by
    simpa [Finset.inter_assoc, Finset.inter_left_comm, Finset.inter_comm] using! hcard
  have hsymm : (support w ∆ support w').card = 12 := by
    calc
      (support w ∆ support w').card
          = (support w).card + (support w').card - 2 * (support w ∩ support w').card := by
            simpa using!
              card_symmDiff_eq_card_add_card_sub_two_mul_card_inter (support w) (support w')
      _ = 12 := by simp [hcardw, hcardw', hinter]
  have hwt : weight u = 12 := by
    calc
      weight u = (support u).card := by
        simp [GolayBounds.weight_eq_card_support]
      _ = (support w ∆ support w').card := by
        simp [u, GolayBounds.support_add_eq_symmDiff]
      _ = 12 := hsymm
  exact ⟨u, huC, hwt⟩

end

end GolayUniquenessSteps.WittDesignUniqueTheory
end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
