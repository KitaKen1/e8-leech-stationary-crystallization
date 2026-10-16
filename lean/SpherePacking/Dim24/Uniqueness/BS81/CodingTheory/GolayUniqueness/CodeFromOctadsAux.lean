-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs

/-!
# Auxiliary lemmas for the octads-to-code step

This file collects infrastructure used in the Golay-uniqueness step "code from octads":
indicator words for finsets (supports), basic finset card identities, and compatibility of
`octadsFromCode` with coordinate permutations.

## Main definitions
* `wordOfFinset`

## Main statements
* `word_eq_wordOfFinset_support`
* `octadsFromCode_permuteCode`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctadsAux

noncomputable section

open scoped symmDiff
open GolayBounds

/-!
## Indicator words and supports
-/

/-- The binary word with support exactly `B`. -/
@[expose] public def wordOfFinset {n : ℕ} (B : Finset (Fin n)) : BinWord n :=
  fun i => if i ∈ B then (1 : ZMod 2) else 0

/-- Evaluation lemma for `wordOfFinset`. -/
@[simp] public lemma wordOfFinset_apply {n : ℕ} (B : Finset (Fin n)) (i : Fin n) :
    wordOfFinset (n := n) B i = (if i ∈ B then (1 : ZMod 2) else 0) := rfl

/-- The support of `wordOfFinset B` is exactly `B`. -/
@[simp] public lemma support_wordOfFinset {n : ℕ} (B : Finset (Fin n)) :
    support (wordOfFinset (n := n) B) = B := by
  ext i
  simp [support, wordOfFinset]

attribute [grind =] support_wordOfFinset

/-- Every word equals the indicator word of its support. -/
public lemma word_eq_wordOfFinset_support {n : ℕ} (w : BinWord n) :
    w = wordOfFinset (n := n) (support w) := by
  funext i
  simpa [wordOfFinset] using! (word_apply_eq_ite_mem_support (w := w) (i := i))

/-!
## Finset card identities
-/

/-- Cardinality identity relating symmetric difference and intersection. -/
public lemma card_symmDiff_add_two_mul_card_inter {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have hdis : Disjoint (A \ B) (B \ A) :=
    disjoint_sdiff_sdiff
  have hsymm :
      (A ∆ B).card = (A \ B).card + (B \ A).card := by
    simpa [symmDiff, Finset.sup_eq_union] using! (Finset.card_union_of_disjoint hdis)
  have hA : (A \ B).card + (A ∩ B).card = A.card :=
    Finset.card_sdiff_add_card_inter A B
  have hB : (B \ A).card + (A ∩ B).card = B.card := by
    simpa [Finset.inter_comm] using! (Finset.card_sdiff_add_card_inter B A)
  lia

/-!
## Permutations
-/

/-!
## Octads under permutation
-/

/-- Mapping by `σ` and then by `σ.symm` returns the original finset. -/
public lemma map_map_equiv_symm {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (B : Finset (Fin n)) :
    (B.map σ.toEmbedding).map σ.symm.toEmbedding = B := by
  ext i
  simp

attribute [grind =] map_map_equiv_symm

/-- Mapping by `σ.symm` and then by `σ` returns the original finset. -/
public lemma map_map_equiv_symm' {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (B : Finset (Fin n)) :
    (B.map σ.symm.toEmbedding).map σ.toEmbedding = B := by
  simpa using! map_map_equiv_symm (σ := σ.symm) (B := B)

attribute [grind =] map_map_equiv_symm'

/-- Description of `octadsFromCode` for a permuted code. -/
public lemma octadsFromCode_permuteCode (σ : Equiv (Fin 24) (Fin 24)) (C : Code 24) :
    octadsFromCode (permuteCode (n := 24) σ C) =
      {B | (Finset.map σ.toEmbedding B) ∈ octadsFromCode C} := by
  ext B
  constructor
  · rintro ⟨w, hw, hw8, rfl⟩
    rcases hw with ⟨w0, hw0, rfl⟩
    refine ⟨w0, hw0, ?_, ?_⟩
    · grind only [= weight_permuteWord]
    · grind only [= support_permuteWord, !map_map_equiv_symm']
  · rintro ⟨w, hwC, hw8, hB⟩
    refine ⟨permuteWord (n := 24) σ w, ⟨w, hwC, rfl⟩, ?_, ?_⟩
    · grind only [= weight_permuteWord]
    · grind only [= support_permuteWord, !map_map_equiv_symm]

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctadsAux
