-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctadsAux

/-!
# Words and supports as a finset equivalence

We bundle the fact that binary words `Fin n → ZMod 2` are in bijection with their supports.
This is a key bridge for translating coding-theory statements into finset combinatorics.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads

noncomputable section

open scoped symmDiff

open GolayBounds
open CodeFromOctadsAux

/-- The equivalence between a binary word and the finset of indices where it is `1`. -/
@[expose] public def wordSupportEquiv (n : ℕ) : BinWord n ≃ Finset (Fin n) where
  toFun := support (n := n)
  invFun := wordOfFinset (n := n)
  left_inv := by
    intro w
    exact (word_eq_wordOfFinset_support (w := w)).symm
  right_inv := by
    intro B
    exact support_wordOfFinset (n := n) B

/-- Unfolding lemma for `wordSupportEquiv`. -/
@[simp] public lemma wordSupportEquiv_apply (n : ℕ) (w : BinWord n) :
    wordSupportEquiv n w = support w := rfl

/-- Unfolding lemma for the inverse of `wordSupportEquiv`. -/
@[simp] public lemma wordSupportEquiv_symm_apply (n : ℕ) (B : Finset (Fin n)) :
    (wordSupportEquiv n).symm B = wordOfFinset (n := n) B := rfl

/-- Addition of indicator words corresponds to symmetric difference of supports. -/
public lemma wordOfFinset_add {n : ℕ} (A B : Finset (Fin n)) :
    (fun i => wordOfFinset (n := n) A i + wordOfFinset (n := n) B i) =
      wordOfFinset (n := n) (A ∆ B) := by
  funext i
  grind (splits := 2) only [wordOfFinset, Finset.mem_symmDiff]

/-- Cardinality of `s ∆ t` in terms of `|s|`, `|t|`, and `|s ∩ t|`. -/
public lemma card_symmDiff_eq_card_add_card_sub_two_mul_card_inter
    {α : Type} [DecidableEq α] (s t : Finset α) :
    (s ∆ t).card = s.card + t.card - 2 * (s ∩ t).card := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using!
    (Nat.eq_sub_of_add_eq (card_symmDiff_add_two_mul_card_inter (A := s) (B := t)))

attribute [grind =] card_symmDiff_eq_card_add_card_sub_two_mul_card_inter

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads
