-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.PunctureEven
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctadsAux

/-!
# Even-weight basis words on a dodecad complement

This file corresponds to Lemma `even_basis` in the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`:
given a labeled `12`-set `T = {t₀,t₁,...,t₁₁}`, the `11` weight-2 words `t₀+tᵢ` form a basis of the
even-weight code on `T`.

In the Lean development we embed those words back into length `24` via `evenWeightCode S`, where
`S : Finset (Fin 24)` plays the role of the dodecad support being punctured away.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneFromSharp

noncomputable section

open GolayUniquenessSteps.CodeFromOctadsAux

/-- The weight-2 word supported on the pair `{t0,t1}`. -/
@[expose] public def evenBasisWord (t0 t1 : Fin 24) : BinWord 24 :=
  wordOfFinset (n := 24) ({t0, t1} : Finset (Fin 24))

/-- The family of weight-2 words `{t0, t i}` indexed by `i : Fin 11`. -/
@[expose] public def evenBasisFamily (t0 : Fin 24) (t : Fin 11 → Fin 24) : Fin 11 → BinWord 24 :=
  fun i => evenBasisWord t0 (t i)

/-- If `t0,t1 ∉ S` are distinct, then `evenBasisWord t0 t1` lies in `evenWeightCode S`. -/
public theorem evenBasisWord_mem_evenWeightCode
    (S : Finset (Fin 24)) {t0 t1 : Fin 24}
    (ht0 : t0 ∉ S) (ht1 : t1 ∉ S) (hne : t0 ≠ t1) :
    evenBasisWord t0 t1 ∈ evenWeightCode S := by
  refine ⟨?_, ?_⟩
  · intro i hiS
    have hiB : i ∉ ({t0, t1} : Finset (Fin 24)) := by
      intro hi
      have : i = t0 ∨ i = t1 := by simpa using! hi
      rcases this with rfl | rfl
      · exact ht0 hiS
      · exact ht1 hiS
    simp [evenBasisWord, wordOfFinset, hiB]
  · have hw : weight (evenBasisWord t0 t1) = 2 := by
      simpa [evenBasisWord, GolayBounds.weight_eq_card_support, support_wordOfFinset] using!
        (Finset.card_pair hne)
    simp [hw]

end

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneFromSharp

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
