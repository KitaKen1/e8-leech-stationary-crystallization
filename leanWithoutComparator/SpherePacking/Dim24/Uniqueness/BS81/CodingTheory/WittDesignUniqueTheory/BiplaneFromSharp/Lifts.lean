-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneFromSharp.EvenBasis
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.DodecadExists

/-!
# Lifting the even-weight basis with a pinned coordinate

This file corresponds to Lemma `lifts_pinned` and Proposition `gen_matrix` in the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.

We keep the output as an existence statement: there exist codewords `vᵢ` mapping to the chosen
even-weight basis words under `eraseCoords (support u)` and satisfying the pinning condition
`(vᵢ) p = 0`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneFromSharp

noncomputable section

open GolayUniquenessSteps.CodeFromOctadsAux

local notation "Word" => BinWord 24

/--
For a sharp Golay input, lift the even-weight basis words to codewords satisfying a pinning
condition at a chosen coordinate `p`.
-/
public theorem exists_pinned_lifts_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C)
    {u : Word} (huC : u ∈ C) (hwt : weight u = 12)
    {p : Fin 24} (hp : p ∈ support u)
    {t0 : Fin 24} {t : Fin 11 → Fin 24}
    (ht0 : t0 ∉ support u) (ht : ∀ i, t i ∉ support u) (hne : ∀ i, t0 ≠ t i) :
    ∃ v : Fin 11 → Word,
      (∀ i, v i ∈ C) ∧
      (∀ i, v i p = 0) ∧
      (∀ i, eraseCoords (support u) (v i) = evenBasisFamily t0 t i) := by
  let S : Finset (Fin 24) := support u
  have hEraseEq : eraseCode S C = evenWeightCode S :=
    eraseCode_eq_evenWeightCode_of_sharp (C := C) hC huC hwt
  have hu_p : u p = 1 := (GolayBounds.mem_support (w := u) p).1 hp
  have hEu : eraseCoords S u = 0 := PunctureEven.eraseCoords_support_eq_zero (u := u)
  have hw_mem : ∀ i : Fin 11, evenBasisFamily t0 t i ∈ eraseCode S C := by
    intro i
    have hw_even : evenBasisFamily t0 t i ∈ evenWeightCode S :=
      evenBasisWord_mem_evenWeightCode (S := S) (t0 := t0) (t1 := t i)
        (by simpa [S] using! ht0) (by simpa [S] using! ht i) (hne i)
    simpa [hEraseEq] using! hw_even
  have hex_pre :
      ∀ i : Fin 11, ∃ c : Word, c ∈ C ∧ eraseCoords S c = evenBasisFamily t0 t i := by
    intro i
    rcases hw_mem i with ⟨c, hc, hcEq⟩; exact ⟨c, hc, hcEq⟩
  -- choose preimages
  let c : Fin 11 → Word := fun i => Classical.choose (hex_pre i)
  have hc_mem : ∀ i : Fin 11, c i ∈ C := fun i => (Classical.choose_spec (hex_pre i)).1
  have hc_erase : ∀ i : Fin 11, eraseCoords S (c i) = evenBasisFamily t0 t i :=
    fun i => (Classical.choose_spec (hex_pre i)).2
  -- pin coordinate by adding `u` if needed
  let v : Fin 11 → Word := fun i => if (c i) p = 0 then c i else c i + u
  have hv_mem : ∀ i : Fin 11, v i ∈ C := by
    intro i
    by_cases hcp0 : (c i) p = 0
    · simpa [v, hcp0] using! hc_mem i
    · simpa [v, hcp0] using! hC.linear.2 (c i) u (hc_mem i) huC
  have hv_p0 : ∀ i : Fin 11, v i p = 0 := by
    intro i
    by_cases hcp0 : (c i) p = 0
    · simp [v, hcp0]
    · have hcp1 : (c i) p = 1 := GolayBounds.zmod2_eq_one_of_ne_zero ((c i) p) hcp0
      simp [v, Pi.add_apply, hcp1, hu_p]
  have hv_erase : ∀ i : Fin 11, eraseCoords S (v i) = evenBasisFamily t0 t i := by
    intro i
    by_cases hcp0 : (c i) p = 0
    · simp [v, hcp0, hc_erase i]
    · have hEraseAdd : eraseCoords S (c i + u) = eraseCoords S (c i) := by
        simpa [hEu] using! (PunctureEven.eraseCoords_add (S := S) (c i) u)
      simpa [v, hcp0, hEraseAdd] using! hc_erase i
  refine ⟨v, hv_mem, hv_p0, hv_erase⟩
end

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneFromSharp

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
