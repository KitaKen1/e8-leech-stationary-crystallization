-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.Span

/-!
# Transporting `octadSubmodule` under permutations

Assuming two codes have matching octad sets after a coordinate permutation, we show that the span
of octad indicator vectors is transported by the induced linear equivalence.

## Main statements
* `octadWordSet_image_eq_of_octads_eq`
* `octadSubmodule_map_eq_of_octads_eq`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads

noncomputable section

open CodeFromOctadsAux

private lemma permuteLinearEquiv_wordOfFinset (σ : Equiv (Fin 24) (Fin 24)) (B : Finset (Fin 24)) :
    permuteLinearEquiv σ.symm (wordOfFinset (n := 24) B) =
      wordOfFinset (n := 24) (B.map σ.toEmbedding) := by
  funext i
  simp [permuteLinearEquiv, wordOfFinset, Finset.mem_map_equiv]

/--
Transport `octadWordSet` along a coordinate permutation, assuming the octad sets correspond.
-/
public lemma octadWordSet_image_eq_of_octads_eq
    (C₁ C₂ : Code 24)
    (σ : Equiv (Fin 24) (Fin 24))
    (hoct : octadsFromCode C₁ = {B | (Finset.map σ.toEmbedding B) ∈ octadsFromCode C₂}) :
    (permuteLinearEquiv σ.symm) '' (octadWordSet C₁) = octadWordSet C₂ := by
  ext w
  constructor
  · rintro ⟨w0, ⟨B, hB, rfl⟩, rfl⟩
    have hB' : (Finset.map σ.toEmbedding B) ∈ octadsFromCode C₂ := by
      simpa [hoct] using! hB
    refine ⟨Finset.map σ.toEmbedding B, hB', ?_⟩
    simpa using! permuteLinearEquiv_wordOfFinset (σ := σ) (B := B)
  · rintro ⟨B2, hB2, rfl⟩
    -- Pull the octad back along `σ`.
    have hB1 : (Finset.map σ.symm.toEmbedding B2) ∈ octadsFromCode C₁ := by
      have :
          Finset.map σ.toEmbedding (Finset.map σ.symm.toEmbedding B2) ∈ octadsFromCode C₂ := by
        simpa [map_map_equiv_symm' (σ := σ) (B := B2)] using! hB2
      simpa [hoct] using! this
    refine ⟨wordOfFinset (n := 24) (Finset.map σ.symm.toEmbedding B2), ?_, ?_⟩
    · exact ⟨Finset.map σ.symm.toEmbedding B2, hB1, rfl⟩
    · -- `permuteLinearEquiv σ.symm` of the pulled-back indicator is the original indicator.
      simpa [map_map_equiv_symm' (σ := σ) (B := B2)] using!
        permuteLinearEquiv_wordOfFinset (σ := σ) (B := Finset.map σ.symm.toEmbedding B2)

/--
Transport `octadSubmodule` along a coordinate permutation, assuming the octad sets correspond.
-/
public lemma octadSubmodule_map_eq_of_octads_eq
    (C₁ C₂ : Code 24)
    (σ : Equiv (Fin 24) (Fin 24))
    (hoct : octadsFromCode C₁ = {B | (Finset.map σ.toEmbedding B) ∈ octadsFromCode C₂}) :
    Submodule.map (permuteLinearEquiv σ.symm).toLinearMap (octadSubmodule C₁) =
      octadSubmodule C₂ := by
  -- `Submodule.map (span s) = span (f '' s)`.
  simp [octadSubmodule, Submodule.map_span,
    octadWordSet_image_eq_of_octads_eq (C₁ := C₁) (C₂ := C₂) σ hoct]

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads
