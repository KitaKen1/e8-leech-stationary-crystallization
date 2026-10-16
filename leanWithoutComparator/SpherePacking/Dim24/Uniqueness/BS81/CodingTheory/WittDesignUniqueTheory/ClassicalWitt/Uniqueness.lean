-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerDefs
import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpGolayUniqueFromBiplane
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctadsAux
import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.ClassicalWitt.SharpInput

/-!
# Classical uniqueness of the Witt design `S(5,8,24)`

The main theorem `steiner_S_5_8_24_unique_classical_via_designCode` shows that any two
`SteinerSystem 24 8 5` are isomorphic. The proof proceeds by associating to a design its
`designCode`, applying sharp Golay code uniqueness to obtain a coordinate permutation, and then
transporting blocks across that permutation.

References:
- Brouwer, *The Witt designs, Golay codes and Mathieu groups* (`paper/Bro08Witt/...`).
- In-repo note: `paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.
- BS81, §4/§5 coding-theory ingredients (`paper/BS81/sources.tex`).
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.ClassicalWitt

noncomputable section

open CodeFromOctadsAux

/-- Any two Steiner systems `S(5,8,24)` are isomorphic, via the associated design code. -/
public theorem steiner_S_5_8_24_unique_classical_via_designCode
    (S₁ S₂ : SteinerSystem 24 8 5) :
    IsomorphicSteinerSystem 24 8 5 S₁ S₂ := by
  -- Build sharp-input codes from the designs.
  let C₁ : Code 24 := designCode S₁
  let C₂ : Code 24 := designCode S₂
  have hC₁ : IsSharpBS81GolayInput C₁ := by
    simpa [C₁] using! isSharpBS81GolayInput_designCode (S := S₁)
  have hC₂ : IsSharpBS81GolayInput C₂ := by
    simpa [C₂] using! isSharpBS81GolayInput_designCode (S := S₂)
  -- Use sharp Golay uniqueness to align codes.
  rcases sharpGolay_unique_of_biplane (C₁ := C₁) (C₂ := C₂) hC₁ hC₂ with ⟨σ, hσ⟩
  -- Identify blocks with octads in each design-code.
  have hOct₁ : octadsFromCode C₁ = S₁.blocks := by
    simpa [C₁] using! (octadsFromCode_designCode_eq_blocks (S := S₁))
  have hOct₂ : octadsFromCode C₂ = S₂.blocks := by
    simpa [C₂] using! (octadsFromCode_designCode_eq_blocks (S := S₂))
  -- Transport octads under the permutation σ and conclude isomorphism.
  -- `octadsFromCode (permuteCode σ C₁) = {B | map σ B ∈ octadsFromCode C₁}`.
  have hOctPerm :
      octadsFromCode C₂ =
        {B | (Finset.map σ.toEmbedding B) ∈ octadsFromCode C₁} := by
    -- rewrite `C₂` as `permuteCode σ C₁`
    simpa [C₂, hσ] using! (octadsFromCode_permuteCode (σ := σ) (C := C₁))
  -- Turn this into the `IsomorphicSteinerSystem` equality, using `σ.symm` as the witness.
  refine ⟨σ.symm, ?_⟩
  ext B
  simp [← hOct₁, ← hOct₂, hOctPerm,
    GolayUniquenessSteps.CodeFromOctadsAux.map_map_equiv_symm' (σ := σ) (B := B)]

end

end GolayUniquenessSteps.WittDesignUniqueTheory.ClassicalWitt

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
