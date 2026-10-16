module
import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpGolayUniqueFromBiplane
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctadsAux
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpInput
import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.ClassicalWitt.Uniqueness

/-!
# Uniqueness of the Witt design from sharp Golay codes

This file converts sharp Golay code uniqueness into uniqueness of the Witt design `S(5,8,24)`.
It also records the classical "absolute" uniqueness theorem, proved via the design-code route.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory

noncomputable section

/-- Sharp Golay code uniqueness induces uniqueness of the associated Steiner systems. -/
public theorem steiner_S_5_8_24_unique_of_sharpCodes
    (C₁ C₂ : Code 24)
    (h₁ : IsSharpBS81GolayInput C₁)
    (h₂ : IsSharpBS81GolayInput C₂) :
    ∃ S₁ S₂ : SteinerSystem 24 8 5,
      S₁.blocks = octadsFromCode C₁ ∧
      S₂.blocks = octadsFromCode C₂ ∧
      IsomorphicSteinerSystem 24 8 5 S₁ S₂ := by
  rcases steiner_S_5_8_24_of_sharp (C := C₁) h₁ with ⟨S₁, hS₁⟩
  rcases steiner_S_5_8_24_of_sharp (C := C₂) h₂ with ⟨S₂, hS₂⟩
  rcases sharpGolay_unique_of_biplane (C₁ := C₁) (C₂ := C₂) h₁ h₂ with ⟨σ, hσ⟩
  refine ⟨S₁, S₂, hS₁, hS₂, ?_⟩
  exact ClassicalWitt.steiner_S_5_8_24_unique_classical_via_designCode S₁ S₂

/-- Classical uniqueness: any two Steiner systems `S(5,8,24)` are isomorphic. -/
public theorem steiner_S_5_8_24_unique_classical :
    ∀ (S₁ S₂ : SteinerSystem 24 8 5), IsomorphicSteinerSystem 24 8 5 S₁ S₂ :=
  fun S₁ S₂ => ClassicalWitt.steiner_S_5_8_24_unique_classical_via_designCode S₁ S₂

end

end GolayUniquenessSteps.WittDesignUniqueTheory
end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
