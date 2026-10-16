module
public import Mathlib.LinearAlgebra.Span.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerDefs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.LinearCode
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctadsAux

/-!
# A binary linear code from a Witt design

Given a Steiner system `S : SteinerSystem 24 8 5`, this file defines the binary linear code
spanned by the indicator vectors of its blocks. Concretely, we take the `ZMod 2`-submodule spanned
by block words and view it as a `Code 24`.

Roadmap source (in-repo): `paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.
Supporting exposition: `paper/Bro08Witt/brouwer_witt_designs_golay_mathieu.tex`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.ClassicalWitt

noncomputable section

open CodeFromOctadsAux

/-- The set of indicator words coming from a block set. -/
@[expose] public def blockWordSet (blocks : Set (Finset (Fin 24))) : Set (BinWord 24) :=
  {w | ∃ B : Finset (Fin 24), B ∈ blocks ∧ w = wordOfFinset (n := 24) B}

/-- The `ZMod 2`-submodule spanned by block indicator words. -/
@[expose] public def blockSubmodule (blocks : Set (Finset (Fin 24))) :
    Submodule (ZMod 2) (BinWord 24) :=
  Submodule.span (ZMod 2) (blockWordSet blocks)

/-- The code spanned by a block set (as a `Set` of words). -/
@[expose] public def codeFromBlocks (blocks : Set (Finset (Fin 24))) : Code 24 :=
  (blockSubmodule blocks : Set (BinWord 24))

/-- The code `codeFromBlocks blocks` is a linear code. -/
public lemma isLinearCode_codeFromBlocks (blocks : Set (Finset (Fin 24))) :
    IsLinearCode (codeFromBlocks blocks) := by
  refine ⟨?_, ?_⟩
  · exact (blockSubmodule blocks).zero_mem
  · intro x y hx hy
    exact (blockSubmodule blocks).add_mem hx hy

/-- The code spanned by the blocks of a Steiner system. -/
@[expose] public def codeFromSteinerSystem (S : SteinerSystem 24 8 5) : Code 24 :=
  codeFromBlocks S.blocks

/-- The code `codeFromSteinerSystem S` is a linear code. -/
public lemma isLinearCode_codeFromSteinerSystem (S : SteinerSystem 24 8 5) :
    IsLinearCode (codeFromSteinerSystem S) :=
  isLinearCode_codeFromBlocks (blocks := S.blocks)

end

end GolayUniquenessSteps.WittDesignUniqueTheory.ClassicalWitt

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
