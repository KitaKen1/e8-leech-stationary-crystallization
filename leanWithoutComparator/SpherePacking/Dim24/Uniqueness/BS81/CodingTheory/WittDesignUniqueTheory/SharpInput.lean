module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Orthogonality

/-!
# Sharp Golay input assumptions

Besides `IsExtendedBinaryGolayCode` (linearity/cardinality/minimum distance), the biplane-reduction
route uses extra hypotheses:
- self-orthogonality,
- doubly evenness,
- and the sharp weight-`8` count `759`.

This file packages those assumptions without changing the project-wide definition of
`IsExtendedBinaryGolayCode`.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

namespace GolayUniquenessSteps.WittDesignUniqueTheory

/-- A code is doubly even if every codeword has weight divisible by `4`. -/
@[expose] public def IsDoublyEven (C : Code 24) : Prop :=
  ∀ ⦃w : BinWord 24⦄, w ∈ C → 4 ∣ weight w

/-- Sharp BS81 Lemma 21 coding input (the hypotheses of `golay_uniqueness_from_biplane.tex`). -/
public structure IsSharpBS81GolayInput (C : Code 24) : Prop where
  linear : IsLinearCode C
  card_eq : Set.ncard C = 2 ^ 12
  minDist_eq : minDist C = 8
  selfOrth : IsSelfOrthogonal C
  doublyEven : IsDoublyEven C
  weight8_card : Set.ncard (weight8Words C) = 759

attribute [grind cases] IsSharpBS81GolayInput

/-- A convenience lemma: `minDist = 8` implies `8 ≤ minDist`. -/
public lemma IsSharpBS81GolayInput.minDist_ge (C : Code 24) (hC : IsSharpBS81GolayInput C) :
    8 ≤ minDist C := by
  simp [hC.minDist_eq]

attribute [grind →] IsSharpBS81GolayInput.minDist_ge

/-!
From the sharp BS81 coding input, the weight-`8` supports form a Steiner system `S(5,8,24)`.

This is Proposition `steiner` in `paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.
In the codebase, it is already available as `WittDesign.steiner_S_5_8_24_of_weight8_count` in
`CodingTheory/GolayDefs.lean`.
-/

/-- From sharp input assumptions, the weight-`8` supports form a Steiner system `S(5,8,24)`. -/
public theorem steiner_S_5_8_24_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C) :
    ∃ S : SteinerSystem 24 8 5, S.blocks = octadsFromCode C := by
  have hmin : 8 ≤ minDist C := hC.minDist_ge
  exact WittDesign.steiner_S_5_8_24_of_weight8_count (C := C) hmin hC.weight8_card

end GolayUniquenessSteps.WittDesignUniqueTheory
end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
