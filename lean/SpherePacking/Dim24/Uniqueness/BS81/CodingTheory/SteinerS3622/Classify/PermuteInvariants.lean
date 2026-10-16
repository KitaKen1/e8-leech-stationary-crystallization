-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerS3622.PermuteFix01

/-!
# Permutation invariance for the classification

We use:
* `permuteCode` / `permuteWord` from `CodingTheory/GolayDefs.lean`, and
* the `extendFix01` combinator from `SteinerS3622/PermuteFix01.lean` which extends a permutation
  of the last 22 coordinates to a permutation of `Fin 24` fixing the first two points `0,1`.
The one genuinely important lemma already proved is
`SteinerS3622PermuteFix01.blocksFromGolay_permuteCode_extendFix01`.

The remaining invariance facts (`IsExtendedBinaryGolayCode` under permutation) are straightforward;
we keep them as explicit lemmas.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerS3622Classify

noncomputable section

namespace PermuteCode

/-- Cardinality is preserved under coordinate permutation of a code. -/
public lemma ncard_permuteCode {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (C : Code n) :
    Set.ncard (permuteCode (n := n) σ C) = Set.ncard C := by
  simpa [permuteCode] using!
    (Set.ncard_image_of_injective (f := permuteWord (n := n) σ) (s := C)
      (permuteWord_injective (σ := σ)))

/-- The distance set used to define `minDist` is invariant under `permuteCode`. -/
public lemma distSet_permuteCode {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (C : Code n) :
    {d : ℕ | ∃ x y : BinWord n,
        x ∈ permuteCode (n := n) σ C ∧ y ∈ permuteCode (n := n) σ C ∧
          x ≠ y ∧ hammingDist x y = d} =
      {d : ℕ | ∃ x y : BinWord n, x ∈ C ∧ y ∈ C ∧ x ≠ y ∧ hammingDist x y = d} := by
  ext d
  constructor
  · rintro ⟨x, y, hx, hy, hxy, hd⟩
    rcases hx with ⟨x0, hx0, rfl⟩
    rcases hy with ⟨y0, hy0, rfl⟩
    refine ⟨x0, y0, hx0, hy0, ?_, ?_⟩ <;> grind
  · rintro ⟨x, y, hx, hy, hxy, hd⟩
    refine
      ⟨permuteWord (n := n) σ x, permuteWord (n := n) σ y,
        ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ?_, ?_⟩ <;> grind

/-- Minimum distance is invariant under coordinate permutation of a code. -/
public lemma minDist_permuteCode {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (C : Code n) :
    minDist (permuteCode (n := n) σ C) = minDist C := by
  unfold minDist
  rw [distSet_permuteCode (σ := σ) (C := C)]

end PermuteCode

/-- `IsExtendedBinaryGolayCode` is invariant under coordinate permutations. -/
public theorem isExtendedBinaryGolayCode_permuteCode
    (σ : Equiv (Fin 24) (Fin 24)) {C : Code 24} :
    IsExtendedBinaryGolayCode C → IsExtendedBinaryGolayCode (permuteCode (n := 24) σ C) := by
  intro hC
  refine
    { linear := isLinearCode_permuteCode (σ := σ) (C := C) hC.linear
      card_eq := by
        simpa [PermuteCode.ncard_permuteCode (σ := σ) (C := C)] using! hC.card_eq
      minDist_eq := by
        -- `minDist` is invariant under coordinate permutations.
        simpa [PermuteCode.minDist_permuteCode (σ := σ) (C := C)] using! hC.minDist_eq }

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerS3622Classify
