module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Coding theory primitives for BS81

We only formalize the minimal API BS81 use:
- binary words of length `n`,
- Hamming weight and distance,
- (linear) binary codes as subsets/subspaces,
- and a few counting bounds/uniqueness statements specialized to the Golay code / Witt designs.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

/-!
## Binary words
-/

/-- A binary word of length `n`. -/
public abbrev BinWord (n : ℕ) := Fin n → ZMod 2

/-- Hamming weight of a binary word. -/
@[expose] public def weight {n : ℕ} (w : BinWord n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => w i = 1)).card

/-- Hamming distance between binary words, computed as the weight of the pointwise sum. -/
@[expose] public def hammingDist {n : ℕ} (w₁ w₂ : BinWord n) : ℕ :=
  weight (n := n) (fun i => w₁ i + w₂ i)

/-!
## Codes
-/

/-- A (binary) code of length `n`, as a set of words. -/
public abbrev Code (n : ℕ) := Set (BinWord n)

/-- Predicate asserting that a code is linear over `ZMod 2`. -/
@[expose] public def IsLinearCode {n : ℕ} (C : Code n) : Prop :=
  (0 : BinWord n) ∈ C ∧
    (∀ x y : BinWord n, x ∈ C → y ∈ C → (fun i => x i + y i) ∈ C)

/-- The minimum distance of a code, defined as an infimum over distances between distinct
codewords. -/
@[expose] public def minDist {n : ℕ} (C : Code n) : ℕ :=
  sInf {d : ℕ | ∃ x y : BinWord n, x ∈ C ∧ y ∈ C ∧ x ≠ y ∧ hammingDist x y = d}

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
