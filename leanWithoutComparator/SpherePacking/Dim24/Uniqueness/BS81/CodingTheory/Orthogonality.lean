module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Dot product and orthogonality for binary words

We keep this file small: only the definitions and basic bilinearity lemmas needed for the Golay/Witt
uniqueness development.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open scoped BigOperators

/-- The dot product on binary words over `ZMod 2`. -/
@[expose] public def dot {n : ℕ} (x y : BinWord n) : ZMod 2 :=
  ∑ i : Fin n, x i * y i

/-- `dot 0 y = 0`. -/
@[simp] public lemma dot_zero_left {n : ℕ} (y : BinWord n) : dot 0 y = 0 := by
  simp [dot]

/-- `dot x 0 = 0`. -/
@[simp] public lemma dot_zero_right {n : ℕ} (x : BinWord n) : dot x 0 = 0 := by
  simp [dot]

/-- Additivity of `dot` in the left argument. -/
public lemma dot_add_left {n : ℕ} (x₁ x₂ y : BinWord n) :
    dot (x₁ + x₂) y = dot x₁ y + dot x₂ y := by
  simp [dot, add_mul, Finset.sum_add_distrib]

/-- Additivity of `dot` in the right argument. -/
public lemma dot_add_right {n : ℕ} (x y₁ y₂ : BinWord n) :
    dot x (y₁ + y₂) = dot x y₁ + dot x y₂ := by
  simp [dot, mul_add, Finset.sum_add_distrib]

/-- A code is self-orthogonal if all pairs of codewords have dot product `0`. -/
@[expose] public def IsSelfOrthogonal {n : ℕ} (C : Code n) : Prop :=
  ∀ ⦃x y : BinWord n⦄, x ∈ C → y ∈ C → dot x y = 0

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
