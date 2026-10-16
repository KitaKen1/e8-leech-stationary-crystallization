module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Minimal vectors in the root lattice `Dₙ`

This file defines the set `minVecDn` of minimal vectors of the root lattice `Dₙ` and the lattice
`latticeDn` as their `ℤ`-span.

These are the basic objects used in the BS81 arguments that count and constrain vectors in `Dₙ`.

## Main definitions
* `minVecDn`
* `latticeDn`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Dn
noncomputable section

open scoped RealInnerProductSpace

variable (n : ℕ)

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Standard basis vector in `ℝⁿ`. -/
@[expose] public def eStd (i : Fin n) : ℝⁿ :=
  EuclideanSpace.single i (1 : ℝ)

/-- Sign choices `{+1,-1}` as integers. -/
@[expose] public def Sign : Set ℤ := {z : ℤ | z = 1 ∨ z = -1}

lemma Sign_finite : (Sign).Finite := by
  simp [Sign, Set.setOf_or]

/-- Minimal vectors of `Dₙ`: the set `{ ±√2 e_i ± √2 e_j | i ≠ j }`. -/
@[expose] public def minVecDn : Set ℝⁿ :=
  {x : ℝⁿ |
    ∃ i j : Fin n,
      i ≠ j ∧
        ∃ s t : ℤ,
          s ∈ Sign ∧ t ∈ Sign ∧
            x =
              (Real.sqrt 2) • ((s : ℝ) • eStd (n := n) i) +
                (Real.sqrt 2) • ((t : ℝ) • eStd (n := n) j)}

/-- The root lattice `Dₙ` as the ℤ-span of its minimal vectors. -/
public def latticeDn : Submodule ℤ ℝⁿ :=
  Submodule.span ℤ (minVecDn (n := n))

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Dn
