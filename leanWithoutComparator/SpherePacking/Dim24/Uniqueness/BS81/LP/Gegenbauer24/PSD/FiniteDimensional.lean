-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite dimensionality of the homogeneous pieces `Pk k`

This file shows that the degree-`k` homogeneous component `Pk k` of `MvPolynomial (Fin 24) ℝ` is
finite dimensional. This is used later to deduce completeness of the Fischer inner product spaces.

## Main statements
* `finiteDimensional_Pk`
-/
namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
noncomputable section

open scoped BigOperators

open Finsupp MvPolynomial

/-- The homogeneous piece `Pk k` is finite dimensional. -/
public noncomputable instance finiteDimensional_Pk (k : ℕ) : FiniteDimensional ℝ (Pk k) := by
  -- Unfold to the concrete `homogeneousSubmodule`.
  change FiniteDimensional ℝ ↥(MvPolynomial.homogeneousSubmodule Var ℝ k)
  exact Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (σ := Var) (R := ℝ) k)

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
