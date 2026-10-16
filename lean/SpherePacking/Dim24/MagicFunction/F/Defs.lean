module
public import SpherePacking.Dim24.MagicFunction.A.Defs
public import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
public import SpherePacking.ForMathlib.Fourier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier


/-!
# Definitions of `f` and `scaledF`

This file defines the auxiliary Schwartz function `f` and its scaled version `scaledF`, used in
the dimension-24 LP bound.

## Main definitions
* `f`
* `scaledF`

## References
`dim_24.tex`, Section 4 (`sec:proof`).
-/

open scoped FourierTransform ENNReal SchwartzMap

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

/-- The auxiliary function `f` (called `f` in `dim_24.tex`). -/
@[expose] public noncomputable def f : 𝓢(ℝ²⁴, ℂ) :=
  (- ((Real.pi : ℂ) * Complex.I) / (113218560 : ℂ)) • a -
    (Complex.I / ((262080 : ℂ) * (Real.pi : ℂ))) • b

/-- A scaled version of `f` satisfying the radius-1 Cohn-Elkies hypotheses.

We take `scaledF(x) = f(2 • x)`.
-/
@[expose] public noncomputable def scaledF : 𝓢(ℝ²⁴, ℂ) :=
  let c : ℝ := 2
  let A : ℝ²⁴ ≃ₗ[ℝ] ℝ²⁴ := LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ²⁴) c two_ne_zero
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f

end SpherePacking.Dim24
