module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.Function


/-!
# Magic function `a`

Definition of the `+1` Fourier eigenfunction `a` in dimension `24`.

Paper reference: `dim_24.tex`, Section 2 (`sec:a`), equation (2.7) and Lemma 2.1.

## Main definitions
* `a`
-/

section


open scoped SchwartzMap

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

/-- The +1 eigenfunction `a : 𝓢(ℝ²⁴,ℂ)`.

Faithfulness note:
In the paper, `a(r)` is first defined for `r>2` by a contour integral, then analytically continued
to all real `r`, and finally interpreted as a radial Schwartz function on `ℝ²⁴`.
-/
@[expose] public noncomputable def a : 𝓢(ℝ²⁴, ℂ) :=
  SpherePacking.Dim24.aAux

end SpherePacking.Dim24

end
