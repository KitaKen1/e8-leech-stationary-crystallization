-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Basic

/-!
# The explicit rational term `pTildeProfile`

In the paper (`dim_24.tex`, around `eq:avalues`), one defines a polynomial/exponential expression
`p(t)` and its Laplace transform `\\tilde p(r)`. Converting to the profile variable `u = r^2`,
this becomes an explicit rational function of `u`, defined here as `pTildeProfile`.

This file also records the principal part of `pTildeProfile` at `u = 2`.

## Main statements
* `pTildeProfile_eq_principalPart_two`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex

/-- The rational function corresponding to `\tilde p(r)` expressed in terms of `u = r^2`. -/
@[expose] public def pTildeProfile (u : ℝ) : ℂ :=
  ((-864 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 4 : ℝ) : ℂ) +
    ((725760 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (((u - 2) ^ (2 : ℕ) : ℝ) : ℂ) +
      ((-2218752 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 2 : ℝ) : ℂ) +
        ((113218560 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u ^ (2 : ℕ) : ℝ) : ℂ) +
          ((-223140096 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u : ℝ) : ℂ)

/-- The principal part of `pTildeProfile` at `u = 2`
(paper: the `(u-2)^{-2}` and `(u-2)^{-1}` terms). -/
public theorem pTildeProfile_eq_principalPart_two :
    ∃ g : ℝ → ℂ,
      ContinuousAt g (2 : ℝ) ∧
        (fun u : ℝ => pTildeProfile u) =ᶠ[𝓝[>] (2 : ℝ)]
          fun u : ℝ =>
            ((725760 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (((u - 2) ^ (2 : ℕ) : ℝ) : ℂ) +
              ((-2218752 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 2 : ℝ) : ℂ) +
                g u := by
  -- The remainder terms are exactly the `u=4` and `u=0` poles, which are continuous at `u=2`.
  let g : ℝ → ℂ := fun u : ℝ =>
    ((-864 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 4 : ℝ) : ℂ) +
      ((113218560 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u ^ (2 : ℕ) : ℝ) : ℂ) +
        ((-223140096 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u : ℝ) : ℂ)
  refine ⟨g, ?_, ?_⟩
  · -- Continuity at `u=2` is routine because all denominators are nonzero there.
    have hsub : ContinuousAt (fun u : ℝ => ((u - 4 : ℝ) : ℂ)) (2 : ℝ) := by fun_prop
    have hsub0 : ((2 - 4 : ℝ) : ℂ) ≠ 0 := by
      norm_num
    have hu : ContinuousAt (fun u : ℝ => ((u : ℝ) : ℂ)) (2 : ℝ) := by fun_prop
    have hu2 : ContinuousAt (fun u : ℝ => ((u ^ (2 : ℕ) : ℝ) : ℂ)) (2 : ℝ) := by
      fun_prop
    have h1' :
        ContinuousAt
          (fun u : ℝ =>
              ((-864 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 4 : ℝ) : ℂ))
          (2 : ℝ) :=
      (continuousAt_const.div hsub (by simpa using! hsub0))
    have h2' :
        ContinuousAt
          (fun u : ℝ =>
              ((113218560 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u ^ (2 : ℕ) : ℝ) : ℂ))
          (2 : ℝ) :=
      (continuousAt_const.div hu2 (by norm_num))
    have h3' :
        ContinuousAt
          (fun u : ℝ => ((-223140096 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u : ℝ) : ℂ))
          (2 : ℝ) :=
      (continuousAt_const.div hu (by norm_num))
    simpa [g, add_assoc] using! (h1'.add (h2'.add h3'))
  · -- The principal part + remainder identity is definitional.
    refine Filter.Eventually.of_forall ?_
    intro u
    simp [pTildeProfile, g, add_assoc, add_left_comm]

end SpecialValuesDerivTwoLaurent

end

end SpherePacking.Dim24
