module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.Radial


/-!
# Applying Laplace representations to `a`, `b`, and `f`

This file records the basic radial rewriting lemmas for `a`, `b`, and `f` in terms of the
one-variable profiles `aProfile` and `bProfile`. These rewrites are used when applying analytic
continuation formulas to prove the Cohn-Elkies sign conditions.

## Main statements
* `LaplaceTmp.LaplaceApply.a_apply`
* `LaplaceTmp.LaplaceApply.b_apply`
* `LaplaceTmp.LaplaceApply.f_apply`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceApply

noncomputable section

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

-- Basic radial application lemmas for `a`, `b`, and `f`.

/-- Rewrite `a x` in terms of the one-variable profile `aProfile`. -/
public lemma a_apply (x : ℝ²⁴) : a x = aProfile (‖x‖ ^ (2 : ℕ)) := by
  simp [Dim24.a, Dim24.aAux]

/-- Rewrite `b x` in terms of the one-variable profile `bProfile`. -/
public lemma b_apply (x : ℝ²⁴) : b x = bProfile (‖x‖ ^ (2 : ℕ)) := by
  simp [Dim24.b]

/-- Rewrite `f x` as a linear combination of `aProfile (‖x‖^2)` and `bProfile (‖x‖^2)`. -/
public lemma f_apply (x : ℝ²⁴) :
    f x =
      (- (Real.pi * Complex.I) / (113218560 : ℂ)) * aProfile (‖x‖ ^ (2 : ℕ)) -
        (Complex.I / ((262080 : ℂ) * Real.pi)) * bProfile (‖x‖ ^ (2 : ℕ)) := by
  simp [Dim24.f, a_apply, b_apply]

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceApply
