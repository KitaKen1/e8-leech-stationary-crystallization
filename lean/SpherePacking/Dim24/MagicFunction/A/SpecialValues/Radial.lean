-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Prelude
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.Values
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoAtTwo
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivFour


/-!
# Special values and derivatives of `aRadial`

This file transfers special values and derivative statements for the profile function `aProfile`
to the radial restriction `aRadial r = a (axisVec r)`, using `aRadial_eq_aProfile` (`u = r^2`).

## Main statements
* `aRadial_zero`
* `aRadial_sqrtTwo`
* `aRadial_hasDerivAt_sqrtTwo`
* `aRadial_two`
* `aRadial_hasDerivAt_two`
-/


namespace SpherePacking.Dim24

/-
Noncomputable because `axisVec` is noncomputable (it uses `EuclideanSpace.single` on `ℝ`).
-/
noncomputable section

open scoped Real

/-- Special value `aRadial 0` (paper: `113218560 * i / π`). -/
public theorem aRadial_zero : aRadial 0 = (113218560 : ℂ) * Complex.I / (π : ℂ) := by
  /- Proof sketch:
  Use the analytic continuation formula `a(r) = 4 i sin(π r^2/2)^2 (p̃(r) + ∫...)` (paper (2.16))
  and evaluate the limit at `r=0`, as done in the paper. -/
  simpa [aRadial_eq_aProfile] using! (aProfile_zero : aProfile (0 : ℝ) = _)

/-- Special value `aRadial (Real.sqrt 2)` (paper: `725760 * i / π`). -/
public theorem aRadial_sqrtTwo : aRadial (Real.sqrt 2) = (725760 : ℂ) * Complex.I / (π : ℂ) := by
  /- Paper: `a(√2) = 725760 i / π`. -/
  have hx : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  have hsq : (Real.sqrt (2 : ℝ)) ^ (2 : ℕ) = (2 : ℝ) := by
    simp [Real.sq_sqrt hx]
  simpa [aRadial_eq_aProfile, hsq] using! (aProfile_two : aProfile (2 : ℝ) = _)

/-- Derivative of `aRadial` at `Real.sqrt 2` (paper: `a'(√2) = -4437504 √2 * i / π`). -/
public theorem aRadial_hasDerivAt_sqrtTwo :
    HasDerivAt aRadial (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) (Real.sqrt 2) := by
  /- Paper: `a'(√2) = -4437504 √2 i / π`. -/
  have hx : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  have hsq : (Real.sqrt (2 : ℝ)) ^ (2 : ℕ) = (2 : ℝ) := by
    simp [Real.sq_sqrt hx]
  have hsqDeriv : HasDerivAt (fun r : ℝ => r ^ (2 : ℕ)) (2 * Real.sqrt 2) (Real.sqrt 2) := by
    simpa using! (hasDerivAt_pow (n := (2 : ℕ)) (x := (Real.sqrt 2 : ℝ)))
  have haProfAt :
      HasDerivAt aProfile (-(2218752 : ℂ) * Complex.I / (π : ℂ)) ((Real.sqrt 2) ^ (2 : ℕ)) := by
    simpa [hsq] using! (SpecialValuesDerivTwo.aProfile_hasDerivAt_two :
      HasDerivAt aProfile (-(2218752 : ℂ) * Complex.I / (π : ℂ)) (2 : ℝ))
  have hcomp :
      HasDerivAt (fun r : ℝ => aProfile (r ^ (2 : ℕ)))
        ((2 * Real.sqrt 2) • (-(2218752 : ℂ) * Complex.I / (π : ℂ))) (Real.sqrt 2) := by
    simpa [Function.comp_def] using!
      (HasDerivAt.scomp (g₁ := aProfile) (h := fun r : ℝ => r ^ (2 : ℕ)) (x := Real.sqrt 2)
        haProfAt hsqDeriv)
  -- Convert back to `aRadial` and simplify the constant.
  have hfun : aRadial = fun r : ℝ => aProfile (r ^ (2 : ℕ)) := by
    funext r
    simp [aRadial_eq_aProfile]
  -- `(2*√2) • (-(2218752) * I / π) = (-(4437504) * √2 * I / π)`.
  have hconst :
      ((2 * Real.sqrt 2) • (-(2218752 : ℂ) * Complex.I / (π : ℂ))) =
        (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) := by
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    -- `simp` turns `•` into multiplication by a real scalar; then it's just arithmetic.
    simp [Algebra.smul_def, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    field_simp [hpi]
    norm_num
  lia

/-- Special value `aRadial 2 = 0` (paper: `a(2) = 0`). -/
public theorem aRadial_two : aRadial 2 = 0 := by
  /- Paper: `a(2)=0`. -/
  have hsq : (2 : ℝ) ^ (2 : ℕ) = (4 : ℝ) := by norm_num
  simpa [aRadial_eq_aProfile, hsq] using! (aProfile_four : aProfile (4 : ℝ) = 0)

/-- Derivative of `aRadial` at `2` (paper: `a'(2) = -3456 * i / π`). -/
public theorem aRadial_hasDerivAt_two :
    HasDerivAt aRadial ((-3456 : ℂ) * Complex.I / (π : ℂ)) 2 := by
  /- Paper: `a'(2) = -3456 i / π`. -/
  have hsq : (2 : ℝ) ^ (2 : ℕ) = (4 : ℝ) := by norm_num
  have hsqDeriv : HasDerivAt (fun r : ℝ => r ^ (2 : ℕ)) (2 * (2 : ℝ)) (2 : ℝ) := by
    simpa using! (hasDerivAt_pow (n := (2 : ℕ)) (x := (2 : ℝ)))
  have haProfAt :
      HasDerivAt aProfile ((-864 : ℂ) * Complex.I / (π : ℂ)) ((2 : ℝ) ^ (2 : ℕ)) := by
    simpa [hsq] using! (aProfile_hasDerivAt_four :
      HasDerivAt aProfile ((-864 : ℂ) * Complex.I / (π : ℂ)) (4 : ℝ))
  have hcomp :
      HasDerivAt (fun r : ℝ => aProfile (r ^ (2 : ℕ)))
        ((2 * (2 : ℝ)) • ((-864 : ℂ) * Complex.I / (π : ℂ))) (2 : ℝ) := by
    simpa [Function.comp_def] using!
      (HasDerivAt.scomp (g₁ := aProfile) (h := fun r : ℝ => r ^ (2 : ℕ)) (x := (2 : ℝ))
        haProfAt hsqDeriv)
  have hfun : aRadial = fun r : ℝ => aProfile (r ^ (2 : ℕ)) := by
    funext r
    simp [aRadial_eq_aProfile]
  have hconst :
      ((2 * (2 : ℝ)) • ((-864 : ℂ) * Complex.I / (π : ℂ))) =
        ((-3456 : ℂ) * Complex.I / (π : ℂ)) := by
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [Algebra.smul_def, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    field_simp [hpi]
    norm_num
  simp_all

end

end SpherePacking.Dim24
