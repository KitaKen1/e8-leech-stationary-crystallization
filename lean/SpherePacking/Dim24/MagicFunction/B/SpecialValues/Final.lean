-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.BProfileDeriv
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.EvenU.BProfileZeros


/-!
# Special values of `bRadial`

This file collects the final special-value statements for the radial profile `bRadial`, obtained
from the corresponding statements about `bProfile` in the variable `u = r ^ 2`.

## Main statements
* `bRadial_zero`
* `bRadial_sqrtTwo`
* `bRadial_hasDerivAt_sqrtTwo`
* `bRadial_two`
* `bRadial_hasDerivAt_two`

-/

open scoped Real

namespace SpherePacking.Dim24

noncomputable section

private lemma bRadial_eq_fun : bRadial = fun r : ℝ => bProfile (r ^ (2 : ℕ)) := by
  funext r
  simpa using! (SpecialValuesAux.bRadial_eq (r := r))

private lemma hasDerivAt_bRadial_of_hasDerivAt_bProfile
    (r0 : ℝ) (d : ℂ) (hb : HasDerivAt bProfile d (r0 ^ (2 : ℕ))) :
    HasDerivAt bRadial ((2 * r0) • d) r0 := by
  have hsqDeriv : HasDerivAt (fun r : ℝ => r ^ (2 : ℕ)) (2 * r0) r0 := by
    simpa using! (hasDerivAt_pow (n := (2 : ℕ)) (x := r0))
  have hcomp :
      HasDerivAt (fun r : ℝ => bProfile (r ^ (2 : ℕ))) ((2 * r0) • d) r0 := by
    simpa [Function.comp_def] using!
      (HasDerivAt.scomp (g₁ := bProfile) (h := fun r : ℝ => r ^ (2 : ℕ)) (x := r0) hb hsqDeriv)
  simpa [bRadial_eq_fun] using! hcomp

/-- The radial profile `bRadial` vanishes at the origin. -/
public theorem bRadial_zero : bRadial 0 = 0 := by
  /- Paper: `b(0)=0`. -/
  rw [SpecialValuesAux.bRadial_eq (r := 0)]
  simpa using! SpecialValuesAux.bProfile_zero

/-- The radial profile `bRadial` vanishes at `r = √2`. -/
public theorem bRadial_sqrtTwo : bRadial (Real.sqrt 2) = 0 := by
  /- Paper: `b(√2)=0`. -/
  rw [SpecialValuesAux.bRadial_eq (r := Real.sqrt 2)]
  simpa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))] using! SpecialValuesAux.bProfile_two

/-! ### Derivatives -/

/-- `bRadial` has derivative `928 * π * √2 * I` at `r = √2`. -/
public theorem bRadial_hasDerivAt_sqrtTwo :
    HasDerivAt bRadial ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I) (Real.sqrt 2) := by
  /- Paper: `b'(√2) = 928 i π √2`. -/
  have hbProfAt :
      HasDerivAt bProfile ((464 : ℝ) * (π : ℝ) * Complex.I) ((Real.sqrt 2) ^ (2 : ℕ)) := by
    simpa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))] using!
      (SpecialValuesAux.bProfile_hasDerivAt_two :
        HasDerivAt bProfile ((464 : ℝ) * (π : ℝ) * Complex.I) (2 : ℝ))
  have h :=
    hasDerivAt_bRadial_of_hasDerivAt_bProfile (r0 := Real.sqrt 2)
      (d := (464 : ℝ) * (π : ℝ) * Complex.I) hbProfAt
  have hmul :
      HasDerivAt bRadial
        (2 * (Real.sqrt 2 : ℂ) * ((464 : ℝ) * (π : ℝ) * Complex.I)) (Real.sqrt 2) := by
    simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using! h
  have hconst :
      2 * (Real.sqrt 2 : ℂ) * ((464 : ℝ) * (π : ℝ) * Complex.I) =
        ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I) := by
    simp [mul_assoc, mul_left_comm, mul_comm]
    ring_nf
  rw [← hconst]
  exact hmul

/-- The radial profile `bRadial` vanishes at `r = 2`. -/
public theorem bRadial_two : bRadial 2 = 0 := by
  /- Paper: `b(2)=0`. -/
  rw [SpecialValuesAux.bRadial_eq (r := 2)]
  have h : (2 : ℝ) ^ 2 = 4 := by norm_num
  simpa [h] using! SpecialValuesAux.bProfile_four

/-- `bRadial` has derivative `-8 * π * I` at `r = 2`. -/
public theorem bRadial_hasDerivAt_two :
    HasDerivAt bRadial ((-8 : ℝ) * (π : ℝ) * Complex.I) 2 := by
  /- Paper: `b'(2) = -8 π i`. -/
  have hbProfAt :
      HasDerivAt bProfile ((-2 : ℝ) * (π : ℝ) * Complex.I) ((2 : ℝ) ^ (2 : ℕ)) := by
    have hsq : ((2 : ℝ) ^ (2 : ℕ)) = (4 : ℝ) := by norm_num
    simpa [hsq] using!
      (SpecialValuesAux.bProfile_hasDerivAt_four :
        HasDerivAt bProfile ((-2 : ℝ) * (π : ℝ) * Complex.I) (4 : ℝ))
  have h :=
    hasDerivAt_bRadial_of_hasDerivAt_bProfile (r0 := 2)
      (d := (-2 : ℝ) * (π : ℝ) * Complex.I) hbProfAt
  have hmul :
      HasDerivAt bRadial (-(2 * (2 : ℂ) * ((2 : ℝ) * (π : ℝ) * Complex.I))) 2 := by
    simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using! h
  have hconst :
      (-(2 * (2 : ℂ) * ((2 : ℝ) * (π : ℝ) * Complex.I))) = ((-8 : ℝ) * (π : ℝ) * Complex.I) := by
    simp [mul_left_comm, mul_comm]
    norm_num
  rw [← hconst]
  exact hmul


end

end SpherePacking.Dim24
