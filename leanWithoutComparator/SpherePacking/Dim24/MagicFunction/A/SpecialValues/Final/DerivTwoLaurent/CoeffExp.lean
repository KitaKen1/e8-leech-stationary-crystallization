-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Basic

/-!
# Normal form for `coeffExp` at `u = 2`

This file rewrites `SpecialValuesDeriv.coeffExp u` to make the second-order zero at `u = 2`
explicit, in terms of the real `sinc` function.

## Main statements
* `coeffExp_eq_neg_pi_sq_mul_sq_mul_sinc_sq_two`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex

/-- Normal form for `coeffExp` exhibiting the factor `(u - 2)^2` and the `sinc` term. -/
public lemma coeffExp_eq_neg_pi_sq_mul_sq_mul_sinc_sq_two (u : ℝ) :
    SpecialValuesDeriv.coeffExp u =
      (-((Real.pi : ℂ) ^ (2 : ℕ))) * ((u - 2) ^ (2 : ℕ) : ℂ) *
        (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hreal :
      (2 * Real.cos (Real.pi * u) - 2) =
        -(Real.pi ^ (2 : ℕ)) * (u - 2) ^ (2 : ℕ) *
          (Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) := by
    -- `2*cos(πu) - 2 = -4 * sin(πu/2)^2`.
    have hcos2 :
        2 * Real.cos (Real.pi * u) - 2 = -4 * (Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) := by
      set y : ℝ := Real.pi * u / 2
      have hcos : Real.cos (Real.pi * u) = Real.cos (2 * y) := by
        simp [y, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
      have hcos' : Real.cos (2 * y) = 2 * (Real.cos y) ^ (2 : ℕ) - 1 := by
        simpa [pow_two] using! (Real.cos_two_mul y)
      have hsinSq : (Real.sin y) ^ (2 : ℕ) = 1 - (Real.cos y) ^ (2 : ℕ) := by
        have h := Real.sin_sq_add_cos_sq y
        linarith
      calc
        2 * Real.cos (Real.pi * u) - 2
            = 2 * Real.cos (2 * y) - 2 := by simp [hcos]
        _ = 2 * (2 * (Real.cos y) ^ (2 : ℕ) - 1) - 2 := by simp [hcos']
        _ = 4 * (Real.cos y) ^ (2 : ℕ) - 4 := by ring
        _ = -4 * (1 - (Real.cos y) ^ (2 : ℕ)) := by ring
        _ = -4 * (Real.sin y) ^ (2 : ℕ) := by simp [hsinSq]
    -- Shift by `2`: `sin(πu/2)^2 = sin(π(u-2)/2)^2`.
    have hsinPerSq :
        (Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) =
          (Real.sin (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) := by
      have hshift : Real.pi * u / 2 = Real.pi * (u - 2) / 2 + Real.pi := by ring
      -- `sin(x+π) = -sin x`.
      have hsin : Real.sin (Real.pi * u / 2) = -Real.sin (Real.pi * (u - 2) / 2) := by
        simp [hshift]
      -- Square removes the sign.
      simp [hsin, pow_two]
    set x : ℝ := Real.pi * (u - 2) / 2
    have hsinSinc : Real.sin x = x * Real.sinc x := SpecialValuesDeriv.sin_eq_mul_sinc x
    grind only
  -- Cast to `ℂ` and rewrite.
  have hcast :
      (SpecialValuesDeriv.coeffExp u : ℂ) =
        ((-(Real.pi ^ (2 : ℕ)) * (u - 2) ^ (2 : ℕ) *
            (Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp [SpecialValuesDeriv.coeffExp_eq_two_mul_cos_sub_two u, hreal]
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using! hcast

end SpecialValuesDerivTwoLaurent

end

end SpherePacking.Dim24
