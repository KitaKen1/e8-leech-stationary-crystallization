-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.EvenAProfile.Basic
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.EvenAProfile.AtFour


/-!
# Special values of `aProfile`

This file records the values `aProfile 0`, `aProfile 2`, and `aProfile 4` from `dim_24.tex`.
It also provides a differentiability lemma used later when passing to the radial profile.

## Main statements
* `aProfile_zero`
* `aProfile_two`
* `aProfile_four`
* `differentiableAt_aProfile_of_lt`
-/


namespace SpherePacking.Dim24

noncomputable section

open scoped Real

/-- Special value `aProfile 0` (paper: `113218560 * i / π`). -/
public theorem aProfile_zero : aProfile 0 = (113218560 : ℂ) * Complex.I / (π : ℂ) := by
  have hu : SpecialValuesAux.expU (0 : ℝ) (1 : ℂ) = 1 := by
    simp [SpecialValuesAux.expU]
  have hu0 : (0 : ℝ) ≤ (0 : ℝ) := le_rfl
  have ha := SpecialValuesAux.aProfile_even_eq_periodIntegral_varphi₁ (u := (0 : ℝ)) hu hu0
  -- Rewrite the height-one integrand using `varphi₁'` and `expU 0 = 1`.
  have hEq :
      (∫ x : ℝ in (0 : ℝ)..1,
          (varphi₁ ⟨(x : ℂ) + Complex.I, by simp⟩) *
            Complex.exp (Real.pi * Complex.I * ((0 : ℂ)) * ((x : ℂ) + Complex.I))) =
        ∫ x : ℝ in (0 : ℝ)..1, SpecialValuesAux.varphi₁' ((x : ℂ) + (1 : ℝ) * Complex.I) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp [SpecialValuesAux.varphi₁', Complex.add_im]
  -- Finish.
  rw [ha]
  simpa [hEq] using! SpecialValuesEvenAProfile.integral_varphi₁'_height_one

/-- Special value `aProfile 2` (paper: `725760 * i / π`). -/
public theorem aProfile_two : aProfile (2 : ℝ) = (725760 : ℂ) * Complex.I / (π : ℂ) := by
  have hu : SpecialValuesAux.expU (2 : ℝ) (1 : ℂ) = 1 := by
    simpa [SpecialValuesAux.expU, mul_assoc, mul_left_comm, mul_comm] using!
      (Complex.exp_nat_mul_two_pi_mul_I 1)
  have hu0 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  -- Reduce to the period integral on `im = 1`.
  have ha :=
    SpecialValuesAux.aProfile_even_eq_periodIntegral_varphi₁ (u := (2 : ℝ)) hu hu0
  -- Identify the integrand with `varphi₁' * expU` and use the height-one evaluation.
  have hEq :
      (∫ x : ℝ in (0 : ℝ)..1,
          (varphi₁ ⟨(x : ℂ) + Complex.I, by simp⟩) *
            Complex.exp (Real.pi * Complex.I * ((2 : ℂ)) * ((x : ℂ) + Complex.I))) =
        ∫ x : ℝ in (0 : ℝ)..1,
          SpecialValuesAux.varphi₁' ((x : ℂ) + (1 : ℝ) * Complex.I) *
            SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + (1 : ℝ) * Complex.I) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp [SpecialValuesAux.varphi₁', SpecialValuesAux.expU, Complex.add_im, mul_comm]
  -- Finish.
  rw [ha]
  simpa [hEq] using! SpecialValuesEvenAProfile.integral_varphi₁'_mul_expU_two_height_one

/-- Special value `aProfile 4 = 0` (paper: `a(2) = 0`). -/
public theorem aProfile_four : aProfile (4 : ℝ) = 0 := by
  have hu : SpecialValuesAux.expU (4 : ℝ) (1 : ℂ) = 1 := by
    -- `exp(π i 4) = exp(2 * (2π i)) = 1`.
    have hbase : Complex.exp (Complex.I * ((Real.pi : ℂ) * ((2 : ℂ) * (2 : ℂ)))) = (1 : ℂ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using! (Complex.exp_nat_mul_two_pi_mul_I 2)
    have h22 : (2 : ℂ) * (2 : ℂ) = (4 : ℂ) := by norm_num
    have hbase' : Complex.exp (Complex.I * ((Real.pi : ℂ) * (4 : ℂ))) = (1 : ℂ) := by
      simpa [h22, mul_assoc] using! hbase
    simpa [SpecialValuesAux.expU, mul_assoc, mul_left_comm, mul_comm] using! hbase'
  have hu0 : (0 : ℝ) ≤ (4 : ℝ) := by norm_num
  have ha :=
    SpecialValuesAux.aProfile_even_eq_periodIntegral_varphi₁ (u := (4 : ℝ)) hu hu0
  have hEq :
      (∫ x : ℝ in (0 : ℝ)..1,
          (varphi₁ ⟨(x : ℂ) + Complex.I, by simp⟩) *
            Complex.exp (Real.pi * Complex.I * ((4 : ℂ)) * ((x : ℂ) + Complex.I))) =
        ∫ x : ℝ in (0 : ℝ)..1,
          SpecialValuesAux.varphi₁' ((x : ℂ) + (1 : ℝ) * Complex.I) *
            SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + (1 : ℝ) * Complex.I) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp [SpecialValuesAux.varphi₁', SpecialValuesAux.expU, Complex.add_im, mul_comm]
  rw [ha]
  -- The height-one integral vanishes.
  have h0 := SpecialValuesEvenAProfile.integral_varphi₁'_mul_expU_four_height_one
  simpa [hEq] using! h0

/-- `aProfile` is differentiable at any `x > -1`. -/
public lemma differentiableAt_aProfile_of_lt {x : ℝ} (hx : (-1 : ℝ) < x) :
    DifferentiableAt ℝ aProfile x := by
  have hxIoi : Set.Ioi (-1 : ℝ) ∈ nhds x :=
    isOpen_Ioi.mem_nhds (by simpa [Set.mem_Ioi] using! hx)
  have hI6 : ContDiffAt ℝ (⊤ : ℕ∞) RealIntegrals.I₆' x :=
    (Schwartz.I6Smooth.contDiffOn_I₆'_Ioi_neg1.contDiffAt (x := x) hxIoi)
  have h1 := (Schwartz.I1Smooth.contDiff_I₁'.contDiffAt (x := x))
  have h2 := (Schwartz.I2Smooth.contDiff_I₂'.contDiffAt (x := x))
  have h3 := (Schwartz.I3Smooth.contDiff_I₃'.contDiffAt (x := x))
  have h4 := (Schwartz.I4Smooth.contDiff_I₄'.contDiffAt (x := x))
  have h5 := (Schwartz.I5Smooth.contDiff_I₅'.contDiffAt (x := x))
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞) aProfile x := by
    have h := ((((h1.add h2).add h3).add h4).add h5).add hI6
    assumption
  have hsum' : ContDiffAt ℝ 1 aProfile x := hsum.of_le (by simp)
  exact hsum'.differentiableAt (by simp)

end

end SpherePacking.Dim24
