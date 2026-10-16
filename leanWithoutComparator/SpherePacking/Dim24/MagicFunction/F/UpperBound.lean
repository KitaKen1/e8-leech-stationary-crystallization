-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.F.RealValued
public import SpherePacking.Dim24.MagicFunction.F.Scaled
public import SpherePacking.Dim24.MagicFunction.F.Constants
public import SpherePacking.CohnElkies.LPBound


/-!
# Upper bound for `SpherePackingConstant 24`

This file proves an upper bound for `SpherePackingConstant 24` via the Cohn-Elkies linear
programming bound, using the scaled auxiliary function `scaledF`.

## Main statement
* `SpherePackingConstant_le_leech_density`
-/

namespace SpherePacking.Dim24

open scoped FourierTransform ENNReal SchwartzMap
open SchwartzMap Complex Real MeasureTheory Metric

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

/-- Upper bound for `SpherePackingConstant 24` obtained from the Cohn-Elkies LP bound
applied to `scaledF`. -/
public theorem SpherePackingConstant_le_leech_density :
    SpherePackingConstant 24 ≤ ENNReal.ofReal π ^ 12 / (Nat.factorial 12) := by
  /- Apply `LinearProgrammingBound` to `scaledF`, then evaluate the constants. -/
  have scaledF_real : ∀ x : ℝ²⁴, (↑(scaledF x).re : ℂ) = scaledF x := by
    intro x
    simpa [scaledF] using! (f_real (x := (2 : ℝ) • x))
  have scaledF_real_fourier :
      ∀ x : ℝ²⁴, (↑((𝓕 scaledF x).re : ℂ)) = (𝓕 scaledF x) := by
    intro x
    have two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
    let A : ℝ²⁴ ≃ₗ[ℝ] ℝ²⁴ :=
      LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ²⁴) (2 : ℝ) two_ne_zero
    let y0 : ℝ²⁴ := (((A.symm : ℝ²⁴ ≃ₗ[ℝ] ℝ²⁴).toLinearMap).adjoint x)
    have hscaled : (⇑scaledF : ℝ²⁴ → ℂ) = fun y : ℝ²⁴ => f (A y) := by
      funext y
      simp [scaledF, A]
    have hfun :
        𝓕 (⇑scaledF) x =
          (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ • 𝓕 (⇑f) y0 := by
      simpa [hscaled, y0] using!
        (SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv (A := A) (f := (⇑f)) (w := x))
    have hScaled :
        (𝓕 scaledF x) =
          (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ • (𝓕 f y0) := by
      assumption
    have hImF : (𝓕 f y0).im = 0 := by
      have h := f_real_fourier (x := y0)
      have him : (FT f y0).im = 0 := by
        simpa using! (congrArg Complex.im h).symm
      assumption
    have hImScaled : (𝓕 scaledF x).im = 0 := by
      have him := congrArg Complex.im hScaled
      simpa [Complex.smul_im, hImF] using! him
    apply Complex.ext <;> simp [hImScaled]
  have hLP :
      SpherePackingConstant 24 ≤
        (scaledF 0).re.toNNReal / (𝓕 (⇑scaledF) 0).re.toNNReal *
          volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) := by
    simpa using!
      (LinearProgrammingBound (d := 24) (f := (scaledF : 𝓢(ℝ²⁴, ℂ)))
        scaledF_ne_zero scaledF_real scaledF_real_fourier
        scaledF_cohnElkies₁ scaledF_cohnElkies₂ (by decide))
  calc
    SpherePackingConstant 24
        ≤ ((2 : ℝ≥0∞) ^ (24 : ℕ)) * volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) := by
            simpa [mul_assoc, scaledF_ratio_toNNReal] using! hLP
    _ = ENNReal.ofReal π ^ 12 / (Nat.factorial 12) := by
          simpa using! twoPow24_mul_volume_ball_half

end SpherePacking.Dim24
