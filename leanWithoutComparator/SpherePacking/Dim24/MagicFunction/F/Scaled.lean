-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
import SpherePacking.Dim24.MagicFunction.F.Zero
import SpherePacking.Dim24.MagicFunction.F.Sign.SignConditions
import SpherePacking.ForMathlib.FourierLinearEquiv


/-!
# Cohn-Elkies hypotheses for `scaledF` (cutoff radius 1)

This file proves the Cohn-Elkies sign conditions for the scaled auxiliary function `scaledF`,
which corresponds to the cutoff radius `1`.

## Main statements
* `scaledF_ne_zero`
* `scaledF_cohnElkies₁`
* `scaledF_cohnElkies₂`
-/

namespace SpherePacking.Dim24

open scoped FourierTransform SchwartzMap

open SchwartzMap Complex Real

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

/-- The scaled auxiliary function `scaledF` is not identically zero. -/
public theorem scaledF_ne_zero : (scaledF : 𝓢(ℝ²⁴, ℂ)) ≠ 0 := by
  /- Proof sketch:
  Evaluate at `0` and use `f_zero`. -/
  intro h
  have h0 : scaledF (0 : ℝ²⁴) = 0 :=
    congrArg (fun g : 𝓢(ℝ²⁴, ℂ) => g (0 : ℝ²⁴)) h
  -- `scaledF 0 = f 0 = 1`.
  simp [scaledF, f_zero] at h0

/-- Cohn-Elkies sign condition for `scaledF`: it is nonpositive outside the unit ball. -/
public theorem scaledF_cohnElkies₁ : ∀ x : ℝ²⁴, ‖x‖ ≥ 1 → (scaledF x).re ≤ 0 := by
  /- Proof sketch:
  `scaledF(x) = f(2x)` and `‖x‖ ≥ 1 ⇒ ‖2x‖ ≥ 2`, then apply `f_cohnElkies₁`. -/
  intro x hx
  have hx2 : (2 : ℝ) ≤ ‖(2 : ℝ) • x‖ := by
    have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    have hn : ‖(2 : ℝ) • x‖ = (2 : ℝ) * ‖x‖ := by
      simp [norm_smul]
    simp_all
  -- Now apply the unscaled sign condition at radius `2`.
  have hf : (f ((2 : ℝ) • x)).re ≤ 0 := f_cohnElkies₁ ((2 : ℝ) • x) hx2
  simpa [scaledF] using! hf

/-- Cohn-Elkies sign condition for `scaledF`: its Fourier transform is nonnegative. -/
public theorem scaledF_cohnElkies₂ : ∀ y : ℝ²⁴, (FT scaledF y).re ≥ 0 := by
  /- Proof sketch:
  Use the Fourier scaling lemma `fourier_comp_linearEquiv` together with `f_cohnElkies₂`. -/
  intro y
  have two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
  let A : ℝ²⁴ ≃ₗ[ℝ] ℝ²⁴ :=
    LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ²⁴) (2 : ℝ) two_ne_zero
  let y0 : ℝ²⁴ := (((A.symm : ℝ²⁴ ≃ₗ[ℝ] ℝ²⁴).toLinearMap).adjoint y)
  have hscaled : (fun x : ℝ²⁴ => scaledF x) = fun x : ℝ²⁴ => f (A x) := by
    funext x
    simp [scaledF, A]
  have hfun :
      𝓕 (fun x : ℝ²⁴ => scaledF x) y =
        (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ • 𝓕 (fun x : ℝ²⁴ => f x) y0 := by
    simpa [hscaled, y0] using!
      (SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv (A := A) (f := (⇑f)) (w := y))
  have hcoeScaled : (FT scaledF y) = 𝓕 (fun x : ℝ²⁴ => scaledF x) y := by
    -- Convert the Schwartz Fourier transform to the function Fourier transform.
    rfl
  have hcoeF : 𝓕 (fun x : ℝ²⁴ => f x) y0 = (FT f) y0 := by
    rfl
  -- Put the scaling identity into `fourierTransformCLE`.
  have hScaled :
      (FT scaledF y) =
        (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ • (FT f) y0 := by
    simp_all
  have hscale : 0 ≤ (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ := by positivity
  have hf0 : 0 ≤ (FT f y0).re := f_cohnElkies₂ y0
  -- Take real parts.
  have hre :
      (FT scaledF y).re =
        (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ * (FT f y0).re := by
    have h := congrArg Complex.re hScaled
    rw [Complex.smul_re] at h
    simpa using! h
  -- Conclude by nonnegativity.
  rw [hre]
  exact mul_nonneg hscale hf0

end SpherePacking.Dim24
