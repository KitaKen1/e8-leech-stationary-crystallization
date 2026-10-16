-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.F.Zero
public import SpherePacking.ForMathlib.FourierLinearEquiv
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls


/-!
# Constants for `scaledF`

This file evaluates constants needed for the LP bound after scaling, notably the ratio
`scaledF 0 / (𝓕 scaledF) 0` and the volume normalization for the unit ball in `ℝ²⁴`.

## Main statements
* `scaledF_ratio_toNNReal`
* `twoPow24_mul_volume_ball_half`
-/

open scoped FourierTransform ENNReal Real SchwartzMap
open MeasureTheory Metric

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

/-- The key constant after scaling: `scaledF(0)/\widehat{scaledF}(0) = 2^24`. -/
public theorem scaledF_ratio_toNNReal :
    (scaledF 0).re.toNNReal / (𝓕 (⇑scaledF) 0).re.toNNReal = ((2 : ℝ≥0∞) ^ (24 : ℕ)) := by
  /- Proof sketch:
  - show `scaledF 0 = f 0 = 1`;
  - compute `𝓕 scaledF 0 = (2^24)⁻¹ * 𝓕 f 0` by `fourier_comp_linearEquiv`;
  - use `fourier_f_zero` to get `𝓕 f 0 = 1`;
  - rewrite `toNNReal` as `ENNReal.ofReal` as done in `SpherePacking.Dim8.MainTheoremUpperBound`. -/
  -- Rewrite `Real.toNNReal` coerced to `ℝ≥0∞` as `ENNReal.ofReal`.
  change ENNReal.ofReal (scaledF 0).re / ENNReal.ofReal (𝓕 (⇑scaledF) 0).re =
    ((2 : ℝ≥0∞) ^ (24 : ℕ))
  have hscaled0 : scaledF (0 : ℝ²⁴) = 1 := by
    -- `scaledF(0) = f(0)` since scaling fixes the origin, and `f(0)=1`.
    simpa [scaledF] using! (f_zero : f (0 : ℝ²⁴) = 1)
  have hfFourier0 : 𝓕 (⇑f) (0 : ℝ²⁴) = 1 := by
    have h : (𝓕 f) (0 : ℝ²⁴) = 1 := by
      simpa using!
        (fourier_f_zero :
          (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ) f) (0 : ℝ²⁴) = 1)
    simpa [SchwartzMap.fourier_coe] using! h
  -- Use the Fourier scaling lemma for the linear equivalence `x ↦ 2 • x`.
  let A : ℝ²⁴ ≃ₗ[ℝ] ℝ²⁴ :=
    LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ²⁴) (2 : ℝ) (by norm_num)
  have hscaledFun : (⇑scaledF : ℝ²⁴ → ℂ) = fun x : ℝ²⁴ => f ((2 : ℝ) • x) := by
    funext x
    simp [scaledF]
  have hdet :
      LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴) = (2 : ℝ) ^ (24 : ℕ) := by
    have hA : (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴) = (2 : ℝ) • (LinearMap.id : ℝ²⁴ →ₗ[ℝ] ℝ²⁴) := by
      ext x
      simp [A]
    simp_all
  have hdet_abs :
      abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)) = (2 : ℝ) ^ (24 : ℕ) := by
    have hnonneg : 0 ≤ (2 : ℝ) ^ (24 : ℕ) := by positivity
    simp [hdet, abs_of_nonneg hnonneg]
  have hFourierScaled0 :
      𝓕 (⇑scaledF) (0 : ℝ²⁴) =
        (((abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ : ℝ) : ℂ) := by
    have h :=
      (SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv (A := A) (f := (⇑f))
            (w := (0 : ℝ²⁴)))
    have hscaledFunA : (fun x : ℝ²⁴ => f (A x)) = (⇑scaledF : ℝ²⁴ → ℂ) := by
      rfl
    have h' :
        𝓕 (⇑scaledF) (0 : ℝ²⁴) =
          (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ • 𝓕 (⇑f) (0 : ℝ²⁴) := by
      simpa [hscaledFunA] using! (by
        simpa using! h)
    -- Now use `𝓕 f 0 = 1` and compute the determinant.
    calc
      𝓕 (⇑scaledF) (0 : ℝ²⁴) =
          (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ • 𝓕 (⇑f) (0 : ℝ²⁴) := h'
      _ = (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ := by simp [hfFourier0]
  have hFourierScaled0_re :
      (𝓕 (⇑scaledF) (0 : ℝ²⁴)).re = (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ := by
    have hre :
        (𝓕 (⇑scaledF) (0 : ℝ²⁴)).re =
          ((((abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ : ℝ) : ℂ)).re :=
      congrArg Complex.re hFourierScaled0
    exact hre.trans (by rfl)
  have hFourierScaled0_re' :
      (𝓕 (⇑scaledF) (0 : ℝ²⁴)).re = ((2 : ℝ) ^ (24 : ℕ))⁻¹ := by
    have hInv :
        (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ = ((2 : ℝ) ^ (24 : ℕ))⁻¹ :=
      congrArg (fun t : ℝ => t⁻¹) hdet_abs
    simp [hFourierScaled0_re, hInv]
  -- Finish in `ℝ≥0∞`.
  have hnum : ENNReal.ofReal (scaledF (0 : ℝ²⁴)).re = 1 := by
    simp [hscaled0]
  have hden :
      ENNReal.ofReal (𝓕 (⇑scaledF) (0 : ℝ²⁴)).re = ((2 : ℝ≥0∞) ^ (24 : ℕ))⁻¹ := by
    have hpow_pos : 0 < (2 : ℝ) ^ (24 : ℕ) := by positivity
    calc
      ENNReal.ofReal (𝓕 (⇑scaledF) (0 : ℝ²⁴)).re =
          ENNReal.ofReal (((2 : ℝ) ^ (24 : ℕ))⁻¹) := by
            simp [hFourierScaled0_re']
      _ = (ENNReal.ofReal ((2 : ℝ) ^ (24 : ℕ)))⁻¹ :=
            ENNReal.ofReal_inv_of_pos hpow_pos
      _ = ((2 : ℝ≥0∞) ^ (24 : ℕ))⁻¹ := by
            -- `ENNReal.ofReal (2^24) = (2 : ℝ≥0∞)^24`.
            have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
            simp [ENNReal.ofReal_pow hnonneg]
  simp [hnum, hden, div_eq_mul_inv]

/-- Geometric simplification: `2^24 * vol(B(0,1/2)) = vol(B(0,1)) = π^12/12!`. -/
public theorem twoPow24_mul_volume_ball_half :
    ((2 : ℝ≥0∞) ^ (24 : ℕ)) * volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) =
      ENNReal.ofReal π ^ 12 / (Nat.factorial 12) := by
  /- Proof sketch:
  Use `EuclideanSpace.volume_ball` in dimension 24 and simplify:
  `(1/2)^24 * 2^24 = 1`. -/
  -- Use the closed-form even-dimensional volume formula.
  have hk : Module.finrank ℝ ℝ²⁴ = 2 * 12 := by simp [finrank_euclideanSpace]
  have hvol :
      volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) =
        ENNReal.ofReal (1 / 2 : ℝ) ^ (24 : ℕ) *
          ENNReal.ofReal (π ^ (12 : ℕ) / (Nat.factorial 12)) := by
    simpa [hk, finrank_euclideanSpace, mul_assoc, mul_comm, mul_left_comm, pow_mul] using!
      (InnerProductSpace.volume_ball_of_dim_even (E := ℝ²⁴) (k := 12) hk (0 : ℝ²⁴) (1 / 2 : ℝ))
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by simp
  -- Rewrite the constant term to match the statement.
  have hfact_pos : 0 < (Nat.factorial 12 : ℝ) := by
    exact_mod_cast Nat.factorial_pos 12
  have hconst :
      ENNReal.ofReal (π ^ (12 : ℕ) / (Nat.factorial 12)) =
        ENNReal.ofReal π ^ (12 : ℕ) / (Nat.factorial 12) := by
    calc
      ENNReal.ofReal (π ^ (12 : ℕ) / (Nat.factorial 12)) =
          ENNReal.ofReal (π ^ (12 : ℕ)) / ENNReal.ofReal (Nat.factorial 12 : ℝ) :=
            ENNReal.ofReal_div_of_pos hfact_pos
      _ = ENNReal.ofReal π ^ (12 : ℕ) / (Nat.factorial 12) := by
            have hpi : 0 ≤ (π : ℝ) := le_of_lt Real.pi_pos
            simp [ENNReal.ofReal_pow hpi]
  -- Combine everything.
  rw [hvol]
  -- Reassociate and cancel the scaling factor.
  simp only [one_div, Nat.ofNat_pos, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat]
  -- `2^24 * (2⁻¹)^24 = (2 * 2⁻¹)^24 = 1`.
  have hcancel : ((2 : ℝ≥0∞) ^ (24 : ℕ)) * ((2 : ℝ≥0∞)⁻¹ ^ (24 : ℕ)) = 1 := by
    calc
      ((2 : ℝ≥0∞) ^ (24 : ℕ)) * ((2 : ℝ≥0∞)⁻¹ ^ (24 : ℕ)) =
          ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) ^ (24 : ℕ) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using!
              (mul_pow (2 : ℝ≥0∞) ((2 : ℝ≥0∞)⁻¹) (24 : ℕ)).symm
      _ = 1 := by
            have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
            have h2top : (2 : ℝ≥0∞) ≠ ∞ := by simp
            simp [ENNReal.mul_inv_cancel h2 h2top]
  -- Finish.
  rw [← mul_assoc]; simp [hcancel, hconst]

end SpherePacking.Dim24
