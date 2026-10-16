-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12CurveIntegrals
public import SpherePacking.Contour.Segments
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.ForMathlib.GaussianFourierCommon
import Mathlib.Tactic.Ring.RingNF


/-!
# Fourier kernels for `I₁` and `I₂`

This file defines the kernels that appear when rewriting the Fourier transforms of `I₁` and `I₂`
as iterated `(x,t)` integrals, and evaluates the inner integrals in terms of `Φ₁_fourier`.

## Main definitions
* `permI1Kernel`, `permI2Kernel`

## Main statements
* `integral_permI1Kernel_x`
* `integral_permI2Kernel_x`
-/

open Complex Real

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.AFourier
open MeasureTheory Set Complex Real Filter
open SpherePacking.ForMathlib
open SpherePacking.Contour
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold

noncomputable section

open MagicFunction.Parametrisations
open scoped Interval


open MeasureTheory Set Complex Real

/-- The integrand in the `(x,t)` representation of the Fourier transform of `I₁`. -/
@[expose] public def permI1Kernel (w : ℝ²⁴) : ℝ²⁴ × ℝ → ℂ :=
  fun p =>
    cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) * ((I : ℂ) * Φ₁' (‖p.1‖ ^ 2) (z₁line p.2))

/-- The integrand in the `(x,t)` representation of the Fourier transform of `I₂`. -/
@[expose] public def permI2Kernel (w : ℝ²⁴) : ℝ²⁴ × ℝ → ℂ :=
  fun p =>
    cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) * (Φ₁' (‖p.1‖ ^ 2) (z₂line p.2))

/-- Evaluate `∫ permI1Kernel w (x,t) dx` as the Fourier-modified integrand `Φ₁_fourier`. -/
public lemma integral_permI1Kernel_x (w : ℝ²⁴) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ²⁴, permI1Kernel w (x, t)) =
      (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
  have hz : 0 < (z₁line t).im := by
    simpa using! (SpherePacking.Contour.z₁line_im_pos_Ioc (t := t) ht)
  let c : ℂ := (I : ℂ) * (varphi' (-1 / (z₁line t + 1)) * (z₁line t + 1) ^ (10 : ℕ))
  have hfactor :
      (fun x : ℝ²⁴ => permI1Kernel w (x, t)) =
        fun x : ℝ²⁴ =>
          c *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₁line t)) := by
    funext x
    dsimp [permI1Kernel, Φ₁', mul_assoc, c]
    ac_rfl
  calc
    (∫ x : ℝ²⁴, permI1Kernel w (x, t)) =
        ∫ x : ℝ²⁴,
            c *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₁line t)) := by
          simpa using! congrArg (fun F : ℝ²⁴ → ℂ => ∫ x : ℝ²⁴, F x) hfactor
    _ =
        c * ((((I : ℂ) / (z₁line t)) ^ (12 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z₁line t))) := by
          simpa using!
            (SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
              (k := 12) (w := w) (z := z₁line t) hz (c := c))
    _ = (I : ℂ) * Φ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
          simp [c, Φ₁_fourier, mul_assoc, mul_left_comm, mul_comm]

/-- Evaluate `∫ permI2Kernel w (x,t) dx` as the Fourier-modified integrand `Φ₁_fourier`. -/
public lemma integral_permI2Kernel_x (w : ℝ²⁴) (t : ℝ) :
    (∫ x : ℝ²⁴, permI2Kernel w (x, t)) =
      Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
  have hz : 0 < (z₂line t).im := by simp
  let c : ℂ := varphi' (-1 / (z₂line t + 1)) * (z₂line t + 1) ^ (10 : ℕ)
  have hfactor :
      (fun x : ℝ²⁴ => permI2Kernel w (x, t)) =
        fun x : ℝ²⁴ =>
          c *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₂line t)) := by
    funext x
    dsimp [permI2Kernel, Φ₁', mul_assoc, c]
    ac_rfl
  calc
    (∫ x : ℝ²⁴, permI2Kernel w (x, t)) =
        ∫ x : ℝ²⁴,
            c *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * z₂line t)) := by
          simpa using! congrArg (fun F : ℝ²⁴ → ℂ => ∫ x : ℝ²⁴, F x) hfactor
    _ =
        c * ((((I : ℂ) / (z₂line t)) ^ (12 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / z₂line t))) := by
          simpa using!
            (SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
              (k := 12) (w := w) (z := z₂line t) hz (c := c))
    _ = Φ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
          simp [c, Φ₁_fourier, mul_assoc, mul_left_comm, mul_comm]


end

end SpherePacking.Dim24.AFourier
