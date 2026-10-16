-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12Measurability
import SpherePacking.Contour.Segments
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import Mathlib.Tactic.Ring.RingNF
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.Integration.EndpointIntegrability
import SpherePacking.ForMathlib.GaussianRexpIntegral


/-!
# Integrability for the `I₁/I₂` kernels

This file proves integrability estimates for the kernels `permI1Kernel` and `permI2Kernel`
needed to justify Fubini/Tonelli in the Fourier permutation argument.

## Main statements
* `integrable_phase_mul_gaussian`
* `ae_integrable_permI1Kernel_slice`, `ae_integrable_permI2Kernel_slice`
* `integrable_integral_norm_permI1Kernel`
-/

open Complex Real

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.AFourier
open MeasureTheory Set Complex Real Filter
open SpherePacking.ForMathlib
open SpherePacking.Integration (μIoc01)
open SpherePacking.Contour
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold

noncomputable section

open MagicFunction.Parametrisations
open scoped Interval

/-- Integrability of a Gaussian times the Fourier phase factor in `ℝ²⁴`. -/
public lemma integrable_phase_mul_gaussian (w : ℝ²⁴) (z : ℂ) (hz : 0 < z.im) :
    Integrable
      (fun x : ℝ²⁴ =>
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
          cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z))
      (volume : Measure ℝ²⁴) := by
  simpa [mul_assoc] using!
    (SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul (V := ℝ²⁴) z hz).bdd_mul
      (aestronglyMeasurable_phase (w := w)) (ae_norm_phase_le_one (w := w))

lemma integral_rexp_neg_pi_mul_sq_norm (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ²⁴, rexp (-Real.pi * (‖x‖ ^ 2) * t)) = (1 / t) ^ (12 : ℕ) := by
  simpa [div_eq_mul_inv, one_div, mul_assoc, mul_comm] using!
    (SpherePacking.ForMathlib.integral_gaussian_rexp_even (k := 12) (s := (1 / t))
      (one_div_pos.2 ht))

lemma norm_permI1Kernel (w : ℝ²⁴) (x : ℝ²⁴) (t : ℝ) :
    ‖permI1Kernel w (x, t)‖ =
      ‖varphi' (-1 / (z₁line t + 1))‖ * ‖(z₁line t + 1) ^ (10 : ℕ)‖ *
        rexp (-Real.pi * (‖x‖ ^ 2) * t) := by
  calc
    ‖permI1Kernel w (x, t)‖ = ‖Φ₁' (‖x‖ ^ 2) (z₁line t)‖ := by
      simpa [permI1Kernel, mul_assoc] using!
        (norm_phase_mul (w := w) (x := x) (z := (I : ℂ) * Φ₁' (‖x‖ ^ 2) (z₁line t)))
    _ = ‖varphi' (-1 / (z₁line t + 1))‖ * ‖(z₁line t + 1) ^ (10 : ℕ)‖ *
          ‖cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * z₁line t)‖ := by
          simp [Φ₁']
    _ = ‖varphi' (-1 / (z₁line t + 1))‖ * ‖(z₁line t + 1) ^ (10 : ℕ)‖ *
          rexp (-Real.pi * (‖x‖ ^ 2) * t) := by
          rw [norm_cexp_pi_mul_I_mul_sq (z := z₁line t) (x := x)]
          simp [mul_assoc, mul_comm]

lemma integrable_permI1Kernel_slice (w : ℝ²⁴) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x : ℝ²⁴ ↦ permI1Kernel w (x, t)) (volume : Measure ℝ²⁴) := by
  have hz : 0 < (z₁line t).im := by simpa using! (z₁line_im_pos_Ioc (t := t) ht)
  let c : ℂ := (I : ℂ) * (varphi' (-1 / (z₁line t + 1)) * (z₁line t + 1) ^ (10 : ℕ))
  refine ((integrable_phase_mul_gaussian (w := w) (z := z₁line t) hz).const_mul c).congr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp [permI1Kernel, Φ₁', c, mul_assoc]
  ac_rfl

lemma integrable_permI2Kernel_slice (w : ℝ²⁴) (t : ℝ) :
    Integrable (fun x : ℝ²⁴ ↦ permI2Kernel w (x, t)) (volume : Measure ℝ²⁴) := by
  have hz : 0 < (z₂line t).im := by simp
  let c : ℂ := varphi' (-1 / (z₂line t + 1)) * (z₂line t + 1) ^ (10 : ℕ)
  refine ((integrable_phase_mul_gaussian (w := w) (z := z₂line t) hz).const_mul c).congr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp [permI2Kernel, Φ₁', c, mul_assoc]
  ac_rfl

/-- For almost every `t ∈ (0, 1]`, the slice `x ↦ permI1Kernel w (x,t)` is integrable. -/
public lemma ae_integrable_permI1Kernel_slice (w : ℝ²⁴) :
    (∀ᵐ t : ℝ ∂μIoc01,
      Integrable (fun x : ℝ²⁴ ↦ permI1Kernel w (x, t)) (volume : Measure ℝ²⁴)) := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t ht => ?_
  exact integrable_permI1Kernel_slice (w := w) (t := t) ht

/-- For almost every `t ∈ (0, 1]`, the slice `x ↦ permI2Kernel w (x,t)` is integrable. -/
public lemma ae_integrable_permI2Kernel_slice (w : ℝ²⁴) :
    (∀ᵐ t : ℝ ∂μIoc01,
      Integrable (fun x : ℝ²⁴ ↦ permI2Kernel w (x, t)) (volume : Measure ℝ²⁴)) := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall fun t _ => ?_
  exact integrable_permI2Kernel_slice (w := w) (t := t)

lemma integral_norm_permI1Kernel (w : ℝ²⁴) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ²⁴, ‖permI1Kernel w (x, t)‖) =
      ‖varphi' (-1 / (z₁line t + 1))‖ * (1 / t ^ (2 : ℕ)) := by
  have hnorm :
      (fun x : ℝ²⁴ => ‖permI1Kernel w (x, t)‖) =
        fun x : ℝ²⁴ =>
          (‖varphi' (-1 / (z₁line t + 1))‖ * t ^ (10 : ℕ)) *
            rexp (-Real.pi * (‖x‖ ^ 2) * t) := by
    funext x
    have hpowz : ‖(z₁line t + 1) ^ (10 : ℕ)‖ = t ^ (10 : ℕ) := by
      simp [Complex.norm_real, abs_of_nonneg ht.1.le]
    simpa only [hpowz] using! (norm_permI1Kernel (w := w) (x := x) (t := t))
  rw [hnorm, MeasureTheory.integral_const_mul, integral_rexp_neg_pi_mul_sq_norm (t := t) ht.1]
  grind only [= mem_Ioc]

lemma aestronglyMeasurable_integral_norm_permI1Kernel (w : ℝ²⁴) :
    AEStronglyMeasurable (fun t : ℝ ↦ ∫ x : ℝ²⁴, ‖permI1Kernel w (x, t)‖) μIoc01 := by
  simpa using!
    (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := μIoc01) (ν := (volume : Measure ℝ²⁴))
      ((permI1Kernel_measurable (w := w)).norm.prod_swap))

lemma norm_varphi'_neg_one_div_z₁line_add_one_le {Cφ : ℝ}
    (hCφ : ∀ t : ℝ, 1 ≤ t → ‖varphi.resToImagAxis t‖ ≤ Cφ * rexp (-(2 * Real.pi) * t))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖varphi' (-1 / (z₁line t + 1))‖ ≤ Cφ * rexp (-(2 * Real.pi) / t) := by
  have hs : 1 ≤ (1 / t : ℝ) := one_le_one_div ht.1 ht.2
  have h := (congrArg norm (varphi'_neg_one_div_z₁line_add_one_eq t ht)).symm ▸ hCφ (1 / t) hs
  simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using! h

/-- Integrability of `t ↦ ∫ ‖permI1Kernel w (x,t)‖ dx` on `t ∈ (0, 1]`. -/
public lemma integrable_integral_norm_permI1Kernel (w : ℝ²⁴) :
    Integrable (fun t : ℝ ↦ ∫ x : ℝ²⁴, ‖permI1Kernel w (x, t)‖) μIoc01 := by
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ, hCφ⟩
  have hmajor :
      Integrable
        (fun t : ℝ ↦ (Cφ : ℝ) * ((1 / t ^ 2) * rexp (-(2 * Real.pi) / t))) μIoc01 := by
    simpa [μIoc01, IntegrableOn, mul_assoc] using!
      (SpherePacking.Integration.integrableOn_one_div_sq_mul_exp_neg_div
        (c := 2 * Real.pi) (by positivity [Real.pi_pos])).const_mul (Cφ : ℝ)
  refine Integrable.mono' hmajor (aestronglyMeasurable_integral_norm_permI1Kernel (w := w)) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
  intro t ht
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)),
    integral_norm_permI1Kernel (w := w) (t := t) ht]
  simpa [mul_assoc, mul_left_comm, mul_comm] using!
    mul_le_mul_of_nonneg_right
      (norm_varphi'_neg_one_div_z₁line_add_one_le (hCφ := hCφ) (t := t) ht)
      (by positivity : 0 ≤ (1 / t ^ (2 : ℕ) : ℝ))


end

end SpherePacking.Dim24.AFourier
