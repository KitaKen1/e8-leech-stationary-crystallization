-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Prelude
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.ForMathlib.ExpBounds
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity
import SpherePacking.Integration.SmoothIntegralCommon


/-!
# Smoothness and decay of `I₄'`

This file proves smoothness and one-sided Schwartz decay bounds for the integral
`RealIntegrals.I₄'`.

## Main statements
* `Schwartz.I4Smooth.contDiff_I₄'`
* `Schwartz.I4Smooth.decay_I₄'`
-/

section

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

namespace Schwartz

open MeasureTheory Filter Topology

namespace I4Smooth

open RealIntegrals
open MagicFunction.Parametrisations
open Complex Real Set MeasureTheory Filter intervalIntegral
open scoped Interval
open SpherePacking.ForMathlib SpherePacking.Integration

private def coeff (t : ℝ) : ℂ := ((Real.pi : ℂ) * Complex.I) * z₄' t

private def h (t : ℝ) : ℂ :=
  (-1 : ℂ) * (varphi' (-1 / (z₄' t - 1)) * (z₄' t - 1) ^ (10 : ℕ))

private lemma I₄'_eq_integral (x : ℝ) :
    RealIntegrals.I₄' x = SmoothIntegralCommon.I (coeff := coeff) (hf := h) 0 x := by
  simp [RealIntegrals.I₄', RealIntegrals.RealIntegrands.Φ₄, RealIntegrals.ComplexIntegrands.Φ₄',
    RealIntegrals.ComplexIntegrands.Φ₃', SmoothIntegralCommon.I,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, h, coeff, mul_assoc, mul_left_comm,
    mul_comm]

private lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * Real.pi := by
  simpa [coeff] using!
    (SpherePacking.ForMathlib.norm_mul_pi_I_le_two_pi (z := z₄' t) (hz := norm_z₄'_le_two t))

private lemma im_neg_one_div_sub_one_z₄'_pos (t : ℝ) : 0 < (-1 / (z₄' t - 1)).im := by
  -- `z₄' t - 1 = -u + I` with imaginary part `1`.
  set u : ℝ := max 0 (min 1 t) with hu
  have hz : z₄' t - 1 = (-u : ℂ) + (Complex.I : ℂ) := by
    have : z₄' t = (1 : ℂ) - (u : ℂ) + (Complex.I : ℂ) := by
      simp [z₄', Set.IccExtend_apply, z₄, hu]
    simp [this, sub_eq_add_neg, add_left_comm, add_comm]
  have him : 0 < (((-u : ℂ) + (Complex.I : ℂ)).im) := by simp
  simpa [hz] using!
    SpherePacking.Integration.im_neg_one_div_pos_of_im_pos (w := (-u : ℂ) + Complex.I) him

private lemma continuous_h_explicit : Continuous h := by
  have hz : Continuous fun t : ℝ => (-1 : ℂ) / (z₄' t - 1) := by
    have hden : Continuous fun t : ℝ => (z₄' t - 1 : ℂ) := continuous_z₄'.sub continuous_const
    have hden0 : ∀ t : ℝ, (z₄' t - 1 : ℂ) ≠ 0 := by
      intro t
      set u : ℝ := max 0 (min 1 t) with hu
      have hz' : z₄' t - 1 = (-u : ℂ) + (Complex.I : ℂ) := by
        have : z₄' t = (1 : ℂ) - (u : ℂ) + (Complex.I : ℂ) := by
          simp [z₄', Set.IccExtend_apply, z₄, hu]
        simp [this, sub_eq_add_neg, add_left_comm, add_comm]
      intro h0
      have hIm : ((-u : ℂ) + (Complex.I : ℂ)).im = 0 := by
        simpa [hz'] using! congrArg Complex.im h0
      have h10 : (1 : ℝ) = 0 := by
        calc
          (1 : ℝ) = ((-u : ℂ) + (Complex.I : ℂ)).im := by simp
          _ = 0 := hIm
      exact one_ne_zero h10
    exact continuous_const.div hden hden0
  have hvarphi' :
      Continuous fun t : ℝ => varphi' ((-1 : ℂ) / (z₄' t - 1)) :=
    SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
      (ψT := varphi) (ψT' := varphi') VarphiExpBounds.continuous_varphi hz
      (fun t => by simpa using! im_neg_one_div_sub_one_z₄'_pos t)
      (fun t =>
        varphi'_def ((fun t => im_neg_one_div_sub_one_z₄'_pos t) t))
  have hpow : Continuous fun t : ℝ => (z₄' t - 1) ^ (10 : ℕ) :=
    (continuous_z₄'.sub continuous_const).pow 10
  have hEq :
      (fun t : ℝ =>
          -(varphi' ((-1 : ℂ) / (z₄' t - 1)) * (z₄' t - 1) ^ (10 : ℕ))) = h := by
    funext t
    simp [h]
  rw [← hEq]
  exact (hvarphi'.mul hpow).neg

private lemma continuous_coeff : Continuous coeff :=
  continuous_const.mul continuous_z₄'

/-- Smoothness of `I₄'`. -/
public theorem contDiff_I₄' : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₄' := by
  have hContinuous : Continuous h :=
    continuous_h_explicit
  have hexists_bound_norm_h :
      ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖h t‖ ≤ M := by
    simpa using!
      (SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous (f := h) hContinuous)
  refine
    (SmoothIntegralCommon.contDiff_of_eq_I0 (coeff := coeff) (hf := h)
      (f := RealIntegrals.I₄') (hfEq := ?_)
      hContinuous continuous_coeff hexists_bound_norm_h coeff_norm_le)
  intro x
  simpa using! I₄'_eq_integral (x := x)

/-- One-sided Schwartz decay of `I₄'` on the ray `0 ≤ x`. -/
public theorem decay_I₄' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₄' x‖ ≤ C := by
  have hContinuous : Continuous h :=
    continuous_h_explicit
  have hexists_bound_norm_h :
      ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖h t‖ ≤ M := by
    simpa using!
      (SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous (f := h) hContinuous)
  have coeff_re (t : ℝ) : (coeff t).re = (-Real.pi : ℝ) := by
    have hzIm : (z₄' t).im = (1 : ℝ) := by
      simp [z₄', Set.IccExtend_apply, z₄]
    calc
      (coeff t).re = (Real.pi : ℝ) * (-(z₄' t).im) := by
        simp [coeff, mul_assoc, Complex.mul_re]
      _ = (-Real.pi : ℝ) := by simp [hzIm]
  refine
    (SmoothIntegralCommon.decay_of_eq_I0_of_coeff_re (coeff := coeff) (hf := h)
      (f := RealIntegrals.I₄') (hfEq := ?_)
      hContinuous continuous_coeff hexists_bound_norm_h coeff_norm_le coeff_re)
  intro x
  simpa using! I₄'_eq_integral (x := x)

end Schwartz.I4Smooth
end

end SpherePacking.Dim24

end
