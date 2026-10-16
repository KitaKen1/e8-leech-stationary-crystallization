-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
import SpherePacking.Dim24.ModularForms.Psi.Relations
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.Integration.SmoothIntegralCommon
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity

/-!
# Smoothness and one-sided Schwartz decay for `RealIntegrals.J₄'`

This follows the `J₂'` proof: differentiate under the integral sign and use `Im(z₄' t) = 1` to
extract the exponential factor `exp(-π x)` for `x ≥ 0`.

## Main statements
* `Schwartz.J4Smooth.contDiff_J₄'`
* `Schwartz.J4Smooth.decay_J₄'`
-/

noncomputable section

namespace SpherePacking.Dim24.Schwartz.J4Smooth

open scoped Interval UpperHalfPlane

open Complex Real Set MeasureTheory intervalIntegral
open UpperHalfPlane

open MagicFunction.Parametrisations
open RealIntegrals

def coeff (t : ℝ) : ℂ := ((Real.pi : ℂ) * (Complex.I : ℂ)) * z₄' t

def hf (t : ℝ) : ℂ := (-1 : ℂ) * ψT' (z₄' t)

lemma im_z₄'_pos (t : ℝ) : 0 < (z₄' t).im := by
  simpa using! (MagicFunction.Parametrisations.im_z₄'_pos_all t)

lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * Real.pi := by
  simpa [coeff, mul_assoc] using!
    (SpherePacking.ForMathlib.norm_mul_pi_I_le_two_pi (z := z₄' t) (hz := norm_z₄'_le_two t))

lemma continuous_ψT'_z₄' : Continuous fun t : ℝ => ψT' (z₄' t) := by
  refine
    SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
      (ψT := ψT) (ψT' := ψT') (SpherePacking.Dim24.continuous_ψT)
      (z := z₄') continuous_z₄' im_z₄'_pos ?_
  intro t
  simp [ψT', im_z₄'_pos]

lemma continuous_coeff : Continuous coeff := by
  simpa [coeff] using! (continuous_const.mul continuous_z₄')

lemma exists_bound_norm_ψT'_z₄' :
    ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖ψT' (z₄' t)‖ ≤ M := by
  simpa using!
    (SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous
      (f := fun t : ℝ => ψT' (z₄' t)) continuous_ψT'_z₄')

/-- The contour-integral term `J₄'` is smooth on `ℝ`. -/
public theorem contDiff_J₄' : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.J₄' := by
  have hhf : Continuous hf := by
    simpa [hf] using! (continuous_const.mul continuous_ψT'_z₄')
  have hexists : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M := by
    simpa [hf] using! exists_bound_norm_ψT'_z₄'
  refine
    (SpherePacking.Integration.SmoothIntegralCommon.contDiff_of_eq_I0
      (coeff := coeff) (hf := hf) (f := RealIntegrals.J₄') (hfEq := ?_)
      hhf continuous_coeff hexists coeff_norm_le)
  intro x
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₄', hf, coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

/-- One-sided Schwartz decay for `J₄'` on `x ≥ 0`. -/
public theorem decay_J₄' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₄' x‖ ≤ C := by
  have hhf : Continuous hf := by
    simpa [hf] using! (continuous_const.mul continuous_ψT'_z₄')
  have hexists : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M := by
    simpa [hf] using! exists_bound_norm_ψT'_z₄'
  refine
    (SpherePacking.Integration.SmoothIntegralCommon.decay_of_eq_I0_of_coeff_re
      (coeff := coeff) (hf := hf) (f := RealIntegrals.J₄') (hfEq := ?_)
      hhf continuous_coeff hexists coeff_norm_le
      (coeff_re := fun t => by simp [coeff, mul_assoc, Complex.mul_re, im_z₄'_eq_one t]))
  intro x
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₄', hf, coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

end SpherePacking.Dim24.Schwartz.J4Smooth

end
