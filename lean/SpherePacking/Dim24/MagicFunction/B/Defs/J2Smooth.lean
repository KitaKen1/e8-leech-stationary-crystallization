-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
import SpherePacking.Dim24.ModularForms.Psi.Relations
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.Integration.SmoothIntegralCommon
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity

/-!
# Smoothness and one-sided Schwartz decay for `RealIntegrals.J₂'`

This follows the dimension-8 argument: we differentiate under the integral sign and use
`Im(z₂' t) = 1`, so the exponential kernel contributes `exp(-π x)` for `x ≥ 0`.

## Main statements
* `Schwartz.J2Smooth.contDiff_J₂'`
* `Schwartz.J2Smooth.decay_J₂'`
-/

noncomputable section

namespace SpherePacking.Dim24.Schwartz.J2Smooth

open scoped Interval UpperHalfPlane

open Complex Real Set MeasureTheory intervalIntegral
open UpperHalfPlane
open MagicFunction.Parametrisations
open RealIntegrals

def coeff (t : ℝ) : ℂ := ((Real.pi : ℂ) * (Complex.I : ℂ)) * z₂' t

def hf (t : ℝ) : ℂ := ψT' (z₂' t)

lemma im_z₂'_pos (t : ℝ) : 0 < (z₂' t).im := by
  simpa using! (MagicFunction.Parametrisations.im_z₂'_pos_all t)

lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * Real.pi := by
  simpa [coeff, mul_assoc] using!
    (SpherePacking.ForMathlib.norm_mul_pi_I_le_two_pi (z := z₂' t) (hz := norm_z₂'_le_two t))

lemma continuous_ψT'_z₂' : Continuous fun t : ℝ => ψT' (z₂' t) := by
  refine
    SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
      (ψT := ψT) (ψT' := ψT') (SpherePacking.Dim24.continuous_ψT)
      (z := z₂') continuous_z₂' im_z₂'_pos ?_
  intro t
  simp [ψT', im_z₂'_pos]

lemma continuous_coeff : Continuous coeff := by
  simpa [coeff] using! (continuous_const.mul continuous_z₂')

lemma exists_bound_norm_ψT'_z₂' :
    ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖ψT' (z₂' t)‖ ≤ M := by
  simpa using!
    (SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous
      (f := fun t : ℝ => ψT' (z₂' t)) continuous_ψT'_z₂')

/-- The contour-integral term `J₂'` is smooth on `ℝ`. -/
public theorem contDiff_J₂' : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.J₂' := by
  have hhf : Continuous hf := by
    simpa [hf] using! continuous_ψT'_z₂'
  have hexists : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M := by
    simpa [hf] using! exists_bound_norm_ψT'_z₂'
  refine
    (SpherePacking.Integration.SmoothIntegralCommon.contDiff_of_eq_I0
      (coeff := coeff) (hf := hf) (f := RealIntegrals.J₂') (hfEq := ?_)
      hhf continuous_coeff hexists coeff_norm_le)
  intro x
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₂', hf, coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

/-- One-sided Schwartz decay for `J₂'` on `x ≥ 0`. -/
public theorem decay_J₂' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₂' x‖ ≤ C := by
  have hhf : Continuous hf := by
    simpa [hf] using! continuous_ψT'_z₂'
  have hexists : ∃ M, ∀ t ∈ (Ι (0 : ℝ) 1), ‖hf t‖ ≤ M := by
    simpa [hf] using! exists_bound_norm_ψT'_z₂'
  refine
    (SpherePacking.Integration.SmoothIntegralCommon.decay_of_eq_I0_of_coeff_re
      (coeff := coeff) (hf := hf) (f := RealIntegrals.J₂') (hfEq := ?_)
      hhf continuous_coeff hexists coeff_norm_le
      (coeff_re := fun t => by simp [coeff, mul_assoc, Complex.mul_re, im_z₂'_eq_one t]))
  intro x
  simp [SpherePacking.Integration.SmoothIntegralCommon.I, RealIntegrals.J₂', hf, coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_left_comm, mul_comm]

end SpherePacking.Dim24.Schwartz.J2Smooth

end
