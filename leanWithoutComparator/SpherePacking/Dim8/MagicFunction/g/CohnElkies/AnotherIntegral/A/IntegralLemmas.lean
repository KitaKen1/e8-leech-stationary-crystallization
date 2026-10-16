-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Complex.Basic
import SpherePacking.Integration.Measure
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.AnotherIntegral.A.Core
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.AnotherIntegral.A.Continuation
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.LaplaceA.LaplaceRepresentation
public import Mathlib.MeasureTheory.Integral.IntegrableOn


/-!
# Laplace-type integrals for `AnotherIntegral.A`

This file collects explicit evaluations and integrability facts for basic Laplace-type integrals
on `t > 0`, in the complex-valued form used by the "another integral" representation of `a'`.

## Main statements
* `integral_exp_neg_pi_mul_Ioi_complex`
* `integral_mul_exp_neg_pi_mul_Ioi_complex`
* `integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex`
* `integrableOn_exp_neg_pi_mul_Ioi_complex`
* `integrableOn_mul_exp_neg_pi_mul_Ioi_complex`
* `integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open MeasureTheory Real Complex
open SpherePacking.Integration (μIoi0)

noncomputable section

/-- Integral of a triple sum is the sum of the integrals, under integrability assumptions. -/
public lemma integral_add_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, ((f x + g x) + h x) ∂ μ) =
      (∫ x, f x ∂ μ) + (∫ x, g x ∂ μ) + (∫ x, h x ∂ μ) := by
  calc
    (∫ x, ((f x + g x) + h x) ∂ μ) = (∫ x, (f x + g x) ∂ μ) + ∫ x, h x ∂ μ := by
      simpa [add_assoc] using! MeasureTheory.integral_add (μ := μ) (hf.add hg) hh
    _ = (∫ x, f x ∂ μ) + (∫ x, g x ∂ μ) + ∫ x, h x ∂ μ := by
      rw [MeasureTheory.integral_add (μ := μ) hf hg]

/-- `∫_{t > 0} exp (-π u t) dt = 1 / (π u)` as a complex-valued integral, for `u > 0`. -/
public lemma integral_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) = ((1 / (π * u) : ℝ) : ℂ)
  have hR : (∫ t : ℝ, Real.exp (-π * u * t) ∂μIoi0) = 1 / (π * u) := by
    simpa [μIoi0] using! MagicFunction.g.CohnElkies.integral_exp_neg_pi_mul_Ioi (u := u) hu
  calc
    (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        (↑(∫ t : ℝ, Real.exp (-π * u * t) ∂μIoi0) : ℂ) := by
          simpa using!
            (integral_ofReal (μ := μIoi0) (𝕜 := ℂ) (f := fun t : ℝ => Real.exp (-π * u * t)))
    _ = ((1 / (π * u) : ℝ) : ℂ) := by simpa using! congrArg (fun r : ℝ => (r : ℂ)) hR

/-- `∫_{t > 0} t * exp (-π u t) dt = 1 / (π u)^2` as a complex-valued integral, for `u > 0`. -/
public lemma integral_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (t * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
  change (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
      ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ)
  have hR :
      (∫ t : ℝ, t * Real.exp (-π * u * t) ∂μIoi0) = 1 / (π * u) ^ (2 : ℕ) := by
    simpa [μIoi0] using! MagicFunction.g.CohnElkies.integral_mul_exp_neg_pi_mul_Ioi (u := u) hu
  calc
    (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        (↑(∫ t : ℝ, t * Real.exp (-π * u * t) ∂μIoi0) : ℂ) := by
          simpa [Complex.ofReal_mul] using!
            (integral_ofReal (μ := μIoi0) (𝕜 := ℂ) (f := fun t : ℝ => t * Real.exp (-π * u * t)))
    _ = ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
          simpa using! congrArg (fun r : ℝ => (r : ℂ)) hR

/--
`∫_{t > 0} exp (2π t) * exp (-π u t) dt = 1 / (π (u - 2))` as a complex-valued integral, for
`u > 2`.
-/
public lemma integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 2 < u) :
    (∫ t in Set.Ioi (0 : ℝ), (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) =
      ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
  have hR :
      (∫ t : ℝ, Real.exp (2 * π * t) * Real.exp (-π * u * t) ∂μIoi0) =
        1 / (π * (u - 2)) := by
    simpa [μIoi0] using!
      MagicFunction.g.CohnElkies.integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi (u := u) hu
  have hC :
      (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        (↑(∫ t : ℝ, Real.exp (2 * π * t) * Real.exp (-π * u * t) ∂μIoi0) : ℂ) := by
    simpa [Complex.ofReal_mul] using! (integral_ofReal (μ := μIoi0) (𝕜 := ℂ)
      (f := fun t : ℝ => Real.exp (2 * π * t) * Real.exp (-π * u * t)))
  rw [hR] at hC
  simpa [μIoi0] using! hC

/-- Integrability of `t ↦ exp (-π u t)` on `t > 0` as a complex-valued function, for `u > 0`. -/
public lemma integrableOn_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  have hI :
      (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) = ((1 / (π * u) : ℝ) : ℂ) := by
    simpa [μIoi0] using! integral_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hne : (∫ t : ℝ, (Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [hI]
    exact_mod_cast (one_div_ne_zero (mul_ne_zero Real.pi_ne_zero (ne_of_gt hu)))
  simpa [MeasureTheory.IntegrableOn, μIoi0] using!
    (MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0)
      (f := fun t : ℝ => (Real.exp (-π * u * t) : ℂ)) hne)

/-- Integrability of `t ↦ t * exp (-π u t)` on `t > 0` as a complex-valued function, for
`u > 0`. -/
public lemma integrableOn_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) (Set.Ioi (0 : ℝ)) := by
  have hI :
      (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        ((1 / (π * u) ^ (2 : ℕ) : ℝ) : ℂ) := by
    simpa [μIoi0] using! integral_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hne : (∫ t : ℝ, (t * Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [hI]
    exact_mod_cast
      (one_div_ne_zero (pow_ne_zero (2 : ℕ) (mul_ne_zero Real.pi_ne_zero (ne_of_gt hu))))
  simpa [MeasureTheory.IntegrableOn, μIoi0] using!
    (MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0)
      (f := fun t : ℝ => (t * Real.exp (-π * u * t) : ℂ)) hne)

/--
Integrability of `t ↦ exp (2π t) * exp (-π u t)` on `t > 0` as a complex-valued function, for
`u > 2`.
-/
public lemma integrableOn_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hI :
      (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) =
        ((1 / (π * (u - 2)) : ℝ) : ℂ) := by
    simpa [μIoi0] using! integral_exp_two_pi_mul_exp_neg_pi_mul_Ioi_complex (u := u) hu
  have hne :
      (∫ t : ℝ, (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ) ∂μIoi0) ≠ 0 := by
    rw [hI]
    exact_mod_cast (one_div_ne_zero (mul_ne_zero Real.pi_ne_zero (ne_of_gt (sub_pos.2 hu))))
  simpa [MeasureTheory.IntegrableOn, μIoi0] using!
    (MeasureTheory.Integrable.of_integral_ne_zero (μ := μIoi0)
      (f := fun t : ℝ => (Real.exp (2 * π * t) * Real.exp (-π * u * t) : ℂ)) hne)

end

end MagicFunction.g.CohnElkies.IntegralReps
