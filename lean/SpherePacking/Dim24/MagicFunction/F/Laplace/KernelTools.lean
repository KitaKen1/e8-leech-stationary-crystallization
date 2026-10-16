-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import SpherePacking.ForMathlib.IntegrablePowMulExp


/-!
# Laplace Kernel Tools

This file collects elementary estimates used in the Laplace-analysis part of the proof.

## Main statements
* `norm_kernelExp`
* `abs_re_sub_le_norm`
* `re_ge_of_mem_ball`
* `integrableOn_pow_mul_exp_neg_mul_Ioi_one`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic

noncomputable section

open scoped Topology

open Complex Filter MeasureTheory Real Set

/-- Compute the norm of the exponential kernel in terms of `u.re`. -/
public lemma norm_kernelExp (u : ℂ) (t : ℝ) :
    ‖Complex.exp (-(Real.pi : ℂ) * u * (t : ℂ))‖ = Real.exp (-Real.pi * u.re * t) := by
  simp [Complex.norm_exp, mul_assoc]

/-- The real-part distance is bounded by the complex norm distance. -/
public lemma abs_re_sub_le_norm (u u0 : ℂ) : |u.re - u0.re| ≤ ‖u - u0‖ := by
  simpa [sub_re] using! (Complex.abs_re_le_norm (u - u0))

/-- If `u` lies in a complex ball around `u0`, then `u.re` is bounded below by `u0.re - r`. -/
public lemma re_ge_of_mem_ball {u u0 : ℂ} {r : ℝ} (hu : u ∈ Metric.ball u0 r) :
    u0.re - r ≤ u.re := by
  have hnorm_lt : ‖u - u0‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg] using! hu
  have hre_lt : |u.re - u0.re| < r := lt_of_le_of_lt (abs_re_sub_le_norm u u0) hnorm_lt
  have : -(r : ℝ) < u.re - u0.re := (abs_lt.1 hre_lt).1
  linarith

/-- Integrability of `t ↦ t ^ n * exp (-b * t)` on the tail `t > 1` for `0 < b`. -/
public lemma integrableOn_pow_mul_exp_neg_mul_Ioi_one (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume := by
  simpa using!
    (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := b) hb).mono_set
      Set.Ioi_subset_Ici_self

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic
