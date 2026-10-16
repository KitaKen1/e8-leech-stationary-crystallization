-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Prelude
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity


/-!
# Setup for `I₁'`

This file introduces the kernel functions used to express `RealIntegrals.I₁'` as an integral on
`(0, 1)`.

## Main definitions
* `coeff`, `h`, `g`, `gN`

## Main statements
* `I₁'_eq_integral`
* `coeff_norm_le`
* `exists_bound_norm_h`
-/

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

namespace Schwartz

open MeasureTheory Filter Topology

namespace I1Smooth


open RealIntegrals
open MagicFunction.Parametrisations
open Complex Real Set MeasureTheory Filter intervalIntegral
open scoped Interval

/-- Coefficient appearing in the exponential kernel. -/
@[expose] public def coeff (t : ℝ) : ℂ := ((Real.pi : ℂ) * (Complex.I : ℂ)) * z₁' t

/-- The non-exponential part of the integrand for `I₁'` (along the contour piece `z₁'`). -/
@[expose] public def h (t : ℝ) : ℂ :=
  (Complex.I : ℂ) * (varphi' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ (10 : ℕ))

/-- The integrand for `I₁'`, written as `h t * exp(x * coeff t)`. -/
@[expose] public def g (x t : ℝ) : ℂ := h t * cexp ((x : ℂ) * coeff t)

/-- Kernel used for differentiating under the integral sign: `(coeff t)^n * g x t`. -/
@[expose] public def gN (n : ℕ) (x t : ℝ) : ℂ := (coeff t) ^ n * g x t

/-- Rewrite `I₁'` as an integral of the kernel `g`. -/
public lemma I₁'_eq_integral (x : ℝ) : RealIntegrals.I₁' x = ∫ t in (0 : ℝ)..1, g x t := by
  simp [RealIntegrals.I₁', RealIntegrals.RealIntegrands.Φ₁, RealIntegrals.ComplexIntegrands.Φ₁',
    g, h, coeff, mul_assoc, mul_left_comm, mul_comm]

/-- Uniform bound on `‖coeff t‖`, used to control derivatives of the exponential kernel. -/
public lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * Real.pi := by
  simpa [coeff] using!
    (SpherePacking.ForMathlib.norm_mul_pi_I_le_two_pi (z := z₁' t) (hz := norm_z₁'_le_two t))

/-- Identify `varphi' (-1 / (z₁' t + 1))` with `varphi.resToImagAxis (1 / t)` on the interval
`t ∈ (0, 1]`. -/
public lemma varphi'_neg_one_div_z₁'_add_one_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    varphi' (-1 / (z₁' t + 1)) = varphi.resToImagAxis (1 / t) := by
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  have ht0 : 0 < t := ht.1
  have hz : z₁' t + 1 = (Complex.I : ℂ) * (t : ℂ) := by
    have hz1 : z₁' t = (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₁'_eq_of_mem (t := t) htIcc)
    simp [hz1, add_left_comm, add_comm]
  have htne : (t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht0)
  have harg : (-1 / (z₁' t + 1) : ℂ) = (Complex.I : ℂ) * (1 / t : ℂ) := by
    -- `-1 / (I * t) = I * (1 / t)`
    calc
      (-1 / (z₁' t + 1) : ℂ) = (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) := by simp [hz]
      _ = (Complex.I : ℂ) * (1 / t : ℂ) := by
            field_simp [htne, Complex.I_ne_zero]
            simp
  simp [Function.resToImagAxis, ResToImagAxis, varphi', ht0, harg]

/-- Uniform bound on `‖h t‖` on the integration interval `(0, 1)`. -/
public lemma exists_bound_norm_h :
    ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖h t‖ ≤ M := by
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖varphi.resToImagAxis 1‖)
      (b := Real.exp (-(2 * Real.pi) * (1 : ℝ))) (C := C) (norm_nonneg _) (by positivity) ?_
    simpa using! (hC 1 (le_rfl : (1 : ℝ) ≤ 1))
  refine ⟨C, ?_⟩
  intro t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have ht1' : t ≤ 1 := le_of_lt ht1
  have hone : (1 : ℝ) ≤ 1 / t := one_le_one_div ht0 ht1'
  have hvarphi :
      ‖varphi.resToImagAxis (1 / t)‖ ≤ C * Real.exp (-(2 * Real.pi) * (1 / t)) := hC (1 / t) hone
  have hvarphi' : ‖varphi' (-1 / (z₁' t + 1))‖ ≤ C := by
    have htIoc : t ∈ Ioc (0 : ℝ) 1 := ⟨ht0, ht1'⟩
    have hEq : varphi' (-1 / (z₁' t + 1)) = varphi.resToImagAxis (1 / t) :=
      varphi'_neg_one_div_z₁'_add_one_eq (t := t) htIoc
    have hexp : Real.exp (-(2 * Real.pi) * (1 / t)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : 0 ≤ (2 * Real.pi) * (1 / t) := by positivity [le_of_lt ht0]
      linarith
    have hmul : C * Real.exp (-(2 * Real.pi) * (1 / t)) ≤ C := by
      simpa [mul_one] using! (mul_le_mul_of_nonneg_left hexp hC0)
    have hvarphi0 : ‖varphi.resToImagAxis (1 / t)‖ ≤ C := le_trans hvarphi hmul
    simpa [hEq] using! hvarphi0
  have ht0' : 0 ≤ t := le_of_lt ht0
  have hz : z₁' t + 1 = (Complex.I : ℂ) * (t : ℂ) := by
    have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht0', ht1'⟩
    have hz1 : z₁' t = (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₁'_eq_of_mem (t := t) htIcc)
    simp [hz1, add_left_comm, add_comm]
  have hzt : ‖z₁' t + 1‖ = t := by
    simp [hz, Complex.norm_real, abs_of_nonneg ht0']
  have hpow : ‖(z₁' t + 1) ^ (10 : ℕ)‖ = t ^ (10 : ℕ) := by
    calc
      ‖(z₁' t + 1) ^ (10 : ℕ)‖ = ‖z₁' t + 1‖ ^ (10 : ℕ) := by simp [norm_pow]
      _ = t ^ (10 : ℕ) := by simp [hzt]
  have ht10 : t ^ (10 : ℕ) ≤ (1 : ℝ) := by
    have : t ^ (10 : ℕ) ≤ (1 : ℝ) ^ (10 : ℕ) := pow_le_pow_left₀ ht0' ht1' 10
    simpa using! this
  calc
    ‖h t‖ =
        ‖varphi' (-1 / (z₁' t + 1))‖ * ‖(z₁' t + 1) ^ (10 : ℕ)‖ := by
          simp [h]
    _ = ‖varphi' (-1 / (z₁' t + 1))‖ * t ^ (10 : ℕ) := by simp [hpow]
    _ ≤ C * t ^ (10 : ℕ) := by
          have ht10' : 0 ≤ t ^ (10 : ℕ) := by positivity [ht0']
          exact mul_le_mul_of_nonneg_right (a := t ^ (10 : ℕ)) hvarphi' ht10'
    _ ≤ C * 1 :=
          mul_le_mul_of_nonneg_left ht10 hC0
    _ = C := by ring


end Schwartz.I1Smooth
end

end SpherePacking.Dim24
