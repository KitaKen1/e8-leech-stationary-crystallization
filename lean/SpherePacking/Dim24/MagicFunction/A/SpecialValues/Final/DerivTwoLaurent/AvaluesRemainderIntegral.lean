-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegralDefs
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.LaplaceIntegrals
import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegralDCT
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import SpherePacking.ForMathlib.IntegrablePowMulExp

/-!
# The `eq:avalues` remainder integral

This file evaluates the Laplace transform `pTildeIntegral` of `pPaper` in closed form. In
particular, for `u > 4` (with `u = r^2`), it agrees with the explicit rational function
`pTildeProfile`.

## Main statements
* `pTildeIntegral_eq_pTildeProfile_of_lt`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex MeasureTheory Set

/-!
## Key identity

The key identity is that `pTildeIntegral` agrees with the explicit rational expression
`pTildeProfile`.
-/

/-- For `u > 4`, the Laplace integral defining `pTildeIntegral u` evaluates to `pTildeProfile u`. -/
public theorem pTildeIntegral_eq_pTildeProfile_of_lt {u : ℝ} (hu : 4 < u) :
    pTildeIntegral u = pTildeProfile u := by
  have hu4 : 0 < u - 4 := sub_pos.2 hu
  have hu2 : 0 < u - 2 := by linarith
  have hu0 : 0 < u := by linarith
  have hr4 : 0 < Real.pi * (u - 4) := mul_pos Real.pi_pos hu4
  have hr2 : 0 < Real.pi * (u - 2) := mul_pos Real.pi_pos hu2
  have hr0 : 0 < Real.pi * u := mul_pos Real.pi_pos hu0
  -- Helper: rewrite the complex Laplace integral lemmas to the
  -- `Real.exp`-as-`ℂ` integrands used here.
  have integral_exp_ofReal {r : ℝ} (hr : 0 < r) :
      (∫ t : ℝ in Set.Ioi (0 : ℝ), (Real.exp (-(r * t)) : ℂ)) = (1 : ℂ) / (r : ℂ) := by
    have hfun :
        (fun t : ℝ => Complex.exp (-(r : ℂ) * (t : ℂ))) =
          fun t : ℝ => (Real.exp (-(r * t)) : ℂ) := by
      norm_num
    simpa [hfun] using! (integral_exp_neg_mul_Ioi_complex (r := r) hr)
  have integral_mul_exp_ofReal {r : ℝ} (hr : 0 < r) :
      (∫ t : ℝ in Set.Ioi (0 : ℝ), (t : ℂ) * (Real.exp (-(r * t)) : ℂ)) =
        (1 : ℂ) / (r : ℂ) ^ (2 : ℕ) := by
    have hfun :
        (fun t : ℝ => (t : ℂ) * Complex.exp (-(r : ℂ) * (t : ℂ))) =
          fun t : ℝ => (t : ℂ) * (Real.exp (-(r * t)) : ℂ) := by
      norm_num
    simpa [hfun] using! (integral_mul_exp_neg_mul_Ioi_complex (r := r) hr)
  -- Exponential product simplifications.
  have exp_shift4 (t : ℝ) :
      (Real.exp (4 * Real.pi * t) : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ) =
        (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
    have harg :
        4 * Real.pi * t + (-Real.pi * u * t) = -Real.pi * (u - 4) * t := by ring
    have hreal :
        Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
          Real.exp (-Real.pi * (u - 4) * t) := by
      calc
        Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
            Real.exp (4 * Real.pi * t + (-Real.pi * u * t)) := by
              simpa using! (Real.exp_add (4 * Real.pi * t) (-Real.pi * u * t)).symm
        _ = Real.exp (-Real.pi * (u - 4) * t) := by
              simpa using! congrArg Real.exp harg
    simpa using! congrArg (fun x : ℝ => (x : ℂ)) hreal
  have exp_shift2 (t : ℝ) :
      (Real.exp (2 * Real.pi * t) : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ) =
        (Real.exp (-Real.pi * (u - 2) * t) : ℂ) := by
    have harg :
        2 * Real.pi * t + (-Real.pi * u * t) = -Real.pi * (u - 2) * t := by ring
    have hreal :
        Real.exp (2 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
          Real.exp (-Real.pi * (u - 2) * t) := by
      calc
        Real.exp (2 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
            Real.exp (2 * Real.pi * t + (-Real.pi * u * t)) := by
              simpa using! (Real.exp_add (2 * Real.pi * t) (-Real.pi * u * t)).symm
        _ = Real.exp (-Real.pi * (u - 2) * t) := by
              simpa using! congrArg Real.exp harg
    simpa using! congrArg (fun x : ℝ => (x : ℂ)) hreal
  -- Set up integrability to split the Laplace integral into explicit pieces.
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hint_exp_r4 :
      Integrable (fun t : ℝ => Real.exp (-Real.pi * (u - 4) * t)) μ := by
    have : IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * (u - 4) * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [neg_mul, mul_assoc] using!
        (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) (b := Real.pi * (u - 4)) hr4)
    simpa [IntegrableOn] using! this
  have hint_exp_r2 :
      Integrable (fun t : ℝ => Real.exp (-Real.pi * (u - 2) * t)) μ := by
    have : IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * (u - 2) * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [neg_mul, mul_assoc] using!
        (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) (b := Real.pi * (u - 2)) hr2)
    simpa [IntegrableOn] using! this
  have hint_exp_r0 :
      Integrable (fun t : ℝ => Real.exp (-Real.pi * u * t)) μ := by
    have : IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * u * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [neg_mul, mul_assoc] using!
        (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) (b := Real.pi * u) hr0)
    simpa [IntegrableOn] using! this
  have hint_mul_exp_r2 :
      Integrable (fun t : ℝ => t * Real.exp (-Real.pi * (u - 2) * t)) μ := by
    have :
        IntegrableOn (fun t : ℝ => t * Real.exp (-Real.pi * (u - 2) * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [pow_one] using!
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ioi (n := 1)
          (b := Real.pi * (u - 2)) hr2)
    simpa [IntegrableOn] using! this
  have hint_mul_exp_r0 :
      Integrable (fun t : ℝ => t * Real.exp (-Real.pi * u * t)) μ := by
    have : IntegrableOn (fun t : ℝ => t * Real.exp (-Real.pi * u * t)) (Set.Ioi (0 : ℝ)) := by
      simpa [pow_one] using!
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ioi (n := 1)
          (b := Real.pi * u) hr0)
    simpa [IntegrableOn] using! this
  -- Cast the real integrability facts to complex-valued integrands.
  have hint_exp_r4C :
      Integrable (fun t : ℝ => (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) μ :=
    (Integrable.ofReal (𝕜 := ℂ) (μ := μ) hint_exp_r4)
  have hint_exp_r2C :
      Integrable (fun t : ℝ => (Real.exp (-Real.pi * (u - 2) * t) : ℂ)) μ :=
    (Integrable.ofReal (𝕜 := ℂ) (μ := μ) hint_exp_r2)
  have hint_exp_r0C :
      Integrable (fun t : ℝ => (Real.exp (-Real.pi * u * t) : ℂ)) μ :=
    (Integrable.ofReal (𝕜 := ℂ) (μ := μ) hint_exp_r0)
  have hint_mul_exp_r2C :
      Integrable (fun t : ℝ => ((t * Real.exp (-Real.pi * (u - 2) * t) : ℝ) : ℂ)) μ :=
    (Integrable.ofReal (𝕜 := ℂ) (μ := μ) hint_mul_exp_r2)
  have hint_mul_exp_r0C :
      Integrable (fun t : ℝ => ((t * Real.exp (-Real.pi * u * t) : ℝ) : ℂ)) μ :=
    (Integrable.ofReal (𝕜 := ℂ) (μ := μ) hint_mul_exp_r0)
  -- Define the five Laplace pieces after multiplying by the kernel.
  let g1 : ℝ → ℂ := fun t =>
    (-(864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (-Real.pi * (u - 4) * t) : ℂ)
  let g2 : ℝ → ℂ := fun t =>
    ((725760 : ℂ) / (π : ℂ)) * (t : ℂ) * (Real.exp (-Real.pi * (u - 2) * t) : ℂ)
  let g3 : ℝ → ℂ := fun t =>
    (-(2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (-Real.pi * (u - 2) * t) : ℂ)
  let g4 : ℝ → ℂ := fun t =>
    ((113218560 : ℂ) / (π : ℂ)) * (t : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ)
  let g5 : ℝ → ℂ := fun t =>
    (-(223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (-Real.pi * u * t) : ℂ)
  have hg1 : Integrable g1 μ := by
    simpa [g1] using! hint_exp_r4C.const_mul (-(864 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))
  have hg3 : Integrable g3 μ := by
    simpa [g3] using! hint_exp_r2C.const_mul (-(2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))
  have hg5 : Integrable g5 μ := by
    simpa [g5] using! hint_exp_r0C.const_mul (-(223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))
  have hg2 : Integrable g2 μ := by
    have hbase :
        Integrable (fun t : ℝ => (t : ℂ) * (Real.exp (-Real.pi * (u - 2) * t) : ℂ)) μ := by
      simpa using! hint_mul_exp_r2C
    simpa [g2, mul_assoc] using! hbase.const_mul ((725760 : ℂ) / (π : ℂ))
  have hg4 : Integrable g4 μ := by
    have hbase :
        Integrable (fun t : ℝ => (t : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ)) μ := by
      simpa using! hint_mul_exp_r0C
    simpa [g4, mul_assoc] using! hbase.const_mul ((113218560 : ℂ) / (π : ℂ))
  -- Replace the Laplace integrand by the explicit sum of the five pieces.
  have hdecomp :
      (fun t : ℝ => pPaper t * (Real.exp (-Real.pi * u * t) : ℂ)) =
        fun t : ℝ => g1 t + g2 t + g3 t + g4 t + g5 t := by
    funext t
    have h1 :
        ((-(864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (4 * Real.pi * t) : ℂ)) *
            (Real.exp (-Real.pi * u * t) : ℂ) =
          g1 t := by
      rw [mul_assoc]
      simpa [g1, mul_assoc] using! congrArg (fun z : ℂ => (-(864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * z)
        (exp_shift4 t)
    have h2 :
        (((725760 : ℂ) / (π : ℂ)) * (t : ℂ) * (Real.exp (2 * Real.pi * t) : ℂ)) *
            (Real.exp (-Real.pi * u * t) : ℂ) =
          g2 t := by
      rw [mul_assoc]
      rw [mul_assoc]
      simpa [g2, mul_assoc] using! congrArg (fun z : ℂ => ((725760 : ℂ) / (π : ℂ)) * (t : ℂ) * z)
        (exp_shift2 t)
    have h3 :
        ((-(2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (2 * Real.pi * t) : ℂ)) *
            (Real.exp (-Real.pi * u * t) : ℂ) =
          g3 t := by
      rw [mul_assoc]
      simpa [g3, mul_assoc] using!
        congrArg (fun z : ℂ => (-(2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * z) (exp_shift2 t)
    have h4 :
        (((113218560 : ℂ) / (π : ℂ)) * (t : ℂ)) * (Real.exp (-Real.pi * u * t) : ℂ) =
          g4 t := by
      simp [g4, mul_assoc]
    have h5 :
        (-(223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (-Real.pi * u * t) : ℂ) =
          g5 t := by
      simp [g5]
    have hk :
        (Real.exp (-(Real.pi * u * t)) : ℂ) = (Real.exp (-Real.pi * u * t) : ℂ) := by
      norm_num
    simp [-Complex.ofReal_exp, pPaper, add_mul, h1, h2, h3, h4, h5, hk, add_assoc]
  -- Split the integral using integrability, but keep the sums explicitly left-associated.
  let s12 : ℝ → ℂ := fun t => g1 t + g2 t
  let s123 : ℝ → ℂ := fun t => s12 t + g3 t
  let s1234 : ℝ → ℂ := fun t => s123 t + g4 t
  let s12345 : ℝ → ℂ := fun t => s1234 t + g5 t
  have hs12 : Integrable s12 μ := hg1.add hg2
  have hs123 : Integrable s123 μ := hs12.add hg3
  have hs1234 : Integrable s1234 μ := hs123.add hg4
  have hs12345 : Integrable s12345 μ := hs1234.add hg5
  have hsplit :
      (∫ t : ℝ, s12345 t ∂μ) =
        ((((∫ t : ℝ, g1 t ∂μ) + (∫ t : ℝ, g2 t ∂μ)) + (∫ t : ℝ, g3 t ∂μ)) +
            (∫ t : ℝ, g4 t ∂μ)) +
          (∫ t : ℝ, g5 t ∂μ) := by
    have h5 :
        (∫ t : ℝ, s12345 t ∂μ) = (∫ t : ℝ, s1234 t ∂μ) + (∫ t : ℝ, g5 t ∂μ) := by
      simpa [s12345] using! (MeasureTheory.integral_add (μ := μ) hs1234 hg5)
    have h4 :
        (∫ t : ℝ, s1234 t ∂μ) = (∫ t : ℝ, s123 t ∂μ) + (∫ t : ℝ, g4 t ∂μ) := by
      simpa [s1234] using! (MeasureTheory.integral_add (μ := μ) hs123 hg4)
    have h3 :
        (∫ t : ℝ, s123 t ∂μ) = (∫ t : ℝ, s12 t ∂μ) + (∫ t : ℝ, g3 t ∂μ) := by
      simpa [s123] using! (MeasureTheory.integral_add (μ := μ) hs12 hg3)
    have h2 :
        (∫ t : ℝ, s12 t ∂μ) = (∫ t : ℝ, g1 t ∂μ) + (∫ t : ℝ, g2 t ∂μ) := by
      simpa [s12] using! (MeasureTheory.integral_add (μ := μ) hg1 hg2)
    calc
      (∫ t : ℝ, s12345 t ∂μ) =
          (∫ t : ℝ, s1234 t ∂μ) + (∫ t : ℝ, g5 t ∂μ) := h5
      _ = ((∫ t : ℝ, s123 t ∂μ) + (∫ t : ℝ, g4 t ∂μ)) + (∫ t : ℝ, g5 t ∂μ) := by
            simp [h4, add_assoc]
      _ = (((∫ t : ℝ, s12 t ∂μ) + (∫ t : ℝ, g3 t ∂μ)) + (∫ t : ℝ, g4 t ∂μ)) +
            (∫ t : ℝ, g5 t ∂μ) := by
            simp [h3, add_assoc]
      _ = ((((∫ t : ℝ, g1 t ∂μ) + (∫ t : ℝ, g2 t ∂μ)) + (∫ t : ℝ, g3 t ∂μ)) +
            (∫ t : ℝ, g4 t ∂μ)) +
            (∫ t : ℝ, g5 t ∂μ) := by
            simp [h2, add_assoc]
  -- Compute each piece explicitly and simplify to `pTildeProfile`.
  have hpi0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu4ne : ((u - 4 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.2 (ne_of_gt hu))
  have hu2ne : ((u - 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.2 (ne_of_gt (lt_trans (by linarith : (2 : ℝ) < 4) hu)))
  have hu0ne : ((u : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hu0)
  have Ig1 :
      (∫ t : ℝ, g1 t ∂μ) = ((-864 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 4 : ℝ) : ℂ) := by
    have hbase :
        (∫ t : ℝ, (Real.exp (-Real.pi * (u - 4) * t) : ℂ) ∂μ) =
          (1 : ℂ) / ((Real.pi * (u - 4)) : ℂ) := by
      simpa [-Complex.ofReal_exp, mul_assoc] using!
        (integral_exp_ofReal (r := Real.pi * (u - 4)) hr4)
    calc
      (∫ t : ℝ, g1 t ∂μ) =
          (-(864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) *
            (∫ t : ℝ, (Real.exp (-Real.pi * (u - 4) * t) : ℂ) ∂μ) := by
        simp [-Complex.ofReal_exp, g1, MeasureTheory.integral_const_mul]
      _ = (-(864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * ((1 : ℂ) / ((Real.pi * (u - 4)) : ℂ)) := by
        rw [hbase]
      _ = ((-864 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 4 : ℝ) : ℂ) := by
        field_simp [hpi0, hu4ne]
        have hu4ne' : ((u : ℝ) : ℂ) - (4 : ℂ) ≠ 0 := by simpa using! hu4ne
        simp [hu4ne']
  have Ig3 :
      (∫ t : ℝ, g3 t ∂μ) = ((-2218752 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 2 : ℝ) : ℂ) := by
    have hbase :
        (∫ t : ℝ, (Real.exp (-Real.pi * (u - 2) * t) : ℂ) ∂μ) =
          (1 : ℂ) / ((Real.pi * (u - 2)) : ℂ) := by
      simpa [-Complex.ofReal_exp, mul_assoc] using!
        (integral_exp_ofReal (r := Real.pi * (u - 2)) hr2)
    calc
      (∫ t : ℝ, g3 t ∂μ) =
          (-(2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) *
              (∫ t : ℝ, (Real.exp (-Real.pi * (u - 2) * t) : ℂ) ∂μ) := by
            simp [-Complex.ofReal_exp, g3, MeasureTheory.integral_const_mul]
      _ = (-(2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * ((1 : ℂ) / ((Real.pi * (u - 2)) : ℂ)) := by
            rw [hbase]
      _ = ((-2218752 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 2 : ℝ) : ℂ) := by
        field_simp [hpi0, hu2ne]
        have hu2ne' : ((u : ℝ) : ℂ) - (2 : ℂ) ≠ 0 := by simpa using! hu2ne
        simp [hu2ne']
  have Ig5 :
      (∫ t : ℝ, g5 t ∂μ) = ((-223140096 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u : ℝ) : ℂ) := by
    have hbase :
        (∫ t : ℝ, (Real.exp (-Real.pi * u * t) : ℂ) ∂μ) = (1 : ℂ) / ((Real.pi * u) : ℂ) := by
      simpa [-Complex.ofReal_exp, mul_assoc] using! (integral_exp_ofReal (r := Real.pi * u) hr0)
    calc
      (∫ t : ℝ, g5 t ∂μ) =
          (-(223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) *
              (∫ t : ℝ, (Real.exp (-Real.pi * u * t) : ℂ) ∂μ) := by
            simp [-Complex.ofReal_exp, g5, MeasureTheory.integral_const_mul]
      _ = (-(223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * ((1 : ℂ) / ((Real.pi * u) : ℂ)) := by
            rw [hbase]
      _ = ((-223140096 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u : ℝ) : ℂ) := by
        field_simp [hpi0, hu0ne]
  have Ig2 :
      (∫ t : ℝ, g2 t ∂μ) =
        ((725760 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (((u - 2) ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hbase :
        (∫ t : ℝ, (t : ℂ) * (Real.exp (-Real.pi * (u - 2) * t) : ℂ) ∂μ) =
          (1 : ℂ) / ((Real.pi * (u - 2)) : ℂ) ^ (2 : ℕ) := by
      simpa [-Complex.ofReal_exp, mul_assoc] using!
        (integral_mul_exp_ofReal (r := Real.pi * (u - 2)) hr2)
    calc
      (∫ t : ℝ, g2 t ∂μ) =
          ((725760 : ℂ) / (π : ℂ)) *
              (∫ t : ℝ, (t : ℂ) * (Real.exp (-Real.pi * (u - 2) * t) : ℂ) ∂μ) := by
            simp [-Complex.ofReal_exp, g2, mul_assoc, MeasureTheory.integral_const_mul]
      _ = ((725760 : ℂ) / (π : ℂ)) * ((1 : ℂ) / ((Real.pi * (u - 2)) : ℂ) ^ (2 : ℕ)) := by
            rw [hbase]
      _ = ((725760 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (((u - 2) ^ (2 : ℕ) : ℝ) : ℂ) := by
        field_simp [hpi0, hu2ne]
        simp
  have Ig4 :
      (∫ t : ℝ, g4 t ∂μ) =
        ((113218560 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hbase :
        (∫ t : ℝ, (t : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ) ∂μ) =
          (1 : ℂ) / ((Real.pi * u) : ℂ) ^ (2 : ℕ) := by
      simpa [-Complex.ofReal_exp, mul_assoc] using! (integral_mul_exp_ofReal (r := Real.pi * u) hr0)
    calc
      (∫ t : ℝ, g4 t ∂μ) =
          ((113218560 : ℂ) / (π : ℂ)) *
              (∫ t : ℝ, (t : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ) ∂μ) := by
            simp [-Complex.ofReal_exp, g4, mul_assoc, MeasureTheory.integral_const_mul]
      _ = ((113218560 : ℂ) / (π : ℂ)) * ((1 : ℂ) / ((Real.pi * u) : ℂ) ^ (2 : ℕ)) := by
            rw [hbase]
      _ = ((113218560 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u ^ (2 : ℕ) : ℝ) : ℂ) := by
            field_simp [hpi0, hu0ne]
            simp
  -- Put everything together.
  rw [pTildeIntegral, if_pos hu]
  change (∫ t : ℝ, pPaper t * (Real.exp (-Real.pi * u * t) : ℂ) ∂μ) = pTildeProfile u
  have hsum : (fun t : ℝ => g1 t + g2 t + g3 t + g4 t + g5 t) = s12345 := by
    funext t
    simp [s12345, s1234, s123, s12, add_assoc]
  have hInt :
      (∫ t : ℝ, pPaper t * (Real.exp (-Real.pi * u * t) : ℂ) ∂μ) =
        ∫ t : ℝ, s12345 t ∂μ :=
    congrArg (fun f : ℝ → ℂ => ∫ t : ℝ, f t ∂μ) (hdecomp.trans hsum)
  calc
    (∫ t : ℝ, pPaper t * (Real.exp (-Real.pi * u * t) : ℂ) ∂μ) =
        ∫ t : ℝ, s12345 t ∂μ := hInt
    _ =
        ((((∫ t : ℝ, g1 t ∂μ) + (∫ t : ℝ, g2 t ∂μ)) + (∫ t : ℝ, g3 t ∂μ)) +
              (∫ t : ℝ, g4 t ∂μ)) +
            (∫ t : ℝ, g5 t ∂μ) := hsplit
    _ = pTildeProfile u := by
        simp [pTildeProfile, Ig1, Ig2, Ig3, Ig4, Ig5, add_assoc]

end SpecialValuesDerivTwoLaurent

end

end SpherePacking.Dim24
