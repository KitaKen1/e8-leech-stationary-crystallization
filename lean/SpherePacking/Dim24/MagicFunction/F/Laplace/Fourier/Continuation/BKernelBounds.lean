-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Continuation.IntegrandSetup
import SpherePacking.Dim24.ModularForms.Psi.ImagAxis


/-!
# Bounds for `BKernel0` on the tail

This file proves a bound for `‖BKernel0 t‖` for `t ≥ 1` by rewriting `BKernel` in terms of the
modular forms `varphi`, `varphi₁` and the remainder term `D` on the imaginary axis.

## Main statement
* `norm_BKernel0_le`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic

noncomputable section

open scoped FourierTransform SchwartzMap

open Complex MeasureTheory Real SchwartzMap Set
open UpperHalfPlane
open SpecialValuesVarphi₁Limits SpecialValuesAux.Deriv

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

lemma norm_D_it_le (t : ℝ) (ht : 1 ≤ t) :
    ‖D (it t (lt_of_lt_of_le (by norm_num) ht))‖ ≤ CDq * Real.exp (2 * Real.pi * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  let zH : ℍ := it t ht0
  let z : ℂ := (zH : ℂ)
  have hzq : q z ≠ 0 := q_ne_zero z
  have hqInv : ‖(q z)⁻¹‖ = Real.exp (2 * Real.pi * t) := by
    have hq : ‖q z‖ = Real.exp (-2 * Real.pi * t) := by
      simpa [zH, z] using! norm_q_it t ht0
    calc
      ‖(q z)⁻¹‖ = (‖q z‖)⁻¹ := by simp
      _ = (Real.exp (-2 * Real.pi * t))⁻¹ := by simp [hq]
      _ = Real.exp (2 * Real.pi * t) := by
            simpa using! congrArg Inv.inv (Real.exp_neg (2 * Real.pi * t))
  have hDq : ‖D zH * q z‖ ≤ CDq := by
    have haxis : ‖(fun z : ℍ => D z * q (z : ℂ)).resToImagAxis t‖ ≤ CDq := hCDq t ht
    have hrepl :
        (fun z : ℍ => D z * q (z : ℂ)).resToImagAxis t = D zH * q z := by
      simpa [zH, z] using! (resToImagAxis_eq_it (F := fun z : ℍ => D z * q (z : ℂ)) (t := t) ht0)
    simpa only [hrepl] using! haxis
  have hrew : D zH = (D zH * q z) * (q z)⁻¹ := by
    simp [hzq]
  calc
    ‖D zH‖ = ‖(D zH * q z) * (q z)⁻¹‖ := by
          simpa using! congrArg (fun w : ℂ => ‖w‖) hrew
    _ = ‖D zH * q z‖ * ‖(q z)⁻¹‖ := by simp []
    _ ≤ CDq * Real.exp (2 * Real.pi * t) := by
      have := mul_le_mul_of_nonneg_right hDq (norm_nonneg ((q z)⁻¹))
      simpa [hqInv] using! this

lemma BKernel_eq_varphi_varphi₁_D (t : ℝ) (ht : 0 < t) :
    BKernel t ht =
      ((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (2 : ℕ) *
          (varphi (it t ht) + varphi₁ (it t ht) / (it t ht))
        + D (it t ht) := by
  have hBK := BKernel_eq (t := t) ht
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hit2 : ((it t ht : ℍ) : ℂ) ^ (2 : ℕ) = -((t : ℂ) ^ (2 : ℕ)) := by
    -- `it t = I*t` and `I^2 = -1`.
    calc
      ((it t ht : ℍ) : ℂ) ^ (2 : ℕ) = (Complex.I * (t : ℂ)) ^ (2 : ℕ) := by
            rfl
      _ = (Complex.I : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (2 : ℕ) := by
            simpa [Dim24.it] using! (mul_pow (Complex.I : ℂ) (t : ℂ) 2)
      _ = -((t : ℂ) ^ (2 : ℕ)) := by
            simp [pow_two, Complex.I_mul_I]
  have hvarphi₂ :
      (t : ℂ) ^ (2 : ℕ) * (varphi₂ (it t ht) / ((it t ht : ℍ) : ℂ) ^ 2) = -varphi₂ (it t ht) := by
    grind only
  -- substitute into `BKernel_eq` and regroup the `varphi₂`/`ψI` combination as `D`
  have hD :
      ((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (2 : ℕ) *
            (varphi₂ (it t ht) / ((it t ht : ℍ) : ℂ) ^ 2) +
          (1 / ((65520 : ℂ) * π)) * ψI (it t ht) =
        D (it t ht) := by
    -- Use `hvarphi₂` to rewrite the `varphi₂` contribution, and then unfold `D`.
    have hφ2' :
        ((π : ℂ) / (28304640 : ℂ)) * ((t : ℂ) ^ (2 : ℕ) *
              (varphi₂ (it t ht) / ((it t ht : ℍ) : ℂ) ^ 2)) =
          (-(π : ℂ) / (28304640 : ℂ)) * varphi₂ (it t ht) := by
      grind only
    calc
      ((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (2 : ℕ) *
            (varphi₂ (it t ht) / ((it t ht : ℍ) : ℂ) ^ 2) +
          (1 / ((65520 : ℂ) * π)) * ψI (it t ht)
          =
          (-(π : ℂ) / (28304640 : ℂ)) * varphi₂ (it t ht) +
            (π : ℂ)⁻¹ * ((65520 : ℂ)⁻¹ * ψI (it t ht)) := by
            -- rewrite the `varphi₂` term via `hφ2'`, and normalize the scalar factor on `ψI`.
            grind only
      _ = D (it t ht) := by
            simp [D]
  -- finish
  -- Expand the `BKernel_eq` RHS and replace the `varphi₂` + `ψI` part.
  grind only

/-- Bound `‖BKernel0 t‖` for `t ≥ 1` using the estimates for `varphi`, `varphi₁`, and `D`. -/
public lemma norm_BKernel0_le (t : ℝ) (ht : 1 ≤ t) :
    ‖BKernel0 t‖ ≤
      ‖((π : ℂ) / (28304640 : ℂ))‖ *
          ((t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
            t * (Cφ1q * Real.exp (2 * Real.pi * t))) +
        CDq * Real.exp (2 * Real.pi * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hB0 : BKernel0 t = BKernel t ht0 := by simp [BKernel0, ht0]
  have hEq := BKernel_eq_varphi_varphi₁_D (t := t) ht0
  have hφ : ‖varphi (it t ht0)‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) := by
    simpa using! norm_varphi_it_le t ht
  have hφ1 : ‖varphi₁ (it t ht0)‖ ≤ Cφ1q * Real.exp (2 * Real.pi * t) := by
    simpa [Dim24.varphi₁] using! norm_varphi₁_it_le t ht
  have hD : ‖D (it t ht0)‖ ≤ CDq * Real.exp (2 * Real.pi * t) := by
    simpa using! norm_D_it_le t ht
  have hitnorm : ‖((it t ht0 : ℍ) : ℂ)‖ = t := by simp [Dim24.it, abs_of_pos ht0]
  have hmain :
      ‖((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (2 : ℕ) *
            (varphi (it t ht0) + varphi₁ (it t ht0) / (it t ht0))‖ ≤
        ‖((π : ℂ) / (28304640 : ℂ))‖ *
          ((t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
            t * (Cφ1q * Real.exp (2 * Real.pi * t))) := by
    have htC : ‖(t : ℂ) ^ (2 : ℕ)‖ = (t ^ (2 : ℕ) : ℝ) := by
      simp [pow_two, Complex.norm_real, abs_of_pos ht0]
    have hφ1div : ‖varphi₁ (it t ht0) / (it t ht0)‖ ≤ (Cφ1q * Real.exp (2 * Real.pi * t)) / t := by
      have :=
        div_le_div_of_nonneg_right hφ1 (by positivity : 0 ≤ ‖((it t ht0 : ℍ) : ℂ)‖)
      simpa [norm_div, hitnorm] using! this
    have hφ1term :
        (t ^ (2 : ℕ) : ℝ) * ‖varphi₁ (it t ht0) / (it t ht0)‖ ≤
          t * (Cφ1q * Real.exp (2 * Real.pi * t)) := by
      have htne : (t : ℝ) ≠ 0 := ne_of_gt ht0
      have hcalc :
          (t ^ (2 : ℕ) : ℝ) * ((Cφ1q * Real.exp (2 * Real.pi * t)) / t) =
            t * (Cφ1q * Real.exp (2 * Real.pi * t)) := by
        field_simp [htne]
      exact (le_trans (mul_le_mul_of_nonneg_left hφ1div (by positivity)) (by simp [hcalc]))
    have hsum :
        (t ^ (2 : ℕ) : ℝ) * ‖varphi (it t ht0) + varphi₁ (it t ht0) / (it t ht0)‖ ≤
          (t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
            t * (Cφ1q * Real.exp (2 * Real.pi * t)) := by
      calc
        (t ^ (2 : ℕ) : ℝ) * ‖varphi (it t ht0) + varphi₁ (it t ht0) / (it t ht0)‖
            ≤ (t ^ (2 : ℕ) : ℝ) * (‖varphi (it t ht0)‖ + ‖varphi₁ (it t ht0) / (it t ht0)‖) := by
              gcongr
              exact norm_add_le _ _
        _ = (t ^ (2 : ℕ) : ℝ) * ‖varphi (it t ht0)‖ +
              (t ^ (2 : ℕ) : ℝ) * ‖varphi₁ (it t ht0) / (it t ht0)‖ := by
              simp [mul_add]
        _ ≤ (t ^ (2 : ℕ) : ℝ) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
              t * (Cφ1q * Real.exp (2 * Real.pi * t)) :=
              add_le_add (mul_le_mul_of_nonneg_left hφ (by positivity)) hφ1term
        _ = (t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
              t * (Cφ1q * Real.exp (2 * Real.pi * t)) := by simp
    calc
      ‖((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (2 : ℕ) *
            (varphi (it t ht0) + varphi₁ (it t ht0) / (it t ht0))‖
          = ‖((π : ℂ) / (28304640 : ℂ))‖ * ‖(t : ℂ) ^ (2 : ℕ)‖ *
              ‖varphi (it t ht0) + varphi₁ (it t ht0) / (it t ht0)‖ := by
              simp [mul_assoc]
      _ = ‖((π : ℂ) / (28304640 : ℂ))‖ * (t ^ (2 : ℕ) : ℝ) *
              ‖varphi (it t ht0) + varphi₁ (it t ht0) / (it t ht0)‖ := by
              simp [htC, mul_assoc]
      _ ≤ ‖((π : ℂ) / (28304640 : ℂ))‖ *
              ((t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
                t * (Cφ1q * Real.exp (2 * Real.pi * t))) := by
              have :=
                mul_le_mul_of_nonneg_left hsum
                  (by positivity : 0 ≤ ‖((π : ℂ) / (28304640 : ℂ))‖)
              simpa [mul_assoc] using! this
  have hsum :
      ‖((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (2 : ℕ) *
            (varphi (it t ht0) + varphi₁ (it t ht0) / (it t ht0)) + D (it t ht0)‖ ≤
        ‖((π : ℂ) / (28304640 : ℂ))‖ *
          ((t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
            t * (Cφ1q * Real.exp (2 * Real.pi * t))) +
        CDq * Real.exp (2 * Real.pi * t) :=
    norm_add_le_of_le hmain hD
  grind only


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic
