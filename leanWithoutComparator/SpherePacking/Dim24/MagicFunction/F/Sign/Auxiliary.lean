-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.MagicFunction.Radial
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Kernels
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Equality.B
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.B
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.BSubLeading
public import SpherePacking.Dim24.Inequalities.VarphiNeg.Statement
public import SpherePacking.Dim24.Inequalities.Ineq2.Statement
public import SpherePacking.Dim24.Inequalities.BLeadingTerms
public import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
import SpherePacking.Dim24.ModularForms.Psi.Relations
import SpherePacking.Tactic.NormNumI
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Order.Filter.AtTopBot.Basic


/-!
# Cohn-Elkies sign lemmas for the Laplace kernels

This file proves auxiliary sign lemmas for the Laplace kernels `AKernel` and `BKernel` on the
imaginary axis. These inequalities are the core input for the Cohn-Elkies sign conditions for `f`
at cutoff radius `2`.

## Main statements
* `AKernel_re_nonpos`
* `BKernel_re_nonneg`
-/

namespace SpherePacking.Dim24

noncomputable section

open scoped FourierTransform SchwartzMap ModularForm Topology

open Complex Filter MeasureTheory Real SchwartzMap

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open UpperHalfPlane

namespace SignAux

/-- The real part of `AKernel t` is nonpositive on the imaginary axis. -/
public lemma AKernel_re_nonpos (t : ℝ) (ht : 0 < t) : (AKernel t ht).re ≤ 0 := by
  have ht' : 0 < 1 / t := by simpa using! (one_div_pos.2 ht)
  have hvar : (varphi (iOverT t ht)).re < 0 := by
    simpa [iOverT] using! (varphi_imagAxis_neg (t := 1 / t) ht')
  have hψ : 0 ≤ (ψI (it t ht)).re := ψI_imagAxis_re_nonneg (t := t) ht
  have hpi : 0 ≤ (Real.pi / 28304640 : ℝ) := by positivity
  have ht10 : 0 ≤ t ^ (10 : ℕ) := pow_nonneg (le_of_lt ht) _
  have hcoefA :
      (((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)).re =
        (Real.pi / 28304640 : ℝ) * t ^ (10 : ℕ) * (varphi (iOverT t ht)).re := by
    set s : ℂ := ((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ)
    have hs : s = (((Real.pi / 28304640 : ℝ) * t ^ (10 : ℕ) : ℝ) : ℂ) := by
      simp [s, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have htPowRe : ((t : ℂ) ^ (10 : ℕ)).re = t ^ (10 : ℕ) := by
      simp [← Complex.ofReal_pow]
    have htPowIm : ((t : ℂ) ^ (10 : ℕ)).im = 0 := by
      simp [← Complex.ofReal_pow]
    calc
      (((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)).re
          = (s * varphi (iOverT t ht)).re := rfl
      _ = (Real.pi / 28304640 : ℝ) * t ^ (10 : ℕ) * (varphi (iOverT t ht)).re := by
            have hsre : s.re = (Real.pi / 28304640 : ℝ) * t ^ (10 : ℕ) := by
              rw [hs]
              simp [htPowRe]
            have hsim : s.im = 0 := by
              rw [hs]
              simp [htPowIm]
            simp [Complex.mul_re, hsre, hsim, mul_assoc, mul_comm]
  have hcoefB :
      (((1 / ((65520 : ℂ) * π)) * ψI (it t ht)).re) =
        (1 / (65520 * Real.pi) : ℝ) * (ψI (it t ht)).re := by
    set s : ℂ := 1 / ((65520 : ℂ) * π)
    have hs : s = ((1 / (65520 * Real.pi) : ℝ) : ℂ) := by
      simp [s, div_eq_mul_inv, mul_left_comm, mul_comm]
    calc
      (((1 / ((65520 : ℂ) * π)) * ψI (it t ht)).re) = (s * ψI (it t ht)).re := rfl
      _ = (1 / (65520 * Real.pi) : ℝ) * (ψI (it t ht)).re := by
            have hsre : s.re = (1 / (65520 * Real.pi) : ℝ) := by
              rw [hs]
              simp
            have hsim : s.im = 0 := by
              rw [hs]
              simp
            simp [Complex.mul_re, hsre, hsim, mul_assoc, mul_comm]
  have hA : (((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)).re ≤ 0 := by
    rw [hcoefA]
    have hscale : 0 ≤ (Real.pi / 28304640 : ℝ) * t ^ (10 : ℕ) := mul_nonneg hpi ht10
    exact mul_nonpos_of_nonneg_of_nonpos hscale (le_of_lt hvar)
  have hB : 0 ≤ (((1 / ((65520 : ℂ) * π)) * ψI (it t ht)).re) := by
    rw [hcoefB]
    have hscale : 0 ≤ (1 / (65520 * Real.pi) : ℝ) := by positivity [Real.pi_pos]
    exact mul_nonneg hscale hψ
  -- `re(A - B) ≤ 0` when `re(A) ≤ 0` and `0 ≤ re(B)`.
  have : (AKernel t ht).re =
      (((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)).re
        - (((1 / ((65520 : ℂ) * π)) * ψI (it t ht)).re) := by
    simp [AKernel, sub_eq_add_neg]
  rw [this]
  linarith

/-- Relate `ψI (it t)` to `ψS (iOverT t)` using the `S`-transformation and a `t^10` factor. -/
public lemma ψI_it_eq_neg_t10_mul_ψS_iOverT (t : ℝ) (ht : 0 < t) :
    ψI (it t ht) = -((t : ℂ) ^ (10 : ℕ)) * ψS (iOverT t ht) := by
  have ht' : 0 < 1 / t := by simpa using! (one_div_pos.2 ht)
  have hI10Nat : (Complex.I : ℂ) ^ (10 : ℕ) = (-1 : ℂ) := by
    norm_num1
  have hres :
      ψI.resToImagAxis t =
        (Complex.I : ℂ) ^ (10 : ℤ) * (t : ℂ) ^ (10 : ℤ) * ψS.resToImagAxis (1 / t) := by
    calc
      ψI.resToImagAxis t = (ψS ∣[-10] ModularGroup.S).resToImagAxis t := by
        simpa using!
          congrArg (fun F : ℍ → ℂ => F.resToImagAxis t) (PsiSlash.ψS_slash_S).symm
      _ =
          (Complex.I : ℂ) ^ (10 : ℤ) * (t : ℂ) ^ (10 : ℤ) * ψS.resToImagAxis (1 / t) := by
        simpa using! (ResToImagAxis.SlashActionS (F := ψS) (k := (-10 : ℤ)) (t := t) ht)
  have hmain :
      ψI (it t ht) =
        (Complex.I : ℂ) ^ (10 : ℤ) * (t : ℂ) ^ (10 : ℤ) * ψS (iOverT t ht) := by
    -- Unfold `resToImagAxis` and rewrite to evaluations at `it`.
    have h :
        ResToImagAxis ψI t =
          (Complex.I : ℂ) ^ (10 : ℤ) * (t : ℂ) ^ (10 : ℤ) * ResToImagAxis ψS (1 / t) := by
      simpa [Function.resToImagAxis, ResToImagAxis] using! hres
    -- Rewrite both restrictions as evaluations at `it`.
    have hψI' : ResToImagAxis ψI t = ψI (it t ht) := resToImagAxis_eq_it (F := ψI) (t := t) ht
    have hψS1 : ResToImagAxis ψS (1 / t) = ψS (iOverT t ht) := by
      have : ResToImagAxis ψS (1 / t) = ψS (it (1 / t) ht') :=
        resToImagAxis_eq_it (F := ψS) (t := 1 / t) ht'
      simpa [iOverT] using! this
    have hψS' : ResToImagAxis ψS t⁻¹ = ψS (iOverT t ht) := by
      simpa [one_div] using! hψS1
    -- Apply the rewrites to `h`.
    simpa [hψI', hψS'] using! h
  -- Convert `zpow` to `pow` and use `I^10 = -1`.
  have hmain' :
      ψI (it t ht) =
        (Complex.I : ℂ) ^ (10 : ℕ) * (t : ℂ) ^ (10 : ℕ) * ψS (iOverT t ht) := by
    simpa [zpow_ofNat] using! hmain
  -- Replace `I^10` and rewrite `(-1) * t^10` as `-(t^10)`.
  simpa [hI10Nat, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using! hmain'

/-- The real part of `BKernel t` is nonnegative on the imaginary axis. -/
public lemma BKernel_re_nonneg (t : ℝ) (ht : 0 < t) : 0 ≤ (BKernel t ht).re := by
  have ht' : 0 < 1 / t := by simpa using! (one_div_pos.2 ht)
  have hineq :
      0 < (varphi (iOverT t ht) - (432 / (Real.pi ^ 2) : ℂ) * ψS (iOverT t ht)).re := by
    simpa [iOverT] using! (ineq2_imagAxis (t := 1 / t) ht')
  have hψI : ψI (it t ht) = -((t : ℂ) ^ (10 : ℕ)) * ψS (iOverT t ht) :=
    ψI_it_eq_neg_t10_mul_ψS_iOverT (t := t) ht
  have hcoef :
      (1 / ((65520 : ℂ) * π)) =
        ((π : ℂ) / (28304640 : ℂ)) * (432 / (Real.pi ^ 2) : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    field_simp [hπ]
    norm_num
  have hB :
      BKernel t ht =
        ((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) *
          (varphi (iOverT t ht) - (432 / (Real.pi ^ 2) : ℂ) * ψS (iOverT t ht)) := by
    -- Expand `BKernel` and rewrite the `ψI` term using `ψS`.
    unfold BKernel
    rw [hψI, hcoef]
    ring
  have hscale : 0 ≤ (Real.pi / 28304640 : ℝ) * t ^ (10 : ℕ) := by
    have : 0 ≤ (Real.pi / 28304640 : ℝ) := by positivity [Real.pi_pos]
    exact mul_nonneg this (pow_nonneg (le_of_lt ht) _)
  have hre :
      (BKernel t ht).re =
        ((Real.pi / 28304640 : ℝ) * t ^ (10 : ℕ)) *
          (varphi (iOverT t ht) - (432 / (Real.pi ^ 2) : ℂ) * ψS (iOverT t ht)).re := by
    rw [hB]
    -- The prefactor is real.
    simp [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, ← Complex.ofReal_pow]
  rw [hre]
  exact mul_nonneg hscale (le_of_lt hineq)

end SignAux

end
end SpherePacking.Dim24
