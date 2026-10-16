-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
import SpherePacking.Dim24.MagicFunction.B.Defs.J5Smooth
import SpherePacking.Integration.InvChangeOfVariables
import SpherePacking.Tactic.NormNumI
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Setup for `perm_J₅`

This follows the dim-8 blueprint (`MagicFunction.b.Fourier.PermJ5`):

1. Rewrite `J₅'` using the substitution `t ↦ 1/t`, yielding an integral over `Ici 1` with an
   explicit factor `s^(-12)` (dimension `24`).
2. Swap integrals using Fubini on a dominated kernel.
3. Evaluate the inner integral using the Gaussian Fourier transform.

The proof uses the same analytic pattern (change-of-variables + integrability for Fubini) as the
dim-8 development, together with the dim-24 Gaussian Fourier transform evaluation.

## Main definitions
* `J5Change.g`

## Main statements
* `J5Change.Complete_Change_of_Variables`
-/

open scoped Real
open Complex

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.BFourier
open MeasureTheory Set

noncomputable section


namespace J5Change

open MeasureTheory Set intervalIntegral
open SpherePacking.Integration.InvChangeOfVariables

/-!
Change of variables for `J₅'` (the `t ↦ 1/t` substitution), following the dim-8 blueprint.

This produces a representation of `J₅'` as an integral over `Ici 1`, compatible with the Fourier
permutation argument (cancellation of the `s^(-12)` and `s^12` factors in dimension 24).
-/

def f : ℝ → ℝ := fun t ↦ 1 / t

def f' : ℝ → ℝ := fun t ↦ -1 / t ^ 2

/-- Integrand on `Ici 1` obtained from `J₅'` after the substitution `t ↦ 1/t`. -/
@[expose] public def g (r : ℝ) (s : ℝ) : ℂ :=
  (-I : ℂ) *
    ψS' ((Complex.I : ℂ) * (s : ℂ)) *
      ((s ^ (-12 : ℤ)) : ℂ) *
        cexp (-π * r / s)

lemma J₅'_eq_Ioc (r : ℝ) :
    RealIntegrals.J₅' r =
      (-2 : ℂ) * ∫ (t : ℝ) in Ioc 0 1,
        (Complex.I : ℂ) * ψI' (MagicFunction.Parametrisations.z₅' t) *
          cexp (π * (Complex.I : ℂ) * (r : ℂ) * (MagicFunction.Parametrisations.z₅' t)) := by
  -- Rewrite the interval integral `∫ t in (0)..1` as a set integral over `Ioc 0 1`.
  simp [RealIntegrals.J₅', intervalIntegral_eq_integral_uIoc, uIoc_of_le, zero_le_one, mul_assoc,
    mul_left_comm, mul_comm]

lemma Reconciling_Change_of_Variables (r : ℝ) :
    RealIntegrals.J₅' r =
      (-2 : ℂ) * ∫ (t : ℝ) in Ioc 0 1, |f' t| • (g r (f t)) := by
  -- Reduce to a pointwise identity of integrands.
  rw [J₅'_eq_Ioc]
  congr 1
  apply setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ ?_
  intro t ht
  have ht0 : 0 < t := ht.1
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  have hz5 : MagicFunction.Parametrisations.z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using!
      (MagicFunction.Parametrisations.z₅'_eq_of_mem (t := t) htIcc)
  have hexp :
      cexp (π * (Complex.I : ℂ) * (r : ℂ) * (MagicFunction.Parametrisations.z₅' t)) =
        cexp (-π * r * t) := by
    -- `z₅' t = I*t` on the integration domain, and `I*I = -1`.
    have h :
        (π : ℂ) * (Complex.I : ℂ) * (r : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) =
          (-π : ℂ) * (r : ℂ) * (t : ℂ) := by
      calc
        (π : ℂ) * (Complex.I : ℂ) * (r : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) =
            (π : ℂ) * (r : ℂ) * ((Complex.I : ℂ) * (Complex.I : ℂ)) * (t : ℂ) := by
              ring
        _ = (π : ℂ) * (r : ℂ) * (-1 : ℂ) * (t : ℂ) := by
              simp [Complex.I_mul_I]
        _ = (-π : ℂ) * (r : ℂ) * (t : ℂ) := by
              ring
    simpa [hz5, mul_assoc] using! congrArg cexp h
  have hψI :
      ψI' (MagicFunction.Parametrisations.z₅' t) =
        ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) :=
    SpherePacking.Dim24.Schwartz.J5Smooth.ψI'_z₅'_eq (t := t) (ht := ht)
  have hψS : ψS' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) = ψS.resToImagAxis (1 / t) := by
    have : 0 < (1 / t : ℝ) := by positivity
    simp [ψS', Function.resToImagAxis, ResToImagAxis, one_div, mul_comm]
  have ht_ne0 : t ≠ 0 := ne_of_gt ht0
  have habs : |-1 / t ^ 2| = 1 / t ^ 2 := by
    rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]
  have hdivexp : cexp (-π * r / (1 / t)) = cexp (-π * r * t) :=
    cexp_neg_pi_mul_div_one_div (r := r) (t := t)
  -- Simplify the scalar Jacobian factor.
  have hscal : (1 / t ^ 2) * ((1 / t : ℝ) ^ (-12 : ℤ)) = t ^ (10 : ℕ) := by
    simpa using!
      (one_div_pow_two_mul_one_div_zpow (k := 12) (t := t)
        (hk := by decide) (ht := ht_ne0))
  have hscalC : ((1 / t ^ 2) * ((1 / t : ℝ) ^ (-12 : ℤ)) : ℂ) = (t ^ (10 : ℕ) : ℂ) := by
    exact_mod_cast hscal
  -- Now compute both sides to a common normal form.
  have hRHS :
      |f' t| • (g r (f t)) =
        (-I : ℂ) * ψS' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) * (t ^ (10 : ℕ) : ℂ) *
          cexp (-π * r * t) := by
    have habs' : |f' t| = 1 / t ^ 2 := by
      simp [f', habs]
    have habsC : ((|f' t| : ℝ) : ℂ) = ((1 / t ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast habs'
    have hscalCmul :
        ((1 / t ^ 2 : ℝ) : ℂ) * (((1 / t : ℝ) ^ (-12 : ℤ)) : ℂ) = (t ^ (10 : ℕ) : ℂ) := by
      -- `hscalC` is the same identity but with `ofReal` of the product.
      simpa [Complex.ofReal_mul] using! hscalC
    -- Unfold and rewrite the scalar piece and exponential term explicitly.
    calc
      |f' t| • g r (f t) = ((|f' t| : ℝ) : ℂ) * g r (f t) := by
        simp [real_smul]
      _ = ((1 / t ^ 2 : ℝ) : ℂ) * g r (f t) := by
        simp [habsC]
      _ = ((1 / t ^ 2 : ℝ) : ℂ) * g r (1 / t) := by
        simp [f]
      _ =
          ((1 / t ^ 2 : ℝ) : ℂ) *
            ((-I : ℂ) *
                ψS' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) *
                  (((1 / t : ℝ) ^ (-12 : ℤ)) : ℂ) * cexp (-π * r / (1 / t))) := by
            simp [g]
      _ =
          (-I : ℂ) * ψS' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) *
            (((1 / t ^ 2 : ℝ) : ℂ) * (((1 / t : ℝ) ^ (-12 : ℤ)) : ℂ)) *
              cexp (-π * r / (1 / t)) := by
            ac_rfl
      _ =
          (-I : ℂ) * ψS' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) *
            (t ^ (10 : ℕ) : ℂ) * cexp (-π * r / (1 / t)) := by
            -- Rewrite the scalar product using `hscalCmul` without any cancellation.
            simp_all
      _ =
          (-I : ℂ) * ψS' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) *
            (t ^ (10 : ℕ) : ℂ) * cexp (-π * r * t) := by
            simp
  have hLHS :
      (Complex.I : ℂ) * ψI' (MagicFunction.Parametrisations.z₅' t) *
          cexp (π * (Complex.I : ℂ) * (r : ℂ) * (MagicFunction.Parametrisations.z₅' t)) =
        (-I : ℂ) * ψS' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) * (t ^ (10 : ℕ) : ℂ) *
          cexp (-π * r * t) := by
    -- Rewrite `ψI'` and the exponential term; then simplify `I * (I*t)^10 = -I * t^10`.
    rw [hψI, hexp, ← hψS]
    have hI10 : (Complex.I : ℂ) ^ (10 : ℕ) = (-1 : ℂ) := by
      norm_num1
    grind only
  simp [hLHS, hRHS]

/-- Change of variables formula expressing `J₅'` as an integral over `Ici 1` with integrand `g`. -/
public theorem Complete_Change_of_Variables (r : ℝ) :
    RealIntegrals.J₅' r = (-2 : ℂ) * ∫ s in Ici (1 : ℝ), g r s := by
  calc
    RealIntegrals.J₅' r = (-2 : ℂ) * ∫ t in Ioc (0 : ℝ) 1, |f' t| • g r (f t) :=
      Reconciling_Change_of_Variables (r := r)
    _ = (-2 : ℂ) * ∫ s in Ici (1 : ℝ), g r s := by
      simpa [f, f'] using!
        congrArg (fun z : ℂ => (-2 : ℂ) * z)
          (integral_Ici_one_eq_integral_abs_deriv_smul (g := g r)).symm

end J5Change

end
end SpherePacking.Dim24.BFourier
