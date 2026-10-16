-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSlash
import SpherePacking.ForMathlib.UpperHalfPlane
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity
import SpherePacking.MagicFunction.PsiTPrimeZ1


/-!
# Smoothness and one-sided Schwartz decay for `RealIntegrals.J₁'`

This mirrors the dimension-8 development, with weight `-10`. The modular identity
`(ψS ∣[-10] (S*T)) = ψT` yields a `t^10` factor near `t = 0`; this integrable factor supplies
Schwartz decay on `x ≥ 0` after an AM-GM estimate.

## Main definitions
* `Schwartz.J1Smooth.coeff`
* `Schwartz.J1Smooth.g`
* `Schwartz.J1Smooth.gN`

## Main statements
* `Schwartz.J1Smooth.ψT'_z₁'_eq`
* `Schwartz.J1Smooth.J₁'_eq_integral`
-/

noncomputable section

namespace SpherePacking.Dim24.Schwartz.J1Smooth

open scoped Interval UpperHalfPlane

open Complex Real Set MeasureTheory Filter intervalIntegral
open UpperHalfPlane
open MagicFunction.Parametrisations
open RealIntegrals PsiExpBounds

section Modular

open ModularGroup Matrix
open scoped MatrixGroups ModularForm

set_option backward.isDefEq.respectTransparency false in
lemma slashST' (z : ℍ) (F : ℍ → ℂ) :
    ((F) ∣[-10] (S * T)) z = F ((S * T) • z) * (z + 1 : ℂ) ^ (10 : ℕ) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.S_mul_T, denom]
  simp only [Int.reduceNeg, Fin.isValue, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom, map_apply,
    of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, Int.cast_one, ofReal_one,
    one_mul]
  -- `(-(-10)) = 10` and convert (postTransparency := .instances) `zpow` to a natural power.
  simp [zpow_ofNat]

/-- Rewrite `ψT' (z₁' t)` in terms of `ψS` restricted to the imaginary axis. -/
public lemma ψT'_z₁'_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ψT' (z₁' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) := by
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  have ht0 : 0 < t := ht.1
  have hz_im : 0 < (z₁' t).im := im_z₁'_pos (t := t) ht
  let z : ℍ := ⟨z₁' t, hz_im⟩
  have hrel := congrArg (fun f : ℍ → ℂ => f z) PsiSlash.ψS_slash_ST
  have hψT : ψT z = ψS ((S * T) • z) * (z + 1 : ℂ) ^ (10 : ℕ) := by
    have h1 : (ψS ∣[-10] (S * T)) z = ψT z := by
      simpa using! hrel
    calc
      ψT z = (ψS ∣[-10] (S * T)) z := by simpa using! h1.symm
      _ = ψS ((S * T) • z) * (z + 1 : ℂ) ^ (10 : ℕ) := by
          simpa using! (slashST' (z := z) (F := ψS))
  have hzplus : (z + 1 : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by
    have :
        z₁' t + (1 : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using!
        congrArg (fun w : ℂ => w + (1 : ℂ)) (z₁'_eq_of_mem (t := t) htIcc)
    simpa [z] using! this
  have htne : (t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht0)
  have hsmul : (S * T) • z = (⟨(Complex.I : ℂ) * (1 / t), by simp [ht0]⟩ : ℍ) := by
    ext1
    have hcoe : (↑((S * T) • z) : ℂ) = (Complex.I : ℂ) * (1 / t) := by
      calc
        (↑((S * T) • z) : ℂ) = (-1 : ℂ) / ((z : ℂ) + 1) := coe_ST_smul (z := z)
        _ = (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) := by simp [hzplus]
        _ = (Complex.I : ℂ) * (1 / t) := by
              field_simp [htne, Complex.I_ne_zero]
              simp
    exact hcoe
  have hψT' : ψT' (z₁' t) = ψT z := by
    simp [ψT', hz_im, z]
  have hψS' : ψS ((S * T) • z) = ψS.resToImagAxis (1 / t) := by
    rw [hsmul]
    simp [Function.resToImagAxis, ResToImagAxis, ht0]
  have hψT'' :
      ψT z = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) := by
    have hψT1 := hψT
    rw [hψS'] at hψT1
    simpa [hzplus] using! hψT1
  simpa [hψT'] using! hψT''

end Modular

lemma norm_ψT'_z₁'_le (t : ℝ) (ht : t ∈ (Ι (0 : ℝ) 1)) :
    ∃ M, ‖ψT' (z₁' t)‖ ≤ M * t ^ (10 : ℕ) := by
  rcases exists_bound_norm_ψS_resToImagAxis_Ici_one with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
    simpa [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
  have ht0 : 0 < t := htIoc.1
  have ht1 : t ≤ 1 := htIoc.2
  have hone : (1 : ℝ) ≤ 1 / t := one_le_one_div ht0 ht1
  have hψS : ‖ψS.resToImagAxis (1 / t)‖ ≤ M := hM (1 / t) hone
  simpa using!
    (MagicFunction.norm_modular_rewrite_Ioc_bound
      (k := (10 : ℕ)) (ψS := ψS) (ψZ := ψT') (z := z₁') (hEq := ψT'_z₁'_eq) htIoc hψS)

/-- Coefficient appearing in the exponential kernel. -/
@[expose] public def coeff (t : ℝ) : ℂ := ((Real.pi : ℂ) * (Complex.I : ℂ)) * z₁' t

/-- The integrand defining `J₁'`, after reparametrizing the contour by `t ∈ (0,1)`. -/
@[expose] public def g (x t : ℝ) : ℂ :=
  ((Complex.I : ℂ) * ψT' (z₁' t)) * cexp ((x : ℂ) * coeff t)

/-- The `n`th differentiated integrand for `J₁'`, used for differentiation under the integral. -/
@[expose] public def gN (n : ℕ) (x t : ℝ) : ℂ := (coeff t) ^ n * g x t

/-- Expression of `J₁'` as an interval integral of the integrand `g`. -/
public lemma J₁'_eq_integral (x : ℝ) : RealIntegrals.J₁' x = ∫ t in (0 : ℝ)..1, g x t := by
  simp [RealIntegrals.J₁', g, coeff, mul_assoc, mul_left_comm, mul_comm]

/-- A uniform bound on the kernel coefficient `‖coeff t‖` on the parametrizing interval. -/
public lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * Real.pi := by
  simpa [coeff, mul_assoc] using!
    (SpherePacking.ForMathlib.norm_mul_pi_I_le_two_pi (z := z₁' t) (hz := norm_z₁'_le_two t))


end SpherePacking.Dim24.Schwartz.J1Smooth

end
