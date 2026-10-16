-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Basic
public import SpherePacking.Dim24.MagicFunction.SpecialValuesExpU


/-!
# Segment identity for `bProfile`

This file proves the dimension-24 analogue of the segment identity for `bProfile`: the block
`J₁' u + J₃' u + J₅' u` can be rewritten as a scalar multiple of the imaginary-axis segment
integral of `ψI'`.

They are preparatory for the Laplace representation of `f` and `𝓕 f`.

## Main statements
* `ψT'_add_one_eq_ψI'`
* `J₁'_add_J₃'_add_J₅'_eq_imag_axis`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceB

noncomputable section

open scoped Interval

open UpperHalfPlane

open MagicFunction.Parametrisations
open RealIntegrals
open SpecialValuesAux

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

lemma expU_sub_one_mul (u : ℝ) (z : ℂ) :
    expU u (z - 1) = expU u z * expU u (-1) := by
  simp [expU, sub_eq_add_neg, mul_add, mul_assoc, Complex.exp_add]

lemma expU_neg_one_eq_inv (u : ℝ) : expU u (-1) = (expU u 1)⁻¹ := by
  simp [expU, Complex.exp_neg]

/-- Translation identity: `ψT' (z + 1) = ψI' z` for the total extensions. -/
public lemma ψT'_add_one_eq_ψI' (z : ℂ) : ψT' (z + 1) = ψI' z := by
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa [Complex.add_im] using! hz
    have hrel :=
      congrArg (fun F : ℍ → ℂ => F (UpperHalfPlane.mk z hz)) PsiSlash.ψT_slash_T
    have hrel' : ψT (((1 : ℝ) +ᵥ UpperHalfPlane.mk z hz) : ℍ) = ψI (UpperHalfPlane.mk z hz) := by
      simpa [modular_slash_T_apply] using! hrel
    have hvadd :
        ((1 : ℝ) +ᵥ UpperHalfPlane.mk z hz : ℍ) = UpperHalfPlane.mk (z + 1) hz' := by
      ext1
      simp [UpperHalfPlane.coe_vadd, add_comm]
    have hψ : ψT (UpperHalfPlane.mk (z + 1) hz') = ψI (UpperHalfPlane.mk z hz) := by
      simpa [hvadd] using! hrel'
    simpa [ψT', ψI', hz, hz'] using! hψ
  · have hz' : ¬ 0 < (z + 1).im := by simpa [Complex.add_im] using! hz
    simp [ψT', ψI', hz]

/-- Segment identity expressing `J₁' u + J₃' u + J₅' u` via the imaginary-axis integral of `ψI'`. -/
public lemma J₁'_add_J₃'_add_J₅'_eq_imag_axis (u : ℝ) :
    J₁' u + J₃' u + J₅' u =
      (Complex.I : ℂ) *
        ((Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
          (∫ t in (0 : ℝ)..1, ψI' (z₅' t) * expU u (z₅' t))) := by
  -- Abbreviate the imaginary-axis segment integral.
  let V0 : ℂ := ∫ t in (0 : ℝ)..1, ψI' (z₅' t) * expU u (z₅' t)
  have hV0 : V0 = ∫ t in (0 : ℝ)..1, ψI' (z₅' t) * expU u (z₅' t) := rfl
  have hJ1 :
      J₁' u = (Complex.I : ℂ) * Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * V0 := by
    -- Rewrite the integrand on `z₁'` as the integrand on `z₅'`, shifted by `-1`.
    have hcongr :
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z₁' t) * expU u (z₁' t)) =
          ∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) *
              (Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * expU u (z₅' t)) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
      have hψ : ψT' (z₁' t) = ψI' (z₅' t) := ψT'_z₁'_eq_ψI'_z₅' (t := t) htIcc
      have hz : z₁' t = z₅' t - 1 := by
        have hz' := z₁'_add_one_eq_z₅' (t := t) htIcc
        have := congrArg (fun w : ℂ => w - 1) hz'
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! this
      -- `expU u (z-1) = exp(-π i u) * expU u z`.
      have hexp :
          expU u (z₁' t) =
            Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) *
              expU u (z₅' t) := by
        have hneg : expU u (-1) = Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) := by
          simp [expU, mul_left_comm, mul_comm]
        calc
          expU u (z₁' t) = expU u (z₅' t - 1) := by simp [hz]
          _ = expU u (z₅' t) * expU u (-1) := expU_sub_one_mul (u := u) (z := z₅' t)
          _ = expU u (-1) * expU u (z₅' t) := by ac_rfl
          _ = Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * expU u (z₅' t) := by
                simp [hneg]
      simp [hψ, hexp, mul_assoc, mul_left_comm, mul_comm]
    -- Pull out constants.
    simpa [RealIntegrals.J₁', expU, V0, hV0, mul_assoc, mul_left_comm, mul_comm,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const] using! hcongr
  have hJ3 :
      J₃' u = (Complex.I : ℂ) * Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * V0 := by
    have hcongr :
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z₃' t) * expU u (z₃' t)) =
          ∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) *
              (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * expU u (z₅' t)) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
      have hz : z₃' t = z₅' t + 1 :=
        MagicFunction.Parametrisations.z₃'_eq_z₅'_add_one (t := t) htIcc
      have hψ : ψT' (z₃' t) = ψI' (z₅' t) := by
        -- `z₃' t = z₅' t + 1`.
        simpa [hz] using! (ψT'_add_one_eq_ψI' (z := z₅' t))
      have hexp :
          expU u (z₃' t) =
            Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) *
              expU u (z₅' t) := by
        have hpos : expU u 1 = Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) := by
          simp [expU, mul_left_comm, mul_comm]
        calc
          expU u (z₃' t) = expU u (z₅' t + 1) := by simp [hz]
          _ = expU u (z₅' t) * expU u 1 := expU_add_one_mul (u := u) (z := z₅' t)
          _ = expU u 1 * expU u (z₅' t) := by ac_rfl
          _ = Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * expU u (z₅' t) := by
                simp [hpos]
      simp [hψ, hexp, mul_assoc, mul_left_comm, mul_comm]
    simpa [RealIntegrals.J₃', expU, V0, hV0, mul_assoc, mul_left_comm, mul_comm,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const] using! hcongr
  have hJ5 : J₅' u = (-2 : ℂ) * (Complex.I : ℂ) * V0 := by
    simp [RealIntegrals.J₅', expU, V0, mul_assoc, mul_left_comm, mul_comm]
  grind only

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceB
