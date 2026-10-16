-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.QHalfTheta4
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.CuspCoefficient.H2
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.CuspCoefficient.H4
public import SpherePacking.Dim24.ModularForms.Psi.Relations


/-!
# Cusp coefficient for `ψI`

This file computes the first `qHalf^2` coefficient of the normalized expression
`ψI z * exp(4π i z)` at the cusp `i∞`.

## Main statements
* `tendsto_ψI_mul_cexp_four_pi_mul_I_sub_two_div_qHalf_sq`
-/

open scoped Real
open scoped Topology
open scoped UpperHalfPlane
open scoped Complex

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter UpperHalfPlane

namespace Deriv

/-- As `Im z → ∞`, the normalized error
`(ψI z * exp(4π i z) - 2) / qHalf(z)^2` tends to `-464`. -/
public lemma tendsto_ψI_mul_cexp_four_pi_mul_I_sub_two_div_qHalf_sq :
    Tendsto
        (fun z : ℍ =>
          (ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ)) - (2 : ℂ)) / (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (-464 : ℂ)) := by
  let q : ℍ → ℂ := qHalf
  let q2 : ℍ → ℂ := fun z : ℍ => (q z) ^ (2 : ℕ)
  let D : ℍ → ℂ := fun z : ℍ => (Δ z) / q2 z
  let N : ℍ → ℂ :=
    fun z : ℍ =>
      7 * (H₄ z) ^ 5 * (H₂ z) ^ 2 +
        7 * (H₄ z) ^ 6 * (H₂ z) +
          2 * (H₄ z) ^ 7
  have hq : Tendsto q2 atImInfty (𝓝 (0 : ℂ)) := by
    simpa [q2, q] using!
      (tendsto_qHalf_atImInfty.pow 2)
  have hDinv2 :
      Tendsto (fun z : ℍ => (D z)⁻¹ ^ (2 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
    have hDsub : Tendsto (fun z : ℍ => (D z - (1 : ℂ)) / q2 z) atImInfty (𝓝 (-24 : ℂ)) := by
      simpa [D, q2] using! tendsto_Delta_div_qHalf_sq_sub_one_div_qHalf_sq
    have hDsub' : Tendsto (fun z : ℍ => D z - (1 : ℂ)) atImInfty (𝓝 (0 : ℂ)) := by
      have hmul :
          Tendsto (fun z : ℍ => q2 z * ((D z - (1 : ℂ)) / q2 z)) atImInfty (𝓝 (0 : ℂ)) := by
        simpa [mul_zero] using! (hq.mul hDsub)
      refine hmul.congr' ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      have hq2z : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
      field_simp [hq2z]
    have hD : Tendsto D atImInfty (𝓝 (1 : ℂ)) :=
      tendsto_sub_nhds_zero_iff.mp hDsub'
    have hDinv : Tendsto (fun z : ℍ => (D z)⁻¹) atImInfty (𝓝 (1 : ℂ)) := by
      simpa using! (hD.inv₀ (by simp))
    simpa using! (hDinv.pow 2)
  have hDinv2coef :
      Tendsto
          (fun z : ℍ => ((D z)⁻¹ ^ (2 : ℕ) - (1 : ℂ)) / q2 z)
          atImInfty (𝓝 (48 : ℂ)) := by
    simpa [D, q2] using! tendsto_Delta_div_qHalf_sq_inv_sq_sub_one_div_qHalf_sq
  have hN :
      Tendsto (fun z : ℍ => (N z - (2 : ℂ)) / q2 z) atImInfty (𝓝 (-560 : ℂ)) := by
    have hH4to : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := by
      simpa using! (H₄_tendsto_atImInfty : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)))
    have htermA :
        Tendsto
            (fun z : ℍ => (7 : ℂ) * (H₄ z) ^ (5 : ℕ) * ((H₂ z) ^ (2 : ℕ) / q2 z))
            atImInfty (𝓝 ((7 : ℂ) * ((1 : ℂ) ^ (5 : ℕ)) * ((16 : ℂ) ^ (2 : ℕ)))) := by
      have hH2sq :
          Tendsto (fun z : ℍ => (H₂ z) ^ (2 : ℕ) / q2 z) atImInfty (𝓝 ((16 : ℂ) ^ (2 : ℕ))) := by
        simpa [q2, q] using! tendsto_H₂_sq_div_qHalf_sq
      have :
          Tendsto (fun z : ℍ => (H₄ z) ^ (5 : ℕ) * ((H₂ z) ^ (2 : ℕ) / q2 z)) atImInfty
            (𝓝 (((1 : ℂ) ^ (5 : ℕ)) * ((16 : ℂ) ^ (2 : ℕ)))) :=
        (hH4to.pow 5).mul hH2sq
      simpa [mul_assoc] using! (tendsto_const_nhds.mul this)
    have htermB :
        Tendsto
            (fun z : ℍ =>
              (7 : ℂ) * (H₄ z) ^ (6 : ℕ) *
                ((H₂ z - (16 : ℂ) * q z) / q2 z))
            atImInfty (𝓝 (0 : ℂ)) := by
      have hH2err :
          Tendsto (fun z : ℍ => (H₂ z - (16 : ℂ) * q z) / q2 z) atImInfty (𝓝 (0 : ℂ)) := by
        simpa [q2, q] using! tendsto_H₂_sub_sixteen_mul_qHalf_div_qHalf_sq
      have :
          Tendsto
              (fun z : ℍ => (H₄ z) ^ (6 : ℕ) * ((H₂ z - (16 : ℂ) * q z) / q2 z))
              atImInfty (𝓝 (((1 : ℂ) ^ (6 : ℕ)) * 0)) := (hH4to.pow 6).mul hH2err
      have :
          Tendsto
              (fun z : ℍ => (7 : ℂ) * ((H₄ z) ^ (6 : ℕ) * ((H₂ z - (16 : ℂ) * q z) / q2 z)))
              atImInfty (𝓝 ((7 : ℂ) * (((1 : ℂ) ^ (6 : ℕ)) * 0))) :=
        tendsto_const_nhds.mul this
      simpa [mul_assoc] using! this
    have htermC :
        Tendsto (fun z : ℍ => (112 : ℂ) * (((H₄ z) ^ (6 : ℕ) - (1 : ℂ)) / q z)) atImInfty
          (𝓝 ((112 : ℂ) * (-48 : ℂ))) := by
      have hH4pow6 :
          Tendsto (fun z : ℍ => ((H₄ z) ^ (6 : ℕ) - (1 : ℂ)) / q z) atImInfty (𝓝 (-48 : ℂ)) := by
        simpa [q] using! tendsto_H₄_pow6_sub_one_div_qHalf
      simpa using! (tendsto_const_nhds.mul hH4pow6)
    have htermD :
        Tendsto
            (fun z : ℍ => (2 : ℂ) * (((H₄ z) ^ (7 : ℕ) - (1 : ℂ) + (56 : ℂ) * q z) / q2 z))
            atImInfty (𝓝 ((2 : ℂ) * (1512 : ℂ))) := by
      have hH4pow7 :
          Tendsto
              (fun z : ℍ => ((H₄ z) ^ (7 : ℕ) - (1 : ℂ) + (56 : ℂ) * q z) / q2 z)
              atImInfty (𝓝 (1512 : ℂ)) := by
        simpa [q2, q] using! tendsto_H₄_pow7_sub_one_add_fiftysix_mul_qHalf_div_qHalf_sq
      simpa using! (tendsto_const_nhds.mul hH4pow7)
    have hEq :
        (fun z : ℍ => (N z - (2 : ℂ)) / q2 z) =
          fun z : ℍ =>
            ((7 : ℂ) * (H₄ z) ^ (5 : ℕ) * ((H₂ z) ^ (2 : ℕ) / q2 z)) +
              ((7 : ℂ) * (H₄ z) ^ (6 : ℕ) * ((H₂ z - (16 : ℂ) * q z) / q2 z)) +
                ((112 : ℂ) * (((H₄ z) ^ (6 : ℕ) - (1 : ℂ)) / q z)) +
                  ((2 : ℂ) * (((H₄ z) ^ (7 : ℕ) - (1 : ℂ) + (56 : ℂ) * q z) / q2 z)) := by
      funext z
      have hq0 : q z ≠ 0 := qHalf_ne_zero z
      have hq20 : q2 z ≠ 0 := pow_ne_zero 2 hq0
      field_simp [N, q2, hq0, hq20]
      ring
    have hmain :
        Tendsto
            (fun z : ℍ =>
              ((7 : ℂ) * (H₄ z) ^ (5 : ℕ) * ((H₂ z) ^ (2 : ℕ) / q2 z)) +
                ((7 : ℂ) * (H₄ z) ^ (6 : ℕ) *
                  ((H₂ z - (16 : ℂ) * q z) / q2 z)) +
                  ((112 : ℂ) * (((H₄ z) ^ (6 : ℕ) - (1 : ℂ)) / q z)) +
                    ((2 : ℂ) * (((H₄ z) ^ (7 : ℕ) - (1 : ℂ) + (56 : ℂ) * q z) / q2 z)))
            atImInfty
            (𝓝
              (((7 : ℂ) * ((1 : ℂ) ^ (5 : ℕ)) * ((16 : ℂ) ^ (2 : ℕ))) +
                  0 +
                ((112 : ℂ) * (-48 : ℂ)) +
                  ((2 : ℂ) * (1512 : ℂ)))) := by
      simpa [add_assoc] using! ((htermA.add htermB).add htermC).add htermD
    have hconst :
        (-((112 : ℂ) * (48 : ℂ)) + ((2 : ℂ) * (1512 : ℂ) + (7 : ℂ) * ((16 : ℂ) ^ (2 : ℕ)))) =
          (-560 : ℂ) := by
      norm_num
    -- `simp` reshuffles the constant into the `-(112*48) + (2*1512 + 7*16^2)` form.
    simpa [hEq, hconst, add_assoc, add_left_comm, add_comm, mul_assoc] using!
      hmain
  have hEq :
      (fun z : ℍ => (ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ)) - (2 : ℂ)) / q2 z) =
        fun z : ℍ =>
          ((N z - (2 : ℂ)) / q2 z) * ((D z)⁻¹ ^ (2 : ℕ)) +
            (2 : ℂ) * (((D z)⁻¹ ^ (2 : ℕ) - (1 : ℂ)) / q2 z) := by
    funext z
    have hq2z : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
    have hΔ0 : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    have hD0 : D z ≠ 0 := by
      exact div_ne_zero hΔ0 hq2z
    have hψ : ψI z = N z / (Δ z) ^ (2 : ℕ) := by
      simpa [N] using! (SpherePacking.Dim24.ψI_eq_H z)
    have hExp :
        cexp (4 * Real.pi * Complex.I * (z : ℂ)) = (q2 z) ^ (2 : ℕ) := by
      have hqFull : qFull z = q2 z := by
        simpa [q2, q] using! (qFull_eq_qHalf_sq (z := z))
      have h := (Complex.exp_nat_mul (2 * Real.pi * Complex.I * (z : ℂ)) 2).symm
      have hmul :
          (2 : ℂ) * (2 * Real.pi * Complex.I * (z : ℂ)) = 4 * Real.pi * Complex.I * (z : ℂ) := by
        ring
      have : (qFull z) ^ (2 : ℕ) = cexp (4 * Real.pi * Complex.I * (z : ℂ)) := by
        simpa [qFull, hmul] using! h
      -- Rewrite `qFull` as `qHalf^2`.
      simpa [hqFull] using!
        this.symm
    -- Rewrite `ψI`, `D` and the exponential into `N, Δ, q2`, then clear denominators.
    simp [hψ, hExp, D, q2]
    field_simp [hq2z, hΔ0]
    ring_nf
  have hmain :
      Tendsto
          (fun z : ℍ =>
            ((N z - (2 : ℂ)) / q2 z) * ((D z)⁻¹ ^ (2 : ℕ)) +
              (2 : ℂ) * (((D z)⁻¹ ^ (2 : ℕ) - (1 : ℂ)) / q2 z))
          atImInfty (𝓝 ((-560 : ℂ) * (1 : ℂ) + (2 : ℂ) * (48 : ℂ))) := by
    have h1 :
        Tendsto (fun z : ℍ => ((N z - (2 : ℂ)) / q2 z) * ((D z)⁻¹ ^ (2 : ℕ))) atImInfty
          (𝓝 ((-560 : ℂ) * (1 : ℂ))) :=
      hN.mul hDinv2
    have h2 :
        Tendsto (fun z : ℍ => (2 : ℂ) * (((D z)⁻¹ ^ (2 : ℕ) - (1 : ℂ)) / q2 z)) atImInfty
          (𝓝 ((2 : ℂ) * (48 : ℂ))) :=
      tendsto_const_nhds.mul hDinv2coef
    simpa [add_assoc] using! h1.add h2
  have hconst : (-560 : ℂ) + (2 : ℂ) * (48 : ℂ) = (-464 : ℂ) := by norm_num
  simpa [q2, q, hEq, hconst] using! hmain

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
