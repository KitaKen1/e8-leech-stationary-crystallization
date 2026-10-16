module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingKernelRewrite
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi1C
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi2
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.CuspAtInfinity
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.CuspCoefficient.H2
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.CuspCoefficient.H4
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.CuspCoefficient.PsiI


/-!
# Asymptotics for `BKernel` on the imaginary axis

This file isolates the cancellation of the `q^{-2}` term (equivalently, the `exp(4 * π * t)`
growth) between the `varphi₂` contribution and `ψI`, and records the resulting `q^{-1}` leading
coefficient. These limits are the analytic input for the convergent range `u > 2` and for the
subtract-leading continuation used for `0 < u < 2`.

## Main statements
* `tendsto_cancel_q2`
* `tendsto_q1_coeff`

## Implementation notes

The `q^{-2}` coefficients cancel exactly:
- `varphi₂(z) ~ (864/π²) q(z)⁻²`
- `ψI(z) ~ 2 q(z)⁻²`
and in `BKernel` the combination is `-(π/28304640) * varphi₂ + (1/(65520π)) * ψI`.
-/

open scoped Real
open scoped Topology
open scoped Complex
open Filter UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace BKernelAsymptotics

open SpecialValuesVarphi₁Limits
open SpecialValuesVarphi₂Limits
open SpecialValuesAux.Deriv


lemma coeff_cancel_q2 :
    (-(π : ℂ) / (28304640 : ℂ)) * ((864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) +
        ((π : ℂ)⁻¹ * ((65520 : ℂ)⁻¹ * (2 : ℂ))) =
      0 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hπ]
  ring_nf

lemma coeff_q1_value :
    (-(π : ℂ) / (28304640 : ℂ)) * ((2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) -
        ((π : ℂ)⁻¹ * ((65520 : ℂ)⁻¹ * (464 : ℂ))) =
      -((10 : ℂ) / ((117 : ℂ) * π)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hπ]
  ring_nf

/-!
## Converting cusp limits to the imaginary axis

We use the general lemma `Function.tendsto_resToImagAxis_atImInfty` to turn a cusp limit `z → i∞`
into a limit along `t → ∞` on the imaginary axis.
-/

/-!
## Cancellation of the `q^{-2}` growth

We record that the linear combination of `varphi₂` and `ψI` appearing in `BKernel` has
vanishing `q^{-2}` coefficient at `i∞`.
-/

lemma tendsto_cancel_q2 :
    Tendsto
        (fun z : ℍ =>
          (-(π : ℂ) / (28304640 : ℂ)) * (Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) +
              (1 / ((65520 : ℂ) * π)) * (ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ))))
        atImInfty (𝓝 0) := by
  -- Use the separate cusp limits and the explicit cancellation of coefficients.
  have hV : Tendsto (fun z : ℍ => Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) atImInfty
      (𝓝 ((864 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))) :=
    tendsto_varphi₂_mul_q_sq
  have hψ :
      Tendsto
        (fun z : ℍ => ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ)))
        atImInfty (𝓝 (2 : ℂ)) :=
    tendsto_ψI_mul_cexp_four_pi_mul_I
  have hlin1 :=
    (tendsto_const_nhds : Tendsto (fun _ : ℍ => (-(π : ℂ) / (28304640 : ℂ))) atImInfty _).mul hV
  have hlin2 :=
    (tendsto_const_nhds : Tendsto (fun _ : ℍ => (1 / ((65520 : ℂ) * π))) atImInfty _).mul hψ
  have hsum := hlin1.add hlin2
  -- Identify the limit and simplify.
  grind only

lemma tendsto_cancel_q2_resToImagAxis :
    Tendsto
        (fun t : ℝ =>
          (fun z : ℍ =>
                (-(π : ℂ) / (28304640 : ℂ)) * (Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) +
                  (1 / ((65520 : ℂ) * π)) *
                    (ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ))))
              |>.resToImagAxis t)
        atTop (𝓝 0) :=
  Function.tendsto_resToImagAxis_atImInfty (F := _) (l := (0 : ℂ)) tendsto_cancel_q2

/-!
## The `q^{-1}` coefficient

Combining the `q^{-1}` coefficients of `varphi₂` and `ψI` gives the constant
`-(10/(117π))` in the paper's leading term.
-/

/-- The `q^{-1}` coefficient of `BKernel` at `i∞`, expressed in terms of cusp limits. -/
public lemma tendsto_q1_coeff :
    Tendsto
        (fun z : ℍ =>
          (-(π : ℂ) / (28304640 : ℂ)) *
              (((Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) - (864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) /
                q (z : ℂ)) +
            (1 / ((65520 : ℂ) * π)) *
              ((ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ)) - (2 : ℂ)) / (qHalf z) ^ (2 : ℕ)))
        atImInfty (𝓝 (-((10 : ℂ) / ((117 : ℂ) * π)))) := by
  have hV :
      Tendsto
          (fun z : ℍ =>
            ((Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) - ((864 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))) /
              q (z : ℂ))
          atImInfty (𝓝 ((2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))) :=
    tendsto_varphi₂_mul_q_sq_sub_const_div_q
  have hψ :
      Tendsto
          (fun z : ℍ =>
            (ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ)) - (2 : ℂ)) / (qHalf z) ^ (2 : ℕ))
          atImInfty (𝓝 (-464 : ℂ)) :=
    tendsto_ψI_mul_cexp_four_pi_mul_I_sub_two_div_qHalf_sq
  have hlin1 :=
    (tendsto_const_nhds : Tendsto (fun _ : ℍ => (-(π : ℂ) / (28304640 : ℂ))) atImInfty _).mul hV
  have hlin2 :=
    (tendsto_const_nhds : Tendsto (fun _ : ℍ => (1 / ((65520 : ℂ) * π))) atImInfty _).mul hψ
  have hsum := hlin1.add hlin2
  have hlim :
      (-(π : ℂ) / (28304640 : ℂ)) * ((2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) -
          ((π : ℂ)⁻¹ * ((65520 : ℂ)⁻¹ * (464 : ℂ))) =
        -((10 : ℂ) / ((117 : ℂ) * π)) := coeff_q1_value
  grind only

end BKernelAsymptotics

end

end SpherePacking.Dim24
