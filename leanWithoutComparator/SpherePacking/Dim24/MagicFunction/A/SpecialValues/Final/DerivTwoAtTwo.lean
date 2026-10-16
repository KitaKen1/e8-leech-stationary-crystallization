-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.Values
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivDefs
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.SingularIntegral
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.CoeffExp
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Aux01
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi2
import Mathlib.Analysis.Calculus.Deriv.Slope


/-!
# Derivative at `u = 2`

This file computes the derivative of `aProfile` at `u = 2` from the right-neighborhood Laurent
expansion obtained from the paper's equation `eq:avalues`.

## Main statement
* `SpecialValuesDerivTwo.aProfile_hasDerivAt_two`
-/


open scoped Real Topology
open Filter

namespace SpherePacking.Dim24

noncomputable section

/-
Derivative of `aProfile` at `u = 2`.

Target (paper `dim_24.tex`, value list after (2.16)):
`aProfile'(2) = -(2218752) * I / π`.

Proof outline:
1. Splitting `aProfile = (I₁'+I₃'+I₅') + (I₂'+I₄'+I₆')`.
2. Showing the "segment block" derivative vanishes at `u=2` since it carries the factor
   `coeffExp u = exp(π i u) + exp(-π i u) - 2`, which has a double zero at even integers.
3. Computing the derivative of the "tail block" using the analytic continuation argument
   (the part of the paper around (2.16)), combining:
   - the `Aux01` rewrite of `I₂'` and `I₄'` as horizontal integrals of `F u`,
   - the `I₆'` tail integral along the imaginary axis,
   - the `q`-expansion limit for the `q^{-1}` coefficient of `varphi₂` from `Varphi2.lean`.
-/

namespace SpecialValuesDerivTwo

open scoped Real
open Filter Complex MeasureTheory Set intervalIntegral SpecialValuesDerivTwoLaurent
open RealIntegrals

lemma coeffExp_two : SpecialValuesDeriv.coeffExp (2 : ℝ) = 0 := by
  -- `coeffExp u = exp(π i u) + exp(-π i u) - 2`.
  have hpos : Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) = (1 : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using! (Complex.exp_two_pi_mul_I)
  have hpos' : Complex.exp ((Real.pi : ℂ) * (2 : ℂ) * Complex.I) = (1 : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hpos
  have hneg : Complex.exp (-((Real.pi : ℂ) * (2 : ℂ) * Complex.I)) = (1 : ℂ) := by
    have h :=
      (Complex.exp_neg ((Real.pi : ℂ) * (2 : ℂ) * Complex.I))
    -- `exp (-x) = (exp x)⁻¹` and `exp x = 1`.
    simpa [hpos'] using! h
  -- Assemble (`1 + 1 - 2 = 0`).
  simp [SpecialValuesDeriv.coeffExp, hpos', hneg]
  norm_num

/-- `aProfile` has derivative `-(2218752) * I / π` at `u = 2`. -/
public theorem aProfile_hasDerivAt_two :
    HasDerivAt aProfile (-(2218752 : ℂ) * Complex.I / (π : ℂ)) (2 : ℝ) := by
  -- Strategy: compute the right-slope limit at `u=2` from the Laurent principal part in the paper.
  -- The differentiability of `aProfile` at `2` then identifies `deriv aProfile 2` with that limit.
  have hdiff : DifferentiableAt ℝ aProfile (2 : ℝ) :=
    differentiableAt_aProfile_of_lt (x := (2 : ℝ)) (by norm_num)
  have hderiv : HasDerivAt aProfile (deriv aProfile (2 : ℝ)) (2 : ℝ) := hdiff.hasDerivAt
  -- The `u=2` Laurent coefficients from `dim_24.tex` (eq. `eq:avalues` / `\tilde p`):
  -- after factoring out `I * coeffExp u`, the `B/(u-2)` coefficient is `B = (2218752)/π^3`.
  let B : ℂ := (2218752 : ℂ) / ((π : ℂ) ^ (3 : ℕ))
  -- The analytic remainder near `u=2` (coming from the integrable part of the Laplace transform).
  have hLaurent :
      ∃ h : ℝ → ℂ,
        ContinuousAt h (2 : ℝ) ∧
          (fun u : ℝ => aProfile u) =ᶠ[𝓝[>] (2 : ℝ)]
            fun u : ℝ =>
              (Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u) *
                (B / ((u - 2 : ℝ) : ℂ) + h u) +
                  ((725760 : ℂ) * Complex.I / (π : ℂ)) := by
    simpa [B, SpecialValuesDerivTwoLaurent.B] using!
      (SpecialValuesDerivTwoLaurent.exists_laurent_aProfile_two : _)
  rcases hLaurent with ⟨h, hhCont, hhEq⟩
  -- Convert the slope at `2` into the explicit Laurent expression.
  have hA2 : aProfile (2 : ℝ) = (725760 : ℂ) * Complex.I / (π : ℂ) := aProfile_two
  -- `coeffExp` has a double zero at `u=2`; use the explicit `sinc`-normal form around `2`.
  have hCoeff :
      (fun u : ℝ => SpecialValuesDeriv.coeffExp u) =ᶠ[𝓝 (2 : ℝ)]
        fun u : ℝ =>
          (-((Real.pi : ℂ) ^ (2 : ℕ))) * ((u - 2) ^ (2 : ℕ) : ℂ) *
            (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro u
    exact SpecialValuesDerivTwoLaurent.coeffExp_eq_neg_pi_sq_mul_sq_mul_sinc_sq_two (u := u)
  -- The right-slope limit (the only surviving contribution is from the `B/(u-2)` term).
  have hSlopeConst :
      Tendsto (slope aProfile (2 : ℝ)) (𝓝[>] (2 : ℝ))
        (𝓝 (-(2218752 : ℂ) * Complex.I / (π : ℂ))) := by
    -- Reduce `slope` to the difference quotient.
    have hle : (𝓝[>] (2 : ℝ)) ≤ (𝓝[≠] (2 : ℝ)) := by
      exact nhdsGT_le_nhdsNE 2
    have hSlopeDeriv :
        Tendsto (slope aProfile (2 : ℝ)) (𝓝[>] (2 : ℝ)) (𝓝 (deriv aProfile (2 : ℝ))) :=
      (hderiv.tendsto_slope).mono_left hle
    -- It suffices to identify `deriv aProfile 2` by uniqueness of the slope limit.
    -- We prove the slope limit directly using the Laurent form, then use uniqueness.
    have hSlopeEq :
        slope aProfile (2 : ℝ) =ᶠ[𝓝[>] (2 : ℝ)]
          fun u : ℝ => (aProfile u - aProfile (2 : ℝ)) / ((u - 2 : ℝ) : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu' : u ≠ (2 : ℝ) := ne_of_gt hu
      have huC : ((u - 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.2 hu')
      -- `slope f x u = (f u - f x) / (u - x)` on `u ≠ x`.
      simp [slope, sub_eq_add_neg, div_eq_mul_inv, mul_comm]
      ring_nf
    -- Replace `aProfile u` by the Laurent form on the punctured right neighborhood.
    have hRewrite :
        (fun u : ℝ => (aProfile u - aProfile (2 : ℝ)) / ((u - 2 : ℝ) : ℂ)) =ᶠ[𝓝[>] (2 : ℝ)]
          fun u : ℝ =>
            (Complex.I : ℂ) *
              (SpecialValuesDeriv.coeffExp u / ((u - 2) ^ (2 : ℕ) : ℂ)) * B +
              (Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u / ((u - 2 : ℝ) : ℂ)) * (h u) := by
      filter_upwards [hhEq, self_mem_nhdsWithin] with u huEq hu
      have hu' : u ≠ (2 : ℝ) := ne_of_gt hu
      have hA2' : aProfile (2 : ℝ) = (725760 : ℂ) * Complex.I / (π : ℂ) := hA2
      -- Expand the difference quotient using the Laurent form,
      -- keeping the cancellation by `(u-2)` explicit.
      set d : ℂ := ((u - 2 : ℝ) : ℂ)
      have hd : d ≠ 0 := by
        dsimp [d]
        exact_mod_cast (sub_ne_zero.2 hu')
      have hdiv : (B / d + h u) / d = B / (d ^ (2 : ℕ)) + (h u) / d := by
        -- Pure field algebra.
        field_simp [hd]
      have hnum :
          aProfile u - aProfile (2 : ℝ) =
            (Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u * (B / d + h u) := by
        -- Cancel the constant term `aProfile 2`.
        simp [huEq, hA2', d, sub_eq_add_neg, add_left_comm, add_comm, mul_assoc]
      calc
        (aProfile u - aProfile (2 : ℝ)) / d
            = ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u * (B / d + h u)) / d := by
                simp [hnum]
        _ = (Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u * ((B / d + h u) / d) := by
              -- regroup the `( / d)` for the outer factor.
              simp [mul_div_assoc]
        _ =
            (Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u * (B / (d ^ (2 : ℕ)) + (h u) / d) := by
              simp [hdiv]
        _ =
            (Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u / (d ^ (2 : ℕ))) * B +
              (Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u / d) * (h u) := by
              -- Distribute and commute factors.
              simp [mul_add, add_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ =
            (Complex.I : ℂ) *
                (SpecialValuesDeriv.coeffExp u / ((u - 2) ^ (2 : ℕ) : ℂ)) * B +
              (Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u / ((u - 2 : ℝ) : ℂ)) * h u := by
              -- Replace `d` by `u-2`.
              simp [d, pow_two, mul_left_comm, mul_comm]
    -- Now compute the limit: `coeffExp/(u-2)^2 → -π^2`, and `coeffExp → 0`.
    have hCoeff2 :
        Tendsto (fun u : ℝ => SpecialValuesDeriv.coeffExp u / ((u - 2) ^ (2 : ℕ) : ℂ))
          (𝓝[>] (2 : ℝ)) (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)))) := by
      -- Use the `sinc` normal form.
      have hEq :
          (fun u : ℝ => SpecialValuesDeriv.coeffExp u / ((u - 2) ^ (2 : ℕ) : ℂ)) =ᶠ[𝓝[>] (2 : ℝ)]
            fun u : ℝ =>
              (-((Real.pi : ℂ) ^ (2 : ℕ))) *
                (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu' : (u - 2 : ℝ) ≠ 0 := sub_ne_zero.2 (ne_of_gt hu)
        have huC : ((u - 2) ^ (2 : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast (pow_ne_zero 2 hu')
        -- Divide the `sinc`-normal form by `(u-2)^2` and cancel.
        let s : ℂ :=
          (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ)
        have hform := coeffExp_eq_neg_pi_sq_mul_sq_mul_sinc_sq_two (u := u)
        grind only
      have hSinc :
          Tendsto
            (fun u : ℝ => (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
            (𝓝[>] (2 : ℝ)) (𝓝 (1 : ℂ)) := by
        have hcont :
            ContinuousAt
              (fun u : ℝ => (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
              (2 : ℝ) := by
          fun_prop
        have hlim :
            Tendsto
              (fun u : ℝ => (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
              (𝓝[>] (2 : ℝ)) (𝓝 (((Real.sinc 0) ^ (2 : ℕ) : ℝ) : ℂ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds (by simpa using! hcont.tendsto)
        simpa using! hlim
      have hmain :
          Tendsto
            (fun u : ℝ =>
              (-((Real.pi : ℂ) ^ (2 : ℕ))) *
                (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
            (𝓝[>] (2 : ℝ)) (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)))) := by
        have hconst :
            Tendsto (fun _u : ℝ => (-((Real.pi : ℂ) ^ (2 : ℕ)))) (𝓝[>] (2 : ℝ))
              (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)))) :=
          (tendsto_const_nhds : Tendsto (fun _u : ℝ => (-((Real.pi : ℂ) ^ (2 : ℕ)))) (𝓝[>] (2 : ℝ))
            (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)))))
        have h := hconst.mul hSinc
        simpa [mul_assoc] using! h
      simpa using! (hmain.congr' hEq.symm)
    have hCoeff1 :
        Tendsto (fun u : ℝ => SpecialValuesDeriv.coeffExp u / ((u - 2 : ℝ) : ℂ))
          (𝓝[>] (2 : ℝ)) (𝓝 (0 : ℂ)) := by
      -- Use the `sinc` normal form and cancel one factor of `(u-2)`.
      have hEq :
          (fun u : ℝ => SpecialValuesDeriv.coeffExp u / ((u - 2 : ℝ) : ℂ)) =ᶠ[𝓝[>] (2 : ℝ)]
            fun u : ℝ =>
              (-((Real.pi : ℂ) ^ (2 : ℕ))) * (((u - 2 : ℝ) : ℂ)) *
                (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu' : (u - 2 : ℝ) ≠ 0 := sub_ne_zero.2 (ne_of_gt hu)
        have huC : ((u - 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu'
        have hform := coeffExp_eq_neg_pi_sq_mul_sq_mul_sinc_sq_two (u := u)
        -- Cancel one factor of `(u-2)`.
        set d : ℂ := ((u - 2 : ℝ) : ℂ)
        set s : ℂ := (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ)
        have hd : d ≠ 0 := by simpa [d] using! huC
        have :
            SpecialValuesDeriv.coeffExp u / d =
              (-((Real.pi : ℂ) ^ (2 : ℕ))) * d * s := by
          calc
            SpecialValuesDeriv.coeffExp u / d =
                (-((Real.pi : ℂ) ^ (2 : ℕ))) * ((u - 2) ^ (2 : ℕ) : ℂ) * s / d := by
                  simp [hform, s, d, mul_assoc]
            _ =
                (-((Real.pi : ℂ) ^ (2 : ℕ))) * (d ^ (2 : ℕ)) * s / d := by
                  simp [d, pow_two, mul_assoc]
            _ = d * ((-((Real.pi : ℂ) ^ (2 : ℕ))) * d * s) / d := by
                  ring_nf
            _ = (-((Real.pi : ℂ) ^ (2 : ℕ))) * d * s := by
                  simpa [mul_assoc] using!
                    (mul_div_cancel_left₀ ((-((Real.pi : ℂ) ^ (2 : ℕ))) * d * s) (a := d) hd)
        simpa [d, s, mul_assoc, mul_left_comm, mul_comm] using! this
      have hsub0 :
          Tendsto (fun u : ℝ => ((u - 2 : ℝ) : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝 (0 : ℂ)) := by
        have hcont : ContinuousAt (fun u : ℝ => ((u - 2 : ℝ) : ℂ)) (2 : ℝ) := by fun_prop
        exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using! hcont.tendsto)
      have hSinc :
          Tendsto
            (fun u : ℝ => (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
            (𝓝[>] (2 : ℝ)) (𝓝 (1 : ℂ)) := by
        have hcont :
            ContinuousAt
              (fun u : ℝ => (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
              (2 : ℝ) := by
          fun_prop
        have hlim :
            Tendsto
              (fun u : ℝ => (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
              (𝓝[>] (2 : ℝ)) (𝓝 (((Real.sinc 0) ^ (2 : ℕ) : ℝ) : ℂ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds (by simpa using! hcont.tendsto)
        simpa using! hlim
      have hconst :
          Tendsto (fun _u : ℝ => (-((Real.pi : ℂ) ^ (2 : ℕ)))) (𝓝[>] (2 : ℝ))
            (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)))) := tendsto_const_nhds
      have hprod :
          Tendsto
              (fun u : ℝ =>
                (-((Real.pi : ℂ) ^ (2 : ℕ))) * ((u - 2 : ℝ) : ℂ) *
                  (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
              (𝓝[>] (2 : ℝ)) (𝓝 (0 : ℂ)) := by
        -- constant * (u-2) * sinc^2 → constant * 0 * 1 = 0
        simpa [mul_assoc] using! (hconst.mul (hsub0.mul hSinc))
      exact (hprod.congr' hEq.symm)
    have hH : Tendsto h (𝓝[>] (2 : ℝ)) (𝓝 (h (2 : ℝ))) :=
      hhCont.tendsto.mono_left nhdsWithin_le_nhds
    have hTerm1 :
        Tendsto
            (fun u : ℝ =>
              (Complex.I : ℂ) *
                (SpecialValuesDeriv.coeffExp u / ((u - 2) ^ (2 : ℕ) : ℂ)) * B)
            (𝓝[>] (2 : ℝ))
            (𝓝 ((Complex.I : ℂ) * (-((Real.pi : ℂ) ^ (2 : ℕ))) * B)) := by
      simpa [mul_assoc] using! (tendsto_const_nhds.mul (hCoeff2.mul tendsto_const_nhds))
    have hTerm2 :
        Tendsto
            (fun u : ℝ =>
              (Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u / ((u - 2 : ℝ) : ℂ)) * h u)
            (𝓝[>] (2 : ℝ)) (𝓝 (0 : ℂ)) := by
      -- `coeffExp/(u-2) → 0` and `h u` is bounded near `2`.
      simpa [mul_assoc] using! (tendsto_const_nhds.mul (hCoeff1.mul hH))
    have hSum :
        Tendsto
            (fun u : ℝ =>
              (Complex.I : ℂ) *
                  (SpecialValuesDeriv.coeffExp u / ((u - 2) ^ (2 : ℕ) : ℂ)) * B +
                (Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u / ((u - 2 : ℝ) : ℂ)) * (h u))
            (𝓝[>] (2 : ℝ))
            (𝓝 ((Complex.I : ℂ) * (-((Real.pi : ℂ) ^ (2 : ℕ))) * B)) := by
      simpa using! (hTerm1.add hTerm2)
    have hMain :
        Tendsto (fun u : ℝ => (aProfile u - aProfile (2 : ℝ)) / ((u - 2 : ℝ) : ℂ))
          (𝓝[>] (2 : ℝ)) (𝓝 ((Complex.I : ℂ) * (-((Real.pi : ℂ) ^ (2 : ℕ))) * B)) := by
      exact (hSum.congr' hRewrite.symm)
    have hMain' :
        Tendsto (fun u : ℝ => slope aProfile (2 : ℝ) u) (𝓝[>] (2 : ℝ))
          (𝓝 ((Complex.I : ℂ) * (-((Real.pi : ℂ) ^ (2 : ℕ))) * B)) := by
      exact hMain.congr' hSlopeEq.symm
    -- Rewrite the constant into the target form.
    have hconst :
        -((Complex.I : ℂ) * ((Real.pi : ℂ) ^ (2 : ℕ)) * B) =
          (-(2218752 : ℂ) * Complex.I / (π : ℂ)) := by
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [B, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      field_simp [hpi]
    simpa [hconst] using! hMain'
  -- Conclude by uniqueness of the slope limit.
  have hEqDeriv : deriv aProfile (2 : ℝ) = (-(2218752 : ℂ) * Complex.I / (π : ℂ)) := by
    have hle : (𝓝[>] (2 : ℝ)) ≤ (𝓝[≠] (2 : ℝ)) := by
      exact nhdsGT_le_nhdsNE 2
    have hSlopeDeriv :
        Tendsto (slope aProfile (2 : ℝ)) (𝓝[>] (2 : ℝ)) (𝓝 (deriv aProfile (2 : ℝ))) :=
      (hderiv.tendsto_slope).mono_left hle
    exact tendsto_nhds_unique hSlopeDeriv hSlopeConst
  simpa [hEqDeriv] using! hderiv

end SpecialValuesDerivTwo

end

end SpherePacking.Dim24
