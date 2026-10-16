-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Basic
import Mathlib.Analysis.Complex.Exponential
import SpherePacking.ModularForms.QExpansion
import SpherePacking.ForMathlib.SigmaSummability

/-!
# Second-order `q`-expansion coefficients for `E₄` and `E₆`

This file extracts the second and third coefficients in the `q`-expansions of `E₄` and `E₆`
as `z → i∞`. These limits are used when identifying the constant term of `varphi₂` and in the
large-`t` remainder estimate for `eq:phip` in `dim_24.tex`.

## Main statements
* `tendsto_E₄_coeff_two`, `tendsto_E₆_coeff_two`
* `tendsto_E₄_coeff_three`, `tendsto_E₆_coeff_three`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesVarphi₁Limits

open scoped Complex Interval Real Topology BigOperators Nat ArithmeticFunction.sigma
open Filter Complex UpperHalfPlane intervalIntegral MeasureTheory Set Function
open SlashInvariantFormClass ModularFormClass

/-!
### Second and third coefficients for `E₄` and `E₆`

We extract coefficients from the `q`-series definitions using `QExp.tendsto_nat` and the same
summability bounds as in `tendsto_E₄_sub_one_div_q` and `tendsto_E₆_sub_one_div_q`.
-/

lemma summable_sigma_three_shift (k : ℕ) :
    Summable (fun n : ℕ => ‖(σ 3 (n + k) : ℂ)‖ * Real.exp (-2 * Real.pi * n)) := by
  refine (ForMathlib.summable_norm_sigma_shift_mul_exp (k := 3) (m := 4) (s := k) ?_)
  intro n
  norm_cast
  simpa using! (ForMathlib.sigma_three_le_pow_four (n + k))

lemma summable_sigma_five_shift (k : ℕ) :
    Summable (fun n : ℕ => ‖(σ 5 (n + k) : ℂ)‖ * Real.exp (-2 * Real.pi * n)) := by
  refine (ForMathlib.summable_norm_sigma_shift_mul_exp (k := 5) (m := 6) (s := k) ?_)
  intro n
  norm_cast
  simpa using! (sigma_five_le_pow_six (n + k))

/-- Second `q`-coefficient for `E₄`: `((E₄-1)/q - 240)/q → 2160` as `z → i∞`. -/
public lemma tendsto_E₄_coeff_two :
    Tendsto
      (fun z : ℍ => ((E₄ z - (1 : ℂ)) / q (z : ℂ) - (240 : ℂ)) / q (z : ℂ))
      atImInfty (𝓝 (2160 : ℂ)) := by
  -- Limit of the shifted `q`-series.
  let a : ℕ → ℂ := fun n => (σ 3 (n + 2) : ℂ)
  have ha :
      Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    simpa [a] using! (summable_sigma_three_shift 2)
  have hseries :
      Tendsto (fun z : ℍ => ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * z * n)) atImInfty
        (𝓝 (a 0)) :=
    QExp.tendsto_nat (a := a) (ha := ha)
  have hσ : σ 3 2 = 9 := by decide
  have ha0 : a 0 = (9 : ℂ) := by
    dsimp [a]
    simpa using! congrArg (fun m : ℕ => (m : ℂ)) hσ
  have hseries' :
      Tendsto (fun z : ℍ => (240 : ℂ) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (2160 : ℂ)) := by
    have hconst :
        Tendsto (fun _z : ℍ => (240 : ℂ)) atImInfty (𝓝 (240 : ℂ)) :=
      (tendsto_const_nhds : Tendsto (fun _z : ℍ => (240 : ℂ)) atImInfty (𝓝 (240 : ℂ)))
    have hmul := hconst.mul hseries
    have hprod : (240 : ℂ) * a 0 = (2160 : ℂ) := by
      simp [ha0]
      norm_num
    simpa [hprod] using! hmul
  have hEq : ∀ z : ℍ,
      ((E₄ z - (1 : ℂ)) / q (z : ℂ) - (240 : ℂ)) / q (z : ℂ) =
        (240 : ℂ) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    intro z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    let qz : ℂ := q (z : ℂ)
    -- Use the `q`-expansion of `E₄` expressed in powers of `qz`.
    let c : ℕ → ℂ := fun m => if m = 0 then 1 else (240 : ℂ) * (σ 3 m : ℂ)
    let f : ℕ → ℂ := fun m => c m * qz ^ m
    have hper :
        (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma 1 : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
      simp [CongruenceSubgroup.strictPeriods_Gamma]
    have hF : HasSum (fun m : ℕ => f m) (E₄ z) := by
      have hsum :=
        ModularForm.hasSum_qExpansion (f := E₄) (h := (1 : ℝ)) (by positivity) hper z
      refine HasSum.congr_fun hsum (fun m => ?_)
      have hcoeff : (qExpansion (1 : ℝ) E₄).coeff m = c m := by
        simpa [c] using! congr_fun E4_q_exp m
      have hqparam : Periodic.qParam (1 : ℝ) (z : ℂ) = qz := by
        simp [Periodic.qParam, qz, q]
      simp [f, smul_eq_mul, hcoeff, hqparam, qz]
    have hsumf : Summable f := hF.summable
    have hsplit :
        (Finset.range 2).sum f + (∑' n : ℕ, f (n + 2)) = ∑' n : ℕ, f n := by
      simpa using! (Summable.sum_add_tsum_nat_add 2 hsumf)
    have hf0 : f 0 = (1 : ℂ) := by simp [f, c]
    have hf1 : f 1 = (240 : ℂ) * qz := by simp [f, c, qz]
    have hsumRange : (Finset.range 2).sum f = f 0 + f 1 := by
      simp [Finset.sum_range_succ]
    have htail :
        (∑' n : ℕ, f (n + 2)) = E₄ z - (f 0 + f 1) := by
      have htail0 :
          (∑' n : ℕ, f (n + 2)) = (∑' n : ℕ, f n) - (Finset.range 2).sum f :=
        eq_sub_of_add_eq' hsplit
      simpa [hF.tsum_eq, hsumRange, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! htail0
    have hL :
        ((E₄ z - (1 : ℂ)) / q (z : ℂ) - (240 : ℂ)) / q (z : ℂ) =
          (E₄ z - (1 : ℂ) - (240 : ℂ) * qz) / qz ^ (2 : ℕ) := by
      -- Pure algebra in the field `ℂ`.
      have hqz2 : qz ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hzq
      field_simp [qz, hzq, hqz2, pow_two]
      ring
    have htail2 :
        (E₄ z - (1 : ℂ) - (240 : ℂ) * qz) = ∑' n : ℕ, f (n + 2) := by
      -- Replace `E₄ z - (f0 + f1)` by the shifted sum.
      simpa [hf0, hf1, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using!
        htail.symm
    have hterm (n : ℕ) :
        f (n + 2) / qz ^ (2 : ℕ) = (240 : ℂ) * a n * qz ^ n := by
      grind only
    have hsumDiv :
        (∑' n : ℕ, f (n + 2)) / qz ^ (2 : ℕ) = ∑' n : ℕ, (240 : ℂ) * a n * qz ^ n := by
      -- Move the scalar division inside the sum and rewrite each term.
      calc
        (∑' n : ℕ, f (n + 2)) / qz ^ (2 : ℕ) = ∑' n : ℕ, f (n + 2) / qz ^ (2 : ℕ) := by
          simpa using!
            (tsum_div_const (f := fun n : ℕ => f (n + 2)) (a := qz ^ (2 : ℕ))).symm
        _ = ∑' n : ℕ, (240 : ℂ) * a n * qz ^ n :=
          tsum_congr hterm
    -- Convert `qz^n` into `cexp(2π i z n)` and pull out constants.
    have hqpow (n : ℕ) :
        qz ^ n = Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      unfold qz q
      simpa [mul_assoc, mul_left_comm, mul_comm] using!
        (Complex.exp_nat_mul (2 * π * Complex.I * (z : ℂ)) n).symm
    have hsumExp :
        (∑' n : ℕ, (240 : ℂ) * a n * qz ^ n) =
          (240 : ℂ) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      -- Factor out `240` and rewrite each `qz^n`.
      calc
        (∑' n : ℕ, (240 : ℂ) * a n * qz ^ n)
            = (∑' n : ℕ, (240 : ℂ) * (a n * qz ^ n)) := by
                refine tsum_congr ?_; intro n; ring_nf
        _ = (240 : ℂ) * ∑' n : ℕ, (a n * qz ^ n) := by
              simp [tsum_mul_left]
        _ = (240 : ℂ) * ∑' n : ℕ, (a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) := by
              refine congrArg (fun S => (240 : ℂ) * S) (tsum_congr ?_)
              intro n
              simp [hqpow n]
        _ = (240 : ℂ) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
              simp [mul_assoc]
    -- Assemble.
    -- Replace `q (z:ℂ)` by `qz` and use the shifted series identity.
    lia
  refine Tendsto.congr' (Filter.Eventually.of_forall (fun z => (hEq z).symm)) hseries'

/-- Second `q`-coefficient for `E₆`: `((E₆-1)/q + 504)/q → -16632` as `z → i∞`. -/
public lemma tendsto_E₆_coeff_two :
    Tendsto
      (fun z : ℍ => ((E₆ z - (1 : ℂ)) / q (z : ℂ) - (-(504 : ℂ))) / q (z : ℂ))
      atImInfty (𝓝 (-(16632 : ℂ))) := by
  -- Limit of the shifted `q`-series.
  let a : ℕ → ℂ := fun n => (σ 5 (n + 2) : ℂ)
  have ha :
      Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    simpa [a] using! (summable_sigma_five_shift 2)
  have hseries :
      Tendsto (fun z : ℍ => ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * z * n)) atImInfty
        (𝓝 (a 0)) :=
    QExp.tendsto_nat (a := a) (ha := ha)
  have hσ : σ 5 2 = 33 := by decide
  have ha0 : a 0 = (33 : ℂ) := by
    dsimp [a]
    simpa using! congrArg (fun m : ℕ => (m : ℂ)) hσ
  have hseries' :
      Tendsto (fun z : ℍ => (-(504 : ℂ)) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (-(16632 : ℂ))) := by
    have hconst :
        Tendsto (fun _z : ℍ => (-(504 : ℂ))) atImInfty (𝓝 (-(504 : ℂ))) :=
      (tendsto_const_nhds : Tendsto (fun _z : ℍ => (-(504 : ℂ))) atImInfty (𝓝 (-(504 : ℂ))))
    have hmul := hconst.mul hseries
    have hprod : (-(504 : ℂ)) * a 0 = (-(16632 : ℂ)) := by
      simp [ha0]
      norm_num
    simpa [hprod] using! hmul
  have hEq : ∀ z : ℍ,
      ((E₆ z - (1 : ℂ)) / q (z : ℂ) - (-(504 : ℂ))) / q (z : ℂ) =
        (-(504 : ℂ)) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    intro z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    let qz : ℂ := q (z : ℂ)
    -- Use the `q`-expansion of `E₆` expressed in powers of `qz`.
    let c : ℕ → ℂ := fun m => if m = 0 then 1 else (-(504 : ℂ)) * (σ 5 m : ℂ)
    let f : ℕ → ℂ := fun m => c m * qz ^ m
    have hper :
        (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma 1 : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
      simp [CongruenceSubgroup.strictPeriods_Gamma]
    have hF : HasSum (fun m : ℕ => f m) (E₆ z) := by
      have hsum :=
        ModularForm.hasSum_qExpansion (f := E₆) (h := (1 : ℝ)) (by positivity) hper z
      refine HasSum.congr_fun hsum (fun m => ?_)
      have hcoeff : (qExpansion (1 : ℝ) E₆).coeff m = c m := by
        simpa [c] using! congr_fun E6_q_exp m
      have hqparam : Periodic.qParam (1 : ℝ) (z : ℂ) = qz := by
        simp [Periodic.qParam, qz, q]
      simp [f, smul_eq_mul, hcoeff, hqparam, qz]
    have hsumf : Summable f := hF.summable
    have hsplit :
        (Finset.range 2).sum f + (∑' n : ℕ, f (n + 2)) = ∑' n : ℕ, f n := by
      simpa using! (Summable.sum_add_tsum_nat_add 2 hsumf)
    have hf0 : f 0 = (1 : ℂ) := by simp [f, c]
    have hf1 : f 1 = (-(504 : ℂ)) * qz := by simp [f, c, qz]
    have hsumRange : (Finset.range 2).sum f = f 0 + f 1 := by
      simp [Finset.sum_range_succ]
    have htail :
        (∑' n : ℕ, f (n + 2)) = E₆ z - (f 0 + f 1) := by
      have htail0 :
          (∑' n : ℕ, f (n + 2)) = (∑' n : ℕ, f n) - (Finset.range 2).sum f :=
        eq_sub_of_add_eq' hsplit
      simpa [hF.tsum_eq, hsumRange, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! htail0
    have hL :
        ((E₆ z - (1 : ℂ)) / q (z : ℂ) - (-(504 : ℂ))) / q (z : ℂ) =
          (E₆ z - (1 : ℂ) - (-(504 : ℂ)) * qz) / qz ^ (2 : ℕ) := by
      have hqz2 : qz ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hzq
      field_simp [qz, hzq, hqz2, pow_two]
      ring
    have htail2 :
        (E₆ z - (1 : ℂ) - (-(504 : ℂ)) * qz) = ∑' n : ℕ, f (n + 2) := by
      simpa [hf0, hf1, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using!
        htail.symm
    have hterm (n : ℕ) :
        f (n + 2) / qz ^ (2 : ℕ) = (-(504 : ℂ)) * a n * qz ^ n := by
      grind only
    have hsumDiv :
        (∑' n : ℕ, f (n + 2)) / qz ^ (2 : ℕ) = ∑' n : ℕ, (-(504 : ℂ)) * a n * qz ^ n := by
      calc
        (∑' n : ℕ, f (n + 2)) / qz ^ (2 : ℕ) = ∑' n : ℕ, f (n + 2) / qz ^ (2 : ℕ) := by
          simpa using!
            (tsum_div_const (f := fun n : ℕ => f (n + 2)) (a := qz ^ (2 : ℕ))).symm
        _ = ∑' n : ℕ, (-(504 : ℂ)) * a n * qz ^ n := by
          exact tsum_congr hterm
    have hqpow (n : ℕ) :
        qz ^ n = Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      unfold qz q
      simpa [mul_assoc, mul_left_comm, mul_comm] using!
        (Complex.exp_nat_mul (2 * π * Complex.I * (z : ℂ)) n).symm
    have hsumExp :
        (∑' n : ℕ, (-(504 : ℂ)) * a n * qz ^ n) =
          (-(504 : ℂ)) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      calc
        (∑' n : ℕ, (-(504 : ℂ)) * a n * qz ^ n)
            = (∑' n : ℕ, (-(504 : ℂ)) * (a n * qz ^ n)) := by
                refine tsum_congr ?_; intro n; ring_nf
        _ = (-(504 : ℂ)) * ∑' n : ℕ, (a n * qz ^ n) := by
              simpa [mul_assoc] using!
                (tsum_mul_left (a := (-(504 : ℂ))) (f := fun n : ℕ => a n * qz ^ n))
        _ =
            (-(504 : ℂ)) *
              ∑' n : ℕ, (a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) := by
              refine congrArg (fun S => (-(504 : ℂ)) * S) (tsum_congr ?_)
              intro n
              simp [hqpow n]
        _ = (-(504 : ℂ)) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
              simp [mul_assoc]
    lia
  refine Tendsto.congr' (Filter.Eventually.of_forall (fun z => (hEq z).symm)) hseries'

/-- Third `q`-coefficient for `E₄`: the next coefficient after `240` and `2160`. -/
public lemma tendsto_E₄_coeff_three :
    Tendsto
        (fun z : ℍ =>
          ((((E₄ z - (1 : ℂ)) / q (z : ℂ) - (240 : ℂ)) / q (z : ℂ)) - (2160 : ℂ)) / q (z : ℂ))
        atImInfty (𝓝 (6720 : ℂ)) := by
  -- Limit of the shifted `q`-series.
  let a : ℕ → ℂ := fun n => (σ 3 (n + 3) : ℂ)
  have ha :
      Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    simpa [a] using! (summable_sigma_three_shift 3)
  have hseries :
      Tendsto (fun z : ℍ => ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * z * n)) atImInfty
        (𝓝 (a 0)) :=
    QExp.tendsto_nat (a := a) (ha := ha)
  have hσ : σ 3 3 = 28 := by decide
  have ha0 : a 0 = (28 : ℂ) := by
    dsimp [a]
    simpa using! congrArg (fun m : ℕ => (m : ℂ)) hσ
  have hseries' :
      Tendsto (fun z : ℍ => (240 : ℂ) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (6720 : ℂ)) := by
    have hconst :
        Tendsto (fun _z : ℍ => (240 : ℂ)) atImInfty (𝓝 (240 : ℂ)) :=
      (tendsto_const_nhds : Tendsto (fun _z : ℍ => (240 : ℂ)) atImInfty (𝓝 (240 : ℂ)))
    have hmul := hconst.mul hseries
    have hprod : (240 : ℂ) * a 0 = (6720 : ℂ) := by
      simp [ha0]
      norm_num
    simpa [hprod] using! hmul
  have hEq : ∀ z : ℍ,
      ((((E₄ z - (1 : ℂ)) / q (z : ℂ) - (240 : ℂ)) / q (z : ℂ)) - (2160 : ℂ)) / q (z : ℂ) =
        (240 : ℂ) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    intro z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    let qz : ℂ := q (z : ℂ)
    let c : ℕ → ℂ := fun m => if m = 0 then 1 else (240 : ℂ) * (σ 3 m : ℂ)
    let f : ℕ → ℂ := fun m => c m * qz ^ m
    have hper :
        (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma 1 : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
      simp [CongruenceSubgroup.strictPeriods_Gamma]
    have hF : HasSum (fun m : ℕ => f m) (E₄ z) := by
      have hsum :=
        ModularForm.hasSum_qExpansion (f := E₄) (h := (1 : ℝ)) (by positivity) hper z
      refine HasSum.congr_fun hsum (fun m => ?_)
      have hcoeff : (qExpansion (1 : ℝ) E₄).coeff m = c m := by
        simpa [c] using! congr_fun E4_q_exp m
      have hqparam : Periodic.qParam (1 : ℝ) (z : ℂ) = qz := by
        simp [Periodic.qParam, qz, q]
      simp [f, smul_eq_mul, hcoeff, hqparam, qz]
    have hsumf : Summable f := hF.summable
    have hsplit :
        (Finset.range 3).sum f + (∑' n : ℕ, f (n + 3)) = ∑' n : ℕ, f n := by
      simpa using! (Summable.sum_add_tsum_nat_add 3 hsumf)
    have hf0 : f 0 = (1 : ℂ) := by simp [f, c]
    have hf1 : f 1 = (240 : ℂ) * qz := by simp [f, c, qz]
    have hsigma2 : σ 3 2 = 9 := by decide
    have hf2 : f 2 = (2160 : ℂ) * qz ^ (2 : ℕ) := by
      have : (σ 3 2 : ℂ) = (9 : ℂ) := by
        simpa using! congrArg (fun m : ℕ => (m : ℂ)) hsigma2
      simp [f, c, this, qz, pow_two, mul_left_comm, mul_comm]
      ring_nf
    have hsumRange : (Finset.range 3).sum f = f 0 + f 1 + f 2 := by
      -- Expand `range 3` by successive `sum_range_succ`.
      simp [Finset.sum_range_succ]
    have htail :
        (∑' n : ℕ, f (n + 3)) = E₄ z - (f 0 + f 1 + f 2) := by
      have htail0 :
          (∑' n : ℕ, f (n + 3)) = (∑' n : ℕ, f n) - (Finset.range 3).sum f :=
        eq_sub_of_add_eq' hsplit
      -- Rewrite `∑ f = E₄ z` and expand the finite sum.
      simpa [hF.tsum_eq, hsumRange] using! htail0
    have hL :
        ((((E₄ z - (1 : ℂ)) / q (z : ℂ) - (240 : ℂ)) / q (z : ℂ)) - (2160 : ℂ)) / q (z : ℂ) =
          (E₄ z - (1 : ℂ) - (240 : ℂ) * qz - (2160 : ℂ) * qz ^ (2 : ℕ)) / qz ^ (3 : ℕ) := by
      have hqz3 : qz ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hzq
      field_simp [qz, hzq, hqz3, pow_two, pow_three]
      ring
    have htail2 :
        (E₄ z - (1 : ℂ) - (240 : ℂ) * qz - (2160 : ℂ) * qz ^ (2 : ℕ)) = ∑' n : ℕ, f (n + 3) := by
      -- Start from the tail identity and rewrite `f 0, f 1, f 2`.
      grind only
    have hterm (n : ℕ) :
        f (n + 3) / qz ^ (3 : ℕ) = (240 : ℂ) * a n * qz ^ n := by
      grind only
    have hsumDiv :
        (∑' n : ℕ, f (n + 3)) / qz ^ (3 : ℕ) = ∑' n : ℕ, (240 : ℂ) * a n * qz ^ n := by
      calc
        (∑' n : ℕ, f (n + 3)) / qz ^ (3 : ℕ) = ∑' n : ℕ, f (n + 3) / qz ^ (3 : ℕ) := by
          simpa using!
            (tsum_div_const (f := fun n : ℕ => f (n + 3)) (a := qz ^ (3 : ℕ))).symm
        _ = ∑' n : ℕ, (240 : ℂ) * a n * qz ^ n :=
          tsum_congr hterm
    have hqpow (n : ℕ) :
        qz ^ n = Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      unfold qz q
      simpa [mul_assoc, mul_left_comm, mul_comm] using!
        (Complex.exp_nat_mul (2 * π * Complex.I * (z : ℂ)) n).symm
    have hsumExp :
        (∑' n : ℕ, (240 : ℂ) * a n * qz ^ n) =
          (240 : ℂ) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      calc
        (∑' n : ℕ, (240 : ℂ) * a n * qz ^ n) = (∑' n : ℕ, (240 : ℂ) * (a n * qz ^ n)) := by
          refine tsum_congr ?_; intro n; ring_nf
        _ = (240 : ℂ) * ∑' n : ℕ, (a n * qz ^ n) := by
              simpa [mul_assoc] using!
                (tsum_mul_left (a := (240 : ℂ)) (f := fun n : ℕ => a n * qz ^ n))
        _ = (240 : ℂ) * ∑' n : ℕ, (a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) := by
              refine congrArg (fun S => (240 : ℂ) * S) (tsum_congr ?_)
              intro n
              simp [hqpow n]
        _ = (240 : ℂ) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
              simp [mul_assoc]
    lia
  refine Tendsto.congr' (Filter.Eventually.of_forall (fun z => (hEq z).symm)) hseries'

/-- Third `q`-coefficient for `E₆`: the next coefficient after `-504` and `-16632`. -/
public lemma tendsto_E₆_coeff_three :
    Tendsto
      (fun z : ℍ =>
        ((((E₆ z - (1 : ℂ)) / q (z : ℂ) - (-(504 : ℂ))) / q (z : ℂ)) - (-(16632 : ℂ))) /
          q (z : ℂ))
      atImInfty (𝓝 (-(122976 : ℂ))) := by
  -- Limit of the shifted `q`-series.
  let a : ℕ → ℂ := fun n => (σ 5 (n + 3) : ℂ)
  have ha :
      Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    simpa [a] using! (summable_sigma_five_shift 3)
  have hseries :
      Tendsto (fun z : ℍ => ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * z * n)) atImInfty
        (𝓝 (a 0)) :=
    QExp.tendsto_nat (a := a) (ha := ha)
  have hσ : σ 5 3 = 244 := by decide
  have ha0 : a 0 = (244 : ℂ) := by
    dsimp [a]
    simpa using! congrArg (fun m : ℕ => (m : ℂ)) hσ
  have hseries' :
      Tendsto (fun z : ℍ => (-(504 : ℂ)) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (-(122976 : ℂ))) := by
    have hconst :
        Tendsto (fun _z : ℍ => (-(504 : ℂ))) atImInfty (𝓝 (-(504 : ℂ))) :=
      (tendsto_const_nhds : Tendsto (fun _z : ℍ => (-(504 : ℂ))) atImInfty (𝓝 (-(504 : ℂ))))
    have hmul := hconst.mul hseries
    have hprod : (-(504 : ℂ)) * a 0 = (-(122976 : ℂ)) := by
      simp [ha0]
      norm_num
    simpa [hprod] using! hmul
  have hEq : ∀ z : ℍ,
      ((((E₆ z - (1 : ℂ)) / q (z : ℂ) - (-(504 : ℂ))) / q (z : ℂ)) - (-(16632 : ℂ))) / q (z : ℂ) =
        (-(504 : ℂ)) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    intro z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    let qz : ℂ := q (z : ℂ)
    let c : ℕ → ℂ := fun m => if m = 0 then 1 else (-(504 : ℂ)) * (σ 5 m : ℂ)
    let f : ℕ → ℂ := fun m => c m * qz ^ m
    have hper :
        (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma 1 : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
      simp [CongruenceSubgroup.strictPeriods_Gamma]
    have hF : HasSum (fun m : ℕ => f m) (E₆ z) := by
      have hsum :=
        ModularForm.hasSum_qExpansion (f := E₆) (h := (1 : ℝ)) (by positivity) hper z
      refine HasSum.congr_fun hsum (fun m => ?_)
      have hcoeff : (qExpansion (1 : ℝ) E₆).coeff m = c m := by
        simpa [c] using! congr_fun E6_q_exp m
      have hqparam : Periodic.qParam (1 : ℝ) (z : ℂ) = qz := by
        simp [Periodic.qParam, qz, q]
      simp [f, smul_eq_mul, hcoeff, hqparam, qz]
    have hsumf : Summable f := hF.summable
    have hsplit :
        (Finset.range 3).sum f + (∑' n : ℕ, f (n + 3)) = ∑' n : ℕ, f n := by
      simpa using! (Summable.sum_add_tsum_nat_add 3 hsumf)
    have hf0 : f 0 = (1 : ℂ) := by simp [f, c]
    have hf1 : f 1 = (-(504 : ℂ)) * qz := by simp [f, c, qz]
    have hsigma2 : σ 5 2 = 33 := by decide
    have hf2 : f 2 = (-(16632 : ℂ)) * qz ^ (2 : ℕ) := by
      have : (σ 5 2 : ℂ) = (33 : ℂ) := by
        simpa using! congrArg (fun m : ℕ => (m : ℂ)) hsigma2
      simp [f, c, this, qz, pow_two, mul_left_comm, mul_comm]
      ring_nf
    have hsumRange : (Finset.range 3).sum f = f 0 + f 1 + f 2 := by
      simp [Finset.sum_range_succ]
    have htail :
        (∑' n : ℕ, f (n + 3)) = E₆ z - (f 0 + f 1 + f 2) := by
      have htail0 :
          (∑' n : ℕ, f (n + 3)) = (∑' n : ℕ, f n) - (Finset.range 3).sum f :=
        eq_sub_of_add_eq' hsplit
      simpa [hF.tsum_eq, hsumRange] using! htail0
    have hL :
        ((((E₆ z - (1 : ℂ)) / q (z : ℂ) - (-(504 : ℂ))) / q (z : ℂ)) - (-(16632 : ℂ))) / q (z : ℂ) =
          (E₆ z - (1 : ℂ) - (-(504 : ℂ)) * qz - (-(16632 : ℂ)) * qz ^ (2 : ℕ)) / qz ^ (3 : ℕ) := by
      have hqz3 : qz ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hzq
      field_simp [qz, hzq, hqz3, pow_two, pow_three]
      ring
    have htail2 :
        (E₆ z - (1 : ℂ) - (-(504 : ℂ)) * qz - (-(16632 : ℂ)) * qz ^ (2 : ℕ)) =
          ∑' n : ℕ, f (n + 3) := by
      have h := htail.symm
      simpa [hf0, hf1, hf2, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using! h
    have hterm (n : ℕ) :
        f (n + 3) / qz ^ (3 : ℕ) = (-(504 : ℂ)) * a n * qz ^ n := by
      grind only
    have hsumDiv :
        (∑' n : ℕ, f (n + 3)) / qz ^ (3 : ℕ) = ∑' n : ℕ, (-(504 : ℂ)) * a n * qz ^ n := by
      calc
        (∑' n : ℕ, f (n + 3)) / qz ^ (3 : ℕ) = ∑' n : ℕ, f (n + 3) / qz ^ (3 : ℕ) := by
          simpa using!
            (tsum_div_const (f := fun n : ℕ => f (n + 3)) (a := qz ^ (3 : ℕ))).symm
        _ = ∑' n : ℕ, (-(504 : ℂ)) * a n * qz ^ n := by
          exact tsum_congr hterm
    have hqpow (n : ℕ) :
        qz ^ n = Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      unfold qz q
      simpa [mul_assoc, mul_left_comm, mul_comm] using!
        (Complex.exp_nat_mul (2 * π * Complex.I * (z : ℂ)) n).symm
    have hsumExp :
        (∑' n : ℕ, (-(504 : ℂ)) * a n * qz ^ n) =
          (-(504 : ℂ)) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      calc
        (∑' n : ℕ, (-(504 : ℂ)) * a n * qz ^ n) = (∑' n : ℕ, (-(504 : ℂ)) * (a n * qz ^ n)) := by
          refine tsum_congr ?_; intro n; ring_nf
        _ = (-(504 : ℂ)) * ∑' n : ℕ, (a n * qz ^ n) := by
              simpa [mul_assoc] using!
                (tsum_mul_left (a := (-(504 : ℂ))) (f := fun n : ℕ => a n * qz ^ n))
        _ =
            (-(504 : ℂ)) *
              ∑' n : ℕ,
                (a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) := by
              refine congrArg (fun S => (-(504 : ℂ)) * S) (tsum_congr ?_)
              intro n
              simp [hqpow n]
        _ = (-(504 : ℂ)) * ∑' n : ℕ, a n * Complex.exp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
              simp [mul_assoc]
    lia
  refine Tendsto.congr' (Filter.Eventually.of_forall (fun z => (hEq z).symm)) hseries'

end SpecialValuesVarphi₁Limits

end

end SpherePacking.Dim24
