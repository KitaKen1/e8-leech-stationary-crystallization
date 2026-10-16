-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi1A
import SpherePacking.ModularForms.QExpansion
import SpherePacking.ModularForms.FG.Positivity


/-!
# Varphi₁: auxiliary `q`-asymptotics (B)

This file proves additional `atImInfty` limits and summability statements used in the first-order
expansion of `varphi₁` and related modular expressions.

## Main statements
* `tendsto_E₄_sub_one_div_q`
* `norm_q`, `tendsto_q_atImInfty`
* `tendsto_Delta_div_q_sub_one_div_q`
* `tendsto_q_div_Delta_sub_one_div_q`, `tendsto_q_div_Delta_sq_sub_one_div_q`
* `tendsto_E₂_mul_q_div_Delta_sub_one_div_q`
* `B_div_q_eq_series`
-/


namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesVarphi₁Limits

open scoped Interval Real Topology BigOperators Nat ArithmeticFunction.sigma
open Filter Complex UpperHalfPlane intervalIntegral MeasureTheory Set Function
open SlashInvariantFormClass ModularFormClass

/-- Leading `q`-coefficient for `E₄`: `(E₄-1)/q → 240` as `z → i∞`. -/
public lemma tendsto_E₄_sub_one_div_q :
    Tendsto (fun z : ℍ => (E₄ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (240 : ℂ)) := by
  -- We use the `q`-expansion of `E₄` to identify the leading coefficient.
  let a : ℕ → ℂ := fun n => (σ 3 (n + 1) : ℂ)
  have ha : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    have hsigma : ∀ n : ℕ, (σ 3 (n + 1) : ℝ) ≤ ((n : ℝ) + (1 : ℕ)) ^ 4 := by
      intro n
      have hsigma0 : (σ 3 (n + 1) : ℝ) ≤ (n + 1 : ℝ) ^ 4 := by
        norm_cast
        simpa using! (ForMathlib.sigma_three_le_pow_four (n + 1))
      simpa [Nat.cast_add] using! hsigma0
    simpa [a] using!
      (SpherePacking.ForMathlib.summable_norm_sigma_shift_mul_exp (k := 3) (m := 4) (s := 1) hsigma)
  have hseries :
      Tendsto (fun z : ℍ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n)) atImInfty (𝓝 (a 0)) :=
    QExp.tendsto_nat (a := a) (ha := ha)
  have hseries' :
      Tendsto (fun z : ℍ => (240 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 ((240 : ℂ) * (a 0))) :=
    tendsto_const_nhds.mul hseries
  have ha0 : a 0 = (1 : ℂ) := by simp [a]
  have hseries'' :
      Tendsto (fun z : ℍ => (240 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (240 : ℂ)) := by
    simpa [ha0] using! hseries'
  -- Identify `(E₄ z - 1) / q` with this `q`-series.
  have hE4_eq (z : ℍ) :
      (E₄ z - (1 : ℂ)) / q (z : ℂ) =
        (240 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    let c : ℕ → ℂ := fun n => if n = 0 then 1 else (240 : ℂ) * (σ 3 n : ℂ)
    let f : ℕ → ℂ := fun n => c n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))
    have hper :
        (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma 1 : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
      simp [CongruenceSubgroup.strictPeriods_Gamma]
    have hF : HasSum (fun n : ℕ => f n) (E₄ z) := by
      have hsum :=
        ModularForm.hasSum_qExpansion (f := E₄) (h := (1 : ℝ)) (by positivity) hper z
      refine HasSum.congr_fun hsum (fun n => ?_)
      have hcoeff : (qExpansion (1 : ℝ) E₄).coeff n = c n := by
        simpa [c] using! congr_fun E4_q_exp n
      have hqpow :
          (Periodic.qParam (1 : ℝ) (z : ℂ)) ^ n =
            cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
        have hq : Periodic.qParam (1 : ℝ) (z : ℂ) = cexp (2 * π * Complex.I * (z : ℂ)) := by
          simp [Periodic.qParam]
        rw [hq]
        simpa [mul_assoc, mul_left_comm, mul_comm] using!
          (Complex.exp_nat_mul (2 * π * Complex.I * (z : ℂ)) n).symm
      simp [f, smul_eq_mul, hcoeff, hqpow, mul_left_comm, mul_comm]
    have hsumf : Summable f := hF.summable
    have hf0 : f 0 = (1 : ℂ) := by simp [f, c]
    have hsplit :
        f 0 + ∑' n : ℕ+, f (n : ℕ) = E₄ z := by
      have := tsum_zero_pnat_eq_tsum_nat (f := f) hsumf
      simpa [hF.tsum_eq] using! this
    have htail :
        E₄ z - (1 : ℂ) = ∑' n : ℕ+, f (n : ℕ) := by
      have hpnat : (∑' n : ℕ+, f (n : ℕ)) = E₄ z - f 0 := eq_sub_of_add_eq' hsplit
      simpa [hf0] using! hpnat.symm
    let g : ℕ+ → ℂ :=
      fun n => (σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))
    have hfg : (∑' n : ℕ+, f (n : ℕ)) = (240 : ℂ) * ∑' n : ℕ+, g n := by
      have h1 :
          (∑' n : ℕ+, f (n : ℕ)) = ∑' n : ℕ+, (240 : ℂ) * g n := by
        refine tsum_congr fun n => ?_
        have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
        have hc : c (n : ℕ) = (240 : ℂ) * (σ 3 n : ℂ) := by simp [c, hn0]
        simp [f, g, hc, mul_assoc, mul_left_comm, mul_comm]
      calc
        (∑' n : ℕ+, f (n : ℕ)) = ∑' n : ℕ+, (240 : ℂ) * g n := h1
        _ = (240 : ℂ) * ∑' n : ℕ+, g n := by
              simpa using! (tsum_mul_left (a := (240 : ℂ)) (f := g))
    have hE4sub :
        E₄ z - (1 : ℂ) = (240 : ℂ) * ∑' n : ℕ+, g n := htail.trans (by simpa using! hfg)
    have hshift :
        (∑' n : ℕ+, (g n) / q (z : ℂ)) =
          ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      -- Convert the `ℕ+` sum into a `ℕ` sum by shifting indices.
      let h : ℕ → ℂ :=
        fun n : ℕ => ((σ 3 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) / q (z : ℂ)
      have hpnat :
          (∑' n : ℕ+, (g n) / q (z : ℂ)) =
            ∑' n : ℕ, h (n + 1) := by
        have hEq : (fun n : ℕ+ => (g n) / q (z : ℂ)) = fun n : ℕ+ => h (n : ℕ) := by
          funext n
          simp [h, g, mul_assoc]
        -- `∑_{n≥1} h(n) = ∑_{n≥0} h(n+1)`.
        simpa [hEq] using! (tsum_pnat_eq_tsum_succ (f := h))
      rw [hpnat]
      refine tsum_congr ?_
      intro n
      dsimp [a, g]
      -- Use `cexp_mul_succ_div_q` to cancel one factor of `q`.
      have hmul :
          ((σ 3 (n + 1) : ℂ) *
                cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) / q (z : ℂ) =
              (σ 3 (n + 1) : ℂ) *
                (cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) / q (z : ℂ)) := by
        ring
      calc
        ((σ 3 (n + 1) : ℂ) *
              cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) / q (z : ℂ)
            = (σ 3 (n + 1) : ℂ) *
                (cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) / q (z : ℂ)) := hmul
        _ = (σ 3 (n + 1) : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
              simpa [Nat.cast_add, Nat.cast_one] using!
                (congrArg (fun w : ℂ => (σ 3 (n + 1) : ℂ) * w)
                  (cexp_mul_succ_div_q (z := (z : ℂ)) (n := n)))
    calc
      (E₄ z - (1 : ℂ)) / q (z : ℂ) =
          ((240 : ℂ) * (∑' n : ℕ+, g n)) / q (z : ℂ) := by
            simpa using! congrArg (fun w : ℂ => w / q (z : ℂ)) hE4sub
      _ = (240 : ℂ) * ((∑' n : ℕ+, g n) / q (z : ℂ)) := by
            simpa [mul_assoc] using! (mul_div_assoc (240 : ℂ) (∑' n : ℕ+, g n) (q (z : ℂ)))
      _ = (240 : ℂ) * ∑' n : ℕ+, (g n) / q (z : ℂ) := by
            simpa using!
              congrArg (fun t : ℂ => (240 : ℂ) * t)
                (tsum_div_const (f := g) (a := q (z : ℂ))).symm
      _ = (240 : ℂ) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
            simp [hshift]
  exact (tendsto_congr hE4_eq).mpr hseries''

lemma tendsto_E₂_sub_one_div_q :
    Tendsto (fun z : ℍ => (E₂ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(24 : ℂ))) := by
  -- Use the `q`-expansion `E₂ = 1 - 24 * ∑_{n≥1} σ₁(n) q^n`.
  let a : ℕ → ℂ := fun n => (σ 1 (n + 1) : ℂ)
  have ha : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    have hsigma : ∀ n : ℕ, (σ 1 (n + 1) : ℝ) ≤ ((n : ℝ) + (1 : ℕ)) ^ 2 := by
      intro n
      have hsigma0 : (σ 1 (n + 1) : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
        exact_mod_cast (sigma_bound 1 (n + 1))
      simpa [Nat.cast_add] using! hsigma0
    simpa [a] using!
      (SpherePacking.ForMathlib.summable_norm_sigma_shift_mul_exp (k := 1) (m := 2) (s := 1) hsigma)
  have hseries :
      Tendsto (fun z : ℍ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n)) atImInfty (𝓝 (a 0)) :=
    QExp.tendsto_nat (a := a) (ha := ha)
  have hseries' :
      Tendsto (fun z : ℍ => (-(24 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 ((-(24 : ℂ)) * (a 0))) :=
    tendsto_const_nhds.mul hseries
  have ha0 : a 0 = (1 : ℂ) := by simp [a]
  have hseries'' :
      Tendsto (fun z : ℍ => (-(24 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (-(24 : ℂ))) := by
    simpa [ha0] using! hseries'
  have hE2_eq (z : ℍ) :
      (E₂ z - (1 : ℂ)) / q (z : ℂ) =
        (-(24 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    -- Rewrite `E₂` as a `ℕ+` `q`-series and shift.
    let S : ℂ := ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))
    have hEσ := E₂_eq_sigma_qexp z
    have hcomm :
        (∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (z : ℂ))) = S := by
      -- Commute `n` and `z` in the exponential, then unfold `S`.
      grind only
    have hE : E₂ z - (1 : ℂ) = (-(24 : ℂ)) * S := by
      -- From `E₂ z = 1 - 24 * S`.
      simp_all
    have hshift :
        (∑' n : ℕ+, ((σ 1 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) / q (z : ℂ)) =
          ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      have hpnat :
          (∑' n : ℕ+, ((σ 1 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) / q (z : ℂ)) =
            ∑' n : ℕ,
              ((σ 1 (n + 1) : ℂ) *
                    cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) /
                q (z : ℂ) := by
        simpa using!
          (tsum_pnat_eq_tsum_succ
            (f := fun n : ℕ =>
              ((σ 1 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) / q (z : ℂ)))
      rw [hpnat]
      refine tsum_congr fun n => ?_
      dsimp [a]
      have hmul :
          ((σ 1 (n + 1) : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) /
              q (z : ℂ) =
            (σ 1 (n + 1) : ℂ) *
              (cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) / q (z : ℂ)) := by
        ring
      calc
        ((σ 1 (n + 1) : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) / q (z : ℂ)
            =
              (σ 1 (n + 1) : ℂ) *
                (cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) / q (z : ℂ)) := hmul
        _ = (σ 1 (n + 1) : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
              simpa [Nat.cast_add, Nat.cast_one] using!
                (congrArg (fun w : ℂ => (σ 1 (n + 1) : ℂ) * w)
                  (cexp_mul_succ_div_q (z := (z : ℂ)) (n := n)))
    calc
      (E₂ z - (1 : ℂ)) / q (z : ℂ) = ((-(24 : ℂ)) * S) / q (z : ℂ) := by simp [hE]
      _ = (-(24 : ℂ)) * (S / q (z : ℂ)) := by
            simpa [mul_assoc] using! (mul_div_assoc (-(24 : ℂ)) S (q (z : ℂ)))
      _ =
          (-(24 : ℂ)) * ∑' n : ℕ+,
            ((σ 1 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) / q (z : ℂ) := by
            simpa using!
              congrArg (fun t : ℂ => (-(24 : ℂ)) * t)
                (tsum_div_const (f := fun n : ℕ+ =>
                      (σ 1 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)))
                    (a := q (z : ℂ))).symm
      _ = (-(24 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
            simp [hshift]
  exact (tendsto_congr hE2_eq).mpr hseries''

/-- Norm of the nome `q(z) = exp(2π i z)` on `ℍ`. -/
public lemma norm_q (z : ℍ) : ‖q (z : ℂ)‖ = Real.exp (-2 * Real.pi * z.im) := by
  have him : (((2 * Real.pi : ℂ) * (z : ℂ)).im) = (2 * Real.pi) * z.im := by
    simp [mul_assoc]
  calc
    ‖q (z : ℂ)‖ = ‖cexp (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ))‖ := by
      simp [q, mul_assoc]
    _ = ‖cexp (((2 * Real.pi : ℂ) * (z : ℂ)) * Complex.I)‖ := by
      simp [mul_left_comm, mul_comm]
    _ = Real.exp (-(((2 * Real.pi : ℂ) * (z : ℂ)).im)) := by
          simpa using! (Complex.norm_exp_mul_I ((2 * Real.pi : ℂ) * (z : ℂ)))
    _ = Real.exp (-2 * Real.pi * z.im) := by
          rw [him]
          simp [mul_assoc]

/-- The nome `q(z)` tends to `0` as `im z → ∞`. -/
public lemma tendsto_q_atImInfty : Tendsto (fun z : ℍ => q (z : ℂ)) atImInfty (𝓝 (0 : ℂ)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hexp : Tendsto (fun z : ℍ => Real.exp (-2 * Real.pi * z.im)) atImInfty (𝓝 (0 : ℝ)) := by
    have him : Tendsto (fun z : ℍ => z.im) atImInfty atTop := tendsto_im_atImInfty
    have hbot : Tendsto (fun z : ℍ => (-2 * Real.pi) * z.im) atImInfty atBot :=
      him.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos])
    exact Real.tendsto_exp_comp_nhds_zero.mpr hbot
  simpa [norm_q] using! hexp

lemma hasDerivAt_tprod_one_sub_pow_succ_zero :
    HasDerivAt (fun y : ℂ => ∏' n : ℕ, (1 - y ^ (n + 1))) (-1 : ℂ) 0 := by
  -- Use locally uniform convergence of the partial products,
  -- together with convergence of derivatives.
  -- We take partial products in the function space `ℂ → ℂ`
  -- so that we can apply `tendstoLocallyUniformlyOn_prod_range_one_sub_pow`.
  let F : ℕ → ℂ → ℂ := fun N =>
    ∏ x ∈ Finset.range N, fun y : ℂ => (1 - y ^ (x + 1))
  let f : ℂ → ℂ := fun y => ∏' n : ℕ, (1 - y ^ (n + 1))
  have hloc :
      TendstoLocallyUniformlyOn (fun N : ℕ => F N) f atTop (Metric.ball (0 : ℂ) (2⁻¹ : ℝ)) := by
    exact tendstoLocallyUniformlyOn_prod_range_one_sub_pow
  have hdiff : ∀ N : ℕ, DifferentiableOn ℂ (F N) (Metric.ball (0 : ℂ) (2⁻¹ : ℝ)) := by
    intro N
    -- Finite products of polynomials are differentiable everywhere.
    simpa [F] using!
      (DifferentiableOn.finset_prod (u := Finset.range N)
        (f := fun x : ℕ => fun y : ℂ => (1 - y ^ (x + 1)))
        (s := Metric.ball (0 : ℂ) (2⁻¹ : ℝ)) (by
          intro x hx
          fun_prop))
  have hderiv_loc :
      TendstoLocallyUniformlyOn (deriv ∘ fun N : ℕ => F N) (deriv f) atTop
        (Metric.ball (0 : ℂ) (2⁻¹ : ℝ)) :=
    (TendstoLocallyUniformlyOn.deriv hloc (Eventually.of_forall fun N => hdiff N)
      Metric.isOpen_ball)
  have hderiv0 : Tendsto (fun N : ℕ => deriv (F N) 0) atTop (𝓝 (deriv f 0)) := by
    have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (2⁻¹ : ℝ) :=
      Metric.mem_ball_self (by positivity : (0 : ℝ) < (2⁻¹ : ℝ))
    simpa [Function.comp_def] using! (hderiv_loc.tendsto_at h0)
  -- Compute the derivatives of the partial products at `0`: for `N ≥ 1` it is constantly `-1`.
  have hFDeriv : ∀ᶠ N : ℕ in atTop, deriv (F N) 0 = (-1 : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos 0) hN)) with
      ⟨N', rfl⟩
    -- Induction on `N'` for `F (N'+1)`.
    induction N' with
    | zero =>
        -- `F 1 y = 1 - y`.
        have hF1 : F 1 = fun y : ℂ => 1 - y := by
          funext y
          simp [F]
        have h : HasDerivAt (fun y : ℂ => 1 - y) (-1 : ℂ) 0 := by
          simpa using! (HasDerivAt.const_sub (c := (1 : ℂ)) (hasDerivAt_id (x := (0 : ℂ))))
        simpa [hF1] using! h.deriv
    | succ N' ih =>
        -- `F (N'+2) = F (N'+1) * (1 - y^(N'+2))`.
        have hrec : F (N' + 2) = fun y : ℂ => F (N' + 1) y * (1 - y ^ (N' + 2)) := by
          funext y
          -- Split off the last factor in the finite product.
          simp [F, Finset.prod_range_succ, Nat.add_left_comm, Nat.add_comm, mul_left_comm, mul_comm]
        have hpow : HasDerivAt (fun y : ℂ => 1 - y ^ (N' + 2)) (0 : ℂ) 0 := by
          have hpow' := (hasDerivAt_pow (n := N' + 2) (x := (0 : ℂ)))
          -- `d/dy y^(k)` at `0` is `0` for `k ≥ 2`, hence `d/dy (1 - y^k)` is also `0`.
          simpa using! (HasDerivAt.const_sub (c := (1 : ℂ)) hpow')
        have hF0 : F (N' + 1) 0 = (1 : ℂ) := by
          simp [F]
        have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (2⁻¹ : ℝ) :=
          Metric.mem_ball_self (by positivity : (0 : ℝ) < (2⁻¹ : ℝ))
        have hFdiffAt : DifferentiableAt ℂ (F (N' + 1)) 0 :=
          (hdiff (N' + 1) 0 h0).differentiableAt (Metric.isOpen_ball.mem_nhds h0)
        have hFderiv : HasDerivAt (F (N' + 1)) (deriv (F (N' + 1)) 0) 0 :=
          hFdiffAt.hasDerivAt
        have hprod :
            HasDerivAt (fun y : ℂ => F (N' + 1) y * (1 - y ^ (N' + 2)))
              (deriv (F (N' + 1)) 0 * (1 - (0 : ℂ) ^ (N' + 2)) + F (N' + 1) 0 * (0 : ℂ)) 0 :=
          hFderiv.mul hpow
        have hprod_deriv :
            deriv (fun y : ℂ => F (N' + 1) y * (1 - y ^ (N' + 2))) 0 =
              deriv (F (N' + 1)) 0 := by
          have h1 : (1 - (0 : ℂ) ^ (N' + 2)) = (1 : ℂ) := by simp
          simpa [h1, hF0, mul_assoc, add_assoc] using! hprod.deriv
        have : deriv (F (N' + 2)) 0 = deriv (F (N' + 1)) 0 := by
          simpa [hrec] using! hprod_deriv
        simp [this, ih]
  have hderiv_const : Tendsto (fun N : ℕ => deriv (F N) 0) atTop (𝓝 (-1 : ℂ)) := by
    exact tendsto_nhds_of_eventually_eq hFDeriv
  have hfderiv : deriv f 0 = (-1 : ℂ) :=
    tendsto_nhds_unique hderiv0 hderiv_const
  -- `f` is differentiable at `0`, with derivative `deriv f 0 = -1`.
  have hdiff_f : DifferentiableAt ℂ f 0 := by
    have hFdiff :
        DifferentiableOn ℂ f (Metric.ball (0 : ℂ) (2⁻¹ : ℝ)) :=
      hloc.differentiableOn (Eventually.of_forall fun N => hdiff N) Metric.isOpen_ball
    have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (2⁻¹ : ℝ) :=
      Metric.mem_ball_self (by positivity : (0 : ℝ) < (2⁻¹ : ℝ))
    exact (hFdiff 0 h0).differentiableAt (Metric.isOpen_ball.mem_nhds h0)
  have : HasDerivAt f (deriv f 0) 0 := hdiff_f.hasDerivAt
  simpa [hfderiv, f] using! this

lemma hasDerivAt_tprod_one_sub_pow_succ_pow_24_zero :
    HasDerivAt (fun y : ℂ => (∏' n : ℕ, (1 - y ^ (n + 1))) ^ (24 : ℕ)) (-(24 : ℂ)) 0 := by
  have hf : HasDerivAt (fun y : ℂ => ∏' n : ℕ, (1 - y ^ (n + 1))) (-1 : ℂ) 0 :=
    hasDerivAt_tprod_one_sub_pow_succ_zero
  have hf0 : (∏' n : ℕ, (1 - (0 : ℂ) ^ (n + 1))) = (1 : ℂ) := by simp
  -- Differentiate `y ↦ f(y)^24`.
  simpa [hf0, mul_assoc] using! (hf.pow 24)

/-- First coefficient of `Δ / q`: `((Δ/q - 1)/q) → -24` as `z → i∞`. -/
public lemma tendsto_Delta_div_q_sub_one_div_q :
    Tendsto (fun z : ℍ => ((Δ z) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(24 : ℂ))) := by
  -- View `Δ/q` as the Euler product in the variable `q = exp(2π i z)`,
  -- and use its derivative at `0`.
  have hq0 : Tendsto (fun z : ℍ => q (z : ℂ)) atImInfty (𝓝 (0 : ℂ)) := tendsto_q_atImInfty
  have hq0' : Tendsto (fun z : ℍ => q (z : ℂ)) atImInfty (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (f := fun z : ℍ => q (z : ℂ)) hq0
      (Filter.Eventually.of_forall fun z => by
        simp [q_ne_zero (z : ℂ)])
  have hderiv :
      Tendsto (fun y : ℂ => slope (fun y : ℂ => (∏' n : ℕ, (1 - y ^ (n + 1))) ^ (24 : ℕ)) 0 y)
        (𝓝[≠] (0 : ℂ)) (𝓝 (-(24 : ℂ))) :=
    (hasDerivAt_tprod_one_sub_pow_succ_pow_24_zero.tendsto_slope (x := (0 : ℂ)))
  have hcomp :
      Tendsto
          ((fun y : ℂ =>
              slope (fun y : ℂ => (∏' n : ℕ, (1 - y ^ (n + 1))) ^ (24 : ℕ)) 0 y) ∘
            fun z : ℍ => q (z : ℂ))
          atImInfty (𝓝 (-(24 : ℂ))) :=
    hderiv.comp hq0'
  -- Identify `Δ/q` with this Euler product (after pulling out the `24`-th power).
  have hEq :
      (fun z : ℍ => ((Δ z) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) =ᶠ[atImInfty]
        (fun y : ℂ => slope (fun y : ℂ => (∏' n : ℕ, (1 - y ^ (n + 1))) ^ (24 : ℕ)) 0 y) ∘
          fun z : ℍ => q (z : ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro z
    -- Rewrite `Δ/q` as `(∏ (1 - q^(n+1)))^24` using the `tprod_pow` lemma.
    have hzq_ball : (q (z : ℂ)) ∈ Metric.ball (0 : ℂ) (1 : ℝ) := by
      -- `‖q‖ = exp(-2π im z) < 1`.
      have hzpos : 0 < z.im := z.2
      have hexp : Real.exp (-2 * Real.pi * z.im) < 1 := by
        have hneg : (-2 * Real.pi * z.im) < 0 := by nlinarith [Real.pi_pos, hzpos]
        simpa using! (Real.exp_lt_one_iff.2 hneg)
      have hnorm : ‖q (z : ℂ)‖ < 1 := by
        simpa [norm_q] using! hexp
      simpa [Metric.mem_ball, dist_eq_norm] using! hnorm
    have hmult : Multipliable (fun n : ℕ => 1 - (q (z : ℂ)) ^ (n + 1)) :=
      multipliable_lt_one (q (z : ℂ)) hzq_ball
    have hΔ_div_q :
        (Δ z) / q (z : ℂ) = (∏' n : ℕ, (1 - (q (z : ℂ)) ^ (n + 1))) ^ (24 : ℕ) := by
      -- Start from the product formula for `Δ/q`.
      have hbase := congrArg (fun f : ℍ → ℂ => f z) Delta_div_q_eq_boundedfactor
      -- Rewrite the exponential term into `q^(n+1)`.
      have hexp' :
          (∏' n : ℕ, (1 - cexp (2 * π * Complex.I * (n + 1) * (z : ℂ))) ^ (24 : ℕ)) =
            ∏' n : ℕ, (1 - (q (z : ℂ)) ^ (n + 1)) ^ (24 : ℕ) := by
        refine tprod_congr ?_
        intro n
        have hpow :
            cexp (2 * π * Complex.I * (n + 1) * (z : ℂ)) = (q (z : ℂ)) ^ (n + 1) := by
          unfold q
          -- `exp((n+1) * (2π i z)) = exp(2π i z)^(n+1)`.
          simpa [mul_assoc, mul_left_comm, mul_comm] using!
            (Complex.exp_nat_mul (2 * π * Complex.I * (z : ℂ)) (n + 1))
        simp [hpow]
      -- Now pull the power out of the infinite product.
      have hpow_out :
          (∏' n : ℕ, (1 - (q (z : ℂ)) ^ (n + 1))) ^ (24 : ℕ) =
            ∏' n : ℕ, (1 - (q (z : ℂ)) ^ (n + 1)) ^ (24 : ℕ) :=
        tprod_pow (f := fun n : ℕ => 1 - (q (z : ℂ)) ^ (n + 1)) hmult 24
      -- Assemble.
      simpa [hpow_out, hexp'] using! hbase
    -- Unfold `slope` at `0` and simplify using `Δ/q = g(q)` and `g(0)=1`.
    -- `slope g 0 (q z) = (q z)⁻¹ * (g(q z) - g 0)`.
    simp [slope, hΔ_div_q, div_eq_mul_inv, sub_eq_add_neg, mul_comm]
  exact Tendsto.congr' hEq.symm hcomp

/-- First coefficient of `q / Δ`: `((q/Δ - 1)/q) → 24` as `z → i∞`. -/
public lemma tendsto_q_div_Delta_sub_one_div_q :
    Tendsto (fun z : ℍ => (q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (24 : ℂ)) := by
  have hlin :
      Tendsto (fun z : ℍ => ((Δ z) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(24 : ℂ))) :=
    tendsto_Delta_div_q_sub_one_div_q
  have hqΔ : Tendsto (fun z : ℍ => q (z : ℂ) / Δ z) atImInfty (𝓝 (1 : ℂ)) := tendsto_q_div_Delta
  have hmul :
      Tendsto
          (fun z : ℍ =>
            (((Δ z) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) * (q (z : ℂ) / Δ z))
          atImInfty (𝓝 ((-(24 : ℂ)) * (1 : ℂ))) :=
    hlin.mul hqΔ
  have hneg :
      Tendsto
          (fun z : ℍ =>
            -((((Δ z) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) * (q (z : ℂ) / Δ z)))
          atImInfty (𝓝 (-((-(24 : ℂ)) * (1 : ℂ)))) :=
    Tendsto.neg hmul
  have hneg' :
      Tendsto
          (fun z : ℍ =>
            -((((Δ z) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) * (q (z : ℂ) / Δ z)))
          atImInfty (𝓝 (24 : ℂ)) := by
    simpa using! hneg
  have hEq :
      (fun z : ℍ => (q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) =
        fun z : ℍ =>
          -((((Δ z) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) * (q (z : ℂ) / Δ z)) := by
    funext z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    have hzΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    field_simp [hzq, hzΔ]
    ring
  simpa [hEq] using! hneg'

/-- First coefficient of `(q/Δ)^2`: `(((q/Δ)^2 - 1)/q) → 48` as `z → i∞`. -/
public lemma tendsto_q_div_Delta_sq_sub_one_div_q :
    Tendsto (fun z : ℍ => ((q (z : ℂ) / Δ z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ)) atImInfty
      (𝓝 (48 : ℂ)) := by
  have hZ : Tendsto (fun z : ℍ => q (z : ℂ) / Δ z) atImInfty (𝓝 (1 : ℂ)) := tendsto_q_div_Delta
  have hZlin :
      Tendsto (fun z : ℍ => (q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (24 : ℂ)) :=
    tendsto_q_div_Delta_sub_one_div_q
  have hEq :
      (fun z : ℍ => ((q (z : ℂ) / Δ z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ)) =
        fun z : ℍ => ((q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) * ((q (z : ℂ) / Δ z) + (1 : ℂ)) := by
    funext z
    ring
  have hZadd : Tendsto (fun z : ℍ => (q (z : ℂ) / Δ z) + (1 : ℂ)) atImInfty (𝓝 ((1 : ℂ) + 1)) :=
    hZ.add tendsto_const_nhds
  have hmul :
      Tendsto
          (fun z : ℍ => ((q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) * ((q (z : ℂ) / Δ z) + (1 : ℂ)))
          atImInfty (𝓝 ((24 : ℂ) * ((1 : ℂ) + 1))) :=
    hZlin.mul hZadd
  have hmul' :
      Tendsto
          (fun z : ℍ => ((q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) * ((q (z : ℂ) / Δ z) + (1 : ℂ)))
          atImInfty (𝓝 (48 : ℂ)) := by
    have hconst : (24 : ℂ) * ((1 : ℂ) + 1) = (48 : ℂ) := by norm_num
    simpa [hconst] using! hmul
  simpa [hEq] using! hmul'

/-- First coefficient of `E₂ * (q/Δ)`: `((E₂*(q/Δ) - 1)/q) → 0` as `z → i∞`. -/
public lemma tendsto_E₂_mul_q_div_Delta_sub_one_div_q :
    Tendsto
        (fun z : ℍ => ((E₂ z) * (q (z : ℂ) / Δ z) - (1 : ℂ)) / q (z : ℂ))
        atImInfty (𝓝 (0 : ℂ)) := by
  have hE2 : Tendsto (fun z : ℍ => E₂ z) atImInfty (𝓝 (1 : ℂ)) := tendsto_E₂_atImInfty
  have hZ : Tendsto (fun z : ℍ => q (z : ℂ) / Δ z) atImInfty (𝓝 (1 : ℂ)) := tendsto_q_div_Delta
  have hE2lin :
      Tendsto (fun z : ℍ => (E₂ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(24 : ℂ))) :=
    tendsto_E₂_sub_one_div_q
  have hZlin :
      Tendsto (fun z : ℍ => (q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (24 : ℂ)) :=
    tendsto_q_div_Delta_sub_one_div_q
  have hEq :
      (fun z : ℍ => ((E₂ z) * (q (z : ℂ) / Δ z) - (1 : ℂ)) / q (z : ℂ)) =
        fun z : ℍ => ((E₂ z - (1 : ℂ)) / q (z : ℂ)) * (q (z : ℂ) / Δ z) +
          ((q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) := by
    funext z
    ring
  have hprod :
      Tendsto (fun z : ℍ => ((E₂ z - (1 : ℂ)) / q (z : ℂ)) * (q (z : ℂ) / Δ z)) atImInfty
        (𝓝 ((-(24 : ℂ)) * (1 : ℂ))) :=
    hE2lin.mul hZ
  have hsum := hprod.add hZlin
  have hsum' :
      Tendsto (fun z : ℍ =>
          ((E₂ z - (1 : ℂ)) / q (z : ℂ)) * (q (z : ℂ) / Δ z) +
            ((q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ))) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using! hsum
  simpa [hEq] using! hsum'

/-- Summability bound for the shifted coefficients in the `B/q` `q`-series. -/
public lemma summable_coeff_B_over_q_shift :
    Summable (fun n : ℕ =>
      ‖(((n + 2 : ℕ) : ℂ) * (σ 5 (n + 2) : ℂ))‖ * Real.exp (-2 * Real.pi * n)) := by
  refine
    (SpherePacking.ForMathlib.summable_norm_mul_sigma_shift_mul_exp (k := 5) (m := 6) (s := 2) ?_)
  intro n
  norm_cast
  simpa using! (sigma_five_le_pow_six (n + 2))

/-- `B/q` as a `q`-series (with constant term `-1008`). -/
public lemma B_div_q_eq_series (z : ℍ) :
    ((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ) =
      (-(1008 : ℂ)) *
        ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ)) * cexp (2 * π * Complex.I * z * n) := by
  -- This is the explicit `q`-series from `tendsto_B_div_q`.
  have hz : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  have hB :
      (E₂ z) * (E₆ z) - (E₄ z) * (E₄ z) =
        (-(1008 : ℂ)) * ∑' (n : ℕ+), (n : ℂ) * (σ 5 n : ℂ) *
          cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using! (E₂_mul_E₆_sub_E₄_sq z)
  -- Divide by `q` and shift `n ↦ n+1`.
  have hshift :
      (∑' (n : ℕ+),
          ((n : ℂ) * ((σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)))) / q (z : ℂ)) =
        ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ)) *
          cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    have hpnat :
        (∑' (n : ℕ+),
            ((n : ℂ) * ((σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)))) / q (z : ℂ)) =
          ∑' n : ℕ,
            ((((n + 1 : ℕ) : ℂ) * ((σ 5 (n + 1) : ℂ) *
                  cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)))) / q (z : ℂ)) := by
      simpa [Nat.cast_add, Nat.cast_one] using!
        (tsum_pnat_eq_tsum_succ
          (f := fun n : ℕ =>
            ((n : ℂ) * ((σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)))) / q (z : ℂ)))
    rw [hpnat]
    refine tsum_congr fun n => ?_
    have hdiv := cexp_mul_succ_div_q (z := (z : ℂ)) (n := n)
    grind only
  calc
    ((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ)
        = ((-(1008 : ℂ)) * (∑' (n : ℕ+), (n : ℂ) * (σ 5 n : ℂ) *
            cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)))) / q (z : ℂ) := by
              simpa using! congrArg (fun w : ℂ => w / q (z : ℂ)) hB
    _ =
          (-(1008 : ℂ)) *
            ((∑' (n : ℕ+), (n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
              q (z : ℂ)) := by
          ring
    _ = (-(1008 : ℂ)) *
          ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ)) *
            cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
          -- Push the division by `q` through the `tsum` and apply `hshift`.
          -- Push `(/ q)` through the sum and massage associativity to match `hshift`.
          rw [(tsum_div_const
            (f := fun n : ℕ+ =>
              (n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)))
            (a := q (z : ℂ))).symm]
          grind only
    _ = (-(1008 : ℂ)) *
          ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ)) * cexp (2 * π * Complex.I * z * n) := by
          -- Commute `z` and `n` in the exponential.
          rfl


end SpecialValuesVarphi₁Limits

end

end SpherePacking.Dim24
