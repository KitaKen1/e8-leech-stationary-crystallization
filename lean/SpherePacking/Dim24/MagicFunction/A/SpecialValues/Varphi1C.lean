-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi1B
import SpherePacking.ModularForms.QExpansion


/-!
# Varphi₁: constant term and vanishing at `i∞`

This file proves two further `atImInfty` limit lemmas for `varphi₁`: the constant term after
subtracting the `q^{-1}` pole, and the vanishing of `varphi₁ * q^2` at `i∞`.

## Main statements
* `tendsto_varphi₁_sub_const_div_q`
* `tendsto_varphi₁_mul_q_sq`
-/


namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesVarphi₁Limits

open scoped Interval Real Topology BigOperators Nat ArithmeticFunction.sigma
open Filter Complex UpperHalfPlane intervalIntegral MeasureTheory Set Function
open SlashInvariantFormClass ModularFormClass

/-- First-order coefficient for `Bdivq`: `((Bdivq+1008)/q) → -66528` as `z → i∞`. -/
lemma tendsto_B_div_q_add_1008_div_q :
    Tendsto
        (fun z : ℍ =>
          (((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ) + (1008 : ℂ)) / q (z : ℂ))
        atImInfty (𝓝 (-(66528 : ℂ))) := by
  -- Write the quotient as `-1008` times a shifted `q`-series, then apply `QExp.tendsto_nat`.
  let b : ℕ → ℂ := fun n => (((n + 2 : ℕ) : ℂ) * (σ 5 (n + 2) : ℂ))
  have hb : Summable (fun n : ℕ => ‖b n‖ * Real.exp (-2 * Real.pi * n)) := by
    simpa [b] using! summable_coeff_B_over_q_shift
  have hseries :
      Tendsto (fun z : ℍ => ∑' n : ℕ, b n * cexp (2 * π * Complex.I * z * n)) atImInfty (𝓝 (b 0)) :=
    QExp.tendsto_nat (a := b) (ha := hb)
  have hb0 : b 0 = (66 : ℂ) := by
    have hsigma : (σ 5 2 : ℂ) = (33 : ℂ) := by
      exact_mod_cast (by decide : (σ 5 2 : ℕ) = 33)
    norm_num [b, hsigma]
  have hscaled :
      Tendsto (fun z : ℍ => (-(1008 : ℂ)) * ∑' n : ℕ, b n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (-(66528 : ℂ))) := by
    have hconst : (-(1008 : ℂ)) * (66 : ℂ) = (-(66528 : ℂ)) := by norm_num
    have htconst :
        Tendsto (fun _ : ℍ => (-(1008 : ℂ))) atImInfty (𝓝 (-(1008 : ℂ))) :=
      tendsto_const_nhds
    have hmul :
        Tendsto (fun z : ℍ => (-(1008 : ℂ)) * (∑' n : ℕ, b n * cexp (2 * π * Complex.I * z * n)))
          atImInfty (𝓝 ((-(1008 : ℂ)) * b 0)) := by
      exact htconst.mul hseries
    simpa [hb0, hconst, mul_assoc] using! hmul
  -- Show that `((B/q)+1008)/q` agrees with the shifted series for large `im z`.
  have hEq :
      (fun z : ℍ =>
          (((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ) + (1008 : ℂ)) / q (z : ℂ)) =ᶠ[atImInfty]
        fun z : ℍ => (-(1008 : ℂ)) * ∑' n : ℕ, b n * cexp (2 * π * Complex.I * z * n) := by
    -- Work on the subset `{z | 1 ≤ im z}` to justify splitting off the constant term.
    have hIm1 : {z : ℍ | (1 : ℝ) ≤ z.im} ∈ atImInfty := by
      refine (UpperHalfPlane.atImInfty_mem _).2 ?_
      refine ⟨1, ?_⟩
      intro z hz
      exact hz
    filter_upwards [hIm1] with z hzIm
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    let a : ℕ → ℂ := fun n => (((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ))
    let f : ℕ → ℂ := fun n => a n * cexp (2 * π * Complex.I * z * n)
    have hBq :
        ((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ) = (-(1008 : ℂ)) * ∑' n : ℕ, f n := by
      simpa [a, f, mul_assoc, mul_left_comm, mul_comm] using! (B_div_q_eq_series (z := z))
    have hf0 : f 0 = (1 : ℂ) := by simp [f, a]
    -- `f` is summable for `im z ≥ 1`.
    have hsum_f : Summable f := by
      have hmaj : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
        simpa [a] using! summable_coeff_B_over_q
      refine Summable.of_norm_bounded hmaj ?_
      intro n
      have hnorm : ‖f n‖ = ‖a n‖ * Real.exp (z.im * (-2 * π * n)) := by
        simp_rw [f, norm_mul, mul_right_comm _ Complex.I, Complex.norm_exp_mul_I]
        simp [mul_assoc, mul_left_comm, mul_comm]
      have ht : (-2 * π * (n : ℝ)) ≤ 0 := by
        nlinarith [Real.pi_pos, (show (0 : ℝ) ≤ (n : ℝ) by positivity)]
      have hmul : z.im * (-2 * π * (n : ℝ)) ≤ (1 : ℝ) * (-2 * π * (n : ℝ)) :=
        mul_le_mul_of_nonpos_right hzIm ht
      have hexp :
          Real.exp (z.im * (-2 * π * (n : ℝ))) ≤ Real.exp ((1 : ℝ) * (-2 * π * (n : ℝ))) :=
        Real.exp_le_exp.2 hmul
      have := mul_le_mul_of_nonneg_left hexp (norm_nonneg (a n))
      simpa [hnorm, mul_assoc, mul_left_comm, mul_comm] using! this
    -- Split `∑ f` into `f 0` plus the tail `∑ f (n+1)`.
    have hsplit : (∑' n : ℕ, f n) - (1 : ℂ) = ∑' n : ℕ, f (n + 1) := by
      have hsum :=
        (hsum_f.sum_add_tsum_nat_add 1 :
          (∑ i ∈ Finset.range 1, f i) + (∑' i : ℕ, f (i + 1)) = ∑' i : ℕ, f i)
      have hsum' : (∑' n : ℕ, f n) = f 0 + ∑' n : ℕ, f (n + 1) := by
        simpa [Finset.sum_range_one] using! hsum.symm
      calc
        (∑' n : ℕ, f n) - (1 : ℂ) = (f 0 + ∑' n : ℕ, f (n + 1)) - (1 : ℂ) := by
              simp [hsum']
        _ = (f 0 + ∑' n : ℕ, f (n + 1)) - f 0 := by simp [hf0]
        _ = ∑' n : ℕ, f (n + 1) := by simp
    -- Reindex the tail and divide by `q`.
    have htail :
        ((∑' n : ℕ, f n) - (1 : ℂ)) / q (z : ℂ) =
          ∑' n : ℕ, b n * cexp (2 * π * Complex.I * z * n) := by
      -- Move the division by `q` inside, then simplify each term using `cexp_mul_succ_div_q`.
      rw [hsplit]
      -- Push `(/ q)` through the `tsum`.
      have hdiv :
          (∑' n : ℕ, f (n + 1)) / q (z : ℂ) =
            ∑' n : ℕ, (f (n + 1)) / q (z : ℂ) := by
        simpa using! (tsum_div_const (f := fun n : ℕ => f (n + 1)) (a := q (z : ℂ))).symm
      rw [hdiv]
      refine tsum_congr ?_
      intro n
      have hexp :
          cexp (2 * π * Complex.I * z * ((n + 1 : ℕ) : ℂ)) / q (z : ℂ) =
            cexp (2 * π * Complex.I * z * (n : ℂ)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using!
          (cexp_mul_succ_div_q (z := (z : ℂ)) (n := n))
      -- Rewrite `f (n+1)` and apply `hexp`.
      grind only
    -- Assemble the algebra.
    have hlin :
        ((((-(1008 : ℂ)) * (∑' n : ℕ, f n)) + (1008 : ℂ)) / q (z : ℂ)) =
          (-(1008 : ℂ)) * (((∑' n : ℕ, f n) - (1 : ℂ)) / q (z : ℂ)) := by
      field_simp [hzq]
      ring
    lia
  -- Conclude using `Tendsto.congr'`.
  exact hscaled.congr' hEq.symm

private def ZΔ (z : ℍ) : ℂ := q (z : ℂ) / Δ z

private def Bdivq (z : ℍ) : ℂ :=
  ((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ)

private lemma varphi₁_rewrite_qPole (z : ℍ) :
    Dim24.varphi₁ z =
      ((288 : ℂ) * Complex.I / (π : ℂ)) * (E₆ z * Bdivq z * (ZΔ z) ^ (2 : ℕ)) / q (z : ℂ) +
        ((1016064 : ℂ) * Complex.I / (π : ℂ)) * ((E₂ z) * (ZΔ z)) / q (z : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  have hzΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
  -- Rewrite `varphi₁` and clear denominators.
  rw [varphi₁_rewrite (z := z)]
  -- Unfold the abbreviations, then clear `π`, `q`, and `Δ` denominators.
  simp [ZΔ, Bdivq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  field_simp [hπ, hzq, hzΔ]
  -- `field_simp` already clears the goal.

/-- Constant term for `varphi₁` after subtracting the principal part `725760 * i / (π * q)`. -/
public lemma tendsto_varphi₁_sub_const_div_q :
    Tendsto
        (fun z : ℍ =>
          Dim24.varphi₁ z - ((725760 : ℂ) * Complex.I / (π : ℂ)) / q (z : ℂ))
        atImInfty (𝓝 ((113218560 : ℂ) * Complex.I / (π : ℂ))) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  let Z : ℍ → ℂ := ZΔ
  let Bq : ℍ → ℂ := Bdivq
  -- Core first-order coefficient:
  -- `core z = (E₆(z) * Bq(z) * (q/Δ)^2 + 1008) / q`.
  let core : ℍ → ℂ := fun z => (E₆ z * Bq z * (Z z) ^ (2 : ℕ) + (1008 : ℂ)) / q (z : ℂ)
  have hZ : Tendsto Z atImInfty (𝓝 (1 : ℂ)) := tendsto_q_div_Delta
  have hZ2 : Tendsto (fun z : ℍ => (Z z) ^ (2 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using! (hZ.pow 2)
  have hBq : Tendsto Bq atImInfty (𝓝 (-(1008 : ℂ))) := tendsto_B_div_q
  have hBqLin :
      Tendsto (fun z : ℍ => (Bq z + (1008 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(66528 : ℂ))) :=
    tendsto_B_div_q_add_1008_div_q
  have hE6Lin :
      Tendsto (fun z : ℍ => (E₆ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(504 : ℂ))) :=
    tendsto_E₆_sub_one_div_q
  have hZ2Lin :
      Tendsto (fun z : ℍ => ((Z z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (48 : ℂ)) :=
    tendsto_q_div_Delta_sq_sub_one_div_q
  have hE2ZLin :
      Tendsto (fun z : ℍ => ((E₂ z) * (Z z) - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (0 : ℂ)) :=
    tendsto_E₂_mul_q_div_Delta_sub_one_div_q
  have hBqZ2 : Tendsto (fun z : ℍ => Bq z * (Z z) ^ (2 : ℕ)) atImInfty (𝓝 (-(1008 : ℂ))) := by
    simpa [mul_one] using! (hBq.mul hZ2)
  -- Decompose `(E₆ * Bq * Z^2 + 1008) / q` into three first-order pieces.
  let term1 : ℍ → ℂ := fun z =>
    ((E₆ z - (1 : ℂ)) / q (z : ℂ)) * (Bq z * (Z z) ^ (2 : ℕ))
  let term2 : ℍ → ℂ := fun z =>
    ((Bq z + (1008 : ℂ)) / q (z : ℂ)) * (Z z) ^ (2 : ℕ)
  let term3 : ℍ → ℂ := fun z =>
    (-(1008 : ℂ)) * (((Z z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ))
  have hCoreEq :
      core =
        fun z : ℍ => term1 z + (term2 z + term3 z) := by
    funext z
    ring
  have hterm1 :
      Tendsto
          (fun z : ℍ => term1 z) atImInfty
          (𝓝 ((-(504 : ℂ)) * (-(1008 : ℂ)))) :=
    hE6Lin.mul hBqZ2
  have hterm2 :
      Tendsto (fun z : ℍ => term2 z) atImInfty
        (𝓝 ((-(66528 : ℂ)) * (1 : ℂ))) :=
    hBqLin.mul hZ2
  have hterm3 :
      Tendsto
          (fun z : ℍ => term3 z) atImInfty
          (𝓝 ((-(1008 : ℂ)) * (48 : ℂ))) :=
    by
      simpa [term3, mul_assoc] using! (tendsto_const_nhds.mul hZ2Lin)
  have hcore :
      Tendsto core atImInfty (𝓝 (393120 : ℂ)) := by
    have hsum := hterm1.add (hterm2.add hterm3)
    have hconst :
        (504 : ℂ) * (1008 : ℂ) + ((-(66528 : ℂ)) + -((1008 : ℂ) * (48 : ℂ))) = (393120 : ℂ) := by
      norm_num
    -- Rewrite the function using `hCoreEq` and the limit using `hconst`.
    simpa [hCoreEq, hconst, mul_one, add_assoc] using! hsum
  -- Rewrite `varphi₁` so that the `q` pole is explicit, then apply the first-order limits.
  have hEq :
      (fun z : ℍ =>
          Dim24.varphi₁ z - ((725760 : ℂ) * Complex.I / (π : ℂ)) / q (z : ℂ)) =
        fun z : ℍ =>
          ((288 : ℂ) * Complex.I / (π : ℂ)) * core z +
            ((1016064 : ℂ) * Complex.I / (π : ℂ)) *
              (((E₂ z) * (Z z) - (1 : ℂ)) / q (z : ℂ)) := by
    funext z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    have hzΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    -- Use the precomputed `q`-pole rewrite and simplify.
    have hvarphi := varphi₁_rewrite_qPole (z := z)
    -- A purely algebraic identity; clear denominators and normalize.
    -- Unfold the local `let`-definitions to expose denominators, then rewrite `varphi₁`.
    grind only
  have hlimit1 :
      Tendsto (fun z : ℍ => ((288 : ℂ) * Complex.I / (π : ℂ)) * core z) atImInfty
        (𝓝 (((288 : ℂ) * Complex.I / (π : ℂ)) * (393120 : ℂ))) := by
    simpa using! (tendsto_const_nhds.mul hcore)
  have hlimit2 :
      Tendsto
          (fun z : ℍ =>
            ((1016064 : ℂ) * Complex.I / (π : ℂ)) * (((E₂ z) * (Z z) - (1 : ℂ)) / q (z : ℂ)))
          atImInfty (𝓝 (0 : ℂ)) := by
    simpa using! (tendsto_const_nhds.mul hE2ZLin)
  have hsum := hlimit1.add hlimit2
  grind only

/-- `varphi₁ z * q(z)^2 → 0` as `z → i∞`. -/
public lemma tendsto_varphi₁_mul_q_sq :
    Tendsto (fun z : ℍ => Dim24.varphi₁ z * (q (z : ℂ)) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
  -- `varphi₁ * q^2 = (varphi₁ * q) * q` and the limit is `c * 0 = 0`.
  simpa [pow_two, mul_assoc] using! (tendsto_varphi₁_mul_q.mul tendsto_q_atImInfty)

end SpecialValuesVarphi₁Limits

end

end SpherePacking.Dim24
