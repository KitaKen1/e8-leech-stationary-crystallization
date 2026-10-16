-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.VarphiNeg.GeOne.TailBound.TailBound
public import SpherePacking.Dim24.Inequalities.VarphiNeg.GeOne.Defs
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.DenomReduction.Numerators


/-!
# Negativity for `t ≥ 1`

Negativity of `varphi(it)` for `t ≥ 1` (Appendix A, Lemma `phinonpos`, first case).

## Main statements
* `varphi_imagAxis_neg_ge_one`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

namespace VarphiNegGeOne

/-- Sturm-style sign check for the truncated polynomial plus the tail error on the relevant
  interval (encoded here in terms of `t ≥ 1`).

Paper reference: Appendix A, proof of Lemma `phinonpos`, first case. -/
private theorem varphi_trunc_geOne_neg (t : ℝ) (ht : 1 ≤ t) :
    (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) + eps * (q t) ^ 6 < 0 := by
  -- All coefficients from degree `3` onwards are nonpositive, so for `q ∈ [0,1]` the evaluation is
  -- bounded above by the cubic term, which easily dominates the tiny error term `eps * q^6`.
  have ht0 : 0 < t := lt_of_lt_of_le (by simp : (0 : ℝ) < 1) ht
  set x : ℝ := q t
  have hx_pos : 0 < x := Real.exp_pos _
  have hx0 : 0 ≤ x := hx_pos.le
  have hx_lt_one : x < 1 := by
    have : (-2 * Real.pi * t) < 0 := by nlinarith [Real.pi_pos, ht0]
    simpa [q, AppendixA.q, x] using! (Real.exp_lt_one_iff.mpr this)
  have hx_le_one : x ≤ 1 := le_of_lt hx_lt_one
  set a3 : ℚ := -3657830400
  set tail : List ℚ := List.drop 4 AppendixA.varphi_trunc_geOne_coeffs
  have hsplit :
      AppendixA.varphi_trunc_geOne_coeffs = 0 :: 0 :: 0 :: a3 :: tail := by
    -- This is just unfolding the concrete list and its `drop`.
    simp [tail, a3, AppendixA.varphi_trunc_geOne_coeffs]
  have htail_forall : List.Forall (fun c : ℚ => c ≤ 0) tail := by
    -- All remaining coefficients are nonpositive integers.
    -- `simp` turns this into a finite list of closed arithmetic goals.
    exact (set_option maxRecDepth 6000 in
      by
        simp [tail, AppendixA.varphi_trunc_geOne_coeffs])
  have htail_coeff : ∀ c ∈ tail, c ≤ 0 :=
    (List.forall_iff_forall_mem.1 htail_forall)
  -- Nonpositivity of the tail evaluation for `x ≥ 0`.
  have htail_eval_nonpos :
      (AppendixA.polyOfCoeffs tail).eval₂ (algebraMap ℚ ℝ) x ≤ 0 :=
    AppendixA.eval₂_polyOfCoeffs_nonpos_of_forall_coeff_nonpos (l := tail) (x := x) hx0
      htail_coeff
  -- Unfold the first four steps of the recursion to isolate the cubic term.
  have hpoly_eval :
      (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) x) =
        x ^ 3 * ((a3 : ℝ) + x * (AppendixA.polyOfCoeffs tail).eval₂ (algebraMap ℚ ℝ) x) := by
    -- Use `hsplit` to avoid expanding the whole coefficient list.
    simp [AppendixA.varphi_trunc_geOne, hsplit, AppendixA.polyOfCoeffs,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
      pow_succ, mul_assoc, mul_comm]
  have hpoly_le_cubic :
      (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) x) ≤ (a3 : ℝ) * x ^ 3 := by
    -- From `x * tailEval ≤ 0`.
    have hx_mul_tail : x * (AppendixA.polyOfCoeffs tail).eval₂ (algebraMap ℚ ℝ) x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hx0 htail_eval_nonpos
    -- Rewrite `a3 * x^3` as `x^3 * a3` and compare.
    have hx3 : 0 ≤ x ^ 3 := by positivity
    -- `x^3 * (a3 + x*tailEval) ≤ x^3 * a3`.
    nlinarith
  have heps_pos : 0 < eps := by
    have : (0 : ℝ) < (10 : ℝ) := by norm_num
    simpa [eps, AppendixA.eps] using! (zpow_pos this (-50 : ℤ))
  have heps_lt_one : eps < 1 := by
    have h10 : (1 : ℝ) < (10 : ℝ) := by norm_num
    have hneg : (-50 : ℤ) < 0 := by decide
    simpa [eps, AppendixA.eps] using! (zpow_lt_one_of_neg₀ h10 hneg)
  have heps_lt_a3 : eps < (3657830400 : ℝ) :=
    lt_trans heps_lt_one (by norm_num)
  have hx3_pos : 0 < x ^ 3 := pow_pos hx_pos 3
  have hx3_le_one : x ^ 3 ≤ 1 := by
    have := pow_le_pow_left₀ hx0 hx_le_one 3
    simpa using! this
  have hinner_neg : eps * x ^ 3 - (3657830400 : ℝ) < 0 := by
    have hle : eps * x ^ 3 ≤ eps := by
      have := mul_le_mul_of_nonneg_left hx3_le_one heps_pos.le
      simpa [mul_one] using! this
    have : eps * x ^ 3 < (3657830400 : ℝ) := lt_of_le_of_lt hle heps_lt_a3
    linarith
  have hmain : (a3 : ℝ) * x ^ 3 + eps * x ^ 6 < 0 := by
    have h6 : (6 : ℕ) = 3 + 3 := by decide
    have : (a3 : ℝ) * x ^ 3 + eps * x ^ 6 = x ^ 3 * (eps * x ^ 3 + (a3 : ℝ)) := by
      -- Factor `x^3` using `x^6 = x^3 * x^3`.
      ring
    rw [this]
    -- `a3 = -3657830400`, and `eps * x^3 + a3 < 0`.
    have : eps * x ^ 3 + (a3 : ℝ) < 0 := by
      simpa [a3, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using! hinner_neg
    exact mul_neg_of_pos_of_neg hx3_pos this
  -- Go back to `q t`.
  exact add_lt_of_add_lt_right hmain hpoly_le_cubic

/-- Negativity of `varphi(it)` for `t ≥ 1` (Appendix A, Lemma `phinonpos`, first case). -/
theorem varphi_imagAxis_neg_ge_one (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    (varphi (it t ht0)).re < 0 := by
  -- Step 1: conclude `varphi_num(it t)` is negative from the tail bound and polynomial check.
  have htail :
      |(varphi_num (it t ht0)).re
          - (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t))|
        ≤ eps * (q t) ^ 6 := by
    simpa using! (varphi_tail_bound_geOne (t := t) (ht0 := ht0) ht)
  have hneg :
      (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) + eps * (q t) ^ 6 < 0 :=
    varphi_trunc_geOne_neg (t := t) ht
  set a : ℝ := (varphi_num (it t ht0)).re
  set b : ℝ := (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t))
  set δ : ℝ := eps * (q t) ^ 6
  have htail' : |a - b| ≤ δ := by simpa [a, b, δ] using! htail
  have ha_le : a ≤ b + δ := by
    have : a - b ≤ δ := (le_abs_self (a - b)).trans htail'
    linarith
  have ha_neg : a < 0 := by
    have : b + δ < 0 := by simpa [b, δ] using! hneg
    exact lt_of_le_of_lt ha_le this
  -- Step 2: divide by the positive real number `Δ(it t)^2` to recover `varphi(it t) < 0`.
  have hΔpos : 0 < (Δ (it t ht0)).re := Delta_it_re_pos (t := t) ht0
  have hΔreal : (Δ (it t ht0)).im = 0 := Delta_it_im (t := t) ht0
  have hnum_real : (varphi_num (it t ht0)).im = 0 := by
    -- Reuse the already-proved "real on the imaginary axis" fact.
    simpa [SpherePacking.Dim24.VarphiNegGeOne.varphi_num, SpherePacking.Dim24.varphi_num] using!
      (SpherePacking.Dim24.varphi_num_it_im (t := t) (ht0 := ht0))
  have hvarphi_re :
      (varphi (it t ht0)).re =
        (varphi_num (it t ht0)).re / (Δ (it t ht0)).re ^ 2 := by
    have hΔne : (Δ (it t ht0)) ≠ 0 :=
      Δ_ne_zero (it t ht0)
    have h0 := varphi_num_eq_varphi_mul_Delta_sq (z := it t ht0)
    -- Rewrite `varphi` as `varphi_num / Δ^2` and take real parts.
    have hvarphi :
        varphi (it t ht0) = varphi_num (it t ht0) / (Δ (it t ht0)) ^ 2 := by
      -- From `varphi_num = varphi * Δ^2`.
      rfl
    -- Use `Complex.ofReal` since both numerator and denominator are real on the imaginary axis.
    have hnum_ofReal : varphi_num (it t ht0) = ((varphi_num (it t ht0)).re : ℂ) := by
      refine Complex.ext ?_ ?_
      · simp
      · simp [hnum_real]
    have hΔ_ofReal : Δ (it t ht0) = ((Δ (it t ht0)).re : ℂ) := by
      refine Complex.ext ?_ ?_
      · simp
      · simp [hΔreal]
    have hΔre_ne : (Δ (it t ht0)).re ≠ 0 := ne_of_gt hΔpos
    -- Take real parts.
    calc
      (varphi (it t ht0)).re
          = (varphi_num (it t ht0) / (Δ (it t ht0)) ^ 2).re := by
                simpa using! (congrArg Complex.re hvarphi)
      _ = (((varphi_num (it t ht0)).re : ℂ) / ((Δ (it t ht0)).re : ℂ) ^ 2).re := by
                -- Rewrite numerator and denominator (both are real on the imaginary axis).
                rw [hnum_ofReal, hΔ_ofReal]
                rfl
      _ = (varphi_num (it t ht0)).re / (Δ (it t ht0)).re ^ 2 := by
                -- Rewrite the complex quotient as `Complex.ofReal (u / v^2)` and take real parts.
                set u : ℝ := (varphi_num (it t ht0)).re
                set v : ℝ := (Δ (it t ht0)).re
                have hdiv :
                    ((u : ℂ) / ((v : ℂ) ^ 2)) = ((u / (v ^ 2) : ℝ) : ℂ) := by
                  -- Convert the denominator and use `Complex.ofReal_div`.
                  norm_num
                -- Now take real parts.
                have hre :
                    ((u : ℂ) / ((v : ℂ) ^ 2)).re = ((u / (v ^ 2) : ℝ) : ℂ).re :=
                  congrArg Complex.re hdiv
                assumption
  -- Finish.
  have : (varphi (it t ht0)).re < 0 := by
    -- Denominator is positive.
    have hden_pos : 0 < (Δ (it t ht0)).re ^ 2 := by positivity
    -- Numerator is negative (`a = re varphi_num`).
    have : (varphi_num (it t ht0)).re < 0 := by simpa [a] using! ha_neg
    -- Divide.
    simpa [hvarphi_re] using! (div_neg_of_neg_of_pos this hden_pos)
  exact this

end VarphiNegGeOne

/-- Negativity of `varphi(it)` for `t ≥ 1` (Appendix A, Lemma `phinonpos`, first case). -/
public theorem varphi_imagAxis_neg_ge_one (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    (varphi (it t ht0)).re < 0 :=
  VarphiNegGeOne.varphi_imagAxis_neg_ge_one (t := t) (ht0 := ht0) (ht := ht)

end SpherePacking.Dim24
