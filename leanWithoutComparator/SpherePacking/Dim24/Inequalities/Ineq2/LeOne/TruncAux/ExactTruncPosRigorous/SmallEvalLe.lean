-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTruncPosRigorous.LargeDefs
public import
  SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTruncPosRigorous.SmallIntervalLB
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Small-`t` truncation bounds for `ineq2`

In the regime `1 ≤ t ≤ t0 = 107 / 100`, we compare the exact truncation
`ExactTrunc.ineq2_exact_trunc t` to a fixed polynomial lower bound `polySmall` evaluated at
`x = r(t)`. A certified interval computation shows `polySmall(x) ≥ 1 / 1000`, and we conclude the
positivity
`0 < ExactTrunc.ineq2_exact_trunc t - eps * r(t)^12`.

## Main statements
* `exact_trunc_sub_eps_pos_of_le_t0`
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open CoeffModel

namespace ExactTruncPosRigorous

lemma polySmall_ge_one_div_1000 (x : ℝ) (hx0 : 0 ≤ x)
    (hxge : (1 / 30 : ℝ) ≤ x) (hxle : x ≤ (1 / 23 : ℝ)) :
    (polySmall.eval₂ (algebraMap ℚ ℝ) x) ≥ (1 / 1000 : ℝ) := by
  -- Split points as rationals, cast to `ℝ` (avoids coercion mismatches).
  -- Using a coarser partition than the original proof keeps the interval certificates fast.
  have hx29 : x ≤ ((1 / 29 : ℚ) : ℝ) ∨ ((1 / 29 : ℚ) : ℝ) ≤ x :=
    le_total x ((1 / 29 : ℚ) : ℝ)
  have hx27 : x ≤ ((1 / 27 : ℚ) : ℝ) ∨ ((1 / 27 : ℚ) : ℝ) ≤ x :=
    le_total x ((1 / 27 : ℚ) : ℝ)
  have hx25 : x ≤ ((1 / 25 : ℚ) : ℝ) ∨ ((1 / 25 : ℚ) : ℝ) ≤ x :=
    le_total x ((1 / 25 : ℚ) : ℝ)
  have hxge' : ((1 / 30 : ℚ) : ℝ) ≤ x := by
    have : ((1 / 30 : ℚ) : ℝ) = (1 / 30 : ℝ) := by norm_num
    simpa [this] using! hxge
  have hxle' : x ≤ ((1 / 23 : ℚ) : ℝ) := by
    have : ((1 / 23 : ℚ) : ℝ) = (1 / 23 : ℝ) := by norm_num
    simpa [this] using! hxle
  set l : List ℚ := coeffsSmall
  -- Truncation order for the interval lower bound. `K = 20` is enough for all subintervals and
  -- is much faster than the original `K = 40`.
  set K : ℕ := 20
  have hinterval (a b : ℚ) (ha0 : 0 ≤ (a : ℝ)) (hb0 : 0 ≤ (b : ℝ)) (hb1 : b ≤ 1)
      (hxa : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) (hpos : (1 / 1000 : ℚ) < intervalLBWeak l a b K) :
      (1 / 1000 : ℝ) ≤ (polySmall.eval₂ (algebraMap ℚ ℝ) x) := by
    have hKlen : K ≤ l.length := by
      dsimp [K, l]
      decide
    have hLB :
        (intervalLB l a b K : ℝ) ≤ (polySmall.eval₂ (algebraMap ℚ ℝ) x) := by
      simpa [polySmall, l, ge_iff_le] using!
        (eval₂_polyOfCoeffs_ge_intervalLB
          (l := l)
          (a := a)
          (b := b)
          (K := K)
          (x := x)
          hx0
          ha0
          hb0
          hKlen
          hxa
          hxb)
    have hb0Q : 0 ≤ b := by exact_mod_cast hb0
    have hb1Q : b ≤ 1 := hb1
    have hweak_le :
        (intervalLBWeak l a b K : ℝ) ≤ (intervalLB l a b K : ℝ) := by
      exact_mod_cast (intervalLBWeak_le_intervalLB (l := l) (a := a) (b := b) (K := K) hb0Q hb1Q)
    have hLB' :
        (intervalLBWeak l a b K : ℝ) ≤ (polySmall.eval₂ (algebraMap ℚ ℝ) x) :=
      le_trans hweak_le hLB
    have hposR : ((1 / 1000 : ℚ) : ℝ) < (intervalLBWeak l a b K : ℝ) := by
      exact_mod_cast hpos
    have hposR'' : (1 / 1000 : ℝ) < (intervalLBWeak l a b K : ℝ) := by simpa using! hposR
    exact le_trans (le_of_lt hposR'') hLB'
  rcases hx29 with hx29 | hx29
  · have hpos' : (1 / 1000 : ℚ) < intervalLBWeakRec l (1 / 30) (1 / 29) K := by
      dsimp [l, K]
      simp_intervalLBWeak_goal
    have hpos : (1 / 1000 : ℚ) < intervalLBWeak l (1 / 30) (1 / 29) K := by
      simpa [intervalLBWeakRec_eq_intervalLBWeak] using! hpos'
    exact hinterval (1 / 30) (1 / 29) (by norm_num) (by norm_num) (by norm_num) hxge' hx29 hpos
  rcases hx27 with hx27 | hx27
  · have hpos' : (1 / 1000 : ℚ) < intervalLBWeakRec l (1 / 29) (1 / 27) K := by
      dsimp [l, K]
      simp_intervalLBWeak_goal
    have hpos : (1 / 1000 : ℚ) < intervalLBWeak l (1 / 29) (1 / 27) K := by
      simpa [intervalLBWeakRec_eq_intervalLBWeak] using! hpos'
    exact hinterval (1 / 29) (1 / 27) (by norm_num) (by norm_num) (by norm_num) hx29 hx27 hpos
  rcases hx25 with hx25 | hx25
  · have hpos' : (1 / 1000 : ℚ) < intervalLBWeakRec l (1 / 27) (1 / 25) K := by
      dsimp [l, K]
      simp_intervalLBWeak_goal
    have hpos : (1 / 1000 : ℚ) < intervalLBWeak l (1 / 27) (1 / 25) K := by
      simpa [intervalLBWeakRec_eq_intervalLBWeak] using! hpos'
    exact hinterval (1 / 27) (1 / 25) (by norm_num) (by norm_num) (by norm_num) hx27 hx25 hpos
  · have hpos' : (1 / 1000 : ℚ) < intervalLBWeakRec l (1 / 25) (1 / 23) K := by
      dsimp [l, K]
      simp_intervalLBWeak_goal
    have hpos : (1 / 1000 : ℚ) < intervalLBWeak l (1 / 25) (1 / 23) K := by
      simpa [intervalLBWeakRec_eq_intervalLBWeak] using! hpos'
    exact hinterval (1 / 25) (1 / 23) (by norm_num) (by norm_num) (by norm_num) hx25 hxle' hpos

lemma polySmall_eval_le_exact_trunc (t : ℝ) (ht : 1 ≤ t) (ht0 : t ≤ t0) :
    (polySmall.eval₂ (algebraMap ℚ ℝ) (AppendixA.r t)) ≤ ExactTrunc.ineq2_exact_trunc t := by
  set x : ℝ := AppendixA.r t
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have ht_le_t0 : t ^ (2 : ℕ) ≤ t0 ^ (2 : ℕ) := by
    nlinarith
  have ht_ge_one : (1 : ℝ) ≤ t := ht
  have ht0' : 0 ≤ t := by nlinarith [ht]
  have ht_mul_invPi :
      invPiLower ≤ t * (1 / Real.pi) := by
    have hpi0 : 0 ≤ (1 / Real.pi : ℝ) := (one_div_pos.2 Real.pi_pos).le
    have h1 : invPiLower ≤ (1 / Real.pi) := invPiLower_le_inv_pi
    nlinarith
  have hinvPiSq_bounds :
      invPiSqLower ≤ (1 / Real.pi) ^ (2 : ℕ) ∧ (1 / Real.pi) ^ (2 : ℕ) ≤ invPiSqUpper :=
    ⟨invPiSqLower_le_inv_pi_sq, inv_pi_sq_le_invPiSqUpper⟩
  have hpoly :
      polySmall.eval₂ (algebraMap ℚ ℝ) x =
        ∑ i ∈ Finset.range N, (coeffSmall i : ℝ) * x ^ i := by
    have hlen : coeffsSmall.length = N := by
      -- Computed from the explicit `coeffsSmall` list.
      decide
    have hsum0 :
        (AppendixA.polyOfCoeffs coeffsSmall).eval₂ (algebraMap ℚ ℝ) x =
          ∑ n ∈ Finset.range coeffsSmall.length, (algebraMap ℚ ℝ) (coeffsSmall.getD n 0) * x ^ n :=
      AppendixA.eval₂_polyOfCoeffs_eq_sum_range_getD (l := coeffsSmall) (x := x)
    have hgetD : ∀ n : ℕ, n < N → coeffsSmall.getD n 0 = coeffSmall n := by
      intro n hn
      exact coeffsSmall_getD_eq_coeffSmall n hn
    have hsum1 :
        polySmall.eval₂ (algebraMap ℚ ℝ) x =
          ∑ n ∈ Finset.range N, (algebraMap ℚ ℝ) (coeffsSmall.getD n 0) * x ^ n := by
      simpa [polySmall, hlen] using! hsum0
    have hsum2 :
        (∑ n ∈ Finset.range N, (algebraMap ℚ ℝ) (coeffsSmall.getD n 0) * x ^ n) =
          ∑ n ∈ Finset.range N, (coeffSmall n : ℝ) * x ^ n := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hn' : n < N := Finset.mem_range.1 hn
      have hget : coeffsSmall.getD n 0 = coeffSmall n := hgetD n hn'
      -- Rewrite the coefficient at index `n`.
      rw [hget]
      rfl
    -- Finish by rewriting the `getD` coefficients to the canonical `coeffSmall`.
    exact hsum1.trans hsum2
  have hexact :
      ExactTrunc.ineq2_exact_trunc t =
        (∑ i ∈ Finset.range N, (A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i) +
        (∑ i ∈ Finset.range N, (B0 i : ℝ) * t * (1 / Real.pi) * x ^ i) +
        (∑ i ∈ Finset.range N, (C0 i : ℝ) * (1 / Real.pi) ^ (2 : ℕ) * x ^ i) := by
    simp [ExactTrunc.ineq2_exact_trunc, ExactTrunc.ineq2_exact_coeff, x, Finset.sum_add_distrib,
      pow_two, add_mul, mul_assoc, add_assoc]
  -- Termwise inequality.
  have hterm :
      ∀ i ∈ Finset.range N,
        (coeffSmall i : ℝ) * x ^ i ≤
          (A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i +
            (B0 i : ℝ) * t * (1 / Real.pi) * x ^ i +
            (C0 i : ℝ) * (1 / Real.pi) ^ (2 : ℕ) * x ^ i := by
    intro i hi
    have hi' : i < N := by simpa [Finset.mem_range] using! hi
    have hxpow : 0 ≤ x ^ i := pow_nonneg hx0 _
    have hA0 : (A0 i : ℝ) ≤ 0 := by exact_mod_cast (A0_nonpos_of_lt i hi')
    have hB0 : 0 ≤ (B0 i : ℝ) := by exact_mod_cast (B0_nonneg_of_lt i hi')
    have hA :
        (A0 i : ℝ) * (t0 ^ (2 : ℕ)) ≤ (A0 i : ℝ) * t ^ (2 : ℕ) :=
      mul_le_mul_of_nonpos_left ht_le_t0 hA0
    have hB :
        (B0 i : ℝ) * invPiLower ≤ (B0 i : ℝ) * (t * (1 / Real.pi)) :=
      mul_le_mul_of_nonneg_left ht_mul_invPi hB0
    have hC :
        (C0 i : ℝ) * (CinvBoundQ i : ℝ) ≤ (C0 i : ℝ) * (1 / Real.pi) ^ (2 : ℕ) := by
      set Ci : ℚ := C0 i
      by_cases hCi : 0 ≤ Ci
      · have hCiR : 0 ≤ (Ci : ℝ) := by exact_mod_cast hCi
        have h' : (CinvBoundQ i : ℝ) = invPiSqLower := by simp [CinvBoundQ, Ci, hCi, invPiSqLower]
        rw [h']
        exact mul_le_mul_of_nonneg_left hinvPiSq_bounds.1 hCiR
      · have hCi' : Ci < 0 := lt_of_not_ge hCi
        have hCiR : (Ci : ℝ) ≤ 0 := by exact_mod_cast hCi'.le
        have h' : (CinvBoundQ i : ℝ) = invPiSqUpper := by simp [CinvBoundQ, Ci, hCi, invPiSqUpper]
        rw [h']
        have := mul_le_mul_of_nonpos_left hinvPiSq_bounds.2 hCiR
        simpa [mul_assoc, mul_left_comm, mul_comm] using! this
    have hA' := mul_le_mul_of_nonneg_right hA hxpow
    have hB' := mul_le_mul_of_nonneg_right hB hxpow
    have hC' := mul_le_mul_of_nonneg_right hC hxpow
    -- Expand `(coeffSmall i : ℝ) * x^i` into the three canonical contributions, then combine.
    have ht0pow : ((t0Q ^ (2 : ℕ) : ℚ) : ℝ) = t0 ^ (2 : ℕ) := by
      calc
        ((t0Q ^ (2 : ℕ) : ℚ) : ℝ) = (t0Q : ℝ) ^ (2 : ℕ) := by simp
        _ = t0 ^ (2 : ℕ) := by
          simpa using! congrArg (fun z : ℝ => z ^ (2 : ℕ)) t0Q_cast
    have hcoeff :
        (coeffSmall i : ℝ) * x ^ i =
          ((A0 i : ℝ) * t0 ^ (2 : ℕ) * x ^ i) +
            ((B0 i : ℝ) * invPiLower * x ^ i) +
            ((C0 i : ℝ) * (CinvBoundQ i : ℝ) * x ^ i) := by
      -- Push casts inside the rational expression and distribute the outer multiplication by `x^i`.
      dsimp [coeffSmall]
      -- Rewrite `t0Q^2` and `invPiLowerQ` to the corresponding real constants.
      -- Then distribute `(a+b+c) * x^i`.
      simp [ht0pow, invPiLower, invPiLowerQ, mul_add, add_assoc, mul_left_comm, mul_comm]
    linarith
  have hsum : (∑ i ∈ Finset.range N, (coeffSmall i : ℝ) * x ^ i) ≤
      ∑ i ∈ Finset.range N,
          ((A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i +
            (B0 i : ℝ) * t * (1 / Real.pi) * x ^ i +
            (C0 i : ℝ) * (1 / Real.pi) ^ (2 : ℕ) * x ^ i) := by
    exact Finset.sum_le_sum hterm
  have hsum' :
      (∑ i ∈ Finset.range N,
            ((A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i +
              (B0 i : ℝ) * t * (1 / Real.pi) * x ^ i +
              (C0 i : ℝ) * (1 / Real.pi) ^ (2 : ℕ) * x ^ i)) =
        (∑ i ∈ Finset.range N, (A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i) +
          (∑ i ∈ Finset.range N, (B0 i : ℝ) * t * (1 / Real.pi) * x ^ i) +
          (∑ i ∈ Finset.range N, (C0 i : ℝ) * (1 / Real.pi) ^ (2 : ℕ) * x ^ i) := by
    simp [Finset.sum_add_distrib, add_assoc]
  rw [hpoly, hexact]
  exact le_trans hsum (le_of_eq hsum')

/-- If `1 ≤ t ≤ t0`, then the exact truncation dominates the error term `eps * r(t)^12`, hence
`ExactTrunc.ineq2_exact_trunc t - eps * r(t)^12` is strictly positive. -/
public lemma exact_trunc_sub_eps_pos_of_le_t0 (t : ℝ) (ht : 1 ≤ t) (ht0 : t ≤ t0) :
    0 < ExactTrunc.ineq2_exact_trunc t - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
  set x : ℝ := AppendixA.r t
  have hxpos : 0 < x := Real.exp_pos _
  have hx0 : 0 ≤ x := hxpos.le
  have hxle : x ≤ (1 / 23 : ℝ) := by simpa [x] using! (AppendixA.r_le_one_div_23 (t := t) ht)
  have hxge : (1 / 30 : ℝ) ≤ x := by simpa [x] using! r_ge_one_div_30_of_le_t0 (t := t) ht ht0
  have hpoly_ge : (1 / 1000 : ℝ) ≤ (polySmall.eval₂ (algebraMap ℚ ℝ) x) :=
    polySmall_ge_one_div_1000 (x := x) hx0 hxge hxle
  have heps_lt : (AppendixA.eps : ℝ) < (1 / 1000 : ℝ) := by
    have h10 : (1 : ℝ) < (10 : ℝ) := by norm_num
    have : (10 : ℝ) ^ (-50 : ℤ) < (10 : ℝ) ^ (-3 : ℤ) :=
      zpow_lt_zpow_right₀ h10 (by decide : (-50 : ℤ) < (-3 : ℤ))
    have hpow : (10 : ℝ) ^ (-3 : ℤ) = (1000 : ℝ)⁻¹ := by
      -- `10^(-3) = 1/(10^3) = 1/1000`.
      norm_num
    -- Rewrite the RHS `1/1000` as `1000⁻¹`.
    simpa [AppendixA.eps, one_div, hpow] using! this
  have hx12_le_one : x ^ (12 : ℕ) ≤ 1 := by
    have hxle1 : x ≤ 1 := hxle.trans (by norm_num)
    simpa using! (pow_le_pow_left₀ hx0 hxle1 (12 : ℕ))
  have hepsx12_lt : AppendixA.eps * x ^ (12 : ℕ) < (1 / 1000 : ℝ) := by
    have heps0 : 0 ≤ (AppendixA.eps : ℝ) := by dsimp [AppendixA.eps]; positivity
    have : AppendixA.eps * x ^ (12 : ℕ) ≤ AppendixA.eps := by
      simpa [mul_one] using! mul_le_mul_of_nonneg_left hx12_le_one heps0
    exact lt_of_le_of_lt this heps_lt
  have hpoly_pos :
      (0 : ℝ) < (polySmall.eval₂ (algebraMap ℚ ℝ) x) - AppendixA.eps * x ^ (12 : ℕ) := by
    grind only
  have hpoly_le : (polySmall.eval₂ (algebraMap ℚ ℝ) x) ≤ ExactTrunc.ineq2_exact_trunc t := by
    simpa [x] using! polySmall_eval_le_exact_trunc (t := t) ht ht0
  have hsub :
      (polySmall.eval₂ (algebraMap ℚ ℝ) x) - AppendixA.eps * x ^ (12 : ℕ) ≤
        ExactTrunc.ineq2_exact_trunc t - AppendixA.eps * x ^ (12 : ℕ) :=
    sub_le_sub_right hpoly_le _
  exact lt_of_lt_of_le hpoly_pos (by simpa [x] using! hsub)

end SpherePacking.Dim24.Ineq2LeOneTruncAux.ExactTruncPosRigorous
