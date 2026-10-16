-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Real.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.RBounds
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTrunc
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTruncPosRigorous.Common
import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTruncPosRigorous.LargeEvalPos
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Large-`t` positivity for the exact truncation

In the large-`t` regime `t0 ≤ t` (with `t ≥ 1`), we have `x = r(t) ≤ 1 / 28`.
This file relates the polynomial lower bound `polyLarge` from `LargeDefs` to the exact truncation
`ExactTrunc.ineq2_exact_trunc` and combines this comparison with the positivity of
`polyLarge - eps * x^12` to obtain positivity of `ExactTrunc.ineq2_exact_trunc - eps * r(t)^12`.

## Main statements
* `exact_trunc_sub_eps_pos_of_t0_le`
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux.ExactTruncPosRigorous

open AppendixA CoeffModel

/-- In the large-`t` regime, `polyLarge` evaluated at `r(t)` is a lower bound for the exact
truncation `ExactTrunc.ineq2_exact_trunc t`. -/
lemma polyLarge_eval_le_exact_trunc (t : ℝ) (ht : 1 ≤ t) (ht0 : t0 ≤ t) :
    (polyLarge.eval₂ (algebraMap ℚ ℝ) (AppendixA.r t)) ≤ ExactTrunc.ineq2_exact_trunc t := by
  set x : ℝ := AppendixA.r t
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have htr : t * x ≤ (1 / 23 : ℝ) := by simpa [x] using! AppendixA.t_mul_r_le_one_div_23 (t := t) ht
  have ht0' : 0 ≤ t := by nlinarith [ht]
  have ht_mul_invPi :
      t0 * invPiLower ≤ t * (1 / Real.pi) := by
    have h1 : t0 * (1 / Real.pi) ≤ t * (1 / Real.pi) := by
      have hpi0 : 0 ≤ (1 / Real.pi : ℝ) := (one_div_pos.2 Real.pi_pos).le
      exact mul_le_mul_of_nonneg_right ht0 hpi0
    have h2 : t0 * invPiLower ≤ t0 * (1 / Real.pi) := by
      have ht0nonneg : 0 ≤ t0 := by norm_num [t0]
      exact mul_le_mul_of_nonneg_left invPiLower_le_inv_pi ht0nonneg
    exact le_trans h2 h1
  have hinvPiSq_bounds :
      invPiSqLower ≤ (1 / Real.pi) ^ (2 : ℕ) ∧ (1 / Real.pi) ^ (2 : ℕ) ≤ invPiSqUpper :=
    ⟨invPiSqLower_le_inv_pi_sq, inv_pi_sq_le_invPiSqUpper⟩
  have hexact :
      ExactTrunc.ineq2_exact_trunc t =
        (∑ i ∈ Finset.range N, (A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i) +
        (∑ i ∈ Finset.range N, (B0 i : ℝ) * t * (1 / Real.pi) * x ^ i) +
        (∑ i ∈ Finset.range N, (C0 i : ℝ) * (1 / Real.pi) ^ (2 : ℕ) * x ^ i) := by
    simp [ExactTrunc.ineq2_exact_trunc, ExactTrunc.ineq2_exact_coeff, x, Finset.sum_add_distrib,
      pow_two, add_mul, mul_assoc, add_assoc]
  have hpoly :
      polyLarge.eval₂ (algebraMap ℚ ℝ) x =
        (∑ i ∈ Finset.range N, (B0 i : ℝ) * t0 * invPiLower * x ^ i) +
        (∑ i ∈ Finset.range N, (C0 i : ℝ) * (CinvBoundQ i : ℝ) * x ^ i) +
        (∑ i ∈ Finset.range N,
            (if i + 2 < N then (A0 (i + 2) : ℝ) * (cQ : ℝ) ^ (2 : ℕ) else 0) * x ^ i) := by
    -- First, rewrite `polyLarge.eval₂` as a coefficient sum over `0..N-1`.
    have hlen : coeffsLarge.length = N := by
      dsimp [coeffsLarge]
      exact List.length_ofFn (f := fun i : Fin N => coeffLarge i.1)
    have hgetD : ∀ n : ℕ, n < N → coeffsLarge.getD n 0 = coeffLarge n := by
      intro n hn
      have hn' : n < coeffsLarge.length := lt_of_lt_of_eq hn hlen.symm
      have hD :
          coeffsLarge.getD n 0 = coeffsLarge[n] :=
        List.getD_eq_getElem (l := coeffsLarge) (d := (0 : ℚ)) hn'
      have hE : coeffsLarge[n] = coeffLarge n := by
        -- `coeffsLarge` is an `ofFn` list.
        have hn'' : n < (List.ofFn (fun i : Fin N => coeffLarge i.1)).length := by
          assumption
        dsimp [coeffsLarge]
        exact (List.getElem_ofFn (f := fun i : Fin N => coeffLarge i.1) (i := n) hn'').trans rfl
      calc
        coeffsLarge.getD n 0 = coeffsLarge[n] := hD
        _ = coeffLarge n := hE
    have hsum0 :
        (AppendixA.polyOfCoeffs coeffsLarge).eval₂ (algebraMap ℚ ℝ) x =
          ∑ n ∈ Finset.range coeffsLarge.length, (algebraMap ℚ ℝ) (coeffsLarge.getD n 0) * x ^ n :=
      AppendixA.eval₂_polyOfCoeffs_eq_sum_range_getD (l := coeffsLarge) (x := x)
    have hsum1 :
        polyLarge.eval₂ (algebraMap ℚ ℝ) x =
          ∑ n ∈ Finset.range N, (algebraMap ℚ ℝ) (coeffsLarge.getD n 0) * x ^ n := by
      simpa [polyLarge, hlen] using! hsum0
    have hsum :
        polyLarge.eval₂ (algebraMap ℚ ℝ) x =
          ∑ n ∈ Finset.range N, (coeffLarge n : ℝ) * x ^ n := by
      assumption
    -- Now split `coeffLarge` termwise.
    have hterm (i : ℕ) :
        (coeffLarge i : ℝ) * x ^ i =
          (B0 i : ℝ) * t0 * invPiLower * x ^ i +
            (C0 i : ℝ) * (CinvBoundQ i : ℝ) * x ^ i +
            (if i + 2 < N then (A0 (i + 2) : ℝ) * (cQ : ℝ) ^ (2 : ℕ) else 0) * x ^ i := by
      by_cases hAi : i + 2 < N <;>
        simp [
          coeffLarge,
          hAi,
          t0Q_cast,
          invPiLower,
          invPiLowerQ,
          mul_add,
          add_comm,
          mul_left_comm,
          mul_comm
        ]
    have hrewrite :
        (∑ i ∈ Finset.range N, (coeffLarge i : ℝ) * x ^ i) =
          ∑ i ∈ Finset.range N,
            ((B0 i : ℝ) * t0 * invPiLower * x ^ i +
              (C0 i : ℝ) * (CinvBoundQ i : ℝ) * x ^ i +
              (if i + 2 < N then (A0 (i + 2) : ℝ) * (cQ : ℝ) ^ (2 : ℕ) else 0) * x ^ i) := by
      exact Finset.sum_congr rfl fun x a => hterm x
    -- Distribute the sums.
    calc
      polyLarge.eval₂ (algebraMap ℚ ℝ) x
          = (∑ i ∈ Finset.range N, (coeffLarge i : ℝ) * x ^ i) := hsum
      _ = ∑ i ∈ Finset.range N,
            ((B0 i : ℝ) * t0 * invPiLower * x ^ i +
              (C0 i : ℝ) * (CinvBoundQ i : ℝ) * x ^ i +
              (if i + 2 < N then (A0 (i + 2) : ℝ) * (cQ : ℝ) ^ (2 : ℕ) else 0) * x ^ i) := hrewrite
      _ = (∑ i ∈ Finset.range N, (B0 i : ℝ) * t0 * invPiLower * x ^ i) +
            (∑ i ∈ Finset.range N, (C0 i : ℝ) * (CinvBoundQ i : ℝ) * x ^ i) +
            (∑ i ∈ Finset.range N,
                (if i + 2 < N then (A0 (i + 2) : ℝ) * (cQ : ℝ) ^ (2 : ℕ) else 0) * x ^ i) := by
            simp [Finset.sum_add_distrib]
  -- Compare termwise.
  have hB :
      (∑ i ∈ Finset.range N, (B0 i : ℝ) * t0 * invPiLower * x ^ i) ≤
        (∑ i ∈ Finset.range N, (B0 i : ℝ) * t * (1 / Real.pi) * x ^ i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi' : i < N := by simpa [Finset.mem_range] using! hi
    have hB0 : 0 ≤ (B0 i : ℝ) := by exact_mod_cast (B0_nonneg_of_lt i hi')
    have hxpow : 0 ≤ x ^ i := pow_nonneg hx0 _
    have hscale : t0 * invPiLower ≤ t * (1 / Real.pi) := ht_mul_invPi
    have h' :
        (B0 i : ℝ) * ((t0 * invPiLower) * x ^ i) ≤ (B0 i : ℝ) * ((t * (1 / Real.pi)) * x ^ i) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hscale hxpow) hB0
    -- Reassociate products.
    simpa [mul_assoc, mul_left_comm, mul_comm] using! h'
  have hC :
      (∑ i ∈ Finset.range N, (C0 i : ℝ) * (CinvBoundQ i : ℝ) * x ^ i) ≤
        (∑ i ∈ Finset.range N, (C0 i : ℝ) * (1 / Real.pi) ^ (2 : ℕ) * x ^ i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi' : i < N := by simpa [Finset.mem_range] using! hi
    have hxpow : 0 ≤ x ^ i := pow_nonneg hx0 _
    set Ci : ℚ := C0 i
    by_cases hCi : 0 ≤ Ci
    · have hcoeff : (Ci : ℝ) * invPiSqLower ≤ (Ci : ℝ) * (1 / Real.pi) ^ (2 : ℕ) := by
        have hCiR : 0 ≤ (Ci : ℝ) := by exact_mod_cast hCi
        exact mul_le_mul_of_nonneg_left hinvPiSq_bounds.1 hCiR
      simpa [CinvBoundQ, Ci, hCi, mul_assoc, mul_left_comm, mul_comm] using!
        (mul_le_mul_of_nonneg_right hcoeff hxpow)
    · have hCi' : Ci < 0 := lt_of_not_ge hCi
      have hcoeff : (Ci : ℝ) * invPiSqUpper ≤ (Ci : ℝ) * (1 / Real.pi) ^ (2 : ℕ) := by
        simp_all
      simpa [CinvBoundQ, Ci, hCi, mul_assoc, mul_left_comm, mul_comm] using!
        (mul_le_mul_of_nonneg_right hcoeff hxpow)
  have hA :
      (∑ i ∈ Finset.range N,
            (if i + 2 < N then (A0 (i + 2) : ℝ) * (cQ : ℝ) ^ (2 : ℕ) else 0) * x ^ i) ≤
        (∑ i ∈ Finset.range N, (A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i) := by
    -- Follow the working proof from `TruncAux/ExactTruncPos.lean`.
    -- Rewrite the RHS as `sum_{j < N-2} A0(j+2) * t^2 * x^(j+2)`.
    have hsplitR :
        (∑ i ∈ Finset.range N, (A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i) =
          (∑ j ∈ Finset.range (N - 2), (A0 (j + 2) : ℝ) * t ^ (2 : ℕ) * x ^ (j + 2)) := by
      -- Split off `i=0,1` and use `A0 0 = 0`, `A0 1 = 0`.
      have hA0_0 : A0 0 = 0 := by
        simp_A0_nonpos_goal
      have hA0_1 : A0 1 = 0 := by
        simp_A0_nonpos_goal
      have hsum' :
          (∑ i ∈ Finset.range N, (A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i) =
            (∑ i ∈ Finset.range 2, (A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i) +
              ∑ j ∈ Finset.range (N - 2), (A0 (j + 2) : ℝ) * t ^ (2 : ℕ) * x ^ (j + 2) := by
        set g : ℕ → ℝ := fun i => (A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i
        have hNle : 2 ≤ N := by decide
        have hN : 2 + (N - 2) = N := Nat.add_sub_of_le hNle
        have := (Finset.sum_range_add (f := g) 2 (N - 2))
        simpa [hN, g, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using! this
      have hhead :
          (∑ i ∈ Finset.range 2, (A0 i : ℝ) * t ^ (2 : ℕ) * x ^ i) = 0 := by
        simp [Finset.sum_range_succ, hA0_0, hA0_1]
      simp [hsum', hhead]
    -- Rewrite the LHS as the same sum over `j < N-2`.
    have hsplitL :
        (∑ i ∈ Finset.range N,
            (if i + 2 < N then (A0 (i + 2) : ℝ) * (cQ : ℝ) ^ (2 : ℕ) else 0) * x ^ i) =
          (∑ j ∈ Finset.range (N - 2), (A0 (j + 2) : ℝ) * (cQ : ℝ) ^ (2 : ℕ) * x ^ j) := by
      have hNle : 2 ≤ N := by decide
      set g : ℕ → ℝ :=
        fun i => (if i + 2 < N then (A0 (i + 2) : ℝ) * (cQ : ℝ) ^ (2 : ℕ) else 0) * x ^ i
      have hN : (N - 2) + 2 = N := Nat.sub_add_cancel hNle
      have hsplit :=
        (Finset.sum_range_add (f := g) (N - 2) 2)
      -- Show the last two terms vanish (the `if` is false at `i = N-2` and `i = N-1`).
      have htail : (∑ k ∈ Finset.range 2, g (N - 2 + k)) = 0 := by
        have hnot0 : ¬ 2 + (N - 2) < N := by omega
        have hnot1 : ¬ (1 + (2 + (N - 2)) < N) := by omega
        -- `range 2` has the two terms `k=0` and `k=1`.
        simp [
          Finset.sum_range_succ,
          g,
          hnot0,
          hnot1,
          Nat.add_left_comm,
          Nat.add_comm
        ]
      have hsumN :
          (∑ i ∈ Finset.range N, g i) = ∑ i ∈ Finset.range (N - 2), g i := by
        -- Expand `range N` as `range (N-2) + range 2`.
        have := congrArg id hsplit
        -- Rewrite the LHS range using `(N-2)+2 = N` and kill the tail.
        simpa [hN, htail, add_assoc] using! this
      -- Now simplify the first `N-2` terms.
      assumption
    rw [hsplitL, hsplitR]
    -- Now compare termwise using `t*x ≤ cQ` and `A0 ≤ 0`.
    refine Finset.sum_le_sum ?_
    intro j hj
    have hj' : j + 2 < N := by
      have : j < N - 2 := Finset.mem_range.1 hj
      omega
    have hA0 : A0 (j + 2) ≤ 0 := A0_nonpos_of_lt (i := j + 2) (by omega)
    have hA0R : (A0 (j + 2) : ℝ) ≤ 0 := by exact_mod_cast hA0
    have hxpow : 0 ≤ x ^ j := pow_nonneg hx0 _
    have htx : t * x ≤ (cQ : ℝ) := by
      simpa [cQ, x] using! htr
    have htx0 : 0 ≤ t * x := mul_nonneg ht0' hx0
    have hsq : (t * x) ^ (2 : ℕ) ≤ (cQ : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ htx0 htx 2
    have hpow : x ^ (j + 2) = x ^ j * x ^ (2 : ℕ) := by
      simp [pow_add]
    have htx_sq :
        t ^ (2 : ℕ) * x ^ (j + 2) = (t * x) ^ (2 : ℕ) * x ^ j := by
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm, hpow]
    have hsq' : (t * x) ^ (2 : ℕ) * x ^ j ≤ (cQ : ℝ) ^ (2 : ℕ) * x ^ j :=
      mul_le_mul_of_nonneg_right hsq hxpow
    have := mul_le_mul_of_nonpos_left hsq' hA0R
    -- Use `t^2 * x^(j+2) = (t*x)^2 * x^j` to rewrite the RHS.
    simpa [htx_sq.symm, mul_assoc, mul_left_comm, mul_comm] using! this
  -- Assemble.
  rw [hpoly, hexact]
  nlinarith [hA, hB, hC]

/-- If `t ≥ 1` and `t0 ≤ t`, then the exact truncation dominates the error term
`eps * r(t)^12`, hence `ExactTrunc.ineq2_exact_trunc t - eps * r(t)^12` is strictly positive. -/
public lemma exact_trunc_sub_eps_pos_of_t0_le (t : ℝ) (ht : 1 ≤ t) (ht0 : t0 ≤ t) :
    0 < ExactTrunc.ineq2_exact_trunc t - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
  set x : ℝ := AppendixA.r t
  have hxpos : 0 < x := Real.exp_pos _
  have hx0 : 0 ≤ x := hxpos.le
  have hxle : x ≤ rUpper := by
    have : x < (1 / 28 : ℝ) := r_lt_one_div_28_of_t0_le (t := t) ht0
    simpa [x, rUpper] using! this.le
  have hpoly_pos : 0 < (polyLarge.eval₂ (algebraMap ℚ ℝ) x) - AppendixA.eps * x ^ (12 : ℕ) :=
    polyLarge_eval_pos (x := x) hx0 hxpos (by simpa [rUpper] using! hxle)
  have hpoly_le : (polyLarge.eval₂ (algebraMap ℚ ℝ) x) ≤ ExactTrunc.ineq2_exact_trunc t := by
    simpa [x] using! polyLarge_eval_le_exact_trunc (t := t) ht ht0
  have hpoly_le' :
      (polyLarge.eval₂ (algebraMap ℚ ℝ) x) - AppendixA.eps * x ^ (12 : ℕ) ≤
        ExactTrunc.ineq2_exact_trunc t - AppendixA.eps * x ^ (12 : ℕ) :=
    sub_le_sub_right hpoly_le _
  exact lt_of_lt_of_le hpoly_pos (by simpa [x] using! hpoly_le')

end SpherePacking.Dim24.Ineq2LeOneTruncAux.ExactTruncPosRigorous
