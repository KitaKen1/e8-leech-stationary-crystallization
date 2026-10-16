-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTruncPosRigorous.LargeDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-!
# Positivity of `polyLarge - eps * x^12`

This file proves that the polynomial lower bound `polyLarge` from `LargeDefs` is strictly positive
after subtracting the error term `eps * x^12` on the interval `0 < x ≤ rUpper = 1 / 28`.

## Main statements
* `polyLarge_eval_pos`
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open CoeffModel

namespace ExactTruncPosRigorous

/-- For `0 < x ≤ rUpper`, the polynomial `polyLarge` satisfies
`0 < polyLarge(x) - eps * x^12`. -/
public lemma polyLarge_eval_pos {x : ℝ} (hx0 : 0 ≤ x) (hxpos : 0 < x) (hx : x ≤ rUpper) :
    0 < (polyLarge.eval₂ (algebraMap ℚ ℝ) x) - AppendixA.eps * x ^ (12 : ℕ) := by
  -- Expand `polyLarge` as a coefficient sum.
  have hlen : coeffsLarge.length = N := by
    dsimp [coeffsLarge]
    exact List.length_ofFn (f := fun i : Fin N => coeffLarge i.1)
  have hgetD : ∀ n : ℕ, n < N → coeffsLarge.getD n 0 = coeffLarge n := by
    intro n hn
    have hn' : n < coeffsLarge.length := by
      -- `coeffsLarge.length = N`.
      exact lt_of_lt_of_eq hn hlen.symm
    have hD :
        coeffsLarge.getD n 0 = coeffsLarge[n] :=
      List.getD_eq_getElem (l := coeffsLarge) (d := (0 : ℚ)) hn'
    have hE : coeffsLarge[n] = coeffLarge n := by
      -- Read the entry from the `ofFn` list.
      have hn'' : n < (List.ofFn (fun i : Fin N => coeffLarge i.1)).length := by
        -- `List.ofFn` has length `N`.
        assumption
      -- Avoid unfolding `getD` (which is a simp lemma) here: go via `getElem_ofFn`.
      dsimp [coeffsLarge]
      exact (List.getElem_ofFn (f := fun i : Fin N => coeffLarge i.1) (i := n) hn'').trans rfl
    calc
      coeffsLarge.getD n 0 = coeffsLarge[n] := hD
      _ = coeffLarge n := hE
  have hsum :
      polyLarge.eval₂ (algebraMap ℚ ℝ) x =
        ∑ n ∈ Finset.range N, (coeffLarge n : ℝ) * x ^ n := by
    have hsum0 :
        (AppendixA.polyOfCoeffs coeffsLarge).eval₂ (algebraMap ℚ ℝ) x =
          ∑ n ∈ Finset.range coeffsLarge.length, (algebraMap ℚ ℝ) (coeffsLarge.getD n 0) * x ^ n :=
      AppendixA.eval₂_polyOfCoeffs_eq_sum_range_getD (l := coeffsLarge) (x := x)
    assumption
  -- Head terms at degrees 0..3 vanish except the degree-2 coefficient.
  have hhead :
      (∑ n ∈ Finset.range 4, (coeffLarge n : ℝ) * x ^ n) = (coeffLarge 2 : ℝ) * x ^ 2 := by
    have h0 : (coeffLarge 0 : ℝ) = 0 := by exact_mod_cast coeffLarge_eq_zero_0
    have h1 : (coeffLarge 1 : ℝ) = 0 := by exact_mod_cast coeffLarge_eq_zero_1
    have h3 : (coeffLarge 3 : ℝ) = 0 := by exact_mod_cast coeffLarge_eq_zero_3
    simp [
      Finset.sum_range_succ,
      h0,
      h1,
      h3,
      pow_zero,
      pow_one,
      pow_two
    ]
  -- Tail is nonnegative by pairwise dominance for `x ≤ 1/28`.
  set f : ℕ → ℝ := fun n => (coeffLarge n : ℝ) * x ^ n
  have hx_le_ru : x ≤ (rUpperQ : ℝ) := by simpa [rUpperQ, rUpper] using! hx
  have hpair_nonneg (k : ℕ) (hk : k < 48) :
      0 ≤ f (2 * k + 4) + f (2 * k + 5) := by
    have hcoeff :
        (coeffLarge (2 * k + 4) : ℝ) ≥ (|coeffLarge (2 * k + 5)| : ℝ) * (rUpperQ : ℝ) := by
      exact_mod_cast (coeffLarge_pair_dom (k := k) hk)
    have hx_ru :
        (|coeffLarge (2 * k + 5)| : ℝ) * x ≤ (|coeffLarge (2 * k + 5)| : ℝ) * (rUpperQ : ℝ) := by
      have habs0 : 0 ≤ (|coeffLarge (2 * k + 5)| : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hx_le_ru habs0
    have hdom_x :
        (|coeffLarge (2 * k + 5)| : ℝ) * x ≤ (coeffLarge (2 * k + 4) : ℝ) :=
      le_trans hx_ru hcoeff
    have hodd_lb :
        -(|coeffLarge (2 * k + 5)| : ℝ) * x ≤ (coeffLarge (2 * k + 5) : ℝ) * x := by
      have h := neg_abs_le (coeffLarge (2 * k + 5) : ℝ)
      exact MulPosMono.mul_le_mul_of_nonneg_right hx0 h
    have hlin :
        0 ≤ (coeffLarge (2 * k + 4) : ℝ) + (coeffLarge (2 * k + 5) : ℝ) * x := by
      have hsub : 0 ≤ (coeffLarge (2 * k + 4) : ℝ) - (|coeffLarge (2 * k + 5)| : ℝ) * x :=
        sub_nonneg.2 hdom_x
      have hsub_le :
          (coeffLarge (2 * k + 4) : ℝ) - (|coeffLarge (2 * k + 5)| : ℝ) * x ≤
            (coeffLarge (2 * k + 4) : ℝ) + (coeffLarge (2 * k + 5) : ℝ) * x := by
        linarith [hodd_lb]
      exact le_trans hsub hsub_le
    have hxpow : 0 ≤ x ^ (2 * k + 4) := pow_nonneg hx0 _
    have hfac :
        f (2 * k + 4) + f (2 * k + 5) =
          x ^ (2 * k + 4) * ((coeffLarge (2 * k + 4) : ℝ) + (coeffLarge (2 * k + 5) : ℝ) * x) := by
      ring
    -- `x^(2*k+4) ≥ 0` and the bracket is `≥ 0`.
    have :
        0 ≤
          x ^ (2 * k + 4) *
            ((coeffLarge (2 * k + 4) : ℝ) + (coeffLarge (2 * k + 5) : ℝ) * x) :=
      mul_nonneg hxpow hlin
    simpa [hfac] using! this
  have htail_nonneg :
      0 ≤ ∑ n ∈ Finset.range (N - 4), f (n + 4) := by
    have hNm4 : N - 4 = 2 * 48 := by decide
    set g : ℕ → ℝ := fun n => f (n + 4)
    have hpair_sum :
        (∑ n ∈ Finset.range (N - 4), g n) =
          ∑ k ∈ Finset.range 48, (g (2 * k) + g (2 * k + 1)) := by
      simpa [hNm4] using! (sum_range_two_mul (g := g) 48)
    have hpair0 :
        ∀ k ∈ Finset.range 48, 0 ≤ g (2 * k) + g (2 * k + 1) := by
      intro k hk
      have hk' : k < 48 := Finset.mem_range.1 hk
      have h := hpair_nonneg k hk'
      assumption
    have : 0 ≤ ∑ k ∈ Finset.range 48, (g (2 * k) + g (2 * k + 1)) :=
      Finset.sum_nonneg (by intro k hk; exact hpair0 k hk)
    have : 0 ≤ ∑ n ∈ Finset.range (N - 4), g n := by simpa [hpair_sum] using! this
    simpa [g] using! this
  have hpoly_ge :
      (coeffLarge 2 : ℝ) * x ^ 2 ≤ polyLarge.eval₂ (algebraMap ℚ ℝ) x := by
    have hsum' :
        ∑ n ∈ Finset.range N, (coeffLarge n : ℝ) * x ^ n =
          (∑ n ∈ Finset.range 4, f n) + ∑ n ∈ Finset.range (N - 4), f (n + 4) := by
      have := (Finset.sum_range_add (f := fun n => f n) 4 (N - 4))
      have hN : 4 ≤ N := by decide
      have h4 : 4 + (N - 4) = N := Nat.add_sub_of_le hN
      simpa [f, h4, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using! this
    grind only
  have hcoeff2_gt_one : (1 : ℝ) < (coeffLarge 2 : ℝ) := by
    exact_mod_cast coeffLarge_pos_two
  have heps_lt_one : AppendixA.eps < 1 := by
    have h10 : (1 : ℝ) < (10 : ℝ) := by norm_num
    have : (10 : ℝ) ^ (-50 : ℤ) < 1 :=
      zpow_lt_one_of_neg₀ h10 (by decide : (-50 : ℤ) < 0)
    simpa [AppendixA.eps] using! this
  have hxle1 : x ≤ 1 := hx.trans (by norm_num [rUpper])
  have hx10_le_one : x ^ (10 : ℕ) ≤ 1 := by
    simpa using! (pow_le_pow_left₀ hx0 hxle1 (10 : ℕ))
  have hepsx10_le_one : AppendixA.eps * x ^ (10 : ℕ) ≤ 1 := by
    have heps0 : 0 ≤ AppendixA.eps := by dsimp [AppendixA.eps]; positivity
    have : AppendixA.eps * x ^ (10 : ℕ) ≤ AppendixA.eps := by
      simpa [mul_one] using! mul_le_mul_of_nonneg_left hx10_le_one heps0
    exact le_trans this (le_of_lt heps_lt_one)
  have hmain :
      0 < (polyLarge.eval₂ (algebraMap ℚ ℝ) x) - AppendixA.eps * x ^ (12 : ℕ) := by
    have hx2pos : 0 < x ^ (2 : ℕ) := pow_pos hxpos 2
    have hpoly_ge' :
        (coeffLarge 2 : ℝ) * x ^ (2 : ℕ) - AppendixA.eps * x ^ (12 : ℕ) ≤
          (polyLarge.eval₂ (algebraMap ℚ ℝ) x) - AppendixA.eps * x ^ (12 : ℕ) :=
      sub_le_sub_right hpoly_ge _
    have hcoeff :
        0 < (coeffLarge 2 : ℝ) * x ^ (2 : ℕ) - AppendixA.eps * x ^ (12 : ℕ) := by
      have hx12 : x ^ (12 : ℕ) = x ^ (2 : ℕ) * x ^ (10 : ℕ) := by
        simpa using! (pow_add x (2 : ℕ) (10 : ℕ))
      have :
          (coeffLarge 2 : ℝ) * x ^ (2 : ℕ) - AppendixA.eps * x ^ (12 : ℕ) =
            x ^ (2 : ℕ) * ((coeffLarge 2 : ℝ) - AppendixA.eps * x ^ (10 : ℕ)) := by
        simp [hx12, sub_eq_add_neg, mul_add, mul_left_comm, mul_comm]
      rw [this]
      have hinner : 0 < (coeffLarge 2 : ℝ) - AppendixA.eps * x ^ (10 : ℕ) := by
        have : (AppendixA.eps * x ^ (10 : ℕ) : ℝ) ≤ 1 := hepsx10_le_one
        linarith [hcoeff2_gt_one, this]
      exact mul_pos hx2pos hinner
    exact lt_of_lt_of_le hcoeff hpoly_ge'
  exact hmain

end SpherePacking.Dim24.Ineq2LeOneTruncAux.ExactTruncPosRigorous
