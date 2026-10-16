-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators


/-!
Lower bound for `AppendixA.Bleading_trunc` on `0 ≤ x ≤ 1/23`.

The original PARI/GP verification (Appendix A, Lemma `Bleadingterms`) uses Sturm's theorem.
In this repo we avoid implementing a full Sturm procedure by giving a direct coefficient-based
lower bound: we factor off the initial `X^4`, then bound the remaining polynomial from below by
keeping the constant term and (at `x = 1/23`) all *negative* coefficients, discarding the
nonnegative ones.
-/


namespace SpherePacking.Dim24.AppendixA

noncomputable section

open scoped BigOperators

private def cQ : ℚ := (1 : ℚ) / 23

private def negPart (a : ℚ) : ℚ := if a < 0 then a else 0

private def Bleading_trunc_tail : List ℚ := Bleading_trunc_coeffs.drop 4

/-- A uniform lower bound for `polyOfCoeffs (Bleading_trunc_coeffs.drop 4)` on `0 ≤ x ≤ 1/23`. -/
public def Bleading_trunc_c0Q : ℚ :=
  ∑ n ∈ Finset.range Bleading_trunc_tail.length,
    if n = 0 then Bleading_trunc_tail.getD 0 0 else negPart (Bleading_trunc_tail.getD n 0) * cQ ^ n

lemma one_div_25_lt_Bleading_trunc_c0Q : (1 : ℚ) / 25 < Bleading_trunc_c0Q := by
  simp [Bleading_trunc_c0Q, Bleading_trunc_tail, Bleading_trunc_coeffs, negPart, cQ,
    Finset.sum_range_succ]
  norm_num

lemma Bleading_trunc_c0Q_pos : 0 < Bleading_trunc_c0Q :=
  (show (0 : ℚ) < (1 : ℚ) / 25 by norm_num).trans one_div_25_lt_Bleading_trunc_c0Q

/--
Lower bound on `Bleading_trunc.eval₂` on the interval `0 ≤ x ≤ 1/23` in terms of the explicit
constant `Bleading_trunc_c0Q`.
-/
public lemma Bleading_trunc_eval₂_lowerBound {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (1 : ℝ) / 23) :
    (Bleading_trunc.eval₂ (algebraMap ℚ ℝ) x) ≥ (Bleading_trunc_c0Q : ℝ) * x ^ (4 : ℕ) := by
  -- Factor off the initial `X^4`.
  have hpoly :
      Bleading_trunc = Polynomial.X ^ (4 : ℕ) * polyOfCoeffs Bleading_trunc_tail := by
    -- The coefficient list begins with four zeros.
    have hlist : Bleading_trunc_coeffs = 0 :: 0 :: 0 :: 0 :: Bleading_trunc_tail := by
      simp [Bleading_trunc_tail, Bleading_trunc_coeffs]
    unfold Bleading_trunc
    rw [hlist]
    simp [polyOfCoeffs_zero_cons, pow_succ, mul_assoc]
  have hP_eval :
      (Bleading_trunc.eval₂ (algebraMap ℚ ℝ) x) =
        x ^ (4 : ℕ) * (polyOfCoeffs Bleading_trunc_tail).eval₂ (algebraMap ℚ ℝ) x := by
    simp [hpoly, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  -- Expand the tail polynomial as a finite sum over coefficients.
  have htail_eval :
      (polyOfCoeffs Bleading_trunc_tail).eval₂ (algebraMap ℚ ℝ) x =
        ∑ n ∈ Finset.range Bleading_trunc_tail.length,
          (algebraMap ℚ ℝ) (Bleading_trunc_tail.getD n 0) * x ^ n :=
    eval₂_polyOfCoeffs_eq_sum_range_getD (l := Bleading_trunc_tail) (x := x)
  -- Compare term-by-term with the certified lower bound `Bleading_trunc_c0Q`.
  have hxle_c : x ≤ (cQ : ℝ) := by
    -- `hx` already bounds by `1/23`.
    simpa [cQ] using! hx
  have hxpow_le : ∀ n : ℕ, x ^ n ≤ (cQ : ℝ) ^ n := fun n =>
    pow_le_pow_left₀ hx0 hxle_c n
  have hterm_ge :
      ∀ n : ℕ, n < Bleading_trunc_tail.length →
        (algebraMap ℚ ℝ) (Bleading_trunc_tail.getD n 0) * x ^ n ≥
          (algebraMap ℚ ℝ)
              (if n = 0 then Bleading_trunc_tail.getD 0 0
               else negPart (Bleading_trunc_tail.getD n 0) * cQ ^ n) := by
    intro n hn
    by_cases hn0 : n = 0
    · subst hn0
      simp
    · have hxpow0 : 0 ≤ x ^ n := pow_nonneg hx0 _
      by_cases hneg : Bleading_trunc_tail.getD n 0 < 0
      · have hxpow_le' : x ^ n ≤ (cQ : ℝ) ^ n := hxpow_le n
        have hcoeff_neg : (algebraMap ℚ ℝ) (Bleading_trunc_tail.getD n 0) ≤ (0 : ℝ) := by
          have : ((Bleading_trunc_tail.getD n 0 : ℚ) : ℝ) ≤ (0 : ℝ) := by
            exact_mod_cast (le_of_lt hneg)
          simpa using! this
        have hmul :
            (algebraMap ℚ ℝ) (Bleading_trunc_tail.getD n 0) * (cQ : ℝ) ^ n ≤
              (algebraMap ℚ ℝ) (Bleading_trunc_tail.getD n 0) * x ^ n := by
          simpa [mul_assoc] using! (mul_le_mul_of_nonpos_left hxpow_le' hcoeff_neg)
        have hnegPart : negPart (Bleading_trunc_tail.getD n 0) = Bleading_trunc_tail.getD n 0 := by
          unfold negPart
          exact if_pos hneg
        have hmap :
            (algebraMap ℚ ℝ) (negPart (Bleading_trunc_tail.getD n 0)) =
              (algebraMap ℚ ℝ) (Bleading_trunc_tail.getD n 0) := by
          simpa using! congrArg (algebraMap ℚ ℝ) hnegPart
        have hmul' :
            (algebraMap ℚ ℝ) (negPart (Bleading_trunc_tail.getD n 0)) * (cQ : ℝ) ^ n ≤
              (algebraMap ℚ ℝ) (Bleading_trunc_tail.getD n 0) * x ^ n := by
          lia
        have hmapmul :
            (algebraMap ℚ ℝ) (negPart (Bleading_trunc_tail.getD n 0) * cQ ^ n) =
              (algebraMap ℚ ℝ) (negPart (Bleading_trunc_tail.getD n 0)) * (cQ : ℝ) ^ n := by
          simp
        lia
      · have hcoeff_nonneg : (0 : ℝ) ≤ (algebraMap ℚ ℝ) (Bleading_trunc_tail.getD n 0) := by
          have : (0 : ℝ) ≤ ((Bleading_trunc_tail.getD n 0 : ℚ) : ℝ) := by
            exact_mod_cast (le_of_not_gt hneg)
          simpa using! this
        have hL : (0 : ℝ) ≤ (algebraMap ℚ ℝ) (Bleading_trunc_tail.getD n 0) * x ^ n :=
          mul_nonneg hcoeff_nonneg hxpow0
        have hnegPart : negPart (Bleading_trunc_tail.getD n 0) = 0 := by
          unfold negPart
          exact if_neg hneg
        grind only [= map_zero]
  have hsum_ge :
      (Bleading_trunc_c0Q : ℝ) ≤
        ∑ n ∈ Finset.range Bleading_trunc_tail.length,
          (algebraMap ℚ ℝ) (Bleading_trunc_tail.getD n 0) * x ^ n := by
    -- Rewrite `Bleading_trunc_c0Q` as the same sum, then compare termwise.
    have hC0 :
        (Bleading_trunc_c0Q : ℝ) =
          ∑ n ∈ Finset.range Bleading_trunc_tail.length,
            (algebraMap ℚ ℝ)
              (if n = 0 then Bleading_trunc_tail.getD 0 0
               else negPart (Bleading_trunc_tail.getD n 0) * cQ ^ n) := by
      simp [Bleading_trunc_c0Q]
    rw [hC0]
    refine Finset.sum_le_sum ?_
    intro n hn
    have hn' : n < Bleading_trunc_tail.length := by
      simpa [Finset.mem_range] using! hn
    exact (hterm_ge n hn').ge
  -- Combine.
  have hx4 : 0 ≤ x ^ (4 : ℕ) := pow_nonneg hx0 _
  nlinarith

lemma Bleading_trunc_c0_pos : (0 : ℝ) < (Bleading_trunc_c0Q : ℝ) := by
  exact_mod_cast Bleading_trunc_c0Q_pos

/-- A convenient rational lower bound: `1/25 < Bleading_trunc_c0Q`. -/
public lemma Bleading_trunc_one_div_25_lt_c0 : ((1 : ℚ) / 25 : ℝ) < (Bleading_trunc_c0Q : ℝ) := by
  exact_mod_cast one_div_25_lt_Bleading_trunc_c0Q

end

end SpherePacking.Dim24.AppendixA
