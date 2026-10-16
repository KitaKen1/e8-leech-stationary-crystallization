-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingTruncBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingTailReduction
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.LowerBound
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Order


/-!
Lower bound for the leading terms of `B(t)` for `t ≥ 1` (Appendix A, Lemma `Bleadingterms`).

This file packages the Appendix A reduction into:
- a certified positivity check for the truncation polynomial,
- a tail bound transferring this positivity to `BKernel - BleadingLeadingTerm`,
- the final strict inequality stated as `B_leadingterms_bound`.
-/


noncomputable section

namespace SpherePacking.Dim24

-- The analytic reduction to an explicit polynomial (including the tail bounds) is proved in the
-- Appendix A files imported above. This file packages the final polynomial positivity check.

/-- Sturm-style sign check showing the truncated polynomial is positive (hence the full expression
is positive after restoring the tail). -/
public theorem Bleading_trunc_pos (t : ℝ) (ht : 1 ≤ t) :
    0 <
      (AppendixA.Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (AppendixA.r t))
        - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
  have hx0 : 0 ≤ AppendixA.r t := (Real.exp_pos _).le
  have hxle : AppendixA.r t ≤ (1 : ℝ) / 23 := by
    simpa [AppendixA.r] using! (AppendixA.r_le_one_div_23 (t := t) ht)
  have hpoly :
      (AppendixA.Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (AppendixA.r t)) ≥
        (AppendixA.Bleading_trunc_c0Q : ℝ) * (AppendixA.r t) ^ (4 : ℕ) := by
    simpa using!
      (AppendixA.Bleading_trunc_eval₂_lowerBound (x := AppendixA.r t) hx0 hxle)
  have hxpos : 0 < AppendixA.r t := Real.exp_pos _
  have hxlt1 : AppendixA.r t < 1 := by
    have : (1 : ℝ) / 23 < 1 := by nlinarith
    exact lt_of_le_of_lt hxle this
  have hxpow : (AppendixA.r t) ^ (12 : ℕ) ≤ (AppendixA.r t) ^ (4 : ℕ) := by
    have hx1 : AppendixA.r t ≤ 1 := le_of_lt hxlt1
    simpa using! (pow_le_pow_of_le_one hx0 hx1 (by decide : (4 : ℕ) ≤ 12))
  have heps : AppendixA.eps < (AppendixA.Bleading_trunc_c0Q : ℝ) := by
    have hc0' : ((1 : ℚ) / 25 : ℝ) < (AppendixA.Bleading_trunc_c0Q : ℝ) :=
      AppendixA.Bleading_trunc_one_div_25_lt_c0
    have heps' : AppendixA.eps < ((1 : ℚ) / 25 : ℝ) := by
      have : (AppendixA.eps : ℝ) = (1 : ℝ) / (10 : ℝ) ^ (50 : ℕ) := by
        simp [AppendixA.eps, zpow_neg, one_div, zpow_ofNat]
      rw [this]
      norm_num
    exact lt_trans heps' hc0'
  have hx4pos : 0 < (AppendixA.r t) ^ (4 : ℕ) := pow_pos hxpos _
  have hcp : 0 < (AppendixA.Bleading_trunc_c0Q : ℝ) - AppendixA.eps := sub_pos.2 heps
  have hmain :
      0 <
        (AppendixA.Bleading_trunc_c0Q : ℝ) * (AppendixA.r t) ^ (4 : ℕ)
          - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
    have hle :
        (AppendixA.Bleading_trunc_c0Q : ℝ) * (AppendixA.r t) ^ (4 : ℕ)
            - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) ≥
          (AppendixA.Bleading_trunc_c0Q : ℝ) * (AppendixA.r t) ^ (4 : ℕ)
            - AppendixA.eps * (AppendixA.r t) ^ (4 : ℕ) := by
      have heps0 : 0 ≤ AppendixA.eps := by
        have heps' : AppendixA.eps = (1 : ℝ) / (10 : ℝ) ^ (50 : ℕ) := by
          simp [AppendixA.eps, zpow_neg, one_div, zpow_ofNat]
        rw [heps']
        positivity
      have :
          AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) ≤
            AppendixA.eps * (AppendixA.r t) ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_left hxpow heps0
      linarith
    have hfactor :
        (AppendixA.Bleading_trunc_c0Q : ℝ) * (AppendixA.r t) ^ (4 : ℕ)
            - AppendixA.eps * (AppendixA.r t) ^ (4 : ℕ) =
          ((AppendixA.Bleading_trunc_c0Q : ℝ) - AppendixA.eps) * (AppendixA.r t) ^ (4 : ℕ) := by
      ring
    have hpos4 :
        0 <
          (AppendixA.Bleading_trunc_c0Q : ℝ) * (AppendixA.r t) ^ (4 : ℕ)
            - AppendixA.eps * (AppendixA.r t) ^ (4 : ℕ) := by
      simpa [hfactor] using! mul_pos hcp hx4pos
    exact lt_of_lt_of_le hpos4 hle
  have hfinal :
      (AppendixA.Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (AppendixA.r t))
          - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) ≥
        (AppendixA.Bleading_trunc_c0Q : ℝ) * (AppendixA.r t) ^ (4 : ℕ)
          - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
    linarith [hpoly]
  exact lt_of_lt_of_le hmain hfinal

/-- Tail bound for truncating the `q`-series in Lemma `Bleadingterms`. -/
public theorem Bleading_tail_bound (t : ℝ) (ht : 1 ≤ t) :
    (BKernel t (lt_of_lt_of_le (by norm_num) ht)).re
        - ((1 / 39 : ℝ) * t * Real.exp (2 * Real.pi * t)
            - (10 / (117 * Real.pi) : ℝ) * Real.exp (2 * Real.pi * t))
      ≥ (AppendixA.Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (AppendixA.r t))
          - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  set L : ℝ :=
      (AppendixA.Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (AppendixA.r t))
        - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ)
  have hL0 : 0 ≤ L := (le_of_lt (Bleading_trunc_pos (t := t) ht))
  have hnum : L ≤ (BleadingNum t ht0).re := by
    simpa [L, AppendixA.r, AppendixA.eps] using! (AppendixA.BleadingNum_lower_bound (t := t) ht)
  have h :=
    Bleading_lowerBound_of_num (t := t) ht0 hL0 hnum
  -- Unfold the leading term to match the statement.
  simpa [L, BleadingLeadingTerm] using! h

/-- Lower bound for the leading terms of `B(t)` for `t≥1` (Lemma A.3 / `lemma:Bleadingterms`). -/
public theorem B_leadingterms_bound (t : ℝ) (ht : 1 ≤ t) :
    let ht' : 0 < t := lt_of_lt_of_le (by norm_num) ht
    (BKernel t ht').re >
      (1 / 39 : ℝ) * t * Real.exp (2 * Real.pi * t)
        - (10 / (117 * Real.pi) : ℝ) * Real.exp (2 * Real.pi * t) := by
  have hbound :
      (BKernel t (lt_of_lt_of_le (by norm_num) ht)).re
          - ((1 / 39 : ℝ) * t * Real.exp (2 * Real.pi * t)
              - (10 / (117 * Real.pi) : ℝ) * Real.exp (2 * Real.pi * t))
        ≥ (AppendixA.Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (AppendixA.r t))
            - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) :=
    Bleading_tail_bound (t := t) ht
  have hpos :
      0 <
        (AppendixA.Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (AppendixA.r t))
          - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) :=
    Bleading_trunc_pos (t := t) ht
  linarith

end SpherePacking.Dim24
