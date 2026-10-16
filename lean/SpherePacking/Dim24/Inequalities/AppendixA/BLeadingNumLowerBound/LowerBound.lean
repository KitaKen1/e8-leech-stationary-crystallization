-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffMatchingComputations
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.RemainderBound


/-!
# Lower bound for `BleadingNum`

This file proves the key truncation inequality used in Appendix A (Lemma `Bleadingterms`):
the explicit polynomial truncation `Bleading_trunc` (with a small error term) is bounded above by
the real part of `BleadingNum`.

## Main statements
* `BleadingNum_lower_bound`

## Implementation notes
This module lives under `AppendixA/BLeadingNumLowerBound/` to avoid `Foo.lean`/`Foo/` name
collisions.
-/


noncomputable section

namespace SpherePacking.Dim24.AppendixA

/-- The key truncation estimate needed for Appendix A, Lemma `Bleadingterms`. -/
public theorem BleadingNum_lower_bound (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by simp : (0 : ℝ) < 1) ht
    (Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (Real.exp (-Real.pi * t)))
        - (10 : ℝ) ^ (-50 : ℤ) * (Real.exp (-Real.pi * t)) ^ (12 : ℕ)
      ≤ (BleadingNum t ht0).re := by
  intro ht0
  -- Step 1: reduce the explicit truncation polynomial to the exact truncation sum.
  have htrunc :
      (Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (r t)) ≤ Bleading_exact_trunc t :=
    Bleading_trunc_eval₂_le_exact_trunc (t := t) ht
  have htrunc' :
      (Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ) ≤
        Bleading_exact_trunc t - eps * (r t) ^ (12 : ℕ) :=
    sub_le_sub_right htrunc _
  -- Step 2: bound the real part of `BleadingNum` using the norm estimate.
  have hEq :
      BleadingNum t ht0 - (Bleading_exact_trunc t : ℂ) = BleadingNumRemainder t ht := by
    simpa using! (BleadingNum_sub_exact_trunc_eq_remainder (t := t) (ht := ht))
  have hnormR : ‖BleadingNumRemainder t ht‖ ≤ eps * (r t) ^ (12 : ℕ) := by
    simpa using! (BleadingNumRemainder_norm_le (t := t) (ht := ht) (ht0 := ht0))
  have hnorm :
      ‖BleadingNum t ht0 - (Bleading_exact_trunc t : ℂ)‖ ≤ eps * (r t) ^ (12 : ℕ) := by
    simpa [hEq] using! hnormR
  have hre :
      Bleading_exact_trunc t - eps * (r t) ^ (12 : ℕ) ≤ (BleadingNum t ht0).re :=
    re_ge_sub_of_norm_sub_le (z := BleadingNum t ht0) (a := Bleading_exact_trunc t)
      (δ := eps * (r t) ^ (12 : ℕ)) hnorm
  have hmain :
      (Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ) ≤
        (BleadingNum t ht0).re :=
    le_trans htrunc' hre
  -- Rewrite the goal back to the explicit `exp(-π t)` / `10^(-50)` form.
  simpa [eps, r, mul_assoc, mul_left_comm, mul_comm] using! hmain

end SpherePacking.Dim24.AppendixA
