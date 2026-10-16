-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Trunc.TransformedRe
public import
  SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Trunc.ExactTruncPosRigorous.Positivity
public import
  SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.TailBound.TailEstimate

/-!
# Exact truncation tail bound

Bridge lemma for the `t ≤ 1` reduction of Lemma `phinonpos` (Appendix A).

We use the exact finite head `AppendixA.VarphiLeOne.exactTrunc t` together with the tail estimate
from `AppendixA.VarphiLeOneNumLowerBound` to bound the transformed expression on the imaginary axis.

The resulting inequality has the form
`exactTrunc t - eps * r(t)^12 ≤ transformed.re`.

## Main statements
* `exactTrunc_sub_eps_le_transformed_re`
-/


open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.VarphiNeg.LeOne.Trunc

open AppendixA
open AppendixA.VarphiLeOne

/-- Tail bound for the `t ≤ 1` reduction, expressed using the exact truncation head. -/
public theorem exactTrunc_sub_eps_le_transformed_re (t : ℝ) (ht : 1 ≤ t) :
    exactTrunc t - eps * (AppendixA.r t) ^ (12 : ℕ)
      ≤ (-((t : ℂ) ^ (2 : ℕ)) * varphi (it t (lt_of_lt_of_le (by norm_num) ht))
            + Complex.I * (t : ℂ) * varphi₁ (it t (lt_of_lt_of_le (by norm_num) ht))
            + varphi₂ (it t (lt_of_lt_of_le (by norm_num) ht))).re := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hit : it t (lt_of_lt_of_le (by norm_num) ht) = it t ht0 := by
    ext1
    rfl
  have hL0 : 0 ≤ exactTrunc t - eps * (AppendixA.r t) ^ (12 : ℕ) :=
    le_of_lt (varphi_exact_trunc_sub_eps_pos (t := t) ht)
  have hnum :
      exactTrunc t - eps * (AppendixA.r t) ^ (12 : ℕ) ≤ (transformed_num t ht0).re := by
    -- This is exactly the main result of `AppendixA.VarphiLeOneNumLowerBound`,
    -- rewritten to the `transformed_num` wrapper.
    have h :=
      (AppendixA.VarphiLeOne.exactTrunc_sub_eps_le_num_re (t := t) ht)
    -- Unfold the `have ht0 := ...` binder in the statement of `exactTrunc_sub_eps_le_num_re`.
    simpa [ht0, hit, Dim24.transformed_num, transformed_num] using! h
  -- Divide by `Δ(it)^2` using the fact `Δ(it).re^2 ≤ 1`.
  simpa [hit] using! transformed_re_lowerBound_of_num (t := t) ht0 hL0 hnum

end SpherePacking.Dim24.VarphiNeg.LeOne.Trunc
