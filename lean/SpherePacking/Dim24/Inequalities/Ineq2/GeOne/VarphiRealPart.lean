-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.AppendixA.Trunc
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.DenomReduction.Numerators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2Varphi.TailBound


/-!
# Real-part bound for `varphi_num` (t ≥ 1)

On the imaginary axis, the truncation polynomial `varphi_trunc_geOne` is real-valued. We combine
the complex norm bound on `varphi_num - varphi_trunc_geOne` with the inequality
`|(z - a).re| ≤ ‖z - a‖` to obtain a lower bound for `re (varphi_num (it t ...))`.

## Main statements
* `varphi_num_trunc_geOne_re_lower`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24


private lemma pow_q_six_eq_pow_r_twelve (t : ℝ) :
    (AppendixA.q t) ^ (6 : ℕ) = (AppendixA.r t) ^ (12 : ℕ) := by
  simpa [AppendixA.q_eq_r_sq] using! (pow_mul (AppendixA.r t) 2 6).symm

private lemma varphi_num_trunc_geOne_re_sub_le (t : ℝ) (ht : 1 ≤ t) :
    ‖(varphi_num (it t (lt_of_lt_of_le (by norm_num) ht))
          - ((AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (AppendixA.q t) : ℝ) : ℂ))‖
      ≤ (AppendixA.eps / 2) * (AppendixA.r t) ^ (12 : ℕ) := by
  simpa [pow_q_six_eq_pow_r_twelve (t := t)] using!
    (Ineq2Varphi.varphi_num_trunc_geOne_norm_sub_le (t := t) ht)

/-- For `1 ≤ t`, convert (postTransparency := .instances) the norm bound on `varphi_num - varphi_trunc_geOne` into a lower bound on
`(varphi_num (it t ...)).re`. -/
public lemma varphi_num_trunc_geOne_re_lower (t : ℝ) (ht : 1 ≤ t) :
    (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (AppendixA.q t))
        - (AppendixA.eps / 2) * (AppendixA.r t) ^ (12 : ℕ)
      ≤ (varphi_num (it t (lt_of_lt_of_le (by norm_num) ht))).re := by
  set z : ℂ := varphi_num (it t (lt_of_lt_of_le (by norm_num) ht))
  set a : ℝ := AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (AppendixA.q t)
  have hnorm :
      ‖z - (a : ℂ)‖ ≤ (AppendixA.eps / 2) * (AppendixA.r t) ^ (12 : ℕ) := by
    simpa [z, a] using! (varphi_num_trunc_geOne_re_sub_le (t := t) ht)
  have habs : |z.re - a| ≤ (AppendixA.eps / 2) * (AppendixA.r t) ^ (12 : ℕ) :=
    by
    simpa using! (Complex.abs_re_le_norm (z - (a : ℂ))).trans hnorm
  -- `|z.re - a| ≤ δ` implies `a - δ ≤ z.re`.
  exact sub_le_of_abs_sub_le_left habs


end SpherePacking.Dim24
