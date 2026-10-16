-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-!
Elementary bounds for `r(t) = exp(-π t)` used in Appendix A truncation arguments.

We keep these lemmas in a dedicated file to avoid duplicating the `exp`/`π` numerics across the
various truncation modules.
-/


open scoped Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- The `r`-parameter used in Appendix A: `r(t) = exp(-π t)`. -/
@[expose] public def r (t : ℝ) : ℝ := Real.exp (-Real.pi * t)

/-- Positivity of the `r`-parameter: `0 < r t`. -/
public lemma r_pos (t : ℝ) : 0 < r t := by
  simpa [r] using! Real.exp_pos (-Real.pi * t)

/-- Nonnegativity of the `r`-parameter: `0 ≤ r t`. -/
public lemma r_nonneg (t : ℝ) : 0 ≤ r t := (r_pos t).le

private lemma exp_pi_gt_23 : (23 : ℝ) < Real.exp (157 / 50 : ℝ) := by
  have hsum_le :
      (Finset.sum (Finset.range 10) fun n : ℕ => (157 / 50 : ℝ) ^ n / (Nat.factorial n)) ≤
        Real.exp (157 / 50 : ℝ) := by
    have hx : (0 : ℝ) ≤ (157 / 50 : ℝ) := by norm_num
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
      exp_lower_bound_range (x := (157 / 50 : ℝ)) hx 9
  have hsum_gt :
      (23 : ℝ) <
        Finset.sum (Finset.range 10) fun n : ℕ => (157 / 50 : ℝ) ^ n / (Nat.factorial n) := by
    -- A closed numerical inequality.
    set_option maxRecDepth 6000 in
    norm_num
  exact lt_of_lt_of_le hsum_gt hsum_le

private lemma exp_pi_gt_23' : (23 : ℝ) < Real.exp Real.pi := by
  have hpi : (157 / 50 : ℝ) < Real.pi := by
    simpa [show (3.14 : ℝ) = (157 / 50 : ℝ) by norm_num] using! Real.pi_gt_d2
  exact exp_pi_gt_23.trans (Real.exp_lt_exp.2 hpi)

private lemma t_le_exp_pi_mul_sub_one (t : ℝ) (ht : 1 ≤ t) :
    t ≤ Real.exp (Real.pi * (t - 1)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have ht1 : 0 ≤ t - 1 := sub_nonneg.2 ht
  have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_d2]
  have hlog : Real.log t ≤ Real.pi * (t - 1) := by
    refine (Real.log_le_sub_one_of_pos ht0).trans ?_
    simpa [one_mul] using! (mul_le_mul_of_nonneg_right hpi ht1)
  simpa [Real.exp_log ht0] using! (Real.exp_le_exp.2 hlog)

public lemma t_mul_r_le_one_div_23 (t : ℝ) (ht : 1 ≤ t) :
    t * r t ≤ (1 / 23 : ℝ) := by
  have h23 : (23 : ℝ) ≤ Real.exp Real.pi := (le_of_lt exp_pi_gt_23')
  have ht_le : t ≤ Real.exp (Real.pi * (t - 1)) := t_le_exp_pi_mul_sub_one t ht
  have h23t : (23 : ℝ) * t ≤ Real.exp (Real.pi * t) := by
    have hmul :
        (23 : ℝ) * t ≤ Real.exp Real.pi * Real.exp (Real.pi * (t - 1)) := by
      nlinarith
    have hexp : Real.exp Real.pi * Real.exp (Real.pi * (t - 1)) = Real.exp (Real.pi * t) := by
      simpa [show Real.pi + Real.pi * (t - 1) = Real.pi * t by ring] using!
        (Real.exp_add Real.pi (Real.pi * (t - 1))).symm
    simpa [hexp] using! hmul
  have hmain :
      (23 : ℝ) * (t * Real.exp (-Real.pi * t)) ≤ 1 := by
    have hmul' :
        (23 : ℝ) * t * Real.exp (-Real.pi * t) ≤
          Real.exp (Real.pi * t) * Real.exp (-Real.pi * t) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using!
        (mul_le_mul_of_nonneg_right h23t (Real.exp_pos (-Real.pi * t)).le)
    have hcancel : Real.exp (Real.pi * t) * Real.exp (-Real.pi * t) = (1 : ℝ) := by
      simpa [Real.exp_add] using! (Real.exp_add (Real.pi * t) (-Real.pi * t)).symm
    calc
      (23 : ℝ) * (t * Real.exp (-Real.pi * t)) = (23 : ℝ) * t * Real.exp (-Real.pi * t) := by ring
      _ ≤ Real.exp (Real.pi * t) * Real.exp (-Real.pi * t) := hmul'
      _ = 1 := hcancel
  have h23pos : (0 : ℝ) < (23 : ℝ) := by norm_num
  have : t * Real.exp (-Real.pi * t) ≤ (1 : ℝ) / 23 :=
    (le_div_iff₀ h23pos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using! hmain)
  simpa [r] using! this

/-- For `t ≥ 1`, the bound `r t ≤ 1/23` used in Appendix A. -/
public lemma r_le_one_div_23 (t : ℝ) (ht : 1 ≤ t) : r t ≤ (1 / 23 : ℝ) := by
  have hr : 0 ≤ r t := r_nonneg t
  have hrt : r t ≤ t * r t := by
    simpa [one_mul] using! (mul_le_mul_of_nonneg_right ht hr)
  exact hrt.trans (t_mul_r_le_one_div_23 (t := t) ht)

end

end SpherePacking.Dim24.AppendixA
