-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity


/-!
# Tail-bound numerics for `ineq2` (`1 ≤ t`)

This file provides the purely numeric ingredients used in the truncation estimates from
`appendix.txt` (Lemma A.2, first case), including:

* bounds on `q(t) = exp(-2πt)` and `r(t) = exp(-πt)` for `1 ≤ t`,
* geometric tail bounds for `∑ (n+1)^20 q^n` and `∑ (n+1)^20 r^n`,
* certified rational inequalities to dominate these tails by `eps * q^6` and `eps * r^12`.

The missing step in `ineq2_tail_bound_geOne` is to connect the analytic expression to these
coefficient bounds (i.e. dominate by a `q`- / `r`-series tail).
-/

noncomputable section

namespace SpherePacking.Dim24


/-!
## `π`-bounds used in `appendix.txt`
In the PARI/GP script, `piLower` / `piUpper` are 10-decimal rational bounds obtained by
rounding `π` down/up at `10^10`. We do not compute those bounds from `π`; instead we use the
explicit rationals `3.1415926535` and `3.1415926536` and justify them from the certified
20-decimal bounds in `Mathlib.Analysis.Real.Pi.Bounds`.
-/

/-- The 10-decimal rational lower bound `3.1415926535` used for `π` in `appendix.txt`. -/
@[expose] public def piLower10 : ℝ := (31415926535 : ℝ) / (10000000000 : ℝ)
/-- The 10-decimal rational upper bound `3.1415926536` used for `π` in `appendix.txt`. -/
@[expose] public def piUpper10 : ℝ := (31415926536 : ℝ) / (10000000000 : ℝ)

/-- `piLower10` spelled as a decimal. -/
public lemma piLower10_eq : piLower10 = (3.1415926535 : ℝ) := by
  norm_num [piLower10]

/-- `piUpper10` spelled as a decimal. -/
public lemma piUpper10_eq : piUpper10 = (3.1415926536 : ℝ) := by
  norm_num [piUpper10]

/-- The lower bound `piLower10 < π`. -/
public lemma piLower10_lt_pi : piLower10 < Real.pi := by
  refine lt_trans ?_ Real.pi_gt_d20
  have : (3.1415926535 : ℝ) < (3.14159265358979323846 : ℝ) := by norm_num
  simpa [piLower10_eq] using! this

/-- The upper bound `π < piUpper10`. -/
public lemma pi_lt_piUpper10 : Real.pi < piUpper10 := by
  refine lt_trans Real.pi_lt_d20 ?_
  have : (3.14159265358979323847 : ℝ) < (3.1415926536 : ℝ) := by norm_num
  simpa [piUpper10_eq] using! this

/-- A convenient numerical bound: `432/π^2 ≤ 44`. -/
public lemma cPi_le_44 : (432 / (Real.pi ^ 2) : ℝ) ≤ 44 := by
  have hpiLower0 : 0 < piLower10 := by
    have : (0 : ℝ) < (3.1415926535 : ℝ) := by norm_num
    simpa [piLower10_eq] using! this
  have hsq : piLower10 ^ 2 ≤ Real.pi ^ 2 := by
    have h : piLower10 ≤ Real.pi := le_of_lt piLower10_lt_pi
    simpa [pow_two] using! (mul_le_mul h h hpiLower0.le Real.pi_pos.le)
  have hle : (432 / (Real.pi ^ 2) : ℝ) ≤ 432 / (piLower10 ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 432) (pow_pos hpiLower0 2) hsq
  exact hle.trans (by norm_num [piLower10])

/-- Certified lower bound `432/piUpper10^2 ≤ 432/π^2`. -/
public lemma cPiLower_le :
    (432 / (piUpper10 ^ 2) : ℝ) ≤ (432 / (Real.pi ^ 2) : ℝ) := by
  have hpu0 : 0 < piUpper10 := by
    have : (0 : ℝ) < (3.1415926536 : ℝ) := by norm_num
    simpa [piUpper10_eq] using! this
  have hsq : Real.pi ^ 2 ≤ piUpper10 ^ 2 := by
    have h : Real.pi ≤ piUpper10 := le_of_lt pi_lt_piUpper10
    simpa [pow_two] using! (mul_le_mul h h Real.pi_pos.le hpu0.le)
  simpa using!
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 432) (pow_pos Real.pi_pos 2) hsq)

end SpherePacking.Dim24
