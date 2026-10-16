-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
public import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Positivity


/-!
# Delta bounds for the `t ≤ 1` truncation

Bounds for `Δ(it)` and basic relations between `q(t)` and `r(t)` for the `t ≤ 1` truncation proof.

## Main statements
* `Delta_it_re_le_q`
* `Delta_it_re_sq_le_q_sq`
-/


open scoped BigOperators Real
open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

/-- Upper bound `Re(Δ(it)) ≤ q(t)` on the imaginary axis. -/
public lemma Delta_it_re_le_q (t : ℝ) (ht0 : 0 < t) : (Δ (it t ht0)).re ≤ q t := by
  have hre :
      (Δ (it t ht0)).re =
        q t * ∏' n : ℕ, (1 - Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t))) ^ 24 := by
    have harg : (-2 * π * t) = -(2 * (π * t)) := by ring
    simpa [AppendixA.q, ResToImagAxis, ht0, it, mul_assoc, harg] using!
      (re_ResToImagAxis_Delta_eq_real_prod (t := t) ht0)
  set f : ℕ → ℝ := fun n =>
    (1 - Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t))) ^ 24
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    have hexp_le_one : Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) ≤ 1 := by
      have hnonneg : 0 ≤ 2 * π * ((n + 1 : ℕ) : ℝ) * t := by positivity [Real.pi_pos, ht0]
      have : (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) ≤ 0 := neg_nonpos.2 hnonneg
      simpa using! (Real.exp_le_one_iff.2 this)
    have hbase0 :
        0 ≤ 1 - Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) := sub_nonneg.2 hexp_le_one
    simpa [f] using! pow_nonneg hbase0 24
  have hf1 : ∀ n, f n ≤ 1 := by
    intro n
    have hexp_le_one : Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) ≤ 1 := by
      have hnonneg : 0 ≤ 2 * π * ((n + 1 : ℕ) : ℝ) * t := by positivity [Real.pi_pos, ht0]
      have : (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) ≤ 0 := neg_nonpos.2 hnonneg
      simpa using! (Real.exp_le_one_iff.2 this)
    have hbase0 :
        0 ≤ 1 - Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t)) := sub_nonneg.2 hexp_le_one
    have hbase1 :
        (1 - Real.exp (-(2 * π * ((n + 1 : ℕ) : ℝ) * t))) ≤ 1 :=
      sub_le_self _ (Real.exp_pos _).le
    have := pow_le_pow_of_le_one hbase0 hbase1 (by decide : (0 : ℕ) ≤ 24)
    simpa [f] using! this
  have hprod_le_one : (∏' n : ℕ, f n) ≤ 1 := by
    by_cases hm : Multipliable f
    · have hlim :
          Filter.Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, f n)
            Filter.atTop (nhds (∏' n : ℕ, f n)) :=
        (hm.hasProd).tendsto_prod_nat
      have hbound : ∀ N : ℕ, (∏ n ∈ Finset.range N, f n) ≤ 1 := by
        intro N
        exact Finset.prod_le_one (fun n _ => hf0 n) (fun n _ => hf1 n)
      exact Multipliable.tprod_le_of_prod_range_le hm hbound
    · have : (∏' n : ℕ, f n) = 1 := tprod_eq_one_of_not_multipliable hm
      simp [this]
  have hq0 : 0 ≤ q t := (Real.exp_pos _).le
  calc
    (Δ (it t ht0)).re = q t * (∏' n : ℕ, f n) := by simp [hre, f]
    _ ≤ q t * 1 := by exact mul_le_mul_of_nonneg_left hprod_le_one hq0
    _ = q t := by simp

/-- Squared version of `Delta_it_re_le_q`. -/
public lemma Delta_it_re_sq_le_q_sq (t : ℝ) (ht0 : 0 < t) :
    (Δ (it t ht0)).re ^ (2 : ℕ) ≤ (q t) ^ (2 : ℕ) := by
  have h0 : 0 ≤ (Δ (it t ht0)).re := (Delta_it_re_pos (t := t) ht0).le
  have h1 : (Δ (it t ht0)).re ≤ q t := Delta_it_re_le_q (t := t) ht0
  have hq0 : 0 ≤ q t := (Real.exp_pos _).le
  simpa [pow_two] using! mul_le_mul h1 h1 h0 hq0

end SpherePacking.Dim24
