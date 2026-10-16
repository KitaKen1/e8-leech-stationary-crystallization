-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Order


/-!
Tail bounds for `q`-series (`q = exp(-2π t)`) used in Appendix A.

This file packages the geometric tail estimate corresponding to the PARI/GP
`PolynomialSum(..., 1/535, 50, ...)` checks in `appendix.txt`.
-/


open scoped BigOperators Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- For `t ≥ 1`, the `q`-parameter satisfies `q t ≤ 1/535`. -/
public lemma q_le_one_div_535 (t : ℝ) (ht : 1 ≤ t) : q t ≤ (1 : ℝ) / 535 := by
  simpa [q] using! (q_le_one_div_535_of_one_le (t := t) ht)

/-- Numeric bound: the geometric ratio at `q = 1/535`, `k = 20`, `N = 50` is at most `1/2`. -/
public lemma powGeomRatio_one_div_535_20_50_le_half :
    powGeomRatio ((1 : ℝ) / 535) 20 50 ≤ (1 : ℝ) / 2 := by
  norm_num [powGeomRatio]

/-- If `q' ≤ 1/535`, then `powGeomRatio q' 20 50 ≤ 1/2`. -/
public lemma powGeomRatio_q_le_half_of_q_le_one_div_535 {q' : ℝ}
    (hq : q' ≤ (1 : ℝ) / 535) :
    powGeomRatio q' 20 50 ≤ (1 : ℝ) / 2 := by
  exact (powGeomRatio_mono_left (q := q') (q' := (1 : ℝ) / 535) hq 20 50).trans
    powGeomRatio_one_div_535_20_50_le_half

/-- A certified bound of the form `tail ≤ eps * q^6` for `q(t) = exp(-2π t)` when `t ≥ 1`. -/
public theorem powGeomTail_bound_eps (t : ℝ) (ht : 1 ≤ t) :
    (∑' m : ℕ, powGeomTerm (q t) 20 (50 + m)) ≤ eps * (q t) ^ (6 : ℕ) := by
  have hq0 : 0 ≤ q t := q_nonneg t
  have hqle : q t ≤ (1 : ℝ) / 535 := q_le_one_div_535 (t := t) ht
  have hρ_le_half : powGeomRatio (q t) 20 50 ≤ (1 : ℝ) / 2 :=
    powGeomRatio_q_le_half_of_q_le_one_div_535 (q' := q t) hqle
  have htail_le' :
      (∑' m : ℕ, powGeomTerm (q t) 20 (50 + m)) ≤
        2 * powGeomTerm (q t) 20 50 :=
    tsum_powGeomTerm_tail_le_two_mul (q := q t) (k := 20) (N := 50) hq0 hρ_le_half
  -- Now dominate `2 * (51^20) * (q t)^50` by `eps * (q t)^6`.
  have hpow50 : (q t) ^ (50 : ℕ) = (q t) ^ (6 : ℕ) * (q t) ^ (44 : ℕ) := by
    simpa [pow_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using! (pow_add (q t) 6 44)
  have hpow44_le : (q t) ^ (44 : ℕ) ≤ ((1 : ℝ) / 535) ^ (44 : ℕ) := by
    simpa using! (pow_le_pow_left₀ hq0 hqle (44 : ℕ))
  have hconstQ :
      (2 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 535) ^ (44 : ℕ) < (10 : ℚ) ^ (-50 : ℤ) := by
    norm_num
  have hconstR :
      (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) < eps := by
    have h' :
        ((2 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 535) ^ (44 : ℕ) : ℝ) <
          ((10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
      exact_mod_cast hconstQ
    have h'' :
        (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) < (10 : ℝ) ^ (-50 : ℤ) := by
      simpa using! h'
    simpa [eps] using! h''
  have hconstR' :
      (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ) ≤ eps := by
    have hle :
        (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ) ≤
          (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow44_le (by positivity)
    exact le_trans hle (le_of_lt hconstR)
  have hqt6 : 0 ≤ (q t) ^ (6 : ℕ) := pow_nonneg hq0 _
  have hmain :
      2 * powGeomTerm (q t) 20 50 ≤ eps * (q t) ^ (6 : ℕ) := by
    dsimp [powGeomTerm]
    have : ((50 + 1 : ℝ) ^ (20 : ℕ)) = (51 : ℝ) ^ (20 : ℕ) := by norm_num
    rw [this]
    rw [hpow50]
    have :
        (2 : ℝ) * ((51 : ℝ) ^ (20 : ℕ) * ((q t) ^ (6 : ℕ) * (q t) ^ (44 : ℕ))) =
          ((q t) ^ (6 : ℕ)) * ((2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ)) := by
      ring_nf
    rw [this]
    have := mul_le_mul_of_nonneg_left hconstR' hqt6
    simpa [mul_assoc, mul_left_comm, mul_comm] using! this
  exact le_trans htail_le' hmain

end

end SpherePacking.Dim24.AppendixA
