-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
public import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.AbsBoundQ
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.List.GetD
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.AppendixA.Trunc
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.DenomReduction.LowerBound


/-!
# Positivity of the truncation polynomial (`1 ≤ t` case)

The main result `ineq2_trunc_geOne_pos` shows
`0 < ineq2_trunc_geOne.eval₂ _ (r t) - eps * (r t)^12` for `1 ≤ t`. This is the "Sturm-style"
polynomial sign check used in Appendix A before restoring the analytic tail bounds.

## Main statements
* `ineq2_trunc_geOne_pos`
-/

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

/-- Sturm-style sign check for the `t ≥ 1` truncated polynomial (positivity). -/
public theorem ineq2_trunc_geOne_pos (t : ℝ) (ht : 1 ≤ t) :
    0 < (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ) := by
  -- On `t ≥ 1`, `x := exp(-πt)` satisfies `0 < x < 1/23`.
  set x : ℝ := r t
  have hxpos : 0 < x := Real.exp_pos _
  have hx0 : 0 ≤ x := hxpos.le
  have hxle : x ≤ (1 / 23 : ℝ) := by
    simpa [x, r] using! (AppendixA.r_le_one_div_23 (t := t) ht)
  have hxlt1 : x < 1 := by
    have : (1 : ℝ) / 23 < 1 := by nlinarith
    exact lt_of_le_of_lt hxle this
  -- Factor off `X^5` (the first five coefficients are zero).
  set l : List ℚ := AppendixA.ineq2_trunc_geOne_coeffs.drop 5
  have hlist : AppendixA.ineq2_trunc_geOne_coeffs = 0 :: 0 :: 0 :: 0 :: 0 :: l := by
    simp [l, AppendixA.ineq2_trunc_geOne_coeffs]
  have hpoly :
      ineq2_trunc_geOne =
        (Polynomial.X : Polynomial ℚ) ^ (5 : ℕ) * AppendixA.polyOfCoeffs l := by
    dsimp [ineq2_trunc_geOne, AppendixA.ineq2_trunc_geOne]
    rw [hlist]
    simp [AppendixA.polyOfCoeffs_zero_cons, pow_succ, mul_assoc, mul_comm]
  -- Split `l` into head/tail and apply the generic absolute tail bound at `c = 1/23`.
  set a5 : ℚ := AppendixA.ineq2_trunc_geOne_coeffs.getD 5 0
  set tail : List ℚ := AppendixA.ineq2_trunc_geOne_coeffs.drop 6
  have hl : l = a5 :: tail := by
    simp [l, a5, tail, AppendixA.ineq2_trunc_geOne_coeffs]
  have hc0 : 0 ≤ (1 / 23 : ℝ) := by norm_num
  have hq_lower :
      (AppendixA.polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x ≥
        (a5 : ℝ) - (1 / 23 : ℝ) * AppendixA.absBound tail (1 / 23 : ℝ) := by
    have := AppendixA.eval₂_polyOfCoeffs_ge_sub_absBound (a := a5) (l := tail) (x := x)
      (c := (1 / 23 : ℝ)) hx0 hc0 hxle
    simpa [hl] using! this
  have habs_cast :
      AppendixA.absBound tail (1 / 23 : ℝ) =
        (AppendixA.absBoundQ tail AppendixA.BleadingCoeffs.cQ : ℝ) := by
    have : ((AppendixA.BleadingCoeffs.cQ : ℝ)) = (1 / 23 : ℝ) := by
      norm_num [AppendixA.BleadingCoeffs.cQ]
    simpa [this] using! (AppendixA.absBoundQ_cast (l := tail) AppendixA.BleadingCoeffs.cQ)
  have hcQ : (AppendixA.BleadingCoeffs.cQ : ℝ) = (1 / 23 : ℝ) := by
    norm_num [AppendixA.BleadingCoeffs.cQ]
  have habs_cast_inv :
      AppendixA.absBound tail ((23 : ℝ)⁻¹) =
        (AppendixA.absBoundQ tail AppendixA.BleadingCoeffs.cQ : ℝ) := by
    simpa [one_div] using! habs_cast
  have hcQ_inv : (AppendixA.BleadingCoeffs.cQ : ℝ) = (23 : ℝ)⁻¹ := by
    simpa [one_div] using! hcQ
  have hq_lower' :
      (Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q : ℝ) ≤
        (AppendixA.polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x :=
        by
    -- Rewrite `hq_lower` in terms of `ineq2_trunc_geOne_c0Q`.
    have : (a5 : ℝ) - (1 / 23 : ℝ) * AppendixA.absBound tail (1 / 23 : ℝ) =
        (Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q : ℝ) := by
      -- Convert the `absBound` term into its rational closed form, then unfold `c0Q`.
      calc
        (a5 : ℝ) - (1 / 23 : ℝ) * AppendixA.absBound tail (1 / 23 : ℝ)
            =
              (a5 : ℝ) - (AppendixA.BleadingCoeffs.cQ : ℝ) *
                (AppendixA.absBoundQ tail AppendixA.BleadingCoeffs.cQ : ℝ) := by
                simp [habs_cast_inv, hcQ_inv]
        _ = (Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q : ℝ) := by
              simp [Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q, a5, tail, sub_eq_add_neg]
    linarith [hq_lower, this]
  -- Lower bound the full evaluation by `c0 * x^5`.
  have hP_eval :
      (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) x) =
        x ^ (5 : ℕ) * (AppendixA.polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x := by
    simp [hpoly, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have hP_lower :
      (Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q : ℝ) * x ^ (5 : ℕ) ≤
        (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) x) := by
    rw [hP_eval]
    have := mul_le_mul_of_nonneg_left hq_lower' (pow_nonneg hx0 (5 : ℕ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using! this
  -- Show `eps < c0` using a certified rational lower bound `1/25 < c0`.
  have heps_lt_one_div_25 : eps < ((1 : ℚ) / 25 : ℝ) := by
    have heps_eq : (eps : ℝ) = (1 : ℝ) / (10 : ℝ) ^ (50 : ℕ) := by
      calc
        (eps : ℝ) = (10 : ℝ) ^ (-50 : ℤ) := by
          simp [eps, AppendixA.eps]
        _ = (10 : ℝ) ^ (-(50 : ℤ)) := by simp
        _ = ((10 : ℝ) ^ (50 : ℤ))⁻¹ := by simp
        _ = ((10 : ℝ) ^ (50 : ℕ))⁻¹ := by
          rfl
        _ = (1 : ℝ) / (10 : ℝ) ^ (50 : ℕ) := by
          simp [one_div]
    rw [heps_eq]
    norm_num
  have hone_div_25_lt_c0 :
      ((1 : ℚ) / 25 : ℝ) < (Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q : ℝ) := by
    exact_mod_cast Ineq2GeOneTruncAux.one_div_25_lt_ineq2_trunc_geOne_c0Q
  have heps_lt_c0 : eps < (Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q : ℝ) :=
    lt_trans heps_lt_one_div_25 hone_div_25_lt_c0
  have hx12_le_x5 : x ^ (12 : ℕ) ≤ x ^ (5 : ℕ) := by
    have hx1 : x ≤ 1 := le_of_lt hxlt1
    exact pow_le_pow_of_le_one hx0 hx1 (by decide : (5 : ℕ) ≤ 12)
  have heps0 : 0 ≤ eps := (show 0 < eps from by
    have : (0 : ℝ) < (10 : ℝ) := by norm_num
    simpa [eps, AppendixA.eps] using! (zpow_pos this (-50 : ℤ))).le
  have hle :
      (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) x) - eps * x ^ (12 : ℕ) ≥
        (Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q : ℝ) * x ^ (5 : ℕ) - eps * x ^ (5 : ℕ) := by
    have : eps * x ^ (12 : ℕ) ≤ eps * x ^ (5 : ℕ) :=
      mul_le_mul_of_nonneg_left hx12_le_x5 heps0
    linarith [hP_lower, this]
  have hx5_pos : 0 < x ^ (5 : ℕ) := pow_pos hxpos _
  have hpos :
      0 < ((Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q : ℝ) - eps) * x ^ (5 : ℕ) :=
    mul_pos (sub_pos.2 heps_lt_c0) hx5_pos
  linarith


end SpherePacking.Dim24
