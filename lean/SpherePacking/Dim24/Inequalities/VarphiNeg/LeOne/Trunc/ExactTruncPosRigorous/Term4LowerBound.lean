-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
 SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Trunc.ExactTruncPosRigorous.Term2LowerBound
public import
 SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.ExactTruncTail.ExactTruncation
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PiBoundsAndTruncCompare


/-!
# Term 4 lower bound

Lower bound for the `i = 4` term in the exact truncation head `exactTrunc t`
used in the `t ≤ 1` reduction of Appendix A.

## Main statements
* `term4_lower_bound`
-/


noncomputable section

namespace SpherePacking.Dim24.VarphiNeg.LeOne.Trunc

open AppendixA
open AppendixA.VarphiLeOne

/-- Lower bound for the contribution of the `i = 4` coefficient to `exactTrunc t` for `t ≥ 1`. -/
public lemma term4_lower_bound (t : ℝ) (ht : 1 ≤ t) :
    exactCoeff t 4 * (AppendixA.r t) ^ (4 : ℕ) ≥
      (Bcoeff 4 : ℝ) * uHi *
        (1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ))) *
        ((1 : ℝ) / (535 : ℝ) ^ (2 : ℕ)) := by
  have hQN2 : (2 : ℕ) < BleadingCoeffs.QN := by decide
  have hA4 : (Acoeff 4 : ℚ) = 0 := by
    simp [Acoeff, BleadingCoeffs.coeffQ_phinumQ_eq_table, hQN2, varphiNumCoeffsZ_table]
  have hrel : (Ccoeff 4 : ℚ) = (-(3 : ℚ) / 2) * (Bcoeff 4) := by
    simp [Bcoeff, Ccoeff,
      BleadingCoeffs.coeffQ_phi1CoreQ_eq_table,
      BleadingCoeffs.coeffQ_phi2CoreQ_eq_table,
      hQN2, phi1CoreCoeffsZ_table, phi2CoreCoeffsZ_table]
    norm_num
  have hB4 : (Bcoeff 4 : ℝ) < 0 := by
    have : (Bcoeff 4 : ℚ) < 0 := by
      simp [Bcoeff, BleadingCoeffs.coeffQ_phi1CoreQ_eq_table, hQN2, phi1CoreCoeffsZ_table]
    exact_mod_cast this
  set u : ℝ := 1 / Real.pi
  have hu : u ≤ uHi := by simpa [u, uHi] using! inv_pi_le_uHi
  -- We bound `(t-a) * exp(-c*t)` without calculus
  -- by comparing against an exponential growth factor.
  set a : ℝ := (3 : ℝ) / (2 * Real.pi)
  set c : ℝ := 4 * Real.pi
  have ha_le_half : a ≤ (1 / 2 : ℝ) := by
    -- `3/(2π) ≤ 1/2` since `3 ≤ π`.
    dsimp [a]
    have hpi : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
    have hden_le : (2 * (3 : ℝ)) ≤ 2 * Real.pi := by nlinarith [hpi]
    have hpos : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
    have hposDen : (0 : ℝ) < 2 * (3 : ℝ) := by norm_num
    have hdiv :
        (3 : ℝ) / (2 * Real.pi) ≤ (3 : ℝ) / (2 * (3 : ℝ)) :=
      div_le_div_of_nonneg_left hpos hposDen hden_le
    simpa [show (3 : ℝ) / (2 * (3 : ℝ)) = (1 / 2 : ℝ) by norm_num] using! hdiv
  have h1a_pos : 0 < (1 - a) := by linarith [ha_le_half]
  have h1a_ne : (1 - a) ≠ 0 := ne_of_gt h1a_pos
  have hta_pos : 0 < t - a := by
    grind only
  set s : ℝ := (t - a) / (1 - a)
  have hs_pos : 0 < s := div_pos hta_pos h1a_pos
  have hs_le_exp : s ≤ Real.exp (c * (t - 1)) := by
    have hlog : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs_pos
    have hs1 : s - 1 = (t - 1) / (1 - a) := by
      dsimp [s]
      field_simp [h1a_ne]
      ring
    have ht1 : 0 ≤ t - 1 := sub_nonneg.2 ht
    have h1a_ge_half : (1 / 2 : ℝ) ≤ 1 - a := by linarith [ha_le_half]
    have hone_div : (1 : ℝ) / (1 - a) ≤ (2 : ℝ) := by
      have h' : (1 : ℝ) / (1 - a) ≤ (1 : ℝ) / (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)) h1a_ge_half
      simpa using! h'
    have hc_ge_two : (2 : ℝ) ≤ c := by
      dsimp [c]
      nlinarith [Real.pi_gt_three]
    have hdiv_le : (t - 1) / (1 - a) ≤ c * (t - 1) := by
      calc
        (t - 1) / (1 - a) = (t - 1) * ((1 : ℝ) / (1 - a)) := by simp [div_eq_mul_inv]
        _ ≤ (t - 1) * 2 :=
          mul_le_mul_of_nonneg_left hone_div ht1
        _ ≤ (t - 1) * c :=
          mul_le_mul_of_nonneg_left hc_ge_two ht1
        _ = c * (t - 1) := by ring
    have hlog_le : Real.log s ≤ c * (t - 1) := by
      have : s - 1 ≤ c * (t - 1) := by simpa [hs1] using! hdiv_le
      exact le_trans hlog this
    have hexp := Real.exp_le_exp.2 hlog_le
    simpa [Real.exp_log hs_pos] using! hexp
  have hfactor :
      (t - a) * Real.exp (-c * t) ≤ (1 - a) * Real.exp (-c) := by
    have hs_def : t - a = (1 - a) * s := by
      dsimp [s]
      field_simp [h1a_ne]
    have hexp0 : 0 ≤ Real.exp (-c * t) := (Real.exp_pos _).le
    have hs_mul :
        (1 - a) * s * Real.exp (-c * t) ≤ (1 - a) * Real.exp (c * (t - 1)) * Real.exp (-c * t) := by
      have h1a0 : 0 ≤ (1 - a) := h1a_pos.le
      have := mul_le_mul_of_nonneg_left hs_le_exp h1a0
      exact MulPosMono.mul_le_mul_of_nonneg_right hexp0 this
    have hexp_simpl : Real.exp (c * (t - 1)) * Real.exp (-c * t) = Real.exp (-c) := by
      have hadd : c * (t - 1) + (-(c * t)) = (-c) := by ring
      calc
        Real.exp (c * (t - 1)) * Real.exp (-c * t) =
            Real.exp (c * (t - 1) + (-c * t)) := (Real.exp_add _ _).symm
        _ = Real.exp (-c) := by simp [hadd]
    have hs_mul' : (1 - a) * s * Real.exp (-c * t) ≤ (1 - a) * Real.exp (-c) := by
      have hstep :
          (1 - a) * Real.exp (c * (t - 1)) * Real.exp (-c * t) = (1 - a) * Real.exp (-c) := by
        -- Avoid cancelling the common factor `(1 - a)` in simp.
        calc
          (1 - a) * Real.exp (c * (t - 1)) * Real.exp (-c * t) =
              (1 - a) * (Real.exp (c * (t - 1)) * Real.exp (-c * t)) := by
                simp [mul_assoc]
          _ = (1 - a) * Real.exp (-c) := by
                -- Avoid `simp` cancelling the common factor `(1 - a)`.
                simpa [mul_assoc] using! congrArg (fun z : ℝ => (1 - a) * z) hexp_simpl
      exact le_trans hs_mul (le_of_eq hstep)
    simpa [hs_def, mul_assoc, mul_left_comm, mul_comm] using! hs_mul'
  -- Factor the `i=4` term and apply the `h` bound.
  have hcoeff :
      exactCoeff t 4 = (Bcoeff 4 : ℝ) * u * (t - a) := by
    have hA4R : (Acoeff 4 : ℝ) = 0 := by exact_mod_cast hA4
    have hC4R : (Ccoeff 4 : ℝ) = (-(3 : ℝ) / 2) * (Bcoeff 4 : ℝ) := by exact_mod_cast hrel
    simp [exactCoeff, hA4R, hC4R, u, a, pow_two, one_div]
    ring
  have hr4 : (AppendixA.r t) ^ (4 : ℕ) = Real.exp (-c * t) := by
    -- `(exp(-πt))^4 = exp(-4πt)`.
    dsimp [AppendixA.r, c]
    have h := (Real.exp_nat_mul (-Real.pi * t) 4).symm
    have hadd : (4 : ℝ) * (-Real.pi * t) = -(4 * Real.pi * t) := by ring
    -- `- (4 * π * t) = (-4 * π) * t` is definitional after `ring`.
    simpa [hadd, mul_assoc] using! h
  have hmain :
      exactCoeff t 4 * (AppendixA.r t) ^ (4 : ℕ) ≥
        (Bcoeff 4 : ℝ) * u * ((1 - a) * Real.exp (-c)) := by
    have hu0 : 0 ≤ u := by positivity [Real.pi_pos.le]
    have hBu0 : (Bcoeff 4 : ℝ) * u ≤ 0 := by
      have : u * (Bcoeff 4 : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0 hB4.le
      simpa [mul_comm, mul_left_comm, mul_assoc] using! this
    have hmul := mul_le_mul_of_nonpos_left hfactor hBu0
    have : (Bcoeff 4 : ℝ) * u * ((t - a) * Real.exp (-c * t)) ≥
        (Bcoeff 4 : ℝ) * u * ((1 - a) * Real.exp (-c)) := by
      simpa [ge_iff_le, mul_assoc, mul_left_comm, mul_comm] using! hmul
    simpa [hcoeff, hr4, mul_assoc, mul_left_comm, mul_comm] using! this
  -- Upper bound the positive factors at `t = 1` by rationals,
  -- then multiply by the negative coefficient.
  have hpi_le : Real.pi ≤ (AppendixA.BleadingCoeffs.piUpper10Q : ℝ) :=
    le_of_lt AppendixA.pi_lt_piUpper10Q
  have ha_bound :
      (1 - a) ≤ 1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ)) := by
    dsimp [a]
    have hpos : 0 < Real.pi := Real.pi_pos
    have hden0 : 0 < (2 * Real.pi : ℝ) := by positivity [Real.pi_pos]
    have hden1 : 0 < (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ) : ℝ) := by
      have : (0 : ℝ) < (AppendixA.BleadingCoeffs.piUpper10Q : ℝ) := by
        norm_num [AppendixA.BleadingCoeffs.piUpper10Q]
      positivity
    have hden_le :
        (2 * Real.pi : ℝ) ≤ (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ) : ℝ) := by
      nlinarith
    have hfrac :
        (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ)) ≤ (3 : ℝ) / (2 * Real.pi) :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ (3 : ℝ)) hden0 hden_le
    linarith [hfrac]
  have hexp : Real.exp (-c) ≤ (1 : ℝ) / (535 : ℝ) ^ (2 : ℕ) := by
    have : Real.exp (-c) < (1 : ℝ) / (535 : ℝ) ^ (2 : ℕ) := by
      simpa [c] using! exp_neg_four_pi_lt_one_div_535_sq
    exact le_of_lt this
  have hbound :
      u * ((1 - a) * Real.exp (-c)) ≤
        uHi * ((1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ))) *
          ((1 : ℝ) / (535 : ℝ) ^ (2 : ℕ))) := by
    have hu' : u ≤ uHi := hu
    have hb0 : 0 ≤ (1 - a) := by
      exact Std.le_of_lt h1a_pos
    have hb1 : 0 ≤ (1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ))) := by
      exact Std.IsPreorder.le_trans 0 (1 - a) (1 - 3 / (2 * ↑BleadingCoeffs.piUpper10Q))
        hb0 ha_bound
    have hexp0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
    have hfac0 : 0 ≤ (1 - a) * Real.exp (-c) := mul_nonneg hb0 hexp0
    have huHi0 : 0 ≤ uHi := by
      have : (0 : ℚ) ≤ uHiQ := by
        dsimp [uHiQ, AppendixA.BleadingCoeffs.invPiUpper10Q, AppendixA.BleadingCoeffs.piLower10Q]
        norm_num
      have : (0 : ℝ) ≤ (uHiQ : ℝ) := by exact_mod_cast this
      simpa [uHi] using! this
    have hprod :
        (1 - a) * Real.exp (-c) ≤
          (1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ))) *
            ((1 : ℝ) / (535 : ℝ) ^ (2 : ℕ)) := by
      exact mul_le_mul ha_bound hexp hexp0 hb1
    have h1 := mul_le_mul hu' hprod hfac0 huHi0
    simpa [mul_assoc, mul_left_comm, mul_comm] using! h1
  have hmul :
      (Bcoeff 4 : ℝ) * uHi *
          ((1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ))) *
            ((1 : ℝ) / (535 : ℝ) ^ (2 : ℕ)))
        ≤ (Bcoeff 4 : ℝ) * u * ((1 - a) * Real.exp (-c)) :=
    by
      -- Multiply the `≤`-bound by the negative coefficient `Bcoeff 4`.
      simpa [mul_assoc, mul_left_comm, mul_comm] using! (mul_le_mul_of_nonpos_left hbound hB4.le)
  linarith


end SpherePacking.Dim24.VarphiNeg.LeOne.Trunc
