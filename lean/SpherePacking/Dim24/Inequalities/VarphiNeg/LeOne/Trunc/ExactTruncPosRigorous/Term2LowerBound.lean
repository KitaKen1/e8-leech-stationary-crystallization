-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Trunc.ExactTruncPosRigorous.Prelude
public import
 SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.ExactTruncTail.ExactTruncation


/-!
# Term 2 lower bound

Lower bound for the `i = 2` term in the exact truncation head `exactTrunc t`
used in the `t ≤ 1` reduction of Appendix A.

## Main statements
* `term2_lower_bound`
-/


noncomputable section

namespace SpherePacking.Dim24.VarphiNeg.LeOne.Trunc

open AppendixA
open AppendixA.VarphiLeOne

/-- Lower bound for the contribution of the `i = 2` coefficient to `exactTrunc t` for `t ≥ 1`. -/
public lemma term2_lower_bound (t : ℝ) (ht : 1 ≤ t) :
    exactCoeff t 2 * (AppendixA.r t) ^ (2 : ℕ) ≥
      (Bcoeff 2 : ℝ) * (uHiSq / 2) * ((1 : ℝ) / 1000) := by
  have hQN1 : (1 : ℕ) < BleadingCoeffs.QN := by
    -- `QN = 50`
    decide
  have hA2 : (Acoeff 2 : ℚ) = 0 := by
    -- Concrete coefficient identity (table lookup).
    simp [Acoeff, BleadingCoeffs.coeffQ_phinumQ_eq_table, hQN1, varphiNumCoeffsZ_table]
  have hrel : (Ccoeff 2 : ℚ) = (-3 : ℚ) * (Bcoeff 2) := by
    -- Concrete coefficient identity (table lookup).
    simp [Bcoeff, Ccoeff,
      BleadingCoeffs.coeffQ_phi1CoreQ_eq_table,
      BleadingCoeffs.coeffQ_phi2CoreQ_eq_table,
      hQN1, phi1CoreCoeffsZ_table, phi2CoreCoeffsZ_table]
    norm_num
  have hB2 : (Bcoeff 2 : ℝ) < 0 := by
    have : (Bcoeff 2 : ℚ) < 0 := by
      simp [Bcoeff, BleadingCoeffs.coeffQ_phi1CoreQ_eq_table, hQN1, phi1CoreCoeffsZ_table]
    exact_mod_cast this
  set u : ℝ := 1 / Real.pi
  have hu : u ≤ uHi := by simpa [u, uHi] using! inv_pi_le_uHi
  have hu2 : u ^ (2 : ℕ) ≤ uHiSq := by
    have hu0 : 0 ≤ u := by positivity [Real.pi_pos.le]
    have := pow_le_pow_left₀ hu0 hu 2
    simpa [uHiSq, uHiSqQ, uHiQ, uHi, u, pow_two] using! this
  have h7 : Real.exp (-7 : ℝ) ≤ (1 : ℝ) / 1000 := le_of_lt exp_neg_seven_lt_one_div_1000
  -- Bound `(t - 3/π) * exp(-2πt)` by `exp(-7)/(2π)` using `y*exp(-y) ≤ exp(-1)`.
  set y : ℝ := 2 * Real.pi * t - 6
  have hy : 0 < y := by
    have h2pi : (6 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have : (6 : ℝ) < 2 * Real.pi * t := by
      have hmul : (2 * Real.pi : ℝ) ≤ 2 * Real.pi * t := by
        have hpos : 0 ≤ (2 * Real.pi : ℝ) := by positivity [Real.pi_pos.le]
        have := mul_le_mul_of_nonneg_left ht hpos
        simpa [mul_assoc] using! this
      exact lt_of_lt_of_le h2pi hmul
    linarith [this]
  have hyBound : y * Real.exp (-y) ≤ Real.exp (-1 : ℝ) :=
    mul_exp_neg_le_exp_neg_one y
  have hterm :
      (t - 3 / Real.pi) * Real.exp (-2 * Real.pi * t) ≤
        (1 / (2 * Real.pi)) * Real.exp (-7 : ℝ) := by
    have hsplit : Real.exp (-2 * Real.pi * t) = Real.exp (-6 : ℝ) * Real.exp (-y) := by
      have harg : (-(2 * Real.pi * t) : ℝ) = (-6 : ℝ) + (-y) := by
        dsimp [y]
        ring
      calc
        Real.exp (-2 * Real.pi * t) = Real.exp (-(2 * Real.pi * t)) := by simp
        _ = Real.exp ((-6 : ℝ) + (-y)) := by simp [harg]
        _ = Real.exp (-6 : ℝ) * Real.exp (-y) := by
              simpa using! (Real.exp_add (-6 : ℝ) (-y))
    have hrep : t - 3 / Real.pi = (1 / (2 * Real.pi)) * y := by
      dsimp [y]
      field_simp [Real.pi_ne_zero]
      ring
    have hEq :
        (t - 3 / Real.pi) * Real.exp (-2 * Real.pi * t) =
          (1 / (2 * Real.pi)) * Real.exp (-6 : ℝ) * (y * Real.exp (-y)) := by
      -- Just rewrite the two factors and rearrange.
      rw [hrep, hsplit]
      ring_nf
    have h0 : 0 ≤ (1 / (2 * Real.pi) : ℝ) * Real.exp (-6 : ℝ) := by positivity [Real.pi_pos.le]
    have hMul :
        (1 / (2 * Real.pi)) * Real.exp (-6 : ℝ) * (y * Real.exp (-y)) ≤
          (1 / (2 * Real.pi)) * Real.exp (-6 : ℝ) * Real.exp (-1 : ℝ) := by
      -- Multiply `hyBound` by the nonnegative constant `(1/(2π))*exp(-6)`.
      simpa [mul_assoc, mul_left_comm, mul_comm] using! (mul_le_mul_of_nonneg_left hyBound h0)
    have hExp : Real.exp (-6 : ℝ) * Real.exp (-1 : ℝ) = Real.exp (-7 : ℝ) := by
      simpa [show (-6 : ℝ) + (-1 : ℝ) = (-7 : ℝ) by ring] using!
        (Real.exp_add (-6 : ℝ) (-1 : ℝ)).symm
    calc
      (t - 3 / Real.pi) * Real.exp (-2 * Real.pi * t)
          = (1 / (2 * Real.pi)) * Real.exp (-6 : ℝ) * (y * Real.exp (-y)) := hEq
      _ ≤ (1 / (2 * Real.pi)) * Real.exp (-6 : ℝ) * Real.exp (-1 : ℝ) := hMul
      _ = (1 / (2 * Real.pi)) * Real.exp (-7 : ℝ) := by
        -- Combine the exponentials without commuting factors.
        calc
          (1 / (2 * Real.pi)) * Real.exp (-6 : ℝ) * Real.exp (-1 : ℝ) =
              (1 / (2 * Real.pi)) * (Real.exp (-6 : ℝ) * Real.exp (-1 : ℝ)) := by
                simp [mul_assoc]
          _ = (1 / (2 * Real.pi)) * Real.exp (-7 : ℝ) := by
                simp [hExp, mul_assoc]
  -- Factor `exactCoeff t 2 = (B2/pi) * (t - 3/pi)` and apply `hterm`.
  have hcoeff :
      exactCoeff t 2 = (Bcoeff 2 : ℝ) * u * (t - 3 / Real.pi) := by
    have hA2R : (Acoeff 2 : ℝ) = 0 := by exact_mod_cast hA2
    have hC2R : (Ccoeff 2 : ℝ) = (-3 : ℝ) * (Bcoeff 2 : ℝ) := by exact_mod_cast hrel
    simp [exactCoeff, hA2R, hC2R, u, pow_two, one_div]
    ring
  have hr2 : (AppendixA.r t) ^ (2 : ℕ) = Real.exp (-2 * Real.pi * t) := by
    dsimp [AppendixA.r]
    calc
      (Real.exp (-Real.pi * t)) ^ (2 : ℕ) = Real.exp (-Real.pi * t) * Real.exp (-Real.pi * t) := by
        simp [pow_two]
      _ = Real.exp ((-Real.pi * t) + (-Real.pi * t)) := by
            simpa using! (Real.exp_add (-Real.pi * t) (-Real.pi * t)).symm
      _ = Real.exp (-2 * Real.pi * t) := by
        congr 1
        ring
  have hmain :
      exactCoeff t 2 * (AppendixA.r t) ^ (2 : ℕ) ≥
        (Bcoeff 2 : ℝ) * (u * (1 / (2 * Real.pi)) * Real.exp (-7 : ℝ)) := by
    have hu0 : 0 ≤ u := by positivity [Real.pi_pos.le]
    have hBu0 : (Bcoeff 2 : ℝ) * u ≤ 0 := by
      have : u * (Bcoeff 2 : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0 hB2.le
      simpa [mul_comm, mul_left_comm, mul_assoc] using! this
    have hmul := mul_le_mul_of_nonpos_left hterm hBu0
    -- rewrite `≥`
    have : (Bcoeff 2 : ℝ) * u * ((t - 3 / Real.pi) * Real.exp (-2 * Real.pi * t)) ≥
        (Bcoeff 2 : ℝ) * u * ((1 / (2 * Real.pi)) * Real.exp (-7 : ℝ)) := by
      simpa [ge_iff_le, mul_assoc, mul_left_comm, mul_comm] using! hmul
    simpa [hcoeff, hr2, mul_assoc, mul_left_comm, mul_comm] using! this
  -- Replace `u*(1/(2π)) = 1/(2π^2)` by `uHiSq/2`, and `exp(-7)` by `1/1000` (since `B2 < 0`).
  have hpiSq :
      u * (1 / (2 * Real.pi)) * Real.exp (-7 : ℝ) ≤ (uHiSq / 2) * ((1 : ℝ) / 1000) := by
    have hmul1 :
        u * (1 / (2 * Real.pi)) ≤ (u ^ (2 : ℕ)) / 2 := by
      -- `u*(1/(2π)) = u^2/2` since `u = 1/π`.
      simp [u, pow_two, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    have hmul2 : (u ^ (2 : ℕ)) / 2 ≤ uHiSq / 2 := by
      have := mul_le_mul_of_nonneg_right hu2 (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ))
      simpa [div_eq_mul_inv, mul_assoc] using! this
    have hleft : u * (1 / (2 * Real.pi)) ≤ uHiSq / 2 := le_trans hmul1 hmul2
    have hExp0 : 0 ≤ Real.exp (-7 : ℝ) := (Real.exp_pos _).le
    have hUhi0 : 0 ≤ uHiSq / 2 := by
      -- `uHiSq` is a square of a nonnegative rational.
      have : (0 : ℚ) ≤ uHiSqQ := by
        -- square is nonnegative
        simpa [uHiSqQ] using! (sq_nonneg uHiQ)
      have : (0 : ℝ) ≤ (uHiSqQ : ℝ) := by exact_mod_cast this
      have : (0 : ℝ) ≤ uHiSq := by simpa [uHiSq] using! this
      nlinarith
    have hmul := mul_le_mul hleft h7 hExp0 hUhi0
    simpa [mul_assoc] using! hmul
  have hmul := mul_le_mul_of_nonpos_left hpiSq hB2.le
  grind only


end SpherePacking.Dim24.VarphiNeg.LeOne.Trunc
