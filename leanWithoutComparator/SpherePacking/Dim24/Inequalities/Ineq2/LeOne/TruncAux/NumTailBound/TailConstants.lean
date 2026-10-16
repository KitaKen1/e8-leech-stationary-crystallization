-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.Defs
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PiBoundsAndTruncCompare
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Numerical constants for the `ineq2_num_tail` bound

This file proves explicit inequalities showing that the numerical constants appearing in the tail
estimates are each bounded by `eps / 4`. These bounds are used in `TailTermBounds` to control the
four terms of `ineq2_num_tail`.

## Main statements
* `const_varphi_le_eps_div_4`
* `const_phi1_le_eps_div_4`
* `const_phi2_le_eps_div_4`
* `const_psi_le_eps_div_4`

-/

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open ExactTrunc

namespace NumTailBound

/-- Nonnegativity of the rational upper bound `invPiUpper10Q` (coerced to `ℝ`). -/
public lemma invPiUpper10Q_nonneg : (0 : ℝ) ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) := by
  have hpos : (0 : ℝ) < (1 / Real.pi) := one_div_pos.2 Real.pi_pos
  exact le_trans hpos.le AppendixA.inv_pi_le_invPiUpper10Q

/-- Nonnegativity of the constant `Cvarphi` appearing in the `qtail` bounds. -/
public lemma Cvarphi_nonneg : 0 ≤ (AppendixA.Cvarphi : ℝ) := by
  norm_num [AppendixA.Cvarphi]

/-- Numerical inequality used to bound the `varphi` tail term by `eps / 4 * r(t)^12`. -/
public lemma const_varphi_le_eps_div_4 :
    (AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
      AppendixA.eps / 4 := by
  set A : ℝ :=
    (AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)
  have hconst_varphi : (4 : ℝ) * A < AppendixA.eps := by
    have hq :
        (4 : ℚ) * (513200655360 : ℚ) * (2 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) <
          (10 : ℚ) ^ (-50 : ℤ) := by
      set_option maxRecDepth 9000 in
      norm_num
    have hR :
        ((4 : ℚ) * (513200655360 : ℚ) * (2 : ℚ) * (51 : ℚ) ^ (20 : ℕ) *
              ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) < ((10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
      exact_mod_cast hq
    simpa [A, AppendixA.Cvarphi, AppendixA.eps, mul_assoc, mul_left_comm, mul_comm] using! hR
  linarith

/-- Numerical inequality used to bound the `phi1` tail term by `eps / 4 * r(t)^12`. -/
public lemma const_phi1_le_eps_div_4 :
    (6 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * (AppendixA.Cvarphi : ℝ) * (2 : ℝ) *
          (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
      AppendixA.eps / 4 := by
  have hconst_phi1 :
      (4 : ℝ) *
          ((6 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * (AppendixA.Cvarphi : ℝ) *
            (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)) < AppendixA.eps := by
    have hq :
        (4 : ℚ) * (6 : ℚ) * AppendixA.BleadingCoeffs.invPiUpper10Q * (513200655360 : ℚ) * (2 : ℚ) *
            (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) <
          (10 : ℚ) ^ (-50 : ℤ) := by
      set_option maxRecDepth 9000 in
      norm_num [AppendixA.BleadingCoeffs.invPiUpper10Q, AppendixA.BleadingCoeffs.piLower10Q]
    have :
        ((4 : ℚ) * (6 : ℚ) * AppendixA.BleadingCoeffs.invPiUpper10Q * (513200655360 : ℚ) * (2 : ℚ) *
              (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
          ((10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
      exact_mod_cast hq
    simpa [AppendixA.Cvarphi, AppendixA.eps, mul_assoc, mul_left_comm, mul_comm] using! this
  linarith

/-- Numerical inequality used to bound the `phi2` tail term by `eps / 4 * r(t)^12`. -/
public lemma const_phi2_le_eps_div_4 :
    (36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ) * (AppendixA.Cvarphi : ℝ) *
          (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
      AppendixA.eps / 4 := by
  set A : ℝ :=
    (36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ) * (AppendixA.Cvarphi : ℝ) *
      (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)
  have hconst_phi2 : (4 : ℝ) * A < AppendixA.eps := by
    have hq :
        (4 : ℚ) * (36 : ℚ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ)) *
            (513200655360 : ℚ) * (2 : ℚ) * (51 : ℚ) ^ (20 : ℕ) *
              ((1 : ℚ) / 23) ^ (88 : ℕ) < (10 : ℚ) ^ (-50 : ℤ) := by
      set_option maxRecDepth 9000 in
      norm_num [AppendixA.BleadingCoeffs.invPiUpper10Q, AppendixA.BleadingCoeffs.piLower10Q]
    have hR :
        ((4 : ℚ) * (36 : ℚ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ)) *
              (513200655360 : ℚ) * (2 : ℚ) * (51 : ℚ) ^ (20 : ℕ) *
                ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) < ((10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
      exact_mod_cast hq
    simpa [A, AppendixA.Cvarphi, AppendixA.eps, mul_assoc, mul_left_comm, mul_comm] using! hR
  linarith

/-- Numerical inequality used to bound the `psi` tail term by `eps / 4 * r(t)^12`. -/
public lemma const_psi_le_eps_div_4 :
    (432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) *
          (2 : ℝ) * (101 : ℝ) ^ (27 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
      AppendixA.eps / 4 := by
  set A : ℝ :=
    (432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) *
      (2 : ℝ) * (101 : ℝ) ^ (27 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)
  have hconst_psi : (4 : ℝ) * A < AppendixA.eps := by
    have hq :
        (4 : ℚ) * (432 : ℚ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ)) *
            ((16 : ℚ) ^ (8 : ℕ)) * (2 : ℚ) * (101 : ℚ) ^ (27 : ℕ) *
              ((1 : ℚ) / 23) ^ (88 : ℕ) < (10 : ℚ) ^ (-50 : ℤ) := by
      set_option maxRecDepth 9000 in
      norm_num [AppendixA.BleadingCoeffs.invPiUpper10Q, AppendixA.BleadingCoeffs.piLower10Q]
    have hR :
        ((4 : ℚ) * (432 : ℚ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ)) *
              ((16 : ℚ) ^ (8 : ℕ)) * (2 : ℚ) * (101 : ℚ) ^ (27 : ℕ) *
                ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) < ((10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
      exact_mod_cast hq
    simpa [A, AppendixA.eps, mul_assoc, mul_left_comm, mul_comm] using! hR
  linarith

end SpherePacking.Dim24.Ineq2LeOneTruncAux.NumTailBound
