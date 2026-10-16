-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.Defs
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PiBoundsAndTruncCompare
import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.TailConstants

/-!
# Per-term bounds for `ineq2_num_tail`

This file bounds the norm of each of the four series tails in `ineq2_num_tail` by
`eps / 4 * r(t)^12` for `t ≥ 1`: the three `qtail` terms coming from `varphi_num`, `phi1_num`,
`phi2_num`, and the `rtail` term coming from `psiI_num`.

## Main statements
* `varphi_term_norm_le`
* `phi1_term_norm_le`
* `phi2_term_norm_le`
* `psi_term_norm_le`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open ExactTrunc
open BleadingCoeffs

namespace NumTailBound

/-- Bound the `varphi` tail contribution in `ineq2_num_tail` by `eps / 4 * r(t)^12`. -/
public lemma varphi_term_norm_le (t : ℝ) (ht : 1 ≤ t) (ht0 : 0 < t) :
    ‖((t : ℂ) ^ (2 : ℕ)) *
          AppendixA.qtail (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) (it t ht0) QN‖
      ≤ (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) := by
  have ht0' : 0 ≤ t := ht0.le
  have hqvar :
      ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) (it t ht0) QN‖ ≤
        (AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (AppendixA.r t) ^ (100 : ℕ) := by
    simpa [QN, mul_assoc, mul_left_comm, mul_comm] using!
      (AppendixA.qtail_varphi_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) (ht := ht))
  have htSqPow :
      t ^ (2 : ℕ) * (AppendixA.r t) ^ (100 : ℕ) ≤
        ((1 : ℝ) / 23) ^ (88 : ℕ) * (AppendixA.r t) ^ (12 : ℕ) :=
    AppendixA.t_sq_mul_rpow100_le (t := t) ht
  have hnorm_t2 : ‖((t : ℂ) ^ (2 : ℕ))‖ = t ^ (2 : ℕ) := by
    simp [Real.norm_eq_abs, abs_of_nonneg ht0']
  have hstep1 :
      ‖((t : ℂ) ^ (2 : ℕ)) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) (it t ht0) QN‖ ≤
        t ^ (2 : ℕ) *
          ((AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
            (AppendixA.r t) ^ (100 : ℕ)) := by
    have ht2_nonneg : 0 ≤ t ^ (2 : ℕ) := pow_nonneg ht0' 2
    calc
      ‖((t : ℂ) ^ (2 : ℕ)) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) (it t ht0) QN‖
          = ‖((t : ℂ) ^ (2 : ℕ))‖ *
              ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) (it t ht0) QN‖ := by
              simp
      _ = t ^ (2 : ℕ) *
              ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) (it t ht0) QN‖ := by
            simp [hnorm_t2]
      _ ≤ (t ^ (2 : ℕ)) *
            ((AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
              (AppendixA.r t) ^ (100 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hqvar ht2_nonneg
  have hK0 :
      0 ≤ (AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) := by
    have : 0 ≤ (AppendixA.Cvarphi : ℝ) := Cvarphi_nonneg
    positivity
  have hscale :
      (t ^ (2 : ℕ)) *
          ((AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
            (AppendixA.r t) ^ (100 : ℕ)) ≤
        ((AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
              ((1 : ℝ) / 23) ^ (88 : ℕ)) *
          (AppendixA.r t) ^ (12 : ℕ) := by
    have hmain := mul_le_mul_of_nonneg_left htSqPow hK0
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hmain
  have hr12_nonneg : 0 ≤ (AppendixA.r t) ^ (12 : ℕ) := by positivity
  have hconst_mul :
      ((AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)) *
            (AppendixA.r t) ^ (12 : ℕ) ≤
          (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) :=
    mul_le_mul_of_nonneg_right const_varphi_le_eps_div_4 hr12_nonneg
  exact le_trans (le_trans hstep1 hscale) hconst_mul

/-- Bound the `phi1` tail contribution in `ineq2_num_tail` by `eps / 4 * r(t)^12`. -/
public lemma phi1_term_norm_le (t : ℝ) (ht : 1 ≤ t) (ht0 : 0 < t) :
    ‖(t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
          AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖
      ≤ (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) := by
  have ht0' : 0 ≤ t := ht0.le
  have hinvPiUpper : (1 / Real.pi) ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) :=
    AppendixA.inv_pi_le_invPiUpper10Q
  have hqphi1 :
      ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖ ≤
        (AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (AppendixA.r t) ^ (100 : ℕ) := by
    simpa [QN, mul_assoc, mul_left_comm, mul_comm] using!
      (AppendixA.qtail_phi1_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) (ht := ht))
  have htPow :
      t * (AppendixA.r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (AppendixA.r t) ^ (12 : ℕ) :=
    AppendixA.t_mul_rpow100_le (t := t) ht
  have hn_t : ‖(t : ℂ)‖ = t := by
    simp [Real.norm_eq_abs, abs_of_nonneg ht0']
  have hn_pi : ‖(1 / (Real.pi : ℂ))‖ = (1 / Real.pi : ℝ) := by
    calc
      ‖(1 / (Real.pi : ℂ))‖ = ‖(Real.pi : ℂ)‖⁻¹ := by simp [one_div]
      _ = (Real.pi : ℝ)⁻¹ := by
            have hpi0 : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
            simp [Real.norm_eq_abs, abs_of_nonneg hpi0]
      _ = (1 / Real.pi : ℝ) := by simp [one_div]
  have hn_6 : ‖(-6 : ℂ)‖ = (6 : ℝ) := by norm_num
  have hnorm_pi6 : ‖(1 / (Real.pi : ℂ)) * (-6 : ℂ)‖ = (1 / Real.pi : ℝ) * 6 := by
    calc
      ‖(1 / (Real.pi : ℂ)) * (-6 : ℂ)‖ = ‖(1 / (Real.pi : ℂ))‖ * ‖(-6 : ℂ)‖ := by
        simp
      _ = (1 / Real.pi : ℝ) * 6 := by
        rw [hn_pi, hn_6]
  have hstep0 :
      ‖(t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖ =
        (t * (1 / Real.pi) * 6) *
          ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖ := by
    calc
      ‖(t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖
          = ‖(t : ℂ)‖ * ‖(1 / (Real.pi : ℂ)) * (-6 : ℂ)‖ *
              ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖ := by
              simp [mul_assoc]
      _ = t * ((1 / Real.pi : ℝ) * 6) *
              ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖ := by
              rw [hn_t, hnorm_pi6]
      _ = (t * (1 / Real.pi) * 6) *
              ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖ := by
              simp [mul_assoc]
  have hle_pi : t * (1 / Real.pi) * 6 ≤ t * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * 6 := by
    have := mul_le_mul_of_nonneg_left hinvPiUpper ht0'
    have := mul_le_mul_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 6)
    simpa [mul_assoc, mul_left_comm, mul_comm] using! this
  have hstep1 :
      (t * (1 / Real.pi) * 6) *
          ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖ ≤
        (t * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * 6) *
          ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖ :=
    mul_le_mul_of_nonneg_right hle_pi (norm_nonneg _)
  have hstep2 :
      (t * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * 6) *
          ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖ ≤
        (t * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * 6) *
          ((AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
            (AppendixA.r t) ^ (100 : ℕ)) := by
    have hmul0 : 0 ≤ t * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * 6 := by
      have : 0 ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) := invPiUpper10Q_nonneg
      positivity
    exact mul_le_mul_of_nonneg_left hqphi1 hmul0
  have hK0 :
      0 ≤
        (6 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * (AppendixA.Cvarphi : ℝ) * (2 : ℝ) *
          (51 : ℝ) ^ (20 : ℕ) := by
    have : 0 ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) := invPiUpper10Q_nonneg
    have : 0 ≤ (AppendixA.Cvarphi : ℝ) := Cvarphi_nonneg
    positivity
  have hscale :
      (t * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * 6) *
          ((AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
            (AppendixA.r t) ^ (100 : ℕ)) ≤
        ((6 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * (AppendixA.Cvarphi : ℝ) *
              (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)) *
          (AppendixA.r t) ^ (12 : ℕ) := by
    have hmain := mul_le_mul_of_nonneg_left htPow hK0
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hmain
  have hr12_nonneg : 0 ≤ (AppendixA.r t) ^ (12 : ℕ) := by positivity
  have hconst_mul :
      ((6 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) * (AppendixA.Cvarphi : ℝ) * (2 : ℝ) *
              (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)) *
            (AppendixA.r t) ^ (12 : ℕ) ≤
          (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) :=
    mul_le_mul_of_nonneg_right const_phi1_le_eps_div_4 hr12_nonneg
  linarith

/-- Bound the `phi2` tail contribution in `ineq2_num_tail` by `eps / 4 * r(t)^12`. -/
public lemma phi2_term_norm_le (t : ℝ) (ht : 1 ≤ t) (ht0 : 0 < t) :
    ‖((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
          AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖
      ≤ (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) := by
  have hinvPiUpper : (1 / Real.pi) ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) :=
    AppendixA.inv_pi_le_invPiUpper10Q
  have hinvPiSqUpper :
      (1 / Real.pi) ^ (2 : ℕ) ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ) := by
    have h0 : 0 ≤ (1 / Real.pi : ℝ) := (one_div_pos.2 Real.pi_pos).le
    simpa [Rat.cast_pow] using! (pow_le_pow_left₀ h0 hinvPiUpper 2)
  have hqphi2 :
      ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖ ≤
        (AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (AppendixA.r t) ^ (100 : ℕ) := by
    simpa [QN, mul_assoc, mul_left_comm, mul_comm] using!
      (AppendixA.qtail_phi2_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) (ht := ht))
  have hrPow :
      (AppendixA.r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (AppendixA.r t) ^ (12 : ℕ) :=
    AppendixA.rpow100_le_oneDiv23Pow88_rpow12 (t := t) ht
  have hn :
      ‖((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)))‖ = (36 : ℝ) * (1 / Real.pi) ^ (2 : ℕ) := by
    have hpi0 : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    have hnorm_pi : ‖(Real.pi : ℂ)‖ = (Real.pi : ℝ) := by
      simp [Real.norm_eq_abs, abs_of_nonneg hpi0]
    calc
      ‖((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)))‖ = ‖(36 : ℂ) * ((Real.pi : ℂ) ^ (2 : ℕ))⁻¹‖ := by
        simp [div_eq_mul_inv]
      _ = ‖(36 : ℂ)‖ * ‖((Real.pi : ℂ) ^ (2 : ℕ))⁻¹‖ := by simp
      _ = (36 : ℝ) * ‖((Real.pi : ℂ) ^ (2 : ℕ))‖⁻¹ := by simp [norm_inv]
      _ = (36 : ℝ) * (‖(Real.pi : ℂ)‖ ^ (2 : ℕ))⁻¹ := by simp [norm_pow]
      _ = (36 : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ := by
            rw [hnorm_pi]
      _ = (36 : ℝ) * (1 / Real.pi) ^ (2 : ℕ) := by simp [one_div]
  have hstep1 :
      ‖((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖ ≤
        ((36 : ℝ) * (1 / Real.pi) ^ (2 : ℕ)) *
          ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖ := by
    have hEq :
        ‖((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
              AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖ =
          ((36 : ℝ) * (1 / Real.pi) ^ (2 : ℕ)) *
            ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖ := by
      calc
        ‖((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
              AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖
            = ‖((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)))‖ *
                ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖ := by
                simp
        _ = ((36 : ℝ) * (1 / Real.pi) ^ (2 : ℕ)) *
              ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖ := by
              rw [hn]
    exact hEq.le
  have hstep_pi :
      ((36 : ℝ) * (1 / Real.pi) ^ (2 : ℕ)) *
            ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖ ≤
          ((36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ)) *
            ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖ := by
    have h36 : 0 ≤ (36 : ℝ) := by norm_num
    have hpiSq :
        (36 : ℝ) * (1 / Real.pi) ^ (2 : ℕ) ≤
          (36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hinvPiSqUpper h36
    exact mul_le_mul_of_nonneg_right hpiSq (norm_nonneg _)
  have hstep_qtail :
      ((36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ)) *
            ‖AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖ ≤
          ((36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ)) *
            ((AppendixA.Cvarphi : ℝ) * (2 : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
              (AppendixA.r t) ^ (100 : ℕ)) := by
    have hmul0 : 0 ≤ (36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ) := by
      have : 0 ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) := invPiUpper10Q_nonneg
      positivity
    exact mul_le_mul_of_nonneg_left hqphi2 hmul0
  have hK0 :
      0 ≤
        (36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ) *
            (AppendixA.Cvarphi : ℝ) * 2 * (51 : ℝ) ^ 20 := by
    have : 0 ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) := invPiUpper10Q_nonneg
    have : 0 ≤ (AppendixA.Cvarphi : ℝ) := Cvarphi_nonneg
    positivity
  have hscale :
      ((36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ)) *
          ((AppendixA.Cvarphi : ℝ) * 2 * (51 : ℝ) ^ 20 * (AppendixA.r t) ^ (100 : ℕ)) ≤
        ((36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ) * (AppendixA.Cvarphi : ℝ) * 2 *
              (51 : ℝ) ^ 20 * ((1 : ℝ) / 23) ^ 88) *
          (AppendixA.r t) ^ 12 := by
    have hmain := mul_le_mul_of_nonneg_left hrPow hK0
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hmain
  have hr12_nonneg : 0 ≤ (AppendixA.r t) ^ 12 := by positivity
  have hconst_mul :
      ((36 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ) * (AppendixA.Cvarphi : ℝ) * 2 *
              (51 : ℝ) ^ 20 * ((1 : ℝ) / 23) ^ 88) *
            (AppendixA.r t) ^ 12 ≤
          (AppendixA.eps / 4) * (AppendixA.r t) ^ 12 :=
    mul_le_mul_of_nonneg_right const_phi2_le_eps_div_4 hr12_nonneg
  linarith

/-- Bound the `psi` tail contribution in `ineq2_num_tail` by `eps / 4 * r(t)^12`. -/
public lemma psi_term_norm_le (t : ℝ) (ht : 1 ≤ t) (ht0 : 0 < t) :
    ‖(432 / (Real.pi ^ 2) : ℂ) * AppendixA.rtail AppendixA.psiCoeffFun t N‖
      ≤ (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) := by
  have hinvPiUpper : (1 / Real.pi) ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) :=
    AppendixA.inv_pi_le_invPiUpper10Q
  have hinvPiSqUpper :
      (1 / Real.pi) ^ (2 : ℕ) ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ) := by
    have h0 : 0 ≤ (1 / Real.pi : ℝ) := (one_div_pos.2 Real.pi_pos).le
    simpa [Rat.cast_pow] using! (pow_le_pow_left₀ h0 hinvPiUpper 2)
  have hrpsi :
      ‖AppendixA.rtail AppendixA.psiCoeffFun t N‖ ≤
        ((16 : ℝ) ^ (8 : ℕ)) * (2 * ((101 : ℝ) ^ (27 : ℕ) * (AppendixA.r t) ^ (100 : ℕ))) := by
    simpa [N] using! (AppendixA.rtail_psi_le_rpow100 (t := t) (ht0 := ht0) (ht := ht))
  have hrPow :
      (AppendixA.r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (AppendixA.r t) ^ (12 : ℕ) :=
    AppendixA.rpow100_le_oneDiv23Pow88_rpow12 (t := t) ht
  have hn :
      ‖(432 / (Real.pi ^ 2) : ℂ)‖ = (432 : ℝ) * (1 / Real.pi) ^ (2 : ℕ) := by
    -- Same computation as `phi2_term_norm_le`, with `36` replaced by `432`.
    have hpi0 : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    have hnorm_pi : ‖(Real.pi : ℂ)‖ = (Real.pi : ℝ) := by
      simp [Real.norm_eq_abs, abs_of_nonneg hpi0]
    calc
      ‖(432 / (Real.pi ^ 2) : ℂ)‖ = ‖(432 : ℂ) * ((Real.pi : ℂ) ^ (2 : ℕ))⁻¹‖ := by
        simp [div_eq_mul_inv]
      _ = ‖(432 : ℂ)‖ * ‖((Real.pi : ℂ) ^ (2 : ℕ))⁻¹‖ := by simp
      _ = (432 : ℝ) * ‖((Real.pi : ℂ) ^ (2 : ℕ))‖⁻¹ := by simp [norm_inv]
      _ = (432 : ℝ) * (‖(Real.pi : ℂ)‖ ^ (2 : ℕ))⁻¹ := by simp [norm_pow]
      _ = (432 : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ := by
            rw [hnorm_pi]
      _ = (432 : ℝ) * (1 / Real.pi) ^ (2 : ℕ) := by simp [one_div]
  have hstep1 :
      ‖(432 / (Real.pi ^ 2) : ℂ) * AppendixA.rtail AppendixA.psiCoeffFun t N‖ ≤
        ((432 : ℝ) * (1 / Real.pi) ^ (2 : ℕ)) * ‖AppendixA.rtail AppendixA.psiCoeffFun t N‖ := by
    have hEq :
        ‖(432 / (Real.pi ^ 2) : ℂ) * AppendixA.rtail AppendixA.psiCoeffFun t N‖ =
          ((432 : ℝ) * (1 / Real.pi) ^ (2 : ℕ)) * ‖AppendixA.rtail AppendixA.psiCoeffFun t N‖ := by
      calc
        ‖(432 / (Real.pi ^ 2) : ℂ) * AppendixA.rtail AppendixA.psiCoeffFun t N‖
            = ‖(432 / (Real.pi ^ 2) : ℂ)‖ * ‖AppendixA.rtail AppendixA.psiCoeffFun t N‖ := by
                simp
        _ = ((432 : ℝ) * (1 / Real.pi) ^ 2) * ‖AppendixA.rtail AppendixA.psiCoeffFun t N‖ := by
              rw [hn]
    exact hEq.le
  have hstep_pi :
      ((432 : ℝ) * (1 / Real.pi) ^ (2 : ℕ)) * ‖AppendixA.rtail AppendixA.psiCoeffFun t N‖ ≤
        ((432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ)) *
          ‖AppendixA.rtail AppendixA.psiCoeffFun t N‖ := by
    have h432 : 0 ≤ (432 : ℝ) := by norm_num
    have hpiSq :
        (432 : ℝ) * (1 / Real.pi) ^ (2 : ℕ) ≤
          (432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hinvPiSqUpper h432
    exact mul_le_mul_of_nonneg_right hpiSq (norm_nonneg _)
  have hstep_tail :
      ((432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ)) *
            ‖AppendixA.rtail AppendixA.psiCoeffFun t N‖ ≤
          ((432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ)) *
            ((16 : ℝ) ^ 8 * (2 * ((101 : ℝ) ^ 27 * (AppendixA.r t) ^ 100))) := by
    have hmul0 : 0 ≤ (432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ 2 : ℝ) := by
      have : 0 ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) := invPiUpper10Q_nonneg
      positivity
    exact mul_le_mul_of_nonneg_left hrpsi hmul0
  have hK0 :
      0 ≤
        (432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) *
            (2 : ℝ) * (101 : ℝ) ^ (27 : ℕ) := by
    have : 0 ≤ (AppendixA.BleadingCoeffs.invPiUpper10Q : ℝ) := invPiUpper10Q_nonneg
    positivity
  have hscale :
      ((432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ)) *
          (((16 : ℝ) ^ (8 : ℕ)) * (2 * ((101 : ℝ) ^ (27 : ℕ) * (AppendixA.r t) ^ (100 : ℕ)))) ≤
        ((432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) *
              (2 : ℝ) * (101 : ℝ) ^ (27 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)) *
          (AppendixA.r t) ^ (12 : ℕ) := by
    have hmain := mul_le_mul_of_nonneg_left hrPow hK0
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hmain
  have hr12_nonneg : 0 ≤ (AppendixA.r t) ^ (12 : ℕ) := by positivity
  have hconst_mul :
      ((432 : ℝ) * (AppendixA.BleadingCoeffs.invPiUpper10Q ^ (2 : ℕ) : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) *
              (2 : ℝ) * (101 : ℝ) ^ (27 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)) *
            (AppendixA.r t) ^ (12 : ℕ) ≤
          (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) :=
    mul_le_mul_of_nonneg_right const_psi_le_eps_div_4 hr12_nonneg
  linarith

end SpherePacking.Dim24.Ineq2LeOneTruncAux.NumTailBound
