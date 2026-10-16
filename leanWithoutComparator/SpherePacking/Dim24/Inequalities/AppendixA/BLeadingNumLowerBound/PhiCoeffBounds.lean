/- Coefficient bounds for `phi` numerator pieces. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.CoeffBoundConstants
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PhiDeltaQSeries.Basic
import Mathlib.Analysis.Real.Pi.Bounds


/-!
### Coefficient bounds needed for the final truncation estimate

We package coarse polynomial bounds for the coefficient functions
`coeffPhi2Core` and `coeffPhi1Core` in the form
`|(a n : ℝ)| ≤ C * (n+1)^20`.

These bounds match the `Cphi*` constants introduced in `Part05`.

## Main statements
* `abs_coeffPhi1Core_le_Cvarphi`
* `abs_coeffPhi2Core_le_Cvarphi`
-/

noncomputable section

namespace SpherePacking.Dim24.AppendixA

private lemma Cphi2Core_nonneg : (0 : ℝ) ≤ Cphi2Core := by
  norm_num [Cphi2Core]

private lemma mul24_Cphi2Core_nonneg : (0 : ℝ) ≤ (24 : ℝ) * Cphi2Core :=
  by positivity [Cphi2Core_nonneg]


private lemma one_le_pi : (1 : ℝ) ≤ Real.pi :=
  (lt_trans (by norm_num) Real.pi_gt_d2).le

private lemma inv_pi_le_one : (1 / Real.pi : ℝ) ≤ 1 := by
  simpa using! (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (1 : ℝ)) one_le_pi)

private lemma pi_le_four : Real.pi ≤ 4 := (Real.pi_lt_four).le

private lemma abs_coeffPhi2Core_le_Cphi2Core_pow14 (n : ℕ) :
    |(coeffPhi2Core n : ℝ)| ≤ Cphi2Core * (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) := by
  simpa [coeffPhi2Core, Cphi2Core_eq] using! (abs_lincomb_E4Cube_E6Sq_le (n := n))

private lemma abs_coeffPhi2Core_le_Cphi2Core (n : ℕ) :
    |(coeffPhi2Core n : ℝ)| ≤ Cphi2Core * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  exact (abs_coeffPhi2Core_le_Cphi2Core_pow14 (n := n)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by decide : (14 : ℕ) ≤ 20))
      Cphi2Core_nonneg)

private lemma abs_conv_coeffE2_coeffPhi2Core_le (n : ℕ) :
    |(conv coeffE2 coeffPhi2Core n : ℝ)| ≤
      ((24 : ℝ) * Cphi2Core) * (((n + 1 : ℕ) : ℝ) ^ (17 : ℕ)) := by
  simpa [mul_assoc, add_assoc, add_left_comm, add_comm] using!
    (abs_conv_le (a := coeffE2) (b := coeffPhi2Core) (Ca := (24 : ℝ)) (Cb := Cphi2Core)
      (ka := 2) (kb := 14) abs_coeffE2_le
      (fun m => abs_coeffPhi2Core_le_Cphi2Core_pow14 (n := m)) n)

private lemma abs_coeffPhi1Core_le_Cphi1Core (n : ℕ) :
    |(coeffPhi1Core n : ℝ)| ≤ Cphi1Core * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hpow16 :
      (((n + 1 : ℕ) : ℝ) ^ (16 : ℕ)) ≤ (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
    pow_le_pow_right₀ hn1 (by decide : (16 : ℕ) ≤ 20)
  have hpow17 :
      (((n + 1 : ℕ) : ℝ) ^ (17 : ℕ)) ≤ (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
    pow_le_pow_right₀ hn1 (by decide : (17 : ℕ) ≤ 20)
  have hE6E4Sq :
      |(conv coeffE6 coeffE4Sq n : ℝ)| ≤
        ((504 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (16 : ℕ)) := by
    simpa using! abs_conv_coeffE6_coeffE4Sq_le (n := n)
  have h1 :
      |(((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℚ) : ℝ)| ≤
        ((48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ))) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
    have hE6E4Sq' :
        |(conv coeffE6 coeffE4Sq n : ℝ)| ≤
          ((504 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
      hE6E4Sq.trans (mul_le_mul_of_nonneg_left hpow16 (by positivity))
    calc
      |(((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℚ) : ℝ)|
          = (48 : ℝ) * |(conv coeffE6 coeffE4Sq n : ℝ)| := by
              simp [Rat.cast_mul, abs_mul]
      _ ≤ (48 : ℝ) *
            (((504 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) := by
            exact mul_le_mul_of_nonneg_left hE6E4Sq' (by positivity)
      _ = ((48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ))) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by ring
  have hE2Phi2 :
      |(conv coeffE2 coeffPhi2Core n : ℝ)| ≤
        ((24 : ℝ) * Cphi2Core) * (((n + 1 : ℕ) : ℝ) ^ (17 : ℕ)) :=
    abs_conv_coeffE2_coeffPhi2Core_le (n := n)
  have h2 :
      |(((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℚ) : ℝ)| ≤
        ((2 : ℝ) * ((24 : ℝ) * Cphi2Core)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
    have hE2Phi2' :
        |(conv coeffE2 coeffPhi2Core n : ℝ)| ≤
          ((24 : ℝ) * Cphi2Core) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
      hE2Phi2.trans (mul_le_mul_of_nonneg_left hpow17 mul24_Cphi2Core_nonneg)
    calc
      |(((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℚ) : ℝ)|
          = (2 : ℝ) * |(conv coeffE2 coeffPhi2Core n : ℝ)| := by
              simp [Rat.cast_mul, Rat.cast_ofNat, abs_mul]
      _ ≤ (2 : ℝ) * (((24 : ℝ) * Cphi2Core) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) := by
            exact mul_le_mul_of_nonneg_left hE2Phi2' (by positivity)
      _ = ((2 : ℝ) * ((24 : ℝ) * Cphi2Core)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by ring
  have htri :
      |(coeffPhi1Core n : ℝ)| ≤
          |(((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℚ) : ℝ)| +
            |(((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℚ) : ℝ)| := by
    simpa
        [coeffPhi1Core, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, add_assoc, add_left_comm,
          add_comm, mul_assoc]
      using!
      (abs_add_le
        (((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℚ) : ℝ)
        (((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℚ) : ℝ))
  have hlin :
      |(((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℚ) : ℝ)| +
            |(((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℚ) : ℝ)| ≤
          (((48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ))) + (2 : ℝ) * ((24 : ℝ) * Cphi2Core)) *
            (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
    have hadd := add_le_add h1 h2
    have hfactor :
        ((48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ))) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) +
              ((2 : ℝ) * ((24 : ℝ) * Cphi2Core)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) =
            (((48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ))) + (2 : ℝ) * ((24 : ℝ) * Cphi2Core)) *
              (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
      ring
    exact le_trans hadd (le_of_eq hfactor)
  have hconst :
      (((48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ))) + (2 : ℝ) * ((24 : ℝ) * Cphi2Core)) =
        Cphi1Core := by
    simp [Cphi1Core_eq]
  exact (htri.trans hlin).trans (by simp [hconst])

/-- Coarse bound for `coeffPhi1Core`, packaged with the common constant `Cvarphi`. -/
public lemma abs_coeffPhi1Core_le_Cvarphi (n : ℕ) :
    |(coeffPhi1Core n : ℝ)| ≤ Cvarphi * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
  (abs_coeffPhi1Core_le_Cphi1Core (n := n)).trans
    (mul_le_mul_of_nonneg_right Cphi1Core_le_Cvarphi (by positivity))

/-- Coarse bound for `coeffPhi2Core`, packaged with the common constant `Cvarphi`. -/
public lemma abs_coeffPhi2Core_le_Cvarphi (n : ℕ) :
    |(coeffPhi2Core n : ℝ)| ≤ Cvarphi * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
  (abs_coeffPhi2Core_le_Cphi2Core (n := n)).trans
    (mul_le_mul_of_nonneg_right Cphi2Core_le_Cvarphi (by positivity))

end SpherePacking.Dim24.AppendixA
