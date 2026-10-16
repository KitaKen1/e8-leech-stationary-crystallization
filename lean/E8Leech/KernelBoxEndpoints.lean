import E8Leech.ExpBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Rat.Cast.Order

/-! Rational bounds for a nonempty rectangle used by the first kernel-box candidate. -/

namespace E8Leech

open scoped Real

theorem exp_neg_pi_mul_bounds {lo hi : ℚ} (hlo : 0 ≤ lo) {x : ℝ}
    (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ hi) {k n : ℕ}
    (hk : (3141593 / 1000000 : ℚ) * hi ≤ 2 ^ k) (hn : 0 < n) :
    (expNegLo ((3141593 / 1000000) * hi) k n : ℝ) ≤ Real.exp (-π * x) ∧
      Real.exp (-π * x) ≤ (expNegHi ((3141592 / 1000000) * lo) k n : ℝ) := by
  have hp0 : (0 : ℝ) < 3141592 / 1000000 := by norm_num
  have hpL : (3141592 / 1000000 : ℝ) ≤ π := by
    have h := Real.pi_gt_d6
    norm_num at h
    linarith
  have hpH : π ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    norm_num at h
    linarith
  have hx0 : 0 ≤ x := le_trans (by exact_mod_cast hlo) hxlo
  have hhi0 : (0 : ℚ) ≤ hi := by exact_mod_cast le_trans hx0 hxhi
  have hLH : (3141592 / 1000000 : ℚ) * lo ≤ (3141593 / 1000000) * hi := by
    have : lo ≤ hi := by exact_mod_cast le_trans hxlo hxhi
    nlinarith
  have hL := expNeg_bounds (y := (3141592 / 1000000) * lo) (by positivity)
    (k := k) (n := n) (le_trans hLH hk) hn
  have hH := expNeg_bounds (y := (3141593 / 1000000) * hi) (by positivity)
    (k := k) (n := n) hk hn
  constructor
  · refine le_trans hH.1 (Real.exp_le_exp.mpr ?_)
    push_cast
    nlinarith
  · refine le_trans (Real.exp_le_exp.mpr ?_) hL.2
    push_cast
    nlinarith

set_option maxHeartbeats 0

theorem kernel_candidate_nome_u {u : ℝ}
    (hlo : (49999 / 10000 : ℝ) ≤ u) (hhi : u ≤ 50001 / 10000) :
    (1506 / 10000000000 : ℝ) ≤ Real.exp (-π * u) ∧
      Real.exp (-π * u) ≤ 1508 / 10000000000 := by
  have h := exp_neg_pi_mul_bounds (lo := 49999 / 10000) (hi := 50001 / 10000)
    (by norm_num) (x := u) (by norm_num at hlo ⊢; exact hlo)
    (by norm_num at hhi ⊢; exact hhi) (k := 4) (n := 10) (by norm_num) (by norm_num)
  have hL : (1506 / 10000000000 : ℚ) ≤
      expNegLo ((3141593 / 1000000) * (50001 / 10000)) 4 10 := by decide +kernel
  have hH : expNegHi ((3141592 / 1000000) * (49999 / 10000)) 4 10 ≤
      (1508 / 10000000000 : ℚ) := by decide +kernel
  have hLr := (Rat.cast_le (K := ℝ)).mpr hL
  have hHr := (Rat.cast_le (K := ℝ)).mpr hH
  push_cast at hLr hHr
  exact ⟨le_trans hLr h.1, le_trans h.2 hHr⟩

theorem kernel_candidate_nome_t {t : ℝ}
    (hlo : (39999 / 10000 : ℝ) ≤ t) (hhi : t ≤ 40001 / 10000) :
    (3486 / 1000000000 : ℝ) ≤ Real.exp (-π * t) ∧
      Real.exp (-π * t) ≤ 3489 / 1000000000 := by
  have h := exp_neg_pi_mul_bounds (lo := 39999 / 10000) (hi := 40001 / 10000)
    (by norm_num) (x := t) (by norm_num at hlo ⊢; exact hlo)
    (by norm_num at hhi ⊢; exact hhi) (k := 4) (n := 10) (by norm_num) (by norm_num)
  have hL : (3486 / 1000000000 : ℚ) ≤
      expNegLo ((3141593 / 1000000) * (40001 / 10000)) 4 10 := by decide +kernel
  have hH : expNegHi ((3141592 / 1000000) * (39999 / 10000)) 4 10 ≤
      (3489 / 1000000000 : ℚ) := by decide +kernel
  have hLr := (Rat.cast_le (K := ℝ)).mpr hL
  have hHr := (Rat.cast_le (K := ℝ)).mpr hH
  push_cast at hLr hHr
  exact ⟨le_trans hLr h.1, le_trans h.2 hHr⟩

theorem kernel_candidate_log_two : (69 / 100 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 7 / 10 := by
  have hL := (expNeg_bounds (y := 69 / 100) (by norm_num) (k := 0) (n := 8)
    (by norm_num) (by norm_num)).1
  have hH := (expNeg_bounds (y := 7 / 10) (by norm_num) (k := 0) (n := 8)
    (by norm_num) (by norm_num)).2
  have hLC : (1 / 2 : ℚ) ≤ expNegLo (69 / 100) 0 8 := by decide +kernel
  have hHC : expNegHi (7 / 10) 0 8 ≤ (1 / 2 : ℚ) := by decide +kernel
  push_cast at hL hH
  have hLCr := (Rat.cast_le (K := ℝ)).mpr hLC
  have hHCr := (Rat.cast_le (K := ℝ)).mpr hHC
  push_cast at hLCr hHCr
  have he : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hl := Real.exp_le_exp.mp (show Real.exp (-Real.log 2) ≤ Real.exp (-(69 / 100 : ℝ)) by
    rw [he]
    exact le_trans hLCr hL)
  have hh := Real.exp_le_exp.mp (show Real.exp (-(7 / 10 : ℝ)) ≤ Real.exp (-Real.log 2) by
    rw [he]
    exact le_trans hH hHCr)
  exact ⟨by linarith, by linarith⟩

end E8Leech
