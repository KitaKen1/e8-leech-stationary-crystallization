/- Coefficient bounds for `Δ(it)^2`. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PhiCoeffBounds
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PhiDeltaQSeries.Identities

/-!
### Coefficient bounds for `Δ` and `Δ^2`

These are coarse but explicit bounds used to control the `Δ^2` tail when rewriting the leading
term contribution.
-/

noncomputable section

namespace SpherePacking.Dim24.AppendixA


/-- Constant `Cdelta` in the growth bound `|coeffDelta n| ≤ Cdelta * (n+1)^14`. -/
@[expose] public def Cdelta : ℝ :=
  (1 / 1728 : ℝ) * (((240 * 240 : ℝ) * (240 : ℝ)) + (504 * 504 : ℝ))

/-- Constant `CdeltaSq = Cdelta^2` in the growth bound for `coeffDeltaSq`. -/
@[expose] public def CdeltaSq : ℝ := Cdelta * Cdelta

/-- Polynomial growth bound for `coeffDelta`. -/
public lemma abs_coeffDelta_le (n : ℕ) :
    |(coeffDelta n : ℝ)| ≤ Cdelta * (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) := by
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hpow13 :
      (((n + 1 : ℕ) : ℝ) ^ (13 : ℕ)) ≤ (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) :=
    pow_le_pow_right₀ hn1 ( Nat.le_succ 13)
  have hE4 :
      |(coeffE4Cube n : ℝ)| ≤
        ((240 * 240 : ℝ) * (240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) := by
    simpa [mul_assoc] using! (abs_coeffE4Cube_le (n := n))
  have hE6 : |(coeffE6Sq n : ℝ)| ≤ (504 * 504 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) := by
    have hE6' : |(coeffE6Sq n : ℝ)| ≤ (504 * 504 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (13 : ℕ)) := by
      simpa using! (abs_coeffE6Sq_le (n := n))
    exact hE6'.trans (mul_le_mul_of_nonneg_left hpow13 (by positivity))
  have hsub :
      |((coeffE4Cube n - coeffE6Sq n : ℚ) : ℝ)| ≤
        (((240 * 240 : ℝ) * (240 : ℝ)) + (504 * 504 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) := by
    have htri :
        |(coeffE4Cube n : ℝ) - (coeffE6Sq n : ℝ)| ≤
          |(coeffE4Cube n : ℝ)| + |(coeffE6Sq n : ℝ)| := by
      simpa [sub_eq_add_neg, abs_neg] using!
        (abs_add_le (coeffE4Cube n : ℝ) (-(coeffE6Sq n : ℝ)))
    have hlin :
        |(coeffE4Cube n : ℝ)| + |(coeffE6Sq n : ℝ)| ≤
          ((240 * 240 : ℝ) * (240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) +
            (504 * 504 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) :=
      add_le_add hE4 hE6
    have hfactor :
        ((240 * 240 : ℝ) * (240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) +
            (504 * 504 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) =
          (((240 * 240 : ℝ) * (240 : ℝ)) + (504 * 504 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (14 : ℕ)) := by
      ring
    simpa [Rat.cast_sub] using! (htri.trans (hlin.trans (le_of_eq hfactor)))
  have h1728 : 0 ≤ (1 / 1728 : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsub h1728
  -- Unfold `coeffDelta` and rewrite the constant as `Cdelta`.
  simpa
      [coeffDelta, Cdelta, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat, abs_mul, mul_assoc,
        add_assoc, add_left_comm, add_comm]
    using! hmul

/-- Polynomial growth bound for `coeffDeltaSq = conv coeffDelta coeffDelta`. -/
public lemma abs_coeffDeltaSq_le (n : ℕ) :
    |(coeffDeltaSq n : ℝ)| ≤ CdeltaSq * (((n + 1 : ℕ) : ℝ) ^ (29 : ℕ)) := by
  simpa [coeffDeltaSq, CdeltaSq, mul_assoc, add_assoc, add_left_comm, add_comm] using!
    (abs_conv_le
      (a := coeffDelta) (b := coeffDelta) (Ca := Cdelta) (Cb := Cdelta) (ka := 14) (kb := 14)
      (fun m => abs_coeffDelta_le (n := m)) (fun m => abs_coeffDelta_le (n := m)) n)

/-- Convenience bound for the shifted coefficients `coeffDeltaSq (n+1)`. -/
public lemma abs_coeffDeltaSq_shift_le (n : ℕ) :
    |(coeffDeltaSq (n + 1) : ℝ)| ≤
      (CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * (((n + 1 : ℕ) : ℝ) ^ (29 : ℕ)) := by
  have h' : |(coeffDeltaSq (n + 1) : ℝ)| ≤ CdeltaSq * (((n + 1 + 1 : ℕ) : ℝ) ^ (29 : ℕ)) := by
    simpa [Nat.add_assoc] using! (abs_coeffDeltaSq_le (n := n + 1))
  have hpow :
      (((n + 1 + 1 : ℕ) : ℝ) ^ (29 : ℕ)) ≤
        ((2 : ℝ) ^ (29 : ℕ)) * (((n + 1 : ℕ) : ℝ) ^ (29 : ℕ)) := by
    have hle : ((n + 1 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by nlinarith : (n + 2 : ℕ) ≤ 2 * (n + 1))
    simpa [mul_pow] using! (pow_le_pow_left₀ (by positivity) hle (29 : ℕ))
  have hC0 : (0 : ℝ) ≤ CdeltaSq := by
    simpa [CdeltaSq] using! (mul_self_nonneg Cdelta)
  calc
    |(coeffDeltaSq (n + 1) : ℝ)| ≤ CdeltaSq * (((n + 1 + 1 : ℕ) : ℝ) ^ (29 : ℕ)) := h'
    _ ≤ CdeltaSq * (((2 : ℝ) ^ (29 : ℕ)) * (((n + 1 : ℕ) : ℝ) ^ (29 : ℕ))) :=
          mul_le_mul_of_nonneg_left hpow hC0
    _ = (CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * (((n + 1 : ℕ) : ℝ) ^ (29 : ℕ)) := by ring

end SpherePacking.Dim24.AppendixA
