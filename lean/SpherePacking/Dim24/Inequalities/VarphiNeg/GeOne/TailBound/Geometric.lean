/-
Numeric geometric tail bound used in the `t ≥ 1` truncation.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.VarphiNeg.GeOne.Defs
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesTailBounds


/-!
# Geometric tail bound for `t ≥ 1`

Numeric geometric tail bound used in the `t ≥ 1` truncation.

We use the certified inequality `q(t) ≤ 1/535` (Appendix A) and a uniform ratio bound
`powGeomRatio ≤ 1/2` to reduce the tail estimate to a single rational inequality.

## Main statements
* `powGeomTail_bound_eps_scaled`
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

namespace VarphiNegGeOne

/-- A scaled geometric tail bound used in `varphi_tail_bound_geOne`. -/
public lemma powGeomTail_bound_eps_scaled (t : ℝ) (ht : 1 ≤ t) :
    (513200655360 : ℝ) * (∑' m : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + m)) ≤
      eps * (q t) ^ (6 : ℕ) := by
  have hq0 : 0 ≤ q t := (Real.exp_pos _).le
  have hqle : q t ≤ (1 : ℝ) / 535 := AppendixA.q_le_one_div_535 (t := t) ht
  have hρ_le_half : AppendixA.powGeomRatio (q t) 20 50 ≤ (1 : ℝ) / 2 :=
    AppendixA.powGeomRatio_q_le_half_of_q_le_one_div_535 (q' := q t) hqle
  have hρ_lt_one : AppendixA.powGeomRatio (q t) 20 50 < 1 :=
    lt_of_le_of_lt hρ_le_half (by norm_num)
  have htail_le :
      (∑' m : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + m)) ≤
        AppendixA.powGeomTerm (q t) 20 50 / (1 - AppendixA.powGeomRatio (q t) 20 50) :=
    AppendixA.tsum_powGeomTerm_tail_le (q := q t) (k := 20) (N := 50) hq0 hρ_lt_one
  have hden : (1 : ℝ) / 2 ≤ 1 - AppendixA.powGeomRatio (q t) 20 50 := by linarith
  have hhalf_pos : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  have hinv_le : (1 / (1 - AppendixA.powGeomRatio (q t) 20 50)) ≤ 2 := by
    have : (1 / (1 - AppendixA.powGeomRatio (q t) 20 50)) ≤ (1 / ((1 : ℝ) / 2)) := by
      simpa [one_div] using! (one_div_le_one_div_of_le hhalf_pos hden)
    simpa using! this
  have hpowGeom_nonneg : 0 ≤ AppendixA.powGeomTerm (q t) 20 50 := by
    exact AppendixA.powGeomTerm_nonneg (q := q t) (k := 20) (n := 50) hq0
  have htail_le' :
      (∑' m : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + m)) ≤
        2 * AppendixA.powGeomTerm (q t) 20 50 := by
    exact tsum_powGeomTerm_tail_le_two_mul (q t) 20 50 hq0 hρ_le_half
  -- Now dominate `2 * 513200655360 * (51^20) * (q t)^44` by `eps`.
  have hqpow_le : ∀ n : ℕ, (q t) ^ n ≤ ((1 : ℝ) / 535) ^ n := fun n =>
    pow_le_pow_left₀ hq0 hqle n
  have hpow44_le : (q t) ^ (44 : ℕ) ≤ ((1 : ℝ) / 535) ^ (44 : ℕ) := hqpow_le 44
  have hconstQ :
      (2 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 535) ^ (44 : ℕ) <
        (10 : ℚ) ^ (-50 : ℤ) := by
    norm_num
  have hconstR_lt :
      ((2 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 535) ^ (44 : ℕ) : ℝ) <
        ((10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
    exact_mod_cast hconstQ
  have hconstR :
      (2 : ℝ) * (513200655360 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) <
        (10 : ℝ) ^ (-50 : ℤ) := by
    simpa using! hconstR_lt
  have hconstR_le :
      (2 : ℝ) * (513200655360 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ) ≤ eps := by
    have hle :
        (2 : ℝ) * (513200655360 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ) ≤
          (2 : ℝ) * (513200655360 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow44_le (by positivity)
    exact le_trans hle (le_of_lt (by simpa [eps] using! hconstR))
  have hqt6 : 0 ≤ (q t) ^ (6 : ℕ) := pow_nonneg hq0 _
  have hpow50 : (q t) ^ (50 : ℕ) = (q t) ^ (6 : ℕ) * (q t) ^ (44 : ℕ) := by
    -- `50 = 6 + 44`.
    ring
  have hmain :
      (513200655360 : ℝ) * (2 * AppendixA.powGeomTerm (q t) 20 50) ≤ eps * (q t) ^ (6 : ℕ) := by
    dsimp [AppendixA.powGeomTerm]
    have : ((50 + 1 : ℝ) ^ (20 : ℕ)) = (51 : ℝ) ^ (20 : ℕ) := by norm_num
    rw [this]
    rw [hpow50]
    -- Rearrange and use `hconstR_le`.
    have :
        (513200655360 : ℝ) * (2 * ((51 : ℝ) ^ (20 : ℕ) * ((q t) ^ (6 : ℕ) * (q t) ^ (44 : ℕ)))) =
          (q t) ^ (6 : ℕ) *
            ((2 : ℝ) * (513200655360 : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ)) := by
      ring_nf
    rw [this]
    have := mul_le_mul_of_nonneg_left hconstR_le hqt6
    simpa [mul_assoc, mul_left_comm, mul_comm] using! this
  -- Combine the geometric reduction with the constant estimate.
  have hscale :
      (513200655360 : ℝ) * (∑' m : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + m)) ≤
        (513200655360 : ℝ) * (2 * AppendixA.powGeomTerm (q t) 20 50) :=
    mul_le_mul_of_nonneg_left htail_le' (by positivity)
  exact le_trans hscale hmain


end SpherePacking.Dim24.VarphiNegGeOne
