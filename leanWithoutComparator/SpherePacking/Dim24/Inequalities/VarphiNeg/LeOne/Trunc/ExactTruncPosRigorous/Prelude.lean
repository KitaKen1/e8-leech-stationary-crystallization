-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.CoeffModel
public import
 SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.ExactTruncTail.ExactTruncation
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PiBoundsAndTruncCompare
public import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-!
# Prelude for exact truncation positivity

This file sets up the certified bounds used to prove nonnegativity of `exactCoeff t i` for even
indices `i ≥ 6` in the `t ≥ 1` regime of Appendix A.

The key idea is to bound `u = 1 / π` (and `u^2`) by rational intervals and then choose a
worst-case endpoint depending on the sign of the coefficient. This reduces the needed inequalities
to finite checks in `ℚ`.

## Main definitions
* `uLoQ`, `uHiQ`
* `bBoundQ`, `cBoundSqQ`
* `coeff1_lbQ`, `deriv_lbQ`

## Main statements
* `exactCoeff_nonneg_even_ge6`
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.VarphiNeg.LeOne.Trunc

open AppendixA
open AppendixA.VarphiLeOne

-- Prevent `simp` from rewriting numerator sign tests back into rational order tests.
attribute [-simp] Rat.num_nonneg Rat.num_neg


/-- A certified rational lower bound for `1 / π`. -/
@[expose] public def uLoQ : ℚ := AppendixA.BleadingCoeffs.invPiLower10Q

/-- A certified rational upper bound for `1 / π`. -/
@[expose] public def uHiQ : ℚ := AppendixA.BleadingCoeffs.invPiUpper10Q

/-- The square of `uLoQ`. -/
@[expose] public def uLoSqQ : ℚ := uLoQ ^ (2 : ℕ)

/-- The square of `uHiQ`. -/
@[expose] public def uHiSqQ : ℚ := uHiQ ^ (2 : ℕ)

/-- Real coercion of `uLoQ`. -/
@[expose] public def uLo : ℝ := (uLoQ : ℝ)

/-- Real coercion of `uHiQ`. -/
@[expose] public def uHi : ℝ := (uHiQ : ℝ)

/-- Real coercion of `uLoSqQ`. -/
@[expose] public def uLoSq : ℝ := (uLoSqQ : ℝ)

/-- Real coercion of `uHiSqQ`. -/
@[expose] public def uHiSq : ℝ := (uHiSqQ : ℝ)

/-- The certified bound `uLo ≤ 1 / π`. -/
public lemma uLo_le_inv_pi : uLo ≤ (1 / Real.pi) := by
  simpa [uLo, uLoQ] using! SpherePacking.Dim24.AppendixA.invPiLower10Q_le_inv_pi

/-- The certified bound `1 / π ≤ uHi`. -/
public lemma inv_pi_le_uHi : (1 / Real.pi) ≤ uHi := by
  simpa [uHi, uHiQ] using! SpherePacking.Dim24.AppendixA.inv_pi_le_invPiUpper10Q

/-- A coarse inequality `1000 < exp 7`, used to control `exp (-7)`. -/
public lemma exp_seven_gt_1000 : (1000 : ℝ) < Real.exp 7 := by
  -- Lower bound `exp 7` by a Taylor partial sum to order 11.
  have hsum_le : (∑ n ∈ Finset.range 12, (7 : ℝ) ^ n / (Nat.factorial n)) ≤ Real.exp 7 := by
    have hexp :
        Real.exp 7 = ∑' n : ℕ, (7 : ℝ) ^ n / (Nat.factorial n) := by
      simpa [Real.exp_eq_exp_ℝ] using!
        congrArg (fun f : ℝ → ℝ => f 7) (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))
    have hs : Summable (fun n : ℕ => (7 : ℝ) ^ n / (Nat.factorial n)) :=
      Real.summable_pow_div_factorial 7
    have hsum_le_tsum :
        (∑ n ∈ Finset.range 12, (7 : ℝ) ^ n / (Nat.factorial n)) ≤
          ∑' n : ℕ, (7 : ℝ) ^ n / (Nat.factorial n) := by
      refine hs.sum_le_tsum (Finset.range 12) ?_
      intro n _hn
      positivity
    simpa [hexp] using! hsum_le_tsum
  linarith

/-- The bound `exp (-7) < 1 / 1000`, obtained from `exp_seven_gt_1000`. -/
public lemma exp_neg_seven_lt_one_div_1000 : Real.exp (-7 : ℝ) < (1 : ℝ) / 1000 := by
  have h : (1000 : ℝ) < Real.exp 7 := exp_seven_gt_1000
  have hdiv : (1 : ℝ) / (Real.exp 7) < (1 : ℝ) / 1000 :=
    one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < (1000 : ℝ)) h
  simpa [Real.exp_neg, one_div] using! hdiv

/-- The numerical inequality `exp (-4π) < 1 / 535^2` used in Appendix A. -/
public lemma exp_neg_four_pi_lt_one_div_535_sq :
    Real.exp (-4 * Real.pi) < (1 : ℝ) / (535 : ℝ) ^ (2 : ℕ) := by
  have h2 : Real.exp (-2 * Real.pi) < (1 : ℝ) / 535 :=
    AppendixA.exp_neg_two_pi_lt_one_div_535
  have hx : 0 ≤ Real.exp (-2 * Real.pi) := (Real.exp_pos _).le
  have hpow : (Real.exp (-2 * Real.pi)) ^ (2 : ℕ) < ((1 : ℝ) / 535) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ h2 hx (n := 2) (by decide)
  have hexp : Real.exp (-4 * Real.pi) = (Real.exp (-2 * Real.pi)) ^ (2 : ℕ) := by
    -- `exp(-4π) = (exp(-2π))^2`.
    have : (-4 * Real.pi) = (-2 * Real.pi) + (-2 * Real.pi) := by ring
    simp [this, Real.exp_add, pow_two]
  have hsq : ((1 : ℝ) / 535) ^ (2 : ℕ) = (1 : ℝ) / (535 : ℝ) ^ (2 : ℕ) := by
    -- `((1/535)^2) = 1/(535^2)`.
    field_simp
  calc
    Real.exp (-4 * Real.pi) = (Real.exp (-2 * Real.pi)) ^ (2 : ℕ) := hexp
    _ < ((1 : ℝ) / 535) ^ (2 : ℕ) := hpow
    _ = (1 : ℝ) / (535 : ℝ) ^ (2 : ℕ) := hsq

/-- For `y > 0`, the function `y * exp(-y)` is maximized at `y = 1`. -/
public lemma mul_exp_neg_le_exp_neg_one (y : ℝ) :
    y * Real.exp (-y) ≤ Real.exp (-1 : ℝ) :=
  Real.mul_exp_neg_le_exp_neg_one y

/-- Odd-index coefficients vanish: `exactCoeff t i = 0` when `i` is odd. -/
public lemma exactCoeff_odd (t : ℝ) (i : ℕ) (hi : i % 2 = 1) :
    exactCoeff t i = 0 := by
  simp [exactCoeff, Acoeff, Bcoeff, Ccoeff, hi]


-- NOTE: `Rat` order on `ℚ` is opaque, so `simp`/`decide` cannot evaluate branches like
-- `if 0 ≤ B then ... else ...` for concrete rationals. We instead branch on the integer numerator,
-- which is computable and equivalent (denominator is positive).
/-- Choose the worst-case bound for `u = 1 / π` depending on the sign of `B`. -/
public def bBoundQ (B : ℚ) : ℚ := if 0 ≤ B.num then uLoQ else uHiQ

/-- Choose the worst-case bound for `u^2` depending on the sign of `C`. -/
public def cBoundSqQ (C : ℚ) : ℚ := if 0 ≤ C.num then uLoSqQ else uHiSqQ

/-- A rational lower bound for `Acoeff i + Bcoeff i * u + Ccoeff i * u^2` at `t = 1`. -/
public def coeff1_lbQ (i : ℕ) : ℚ :=
  Acoeff i + (Bcoeff i) * bBoundQ (Bcoeff i) + (Ccoeff i) * cBoundSqQ (Ccoeff i)

/-- A rational lower bound for `2 * Acoeff i + Bcoeff i * u` at `t = 1`. -/
public def deriv_lbQ (i : ℕ) : ℚ :=
  (2 : ℚ) * Acoeff i + (Bcoeff i) * bBoundQ (Bcoeff i)

/-- Nonnegativity of `coeff1_lbQ` for even indices `i` in the certified range. -/
public lemma coeff1_lbQ_nonneg_fin :
    ∀ i : Fin BleadingCoeffs.N, (6 ≤ i.1) → (i.1 % 2 = 0) → (0 : ℚ) ≤ coeff1_lbQ i.1 := by
  intro i hi6 hi2
  have hi_lt' : i.1 < BleadingCoeffs.N := i.2
  have hi_lt : i.1 < 100 := by
    dsimp [BleadingCoeffs.N] at hi_lt'
    exact hi_lt'
  have hi_le : i.1 ≤ 99 := Nat.le_of_lt_succ hi_lt
  interval_cases i.1 using hi6, hi_le
  all_goals
    simp [coeff1_lbQ, bBoundQ, cBoundSqQ, uLoQ, uHiQ, uLoSqQ, uHiSqQ, Acoeff, Bcoeff, Ccoeff,
      BleadingCoeffs.QN,
      varphiNumCoeffsZ_table, phi1CoreCoeffsZ_table, phi2CoreCoeffsZ_table,
      AppendixA.BleadingCoeffs.invPiLower10Q, AppendixA.BleadingCoeffs.invPiUpper10Q,
      AppendixA.BleadingCoeffs.piLower10Q, AppendixA.BleadingCoeffs.piUpper10Q]
    try norm_num

/-- Nonnegativity of `deriv_lbQ` for even indices `i` in the certified range. -/
public lemma deriv_lbQ_nonneg_fin :
    ∀ i : Fin BleadingCoeffs.N, (6 ≤ i.1) → (i.1 % 2 = 0) → (0 : ℚ) ≤ deriv_lbQ i.1 := by
  intro i hi6 hi2
  have hi_lt' : i.1 < BleadingCoeffs.N := i.2
  have hi_lt : i.1 < 100 := by
    dsimp [BleadingCoeffs.N] at hi_lt'
    exact hi_lt'
  have hi_le : i.1 ≤ 99 := Nat.le_of_lt_succ hi_lt
  interval_cases i.1 using hi6, hi_le
  all_goals
    simp [deriv_lbQ, bBoundQ, uLoQ, uHiQ, Acoeff, Bcoeff,
      BleadingCoeffs.QN,
      varphiNumCoeffsZ_table, phi1CoreCoeffsZ_table,
      AppendixA.BleadingCoeffs.invPiLower10Q, AppendixA.BleadingCoeffs.invPiUpper10Q,
      AppendixA.BleadingCoeffs.piLower10Q, AppendixA.BleadingCoeffs.piUpper10Q]
    try norm_num

/-- Nonnegativity of `exactCoeff t i` for `t ≥ 1` and even indices `i ≥ 6` in the certified
range. -/
public lemma exactCoeff_nonneg_even_ge6 (t : ℝ) (ht : 1 ≤ t) (i : ℕ) (hiN : i < BleadingCoeffs.N)
    (hi6 : 6 ≤ i) (hi2 : i % 2 = 0) :
    0 ≤ exactCoeff t i := by
  set u : ℝ := 1 / Real.pi
  have hu_lo : uLo ≤ u := by simpa [u, uLo] using! uLo_le_inv_pi
  have hu_hi : u ≤ uHi := by simpa [u, uHi] using! inv_pi_le_uHi
  have huLo0 : 0 ≤ uLo := by
    have : (0 : ℚ) ≤ uLoQ := by
      -- `uLoQ = 1 / piUpper10Q` with `piUpper10Q > 0`.
      -- `norm_num` proves the resulting rational inequality directly.
      dsimp [uLoQ, AppendixA.BleadingCoeffs.invPiLower10Q, AppendixA.BleadingCoeffs.piUpper10Q]
      norm_num
    have : (0 : ℝ) ≤ (uLoQ : ℝ) := by exact_mod_cast this
    simpa [uLo] using! this
  have huHi0 : 0 ≤ uHi :=
    le_imp_le_of_le_of_le huLo0 hu_hi hu_lo
  have huSq_lo : uLoSq ≤ u ^ (2 : ℕ) := by
    have := pow_le_pow_left₀ huLo0 hu_lo 2
    simpa [uLoSq, uLoSqQ, uLoQ, uLo, pow_two, one_div, u] using! this
  have huSq_hi : u ^ (2 : ℕ) ≤ uHiSq := by
    have hu0 : 0 ≤ u := by positivity [Real.pi_pos.le]
    have := pow_le_pow_left₀ hu0 hu_hi 2
    simpa [uHiSq, uHiSqQ, uHiQ, uHi, pow_two, one_div, u] using! this
  have hA0 : 0 ≤ (Acoeff i : ℝ) := by
    exact_mod_cast (Acoeff_nonneg_fin ⟨i, hiN⟩)
  -- Lower bound `exactCoeff 1 i`.
  have hcoeff1_lbQ : (0 : ℚ) ≤ coeff1_lbQ i := coeff1_lbQ_nonneg_fin ⟨i, hiN⟩ hi6 hi2
  have hcoeff1_lb : (0 : ℝ) ≤ (coeff1_lbQ i : ℝ) := by exact_mod_cast hcoeff1_lbQ
  have hBu : (Bcoeff i : ℝ) * u ≥ (Bcoeff i : ℝ) * (bBoundQ (Bcoeff i) : ℝ) := by
    by_cases hB : 0 ≤ Bcoeff i
    · have hBnum : 0 ≤ (Bcoeff i).num := (Rat.num_nonneg).2 hB
      have hb : (bBoundQ (Bcoeff i) : ℝ) = uLo := by simp [bBoundQ, hBnum, uLo, uLoQ]
      have hB0 : 0 ≤ (Bcoeff i : ℝ) := by exact_mod_cast hB
      have := mul_le_mul_of_nonneg_left hu_lo hB0
      simpa [hb, mul_assoc, mul_left_comm, mul_comm, ge_iff_le] using! this
    · have hBneg : (Bcoeff i : ℝ) < 0 := by
        have : Bcoeff i < 0 := lt_of_not_ge hB
        exact_mod_cast this
      have hBnum : ¬0 ≤ (Bcoeff i).num := by
        intro hnum
        have : 0 ≤ Bcoeff i := (Rat.num_nonneg).1 hnum
        exact hB this
      have hb : (bBoundQ (Bcoeff i) : ℝ) = uHi := by simp [bBoundQ, hBnum, uHi, uHiQ]
      have := mul_le_mul_of_nonpos_left hu_hi hBneg.le
      simpa [hb, mul_assoc, mul_left_comm, mul_comm, ge_iff_le] using! this
  have hCu2 : (Ccoeff i : ℝ) * (u ^ (2 : ℕ)) ≥ (Ccoeff i : ℝ) * (cBoundSqQ (Ccoeff i) : ℝ) := by
    by_cases hC : 0 ≤ Ccoeff i
    · have hCnum : 0 ≤ (Ccoeff i).num := (Rat.num_nonneg).2 hC
      have hc : (cBoundSqQ (Ccoeff i) : ℝ) = uLoSq := by simp [cBoundSqQ, hCnum, uLoSq, uLoSqQ]
      have hC0 : 0 ≤ (Ccoeff i : ℝ) := by exact_mod_cast hC
      have := mul_le_mul_of_nonneg_left huSq_lo hC0
      simpa [hc, mul_assoc, mul_left_comm, mul_comm, ge_iff_le] using! this
    · have hCneg : (Ccoeff i : ℝ) < 0 := by
        have : Ccoeff i < 0 := lt_of_not_ge hC
        exact_mod_cast this
      have hCnum : ¬0 ≤ (Ccoeff i).num := by
        intro hnum
        have : 0 ≤ Ccoeff i := (Rat.num_nonneg).1 hnum
        exact hC this
      have hc : (cBoundSqQ (Ccoeff i) : ℝ) = uHiSq := by simp [cBoundSqQ, hCnum, uHiSq, uHiSqQ]
      have := mul_le_mul_of_nonpos_left huSq_hi hCneg.le
      simpa [hc, mul_assoc, mul_left_comm, mul_comm, ge_iff_le] using! this
  have hcoeff1 : 0 ≤ exactCoeff (t := (1 : ℝ)) i := by
    -- `exactCoeff 1 i ≥ coeff1_lbQ i ≥ 0`.
    have hmain :
        (coeff1_lbQ i : ℝ) ≤
          (Acoeff i : ℝ) + (Bcoeff i : ℝ) * u + (Ccoeff i : ℝ) * (u ^ (2 : ℕ)) := by
      have hBterm : (Bcoeff i : ℝ) * (bBoundQ (Bcoeff i) : ℝ) ≤ (Bcoeff i : ℝ) * u := by
        simpa [ge_iff_le] using! hBu
      have hCterm :
          (Ccoeff i : ℝ) * (cBoundSqQ (Ccoeff i) : ℝ) ≤ (Ccoeff i : ℝ) * (u ^ (2 : ℕ)) := by
        simpa [ge_iff_le] using! hCu2
      -- Expand `coeff1_lbQ` and compare termwise.
      simp [coeff1_lbQ, u, pow_two, one_div] at hBterm hCterm ⊢
      nlinarith [hBterm, hCterm]
    have : (0 : ℝ) ≤ (Acoeff i : ℝ) + (Bcoeff i : ℝ) * u + (Ccoeff i : ℝ) * (u ^ (2 : ℕ)) :=
      le_trans hcoeff1_lb hmain
    simpa [exactCoeff, u, pow_two, one_div, add_assoc, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm] using! this
  -- Monotone step: show `exactCoeff t i ≥ exactCoeff 1 i` for `t ≥ 1`.
  have hderiv_lbQ : (0 : ℚ) ≤ deriv_lbQ i := deriv_lbQ_nonneg_fin ⟨i, hiN⟩ hi6 hi2
  have hderiv_lb : (0 : ℝ) ≤ (deriv_lbQ i : ℝ) := by exact_mod_cast hderiv_lbQ
  have hfactor : 0 ≤ (Acoeff i : ℝ) * (t + 1) + (Bcoeff i : ℝ) * u := by
    have ht2 : (2 : ℝ) ≤ t + 1 := by linarith [ht]
    have hA2 : (2 : ℝ) * (Acoeff i : ℝ) ≤ (Acoeff i : ℝ) * (t + 1) :=
      by
        have h := mul_le_mul_of_nonneg_left ht2 hA0
        -- `h : (Acoeff i) * 2 ≤ (Acoeff i) * (t + 1)`; commute the left factor.
        simpa [mul_assoc, mul_left_comm, mul_comm] using! h
    have hBbound :
        (Bcoeff i : ℝ) * (bBoundQ (Bcoeff i) : ℝ) ≤ (Bcoeff i : ℝ) * u := by
      simpa [ge_iff_le] using! hBu
    have : (0 : ℝ) ≤ (2 : ℝ) * (Acoeff i : ℝ) + (Bcoeff i : ℝ) * (bBoundQ (Bcoeff i) : ℝ) := by
      simpa [deriv_lbQ, two_mul, mul_assoc, add_assoc, add_left_comm, add_comm] using! hderiv_lb
    nlinarith [hA2, hBbound, this]
  have hdiff :
      exactCoeff t i - exactCoeff (t := (1 : ℝ)) i =
        (t - 1) * ((Acoeff i : ℝ) * (t + 1) + (Bcoeff i : ℝ) * u) := by
    simp [exactCoeff, u]
    ring
  have hdiff_nonneg : 0 ≤ exactCoeff t i - exactCoeff (t := (1 : ℝ)) i := by
    have ht1 : 0 ≤ t - 1 := sub_nonneg.2 ht
    have := mul_nonneg ht1 hfactor
    simpa [hdiff] using! this
  have hge1 : exactCoeff (t := (1 : ℝ)) i ≤ exactCoeff t i := by linarith [hdiff_nonneg]
  exact le_trans hcoeff1 hge1


end SpherePacking.Dim24.VarphiNeg.LeOne.Trunc
