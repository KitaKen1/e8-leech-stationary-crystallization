-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ConvolutionAlgebra
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ShiftSums
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.TruncCoeffCertificate

/-!
### Rational bounds for `π` and `1/π`

These are auxiliary constants matching the PARI/GP bounding procedure used for Appendix A.
-/

open scoped BigOperators

noncomputable section

-- NOTE: We avoid using simp lemmas like `mul_eq_mul_right_iff` in this file; they can turn
-- coefficient-rewriting goals into disjunctions and break automation in later lemmas.
attribute [-simp] mul_eq_mul_right_iff mul_eq_mul_left_iff

namespace SpherePacking.Dim24.AppendixA

private def piLowerD20 : ℝ := (3.14159265358979323846 : ℝ)
private def piUpperD20 : ℝ := (3.14159265358979323847 : ℝ)

private lemma piLowerD20_lt_pi : piLowerD20 < Real.pi := by simpa [piLowerD20] using! Real.pi_gt_d20

private lemma pi_lt_piUpperD20 : Real.pi < piUpperD20 := by simpa [piUpperD20] using! Real.pi_lt_d20

private lemma piLowerD20_pos : (0 : ℝ) < piLowerD20 := by norm_num [piLowerD20]

private lemma piUpperD20_pos : (0 : ℝ) < piUpperD20 := by norm_num [piUpperD20]


/-! ## Rational bounds for `Real.pi` -/

/-- A rational lower bound for `Real.pi` used in the coefficient bounding procedure. -/
@[expose] public def piLowerQ : ℚ := 2819886971 / 897597901
/-- A rational upper bound for `Real.pi` used in the coefficient bounding procedure. -/
@[expose] public def piUpperQ : ℚ := 2819886972 / 897597901

private lemma piLowerQ_lt_pi : (piLowerQ : ℝ) < Real.pi := by
  have hlt : (piLowerQ : ℝ) < piLowerD20 := by norm_num [piLowerQ, piLowerD20]
  exact lt_trans hlt piLowerD20_lt_pi

private lemma pi_lt_piUpperQ : Real.pi < (piUpperQ : ℝ) := by
  have hlt : piUpperD20 < (piUpperQ : ℝ) := by norm_num [piUpperQ, piUpperD20]
  exact lt_trans pi_lt_piUpperD20 hlt

/-- The 10-digit lower bound `BleadingCoeffs.piLower10Q` is strictly below `Real.pi`. -/
public lemma piLower10Q_lt_pi : (BleadingCoeffs.piLower10Q : ℝ) < Real.pi :=
  (lt_trans (by norm_num [BleadingCoeffs.piLower10Q, piLowerD20]) piLowerD20_lt_pi)

/-- The 10-digit upper bound `BleadingCoeffs.piUpper10Q` is strictly above `Real.pi`. -/
public lemma pi_lt_piUpper10Q : Real.pi < (BleadingCoeffs.piUpper10Q : ℝ) :=
  (lt_trans pi_lt_piUpperD20 (by norm_num [BleadingCoeffs.piUpper10Q, piUpperD20]))

/-- A rational lower bound for `1 / Real.pi` used in the coefficient bounding procedure. -/
@[expose] public def invPiLowerQ : ℚ := 285714285 / 897597901
/-- A rational upper bound for `1 / Real.pi` used in the coefficient bounding procedure. -/
@[expose] public def invPiUpperQ : ℚ := 285714286 / 897597901

private lemma invPiLowerQ_lt_inv_pi : (invPiLowerQ : ℝ) < (1 / Real.pi) := by
  have hinv : (1 / piUpperD20) < (1 / Real.pi) :=
    one_div_lt_one_div_of_lt Real.pi_pos pi_lt_piUpperD20
  exact lt_trans (by norm_num [invPiLowerQ, piUpperD20]) hinv

private lemma inv_pi_lt_invPiUpperQ : (1 / Real.pi) < (invPiUpperQ : ℝ) := by
  have hinv : (1 / Real.pi) < (1 / piLowerD20) :=
    one_div_lt_one_div_of_lt piLowerD20_pos piLowerD20_lt_pi
  exact lt_trans hinv (by norm_num [invPiUpperQ, piLowerD20])

/-- The 10-digit lower bound `BleadingCoeffs.invPiLower10Q` is below `1 / Real.pi`. -/
public lemma invPiLower10Q_le_inv_pi : (BleadingCoeffs.invPiLower10Q : ℝ) ≤ (1 / Real.pi) := by
  simpa [BleadingCoeffs.invPiLower10Q] using!
    one_div_le_one_div_of_le Real.pi_pos (le_of_lt pi_lt_piUpper10Q)

/-- The 10-digit upper bound `BleadingCoeffs.invPiUpper10Q` is above `1 / Real.pi`. -/
public lemma inv_pi_le_invPiUpper10Q : (1 / Real.pi) ≤ (BleadingCoeffs.invPiUpper10Q : ℝ) := by
  have hpos : (0 : ℝ) < (BleadingCoeffs.piLower10Q : ℝ) := by
    norm_num [BleadingCoeffs.piLower10Q]
  simpa [BleadingCoeffs.invPiUpper10Q, one_div] using!
    one_div_le_one_div_of_le hpos (le_of_lt piLower10Q_lt_pi)

/-!
### Comparing `Bleading_trunc` to the degree-99 numerator truncation

`AppendixA.Bleading_trunc` is built coefficientwise by the PARI/GP-style `LowerBound` procedure
implemented in `BLeadingCoeffs.lean`. Here we show that, for `t ≥ 1`, evaluating this polynomial
at `r(t) = exp(-π t)` is bounded above by the exact truncated `r`-series built from the
coefficients `Acoeff/Bcoeff/Ccoeff`.
-/

/-- The coefficient list `Bleading_trunc_coeffs` has length `N`. -/
public lemma Bleading_trunc_coeffs_length :
    Bleading_trunc_coeffs.length = BleadingCoeffs.N := by
  decide

/-- The `i`-th coefficient in the exact truncation, as a function of `t`. -/
@[expose] public def Bleading_exact_coeff (t : ℝ) (i : ℕ) : ℝ :=
  (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) +
    (BleadingCoeffs.Bcoeff i : ℝ) * t +
      (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi)

/-- The exact truncation evaluated at `r(t)`, as a finite sum over `i < N`. -/
@[expose] public def Bleading_exact_trunc (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range BleadingCoeffs.N, Bleading_exact_coeff t i * (r t) ^ i

/-- Closed-form coefficient formula for the polynomial `Bleading_trunc`. -/
@[expose] public def Bleading_trunc_coeff_formula (k : ℕ) : ℚ :=
  BleadingCoeffs.Akeep k +
    (if k + 2 < BleadingCoeffs.N then BleadingCoeffs.Ashift (k + 2) else 0) +
    BleadingCoeffs.Bkeep k +
      (if k + 1 < BleadingCoeffs.N then BleadingCoeffs.Bshift (k + 1) else 0) +
      BleadingCoeffs.Ckeep k

/-- For `k < N`, the list coefficient `getD k 0` agrees with `Bleading_trunc_coeff_formula k`. -/
public lemma Bleading_trunc_coeffs_getD_of_lt (k : ℕ) (hk : k < BleadingCoeffs.N) :
    Bleading_trunc_coeffs.getD k 0 = Bleading_trunc_coeff_formula k := by
  simpa [Bleading_trunc_coeff_formula] using! (Bleading_trunc_coeffs_getD_eq_formula (k := ⟨k, hk⟩))


/-- Evaluate `Bleading_trunc` at `r(t)` as an explicit sum using `Bleading_trunc_coeff_formula`. -/
public lemma Bleading_trunc_eval₂_eq_sum_range_formula (t : ℝ) :
    (Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (r t)) =
      ∑ n ∈ Finset.range BleadingCoeffs.N, (Bleading_trunc_coeff_formula n : ℝ) * (r t) ^ n := by
  have h :
      (Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (r t)) =
        ∑ n ∈ Finset.range BleadingCoeffs.N,
          (algebraMap ℚ ℝ) (Bleading_trunc_coeffs.getD n 0) * (r t) ^ n := by
    simpa [Bleading_trunc_coeffs_length] using! (Bleading_trunc_eval₂_eq_sum_range (x := r t))
  refine h.trans ?_
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hnlt : n < BleadingCoeffs.N := by simpa [Finset.mem_range] using! hn
  have hcoeff :
      (algebraMap ℚ ℝ) (Bleading_trunc_coeffs.getD n 0) = (Bleading_trunc_coeff_formula n : ℝ) := by
    simpa using! congrArg (algebraMap ℚ ℝ) (Bleading_trunc_coeffs_getD_of_lt n hnlt)
  simpa [mul_assoc] using! congrArg (fun y : ℝ => y * (r t) ^ n) hcoeff

end SpherePacking.Dim24.AppendixA
