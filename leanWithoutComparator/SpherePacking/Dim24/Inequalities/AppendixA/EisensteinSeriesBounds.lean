/-
Reusable `q`-series expansions and coarse coefficient bounds for `E₂, E₄, E₆`.

These lemmas are used in Appendix A truncation arguments (e.g. Lemma `Bleadingterms`) to:
- rewrite `E₂, E₄, E₆` as explicit `q`-series on the upper half-plane,
- take products via Cauchy convolution coefficients,
- bound coefficients by a polynomial in `n` (using `sigma_bound`).
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import SpherePacking.ModularForms.EisensteinBase
import SpherePacking.ModularForms.FG.Positivity
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finset.NatAntidiagonal


/-!
`q`-series expansions and coefficient bounds for `E₂`, `E₄`, and `E₆`.

We package the standard `q`-expansions of the Eisenstein series as explicit coefficient functions
`coeffE2`, `coeffE4`, and `coeffE6`, together with lemmas rewriting `E₂`, `E₄`, and `E₆` as
`qseries`. We also prove coarse bounds on the absolute values of these coefficients and a generic
convolution estimate `abs_conv_le` used to bound products of `q`-series.

These results are used in Appendix A truncation and tail estimates.
-/


open scoped BigOperators
open scoped ArithmeticFunction.sigma
open scoped MatrixGroups CongruenceSubgroup ModularForm
open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA


/-- Coefficients of the `q`-expansion of `E₂`: `1 - 24 * ∑_{n≥1} σ₁(n) q^n`. -/
@[expose]
public def coeffE2 : ℕ → ℚ := fun n => if n = 0 then 1 else (-24 : ℚ) * (σ 1 n)

/-- Coefficients of the `q`-expansion of `E₄`: `1 + 240 * ∑_{n≥1} σ₃(n) q^n`. -/
@[expose]
public def coeffE4 : ℕ → ℚ := fun n => if n = 0 then 1 else (240 : ℚ) * (σ 3 n)

/-- Coefficients of the `q`-expansion of `E₆`: `1 - 504 * ∑_{n≥1} σ₅(n) q^n`. -/
@[expose]
public def coeffE6 : ℕ → ℚ := fun n => if n = 0 then 1 else (-504 : ℚ) * (σ 5 n)

private lemma qParam_pow_eq_qterm (z : ℍ) (n : ℕ) :
    (Function.Periodic.qParam (1 : ℝ) z) ^ n = qterm z n := by
  simpa [Function.Periodic.qParam, qterm, mul_assoc, mul_left_comm, mul_comm] using!
    (Complex.exp_nat_mul (2 * Real.pi * Complex.I * (z : ℂ)) n).symm

/-- Rewrite `E₂` as a `qseries` whose coefficients are given by `coeffE2`. -/
public lemma E₂_eq_qseries (z : ℍ) :
    E₂ z = qseries (fun n : ℕ => (coeffE2 n : ℂ)) z := by
  change E₂ z = ∑' n : ℕ, (coeffE2 n : ℂ) * qterm z n
  have hcoeff (n : ℕ) :
      (coeffE2 n : ℂ) = if n = 0 then (1 : ℂ) else (-24 : ℂ) * (σ 1 n : ℂ) := by
    by_cases hn : n = 0 <;> simp [coeffE2, hn]
  -- Use the `ℕ`-indexed `q`-expansion of `E₂` and match coefficients termwise.
  simpa [qterm, hcoeff] using! (_root_.E₂_eq_qexp z)

/-- Rewrite `E₄` as a `qseries` whose coefficients are given by `coeffE4`. -/
public lemma E₄_eq_qseries (z : ℍ) :
    E₄ z = qseries (fun n : ℕ => (coeffE4 n : ℂ)) z := by
  have hper : (1 : ℝ) ∈ ((Γ(1) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by simp
  have hsum :=
    ModularForm.hasSum_qExpansion (f := E₄) (h := (1 : ℝ)) (by positivity) hper z
  have hsum' :
      HasSum (fun n : ℕ => (coeffE4 n : ℂ) * qterm z n) (E₄ z) := by
    refine HasSum.congr_fun hsum (fun n => ?_)
    have hcoeff : (UpperHalfPlane.qExpansion (1 : ℝ) E₄).coeff n = (coeffE4 n : ℂ) := by
      by_cases hn : n = 0
      · subst hn
        simpa [coeffE4] using! congr_fun E4_q_exp 0
      · simpa [coeffE4, hn] using! congr_fun E4_q_exp n
    simp [smul_eq_mul, hcoeff, qParam_pow_eq_qterm z n]
  simpa [qseries] using! (hsum'.tsum_eq).symm

/-- Rewrite `E₆` as a `qseries` whose coefficients are given by `coeffE6`. -/
public lemma E₆_eq_qseries (z : ℍ) :
    E₆ z = qseries (fun n : ℕ => (coeffE6 n : ℂ)) z := by
  have hper : (1 : ℝ) ∈ ((Γ(1) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by simp
  have hsum :=
    ModularForm.hasSum_qExpansion (f := E₆) (h := (1 : ℝ)) (by positivity) hper z
  have hsum' :
      HasSum (fun n : ℕ => (coeffE6 n : ℂ) * qterm z n) (E₆ z) := by
    refine HasSum.congr_fun hsum (fun n => ?_)
    have hcoeff : (UpperHalfPlane.qExpansion (1 : ℝ) E₆).coeff n = (coeffE6 n : ℂ) := by
      by_cases hn : n = 0
      · subst hn
        simpa [coeffE6] using! congr_fun E6_q_exp 0
      · simpa [coeffE6, hn] using! congr_fun E6_q_exp n
    simp [smul_eq_mul, hcoeff, qParam_pow_eq_qterm z n]
  simpa [qseries] using! (hsum'.tsum_eq).symm

/-! ### Coefficient bounds -/

private lemma sigma_le_succ_pow (k n : ℕ) : (σ k n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (k + 1) := by
  refine (show (σ k n : ℝ) ≤ (n : ℝ) ^ (k + 1) from (by exact_mod_cast sigma_bound k n)).trans ?_
  exact pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ (n : ℝ))
    (by exact_mod_cast Nat.le_succ n)
    (k + 1)

/-- Coarse bound on `|coeffE2 n|` in terms of `(n + 1)^2`. -/
public lemma abs_coeffE2_le (n : ℕ) : |(coeffE2 n : ℝ)| ≤ 24 * (((n + 1 : ℕ) : ℝ) ^ 2) := by
  by_cases hn : n = 0
  · subst hn
    simp [coeffE2]
  · have hσ : (σ 1 n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by simpa using! sigma_le_succ_pow 1 n
    have hσ0 : 0 ≤ (σ 1 n : ℝ) := by positivity
    have : 24 * (σ 1 n : ℝ) ≤ 24 * (((n + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hσ (by positivity)
    simpa [coeffE2, hn, abs_mul, abs_of_nonneg hσ0, mul_assoc, mul_left_comm, mul_comm] using! this

/-- Coarse bound on `|coeffE4 n|` in terms of `(n + 1)^4`. -/
public lemma abs_coeffE4_le (n : ℕ) : |(coeffE4 n : ℝ)| ≤ 240 * (((n + 1 : ℕ) : ℝ) ^ 4) := by
  by_cases hn : n = 0
  · subst hn
    simp [coeffE4]
  · have hσ : (σ 3 n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 := by simpa using! sigma_le_succ_pow 3 n
    have hσ0 : 0 ≤ (σ 3 n : ℝ) := by positivity
    have : 240 * (σ 3 n : ℝ) ≤ 240 * (((n + 1 : ℕ) : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hσ (by positivity)
    simpa [coeffE4, hn, abs_mul, abs_of_nonneg hσ0, mul_assoc, mul_left_comm, mul_comm] using! this

/-- Coarse bound on `|coeffE6 n|` in terms of `(n + 1)^6`. -/
public lemma abs_coeffE6_le (n : ℕ) : |(coeffE6 n : ℝ)| ≤ 504 * (((n + 1 : ℕ) : ℝ) ^ 6) := by
  by_cases hn : n = 0
  · subst hn
    simp [coeffE6]
  · have hσ : (σ 5 n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 6 := by simpa using! sigma_le_succ_pow 5 n
    have hσ0 : 0 ≤ (σ 5 n : ℝ) := by positivity
    have : 504 * (σ 5 n : ℝ) ≤ 504 * (((n + 1 : ℕ) : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left hσ (by positivity)
    simpa [coeffE6, hn, abs_mul, abs_of_nonneg hσ0, mul_assoc, mul_left_comm, mul_comm] using! this

/-! ### Convolution coefficient bounds -/

/--
Coefficient bound for the Cauchy product `conv a b` given polynomial bounds on `|a n|` and `|b n|`.

This is the estimate used to control coefficients of products of `q`-series in Appendix A.
-/
public lemma abs_conv_le (a b : ℕ → ℚ) (Ca Cb : ℝ) (ka kb : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ Ca * (((n + 1 : ℕ) : ℝ) ^ ka))
    (hb : ∀ n : ℕ, |(b n : ℝ)| ≤ Cb * (((n + 1 : ℕ) : ℝ) ^ kb)) :
    ∀ n : ℕ, |(conv a b n : ℝ)| ≤ (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb + 1)) := by
  intro n
  have hCa : 0 ≤ Ca := le_trans (abs_nonneg (a 0 : ℝ)) (by simpa using! ha 0)
  have hCb : 0 ≤ Cb := le_trans (abs_nonneg (b 0 : ℝ)) (by simpa using! hb 0)
  have hterm :
      ∀ p ∈ Finset.antidiagonal n,
        |(a p.1 : ℝ) * (b p.2 : ℝ)| ≤ (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb)) := by
    intro p hp
    have hp1 : ((p.1 + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.Nat.antidiagonal.fst_lt hp)
    have hp2 : ((p.2 + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.Nat.antidiagonal.snd_lt hp)
    have hpow1 : (((p.1 + 1 : ℕ) : ℝ) ^ ka) ≤ (((n + 1 : ℕ) : ℝ) ^ ka) :=
      pow_le_pow_left₀ (by positivity) hp1 _
    have hpow2 : (((p.2 + 1 : ℕ) : ℝ) ^ kb) ≤ (((n + 1 : ℕ) : ℝ) ^ kb) :=
      pow_le_pow_left₀ (by positivity) hp2 _
    have ha' : |(a p.1 : ℝ)| ≤ Ca * (((p.1 + 1 : ℕ) : ℝ) ^ ka) := ha p.1
    have hb' : |(b p.2 : ℝ)| ≤ Cb * (((p.2 + 1 : ℕ) : ℝ) ^ kb) := hb p.2
    calc
      |(a p.1 : ℝ) * (b p.2 : ℝ)| = |(a p.1 : ℝ)| * |(b p.2 : ℝ)| := by simp [abs_mul]
      _ ≤ (Ca * (((p.1 + 1 : ℕ) : ℝ) ^ ka)) * (Cb * (((p.2 + 1 : ℕ) : ℝ) ^ kb)) := by
            exact mul_le_mul ha' hb' (abs_nonneg _) (mul_nonneg hCa (by positivity))
      _ ≤ (Ca * (((n + 1 : ℕ) : ℝ) ^ ka)) * (Cb * (((n + 1 : ℕ) : ℝ) ^ kb)) := by
            gcongr
      _ = (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb)) := by
            simp [mul_assoc, mul_left_comm, pow_add]
  calc
    |(conv a b n : ℝ)|
        = |∑ p ∈ Finset.antidiagonal n, (a p.1 : ℝ) * (b p.2 : ℝ)| := by simp [conv]
    _ ≤ ∑ p ∈ Finset.antidiagonal n, |(a p.1 : ℝ) * (b p.2 : ℝ)| := by
          simpa using!
            (Finset.abs_sum_le_sum_abs (f := fun p => (a p.1 : ℝ) * (b p.2 : ℝ))
              (s := Finset.antidiagonal n))
    _ ≤ (∑ _p ∈ Finset.antidiagonal n, (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb))) :=
          Finset.sum_le_sum hterm
    _ = ((n + 1 : ℕ) : ℝ) * ((Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb))) := by
          simp [mul_assoc]
    _ = (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb + 1)) := by
          simp [mul_assoc, pow_succ, pow_add, mul_left_comm, mul_comm]

end SpherePacking.Dim24.AppendixA
