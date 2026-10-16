-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.AppendixA.TruncPos
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.DenomReduction.LowerBound
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.TruncEvalRewrite
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.VarphiRealPart
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.TailNumerics.Majorant

/-!
# Truncation bound for the `ineq2` numerator (`1 ≤ t`)

This file combines:

* the polynomial truncation positivity (`AppendixA.TruncPos`),
* the denominator reduction step (`DenomReduction.LowerBound`),
* and the analytic tail bounds (`TailNumerics.Majorant`)

to prove `varphi(it) - (432/π^2) * ψS(it)` has positive real part for `1 ≤ t`.

## Main statements
* `ineq2_imagAxis_ge_one`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

theorem ineq2_num_trunc_bound_geOne (t : ℝ) (ht : 1 ≤ t) :
    (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ) ≤
      (varphi_num (it t (lt_of_lt_of_le (by norm_num) ht))
          - (432 / (Real.pi ^ 2) : ℂ) * psiS_num (it t (lt_of_lt_of_le (by norm_num) ht))).re := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  set z : ℍ := it t ht0
  -- Monotonicity step: it suffices to work with the rational lower bound `cPiLower10`.
  have hmono :
      (varphi_num z - (cPiLower10 : ℂ) * psiS_num z).re ≤
        (varphi_num z - (432 / (Real.pi ^ 2) : ℂ) * psiS_num z).re := by
    simpa [z, ge_iff_le] using! (ineq2_num_it_re_ge_cPiLower10 (t := t) ht)
  -- Rewrite the truncation polynomial.
  have htrunc_eval :
      (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)) =
        (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) -
          cPiLower10 * psiSnum_trunc_eval (t := t) :=
    ineq2_trunc_geOne_eval_eq_varphi_sub_cPiLower10_mul_psiSnum_trunc (t := t)
  -- Real-part formula for the `cPiLower10` numerator.
  have hψim : (psiS_num z).im = 0 := by
    simpa [z] using! (psiS_num_it_im (t := t) ht0)
  have hre_cPi :
      (varphi_num z - (cPiLower10 : ℂ) * psiS_num z).re =
        (varphi_num z).re - cPiLower10 * (psiS_num z).re := by
    norm_num
  -- Lower bound for the `varphi_num` truncation.
  have hvarphi :
      (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) -
            (eps / 2) * (r t) ^ (12 : ℕ)
        ≤ (varphi_num z).re := by
    simpa [z] using! (varphi_num_trunc_geOne_re_lower (t := t) ht)
  -- Upper bound for the `psiS_num` truncation (via the coefficient majorant).
  have hpsi_abs :
      |(psiS_num z).re - psiSnum_trunc_eval (t := t)| ≤
        (16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) := by
    have hre : |(psiS_num z - (psiSnum_trunc_eval (t := t) : ℂ)).re| ≤
        ‖psiS_num z - (psiSnum_trunc_eval (t := t) : ℂ)‖ := by
      simpa using! (Complex.abs_re_le_norm (psiS_num z - (psiSnum_trunc_eval (t := t) : ℂ)))
    have hre' :
        (psiS_num z - (psiSnum_trunc_eval (t := t) : ℂ)).re =
          (psiS_num z).re - psiSnum_trunc_eval (t := t) := by simp
    have hnorm :
        ‖psiS_num z - (psiSnum_trunc_eval (t := t) : ℂ)‖ ≤
          (16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) := by
      simpa [z] using! (psiS_num_trunc_geOne_norm_sub_le (t := t) ht)
    exact le_trans (by simpa [hre'] using! hre) hnorm
  have hpsi_re :
      (psiS_num z).re ≤
        psiSnum_trunc_eval (t := t) +
          (16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) := by
    have hx := (abs_le.mp hpsi_abs).2
    linarith
  -- The tail constant bound: `cPiLower10 * 16^8 * tail ≤ (eps/2) * r^12`.
  have htail :
      cPiLower10 *
            ((16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)))
        ≤ (eps / 2) * (r t) ^ (12 : ℕ) := by
    have hsum0 :
        0 ≤ (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) := by
      have hr0 : 0 ≤ r t := (Real.exp_pos _).le
      have hterm0 : ∀ m : ℕ, 0 ≤ AppendixA.powGeomTerm (r t) 27 (100 + m) :=
        fun m => AppendixA.powGeomTerm_nonneg (q := r t) (k := 27) (n := 100 + m) hr0
      exact tsum_nonneg hterm0
    have hC0 : 0 ≤ (16 : ℝ) ^ (8 : ℕ) := by positivity
    have hnonneg :
        0 ≤ (16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) :=
      mul_nonneg hC0 hsum0
    have hc : cPiLower10 ≤ (432 / (Real.pi ^ 2) : ℝ) := cPiLower10_le_cPi
    have hscale :
        cPiLower10 *
              ((16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m))) ≤
            (432 / (Real.pi ^ 2) : ℝ) *
              ((16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m))) :=
      mul_le_mul_of_nonneg_right hc hnonneg
    have hpsiTail := psi_majorant_tail_bound_cPi27 (t := t) ht
    linarith
  -- Scale the `psiS_num` real-part bound.
  have hpsi_scaled :
      cPiLower10 * (psiS_num z).re ≤
        cPiLower10 * psiSnum_trunc_eval (t := t) + (eps / 2) * (r t) ^ (12 : ℕ) := by
    have h1 :
        cPiLower10 * (psiS_num z).re ≤
          cPiLower10 * (psiSnum_trunc_eval (t := t) +
            (16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m))) :=
      mul_le_mul_of_nonneg_left hpsi_re (le_of_lt cPiLower10_pos)
    linarith
  -- Combine the `varphi` lower bound and the `psi` upper bound.
  linarith

/-- Tail bound for truncating the `q^{1/2}`-series at order 50 in the `t ≥ 1` case. -/
theorem ineq2_tail_bound_geOne (t : ℝ) (ht : 1 ≤ t) :
    (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ)
      ≤ (varphi (it t (lt_of_lt_of_le (by norm_num) ht))
          - (432 / (Real.pi ^ 2) : ℂ) * ψS (it t (lt_of_lt_of_le (by norm_num) ht))).re := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  -- Reduce to a lower bound on the numerator `((varphi - (432/π^2)ψS)Δ^2)(it).re`.
  have hL0 :
      0 ≤ (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ) :=
    (le_of_lt (ineq2_trunc_geOne_pos (t := t) ht))
  refine
    ineq2_lowerBound_of_num (t := t) (ht0 := ht0)
      (L :=
        (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ))
      hL0 ?_
  simpa using! (ineq2_num_trunc_bound_geOne (t := t) ht)

/-- Positivity of `varphi(it) - (432/π^2) ψS(it)` for `t ≥ 1`. -/
public theorem ineq2_imagAxis_ge_one (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    0 < (varphi (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * ψS (it t ht0)).re := by
  have hbound :
      (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ)
        ≤ (varphi (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * ψS (it t ht0)).re := by
    have ht0' : 0 < t := lt_of_lt_of_le (by norm_num) ht
    simpa [it, ht0'] using! (ineq2_tail_bound_geOne (t := t) ht)
  have hpos : 0 < (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ) :=
    ineq2_trunc_geOne_pos (t := t) ht
  linarith


end SpherePacking.Dim24
