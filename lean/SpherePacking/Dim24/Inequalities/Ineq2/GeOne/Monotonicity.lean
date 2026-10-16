-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.TailNumerics.ConstantsPi
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.DenomReduction.Numerators


/-!
# Monotonicity step for `432/π^2` using `psiS_num(it) ≤ 0`

On the imaginary axis, `H₂(it)` and `H₄(it)` are positive real numbers, hence `psiS_num(it)` is
real and nonpositive. Since `432/π^2` is positive and `432/piUpper10^2 ≤ 432/π^2`, we can replace
`432/π^2` by the rational lower bound `cPiLower10 = 432/piUpper10^2` when proving a lower bound for
`(varphi_num (it t) - (432/π^2) * psiS_num (it t)).re`.

## Main definitions
* `cPiLower10`

## Main statements
* `ineq2_num_it_re_ge_cPiLower10`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

/--
A convenient lower bound for `432/π^2`, obtained by replacing `π` with the upper bound `piUpper10`.
-/
@[expose] public def cPiLower10 : ℝ := 432 / (piUpper10 ^ 2)

/-- The certified inequality `cPiLower10 ≤ 432/π^2`. -/
public lemma cPiLower10_le_cPi : cPiLower10 ≤ (432 / (Real.pi ^ 2) : ℝ) := by
  simpa [cPiLower10] using! cPiLower_le

/-- Positivity of the constant `cPiLower10`. -/
public lemma cPiLower10_pos : 0 < cPiLower10 := by
  have hpu0 : 0 < piUpper10 := by
    have : (0 : ℝ) < (3.1415926536 : ℝ) := by norm_num
    simpa [piUpper10_eq] using! this
  have hsq0 : 0 < piUpper10 ^ (2 : ℕ) := pow_pos hpu0 _
  have : (0 : ℝ) < 432 := by norm_num
  exact (div_pos this hsq0)

lemma psiS_num_it_re_nonpos (t : ℝ) (ht0 : 0 < t) :
    (psiS_num (it t ht0)).re ≤ 0 := by
  have hψS : (ψS (it t ht0)).re ≤ 0 := ψS_imagAxis_nonpos (t := t) ht0
  have hψ :
      ψS (it t ht0) = psiS_num (it t ht0) / (Δ (it t ht0)) ^ 2 := by
    simpa using! (psiS_eq_psiS_num_div_Delta_sq (z := it t ht0))
  have hΔpos : 0 < (Δ (it t ht0)).re := Delta_it_re_pos (t := t) ht0
  have hdpos : 0 < (Δ (it t ht0)).re ^ (2 : ℕ) := pow_pos hΔpos _
  have hΔim : (Δ (it t ht0)).im = 0 := by simp
  have hψim : (psiS_num (it t ht0)).im = 0 := psiS_num_it_im (t := t) ht0
  set a : ℝ := (psiS_num (it t ht0)).re
  set d : ℝ := (Δ (it t ht0)).re ^ 2
  have hψeq : psiS_num (it t ht0) = (a : ℂ) := by
    dsimp [a]
    refine Complex.ext ?_ ?_ <;> simp [hψim]
  have hΔ2 : (Δ (it t ht0)) ^ 2 = (d : ℂ) := by
    dsimp [d]
    have hΔeq : Δ (it t ht0) = ((Δ (it t ht0)).re : ℂ) := by
      refine Complex.ext ?_ ?_
      · simp
      · simp [hΔim]
    -- Square both sides; `((x : ℂ)^2) = (x^2 : ℂ)` for real `x`.
    calc
      (Δ (it t ht0)) ^ 2 = (((Δ (it t ht0)).re : ℂ)) ^ 2 :=
        congrArg (fun w : ℂ => w ^ (2 : ℕ)) hΔeq
      _ = (((Δ (it t ht0)).re ^ 2 : ℝ) : ℂ) := by simp
  have hre : (ψS (it t ht0)).re = a / d := by
    have hψ' : ψS (it t ht0) = (a : ℂ) / (d : ℂ) := by
      -- rewrite `ψS` via the numerator/denominator description, then normalize to `ofReal`s
      calc
        ψS (it t ht0) = psiS_num (it t ht0) / (Δ (it t ht0)) ^ 2 := hψ
        _ = (a : ℂ) / (d : ℂ) := by simp [hψeq, hΔ2]
    have hre_div : ((a : ℂ) / (d : ℂ)).re = a / d := by
      norm_num
    calc
      (ψS (it t ht0)).re = ((a : ℂ) / (d : ℂ)).re := by simp [hψ']
      _ = a / d := hre_div
  have hdpos' : 0 < d := by simpa [d] using! hdpos
  have hfrac : a / d ≤ 0 := by simpa [hre] using! hψS
  have ha : a ≤ 0 := by
    have := (div_le_iff₀ hdpos').1 hfrac
    simpa using! this
  simpa [a] using! ha

lemma re_mul_ofReal_of_im_eq_zero (c : ℝ) (w : ℂ) (hw : w.im = 0) :
    (((c : ℂ) * w).re) = c * w.re := by
  -- `w.im = 0` and `(c : ℂ).im = 0`.
  simp [Complex.mul_re, hw]

lemma cPi_complex_eq_ofReal :
    (432 / (Real.pi ^ 2) : ℂ) = ((432 / (Real.pi ^ 2) : ℝ) : ℂ) := by
  norm_num

/--
Monotonicity step: replace `432/π^2` by the smaller constant `cPiLower10` in a numerator
lower bound.

This is valid because `psiS_num (it t)` is real and nonpositive on the imaginary axis.
-/
public lemma ineq2_num_it_re_ge_cPiLower10 (t : ℝ) (ht : 1 ≤ t) :
    (varphi_num (it t (lt_of_lt_of_le (by norm_num) ht))
          - (432 / (Real.pi ^ 2) : ℂ) * psiS_num (it t (lt_of_lt_of_le (by norm_num) ht))).re
      ≥
    (varphi_num (it t (lt_of_lt_of_le (by norm_num) ht))
          - (cPiLower10 : ℂ) * psiS_num (it t (lt_of_lt_of_le (by norm_num) ht))).re := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  set z : ℍ := it t ht0
  have hψ : (psiS_num z).re ≤ 0 := psiS_num_it_re_nonpos (t := t) ht0
  have hψim : (psiS_num z).im = 0 := psiS_num_it_im (t := t) ht0
  have hvim : (varphi_num z).im = 0 := varphi_num_it_im (t := t) ht0
  have hc : cPiLower10 ≤ (432 / (Real.pi ^ 2) : ℝ) := cPiLower10_le_cPi
  have hmain :
      (varphi_num z).re - (432 / (Real.pi ^ 2) : ℝ) * (psiS_num z).re ≥
        (varphi_num z).re - cPiLower10 * (psiS_num z).re := by
    -- If `ψ ≤ 0` and `c0 ≤ c1`, then `-c1*ψ ≥ -c0*ψ`.
    nlinarith [hψ, hc]
  have hreπ :
      (varphi_num z - (432 / (Real.pi ^ 2) : ℂ) * psiS_num z).re =
        (varphi_num z).re - (432 / (Real.pi ^ 2) : ℝ) * (psiS_num z).re := by
    have hmul :
        (((432 / (Real.pi ^ 2) : ℂ) * psiS_num z).re) =
          (432 / (Real.pi ^ 2) : ℝ) * (psiS_num z).re := by
      -- Rewrite the coefficient as a real scalar cast to `ℂ`, then use the `im = 0` hypothesis.
      rw [cPi_complex_eq_ofReal]
      exact re_mul_ofReal_of_im_eq_zero (c := (432 / (Real.pi ^ 2) : ℝ)) (w := psiS_num z) hψim
    -- now expand `(a - b).re`
    simp [Complex.sub_re, hmul]
  have hre0 :
      (varphi_num z - (cPiLower10 : ℂ) * psiS_num z).re =
        (varphi_num z).re - cPiLower10 * (psiS_num z).re := by
    have hmul :
        (((cPiLower10 : ℂ) * psiS_num z).re) = cPiLower10 * (psiS_num z).re :=
      re_mul_ofReal_of_im_eq_zero (c := cPiLower10) (w := psiS_num z) hψim
    simp [Complex.sub_re, hmul]
  -- `hvim` isn't needed after the rewrite, but keep it in the context for robustness.
  simpa [hreπ, hre0, z] using! hmain

end SpherePacking.Dim24
