-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
import Mathlib.Tactic.Positivity
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.DenomReduction.Numerators
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds


/-!
# Denominator reduction via `Δ(it).re^2`

Appendix A first bounds the numerator
`(varphi_num (it t) - (432/π^2) * psiS_num (it t)).re`,
then divides by `Δ(it).re ^ 2` using the estimate `Δ(it).re ^ 2 ≤ 1`.
This file isolates that reduction step.

## Main statements
* `ineq2_lowerBound_of_num`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

/--
Denominator reduction: a lower bound on the numerator real part implies the same lower bound for
`(varphi - (432/π^2) * ψS).re` on the imaginary axis.
-/
public theorem ineq2_lowerBound_of_num {t : ℝ} (ht0 : 0 < t) {L : ℝ}
    (hL : 0 ≤ L)
    (hnum :
      L ≤ (varphi_num (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * psiS_num (it t ht0)).re) :
    L ≤ (varphi (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * ψS (it t ht0)).re := by
  set d : ℝ := (Δ (it t ht0)).re ^ 2
  have hdpos : 0 < d := by
    have hΔpos : 0 < (Δ (it t ht0)).re := Delta_it_re_pos (t := t) ht0
    simpa [d] using! pow_pos hΔpos 2
  have hdle : d ≤ 1 := by
    simpa [d] using! (Delta_it_re_sq_le_one (t := t) ht0)
  have hinv_ge_one : (1 : ℝ) ≤ 1 / d := by
    simpa using! (one_div_le_one_div_of_le hdpos hdle)
  have hL' : L ≤ L * (1 / d) := by
    simpa [mul_one] using! (mul_le_mul_of_nonneg_left hinv_ge_one hL)
  have hnum' :
      L * (1 / d) ≤
        (varphi_num (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * psiS_num (it t ht0)).re * (1 / d) :=
    mul_le_mul_of_nonneg_right hnum (by positivity)
  have hdiv :
      (varphi (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * ψS (it t ht0)).re =
        (varphi_num (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * psiS_num (it t ht0)).re / d := by
    simpa [d] using! (ineq2_num_it_re_eq (t := t) (ht0 := ht0))
  have : L ≤
      (varphi_num (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * psiS_num (it t ht0)).re / d := by
    rw [div_eq_mul_one_div]
    linarith
  simpa [hdiv] using! this

end SpherePacking.Dim24
