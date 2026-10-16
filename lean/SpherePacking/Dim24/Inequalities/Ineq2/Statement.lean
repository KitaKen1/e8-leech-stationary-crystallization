module
public import SpherePacking.Dim24.ModularForms.Psi.Defs
public import SpherePacking.Dim24.ModularForms.Varphi
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.NumTruncBound
import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.Positivity


/-!
# Positivity statement for Lemma `ineq2`

This file combines the `t ≥ 1` and `t ≤ 1` cases of Appendix A, Lemma `ineq2` to show that, for all
`t > 0`, the real part of
`varphi (it t) - (432 / Real.pi ^ 2) * ψS (it t)` is strictly positive.

## Main statements
* `ineq2_imagAxis`
-/

namespace SpherePacking.Dim24

/-- Positivity of `varphi (it t) - (432 / Real.pi ^ 2) * ψS (it t)` for all `t > 0`
(Appendix A, Lemma `ineq2`). -/
public theorem ineq2_imagAxis (t : ℝ) (ht : 0 < t) :
    0 < (varphi (it t ht) - (432 / (Real.pi ^ 2) : ℂ) * ψS (it t ht)).re := by
  by_cases h : 1 ≤ t
  · exact ineq2_imagAxis_ge_one (t := t) (ht0 := ht) h
  · exact ineq2_imagAxis_le_one (t := t) (ht0 := ht) (le_of_not_ge h)

end SpherePacking.Dim24
