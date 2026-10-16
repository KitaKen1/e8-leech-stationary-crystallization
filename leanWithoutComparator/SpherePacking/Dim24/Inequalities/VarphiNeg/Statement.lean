module
public import SpherePacking.Dim24.ModularForms.Psi.Defs
public import SpherePacking.Dim24.ModularForms.Varphi
import SpherePacking.Dim24.Inequalities.VarphiNeg.GeOne.Negativity
import SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Negativity


/-!
# Negativity of `varphi(it)`

Negativity of `varphi(it)` for all `t > 0` (Appendix A, Lemma `phinonpos`).

## Main statements
* `varphi_imagAxis_neg`
-/

namespace SpherePacking.Dim24

/-- Negativity of `varphi(it)` for all `t > 0` (Lemma A.1 / `lemma:phinonpos` in `dim_24.tex`). -/
public theorem varphi_imagAxis_neg (t : ℝ) (ht : 0 < t) :
    (varphi (it t ht)).re < 0 := by
  by_cases h : 1 ≤ t
  · exact varphi_imagAxis_neg_ge_one (t := t) (ht0 := ht) h
  · exact varphi_imagAxis_neg_le_one (t := t) (ht0 := ht) (le_of_not_ge h)

end SpherePacking.Dim24
