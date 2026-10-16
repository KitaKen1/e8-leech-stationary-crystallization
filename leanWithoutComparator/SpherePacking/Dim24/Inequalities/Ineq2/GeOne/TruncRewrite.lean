module
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2PsiSnum.PsiSnumCoeffs.Bounds
import Mathlib.Tactic.NormNum
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Monotonicity
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2PsiSnum.PsiSnumCoeffs.Cert
import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumCert.VerifyH4H2

/-!
# Truncation polynomial rewrite (t ≥ 1)

This file uses the certified coefficient identity from `SpherePacking.Dim24.Ineq2GeOneCoeffs` to
rewrite the truncation polynomial `ineq2_trunc_geOne` as the difference of the `varphi` truncation
(in the variable `q = r^2`) and `cPiLower10` times a finite `r`-sum `psiSnum_trunc_eval` built from
the first `N = 100` coefficients of `psiS_num`.

## Main definitions
* `psiSnum_trunc_eval`

## Main statements
* `psiSnum_trunc_eval_eq_sum_coeffFun`
-/

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

private lemma piUpper10Q_cast : (Ineq2GeOneCoeffs.piUpper10Q : ℝ) = piUpper10 := by
  -- Same rational number, coerced to `ℝ` in two ways.
  norm_num [Ineq2GeOneCoeffs.piUpper10Q, piUpper10]

/-- Identify the rational constant `Ineq2GeOneCoeffs.cPiLower10Q` with the real constant
`cPiLower10`. -/
public lemma cPiLower10Q_cast : (Ineq2GeOneCoeffs.cPiLower10Q : ℝ) = cPiLower10 := by
  simp [Ineq2GeOneCoeffs.cPiLower10Q, cPiLower10, piUpper10Q_cast]

/-- The truncated `r`-series sum for `psiS_num`, using the coefficient table
`Ineq2GeOneCoeffs.psiSnumCoeffs` and truncation length `N = 100`. -/
@[expose] public def psiSnum_trunc_eval (t : ℝ) : ℝ :=
  Finset.sum (Finset.range Ineq2GeOneCoeffs.N) fun n =>
    ((Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 : ℚ) : ℝ) * (r t) ^ n

private lemma psiSnumCoeff_eq_cert_getD (n : ℕ) (hn : n < Ineq2GeOneCoeffs.N) :
    Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 = Ineq2PsiSnum.psiSnumCoeffFun n :=
  (congrArg (fun l : List ℤ => l.getD n 0) Ineq2PsiSnum.psiSnumCoeffs_calc_eq_cert).symm.trans
      (Ineq2PsiSnum.psiSnumCoeffs_calc_getD_eq (n := n) hn)

/-- Rewrite `psiSnum_trunc_eval` as a finite sum using the coefficient function
`Ineq2PsiSnum.psiSnumCoeffFun`, via the certificate `Ineq2PsiSnum.psiSnumCoeffs_calc_eq_cert`. -/
public lemma psiSnum_trunc_eval_eq_sum_coeffFun (t : ℝ) :
    psiSnum_trunc_eval (t := t) =
      ∑ n ∈ Finset.range Ineq2GeOneCoeffs.N, (Ineq2PsiSnum.psiSnumCoeffFun n : ℝ) * (r t) ^ n := by
  -- Expand `psiSnum_trunc_eval` and rewrite the coefficients using the certificate.
  unfold psiSnum_trunc_eval
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hcoeff :
      ((Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 : ℚ) : ℝ) =
        (Ineq2PsiSnum.psiSnumCoeffFun n : ℝ) := by
    exact_mod_cast
      psiSnumCoeff_eq_cert_getD (n := n) (Finset.mem_range.1 hn)
  rw [hcoeff]

end SpherePacking.Dim24
