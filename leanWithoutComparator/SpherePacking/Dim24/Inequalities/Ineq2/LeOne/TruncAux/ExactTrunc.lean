module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.CoeffModel
public import SpherePacking.Dim24.Inequalities.AppendixA.RBounds
public import Mathlib.Analysis.Real.Pi.Bounds


/-!
# Exact truncation for `ineq2_num` (`t ≤ 1` case)

This file defines the explicit degree-99 truncation used in the `t ≤ 1` case of Appendix A, Lemma
`ineq2`, after clearing the denominator `Δ(it)^2`.

The coefficient at degree `i` is the real number `ineq2_exact_coeff t i`, built from the rational
tables `CoeffModel.A0`, `CoeffModel.B0`, `CoeffModel.C0` by inserting the factors `t^2`, `t / pi`,
and `1 / pi^2`. The truncation sum is `ineq2_exact_trunc t`.

## Main definitions
* `ExactTrunc.ineq2_exact_coeff`
* `ExactTrunc.ineq2_exact_trunc`
-/


open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open CoeffModel

namespace ExactTrunc

/-- The exact degree-99 truncation coefficient used in Appendix A for the `ineq2` numerator
(after clearing `Δ(it)^2`). -/
@[expose]
public def ineq2_exact_coeff (t : ℝ) (i : ℕ) : ℝ :=
  (A0 i : ℝ) * t ^ (2 : ℕ)
    + (B0 i : ℝ) * t * (1 / Real.pi)
    + (C0 i : ℝ) * (1 / Real.pi) ^ (2 : ℕ)

/-- The exact degree-99 truncation sum built from `ineq2_exact_coeff` and the variable `r(t)`. -/
@[expose]
public def ineq2_exact_trunc (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range CoeffModel.N, ineq2_exact_coeff t i * (AppendixA.r t) ^ i

end SpherePacking.Dim24.Ineq2LeOneTruncAux.ExactTrunc
