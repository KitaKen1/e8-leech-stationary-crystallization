module
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
public import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.AbsBoundQ
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.List.GetD
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.NormNum

/-!
# Truncation polynomial for `ineq2` (`1 ≤ t` case)

We reuse the cached coefficient list `AppendixA.ineq2_trunc_geOne_coeffs` to define the polynomial
`ineq2_trunc_geOne`.

The auxiliary rational constant `Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q` is a uniform lower bound
for the tail polynomial on `0 ≤ x ≤ 1/23`, used later in the positivity check for
`ineq2_trunc_geOne.eval₂ _ (r t) - eps * (r t)^12`.

## Main definitions
* `ineq2_trunc_geOne`
* `Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q`

## Main statements
* `Ineq2GeOneTruncAux.ineq2_trunc_geOne_c0Q_pos`
* `Ineq2GeOneTruncAux.one_div_25_lt_ineq2_trunc_geOne_c0Q`
-/

noncomputable section

namespace SpherePacking.Dim24

/-- Truncated polynomial approximation for the inequality in the `t ≥ 1` case.
Paper reference: Appendix A, proof of Lemma `ineq2`, first case. -/
@[expose]
public noncomputable def ineq2_trunc_geOne : Polynomial ℚ :=
  AppendixA.ineq2_trunc_geOne

namespace Ineq2GeOneTruncAux

open AppendixA

/-- A rational lower bound for the tail polynomial on `0 ≤ x ≤ 1/23` (constant term minus tail). -/
@[expose]
public def ineq2_trunc_geOne_c0Q : ℚ :=
  -- `ineq2_trunc_geOne_coeffs = 0 + ... + a₅ X⁵ + X⁶*(...)`.
  (ineq2_trunc_geOne_coeffs.getD 5 0) -
    BleadingCoeffs.cQ * absBoundQ (ineq2_trunc_geOne_coeffs.drop 6) BleadingCoeffs.cQ

/-- Positivity of the lower bound constant `ineq2_trunc_geOne_c0Q`. -/
public lemma ineq2_trunc_geOne_c0Q_pos : 0 < ineq2_trunc_geOne_c0Q := by
  -- Closed rational inequality; `decide` does not reduce far enough on this toolchain.
  set_option maxRecDepth 20000 in
  norm_num [ineq2_trunc_geOne_c0Q, absBoundQ, BleadingCoeffs.cQ, ineq2_trunc_geOne_coeffs]

/-- Convenient explicit bound: `1/25 < ineq2_trunc_geOne_c0Q`. -/
public lemma one_div_25_lt_ineq2_trunc_geOne_c0Q : (1 : ℚ) / 25 < ineq2_trunc_geOne_c0Q := by
  set_option maxRecDepth 20000 in
  norm_num [ineq2_trunc_geOne_c0Q, absBoundQ, BleadingCoeffs.cQ, ineq2_trunc_geOne_coeffs]

end SpherePacking.Dim24.Ineq2GeOneTruncAux
