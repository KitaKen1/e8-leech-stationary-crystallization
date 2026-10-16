module
public import Mathlib.Algebra.Polynomial.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.Ineq2TruncLeOneCoeffsRigor
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.CoeffsVarphi
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.CoeffsIneq2
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.CoeffsBleading


/-!
Truncation polynomials from explicit coefficient lists.

This file defines `polyOfCoeffs`, which turns a coefficient list `[a₀, a₁, ...]` into the
polynomial `∑ aₙ X^n`, and instantiates the core truncation polynomials used in Appendix A
(`varphi_trunc_geOne`, `varphi_trunc_leOne`, `ineq2_trunc_geOne`, `ineq2_trunc_leOne`,
`Bleading_trunc`).
-/

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- Build a polynomial `∑ a_n X^n` from a coefficient list `[a₀, a₁, ...]`. -/
@[expose]
public def polyOfCoeffs : List ℚ → Polynomial ℚ
  | [] => 0
  | a :: l => Polynomial.C a + Polynomial.X * polyOfCoeffs l

/-- Truncation polynomial for `varphi` used in the `t ≥ 1` part of Appendix A. -/
@[expose]
public noncomputable def varphi_trunc_geOne : Polynomial ℚ :=
  polyOfCoeffs varphi_trunc_geOne_coeffs

/-- Truncation polynomial for `varphi` used in the `t ≤ 1` part of Appendix A. -/
@[expose]
public noncomputable def varphi_trunc_leOne : Polynomial ℚ :=
  polyOfCoeffs varphi_trunc_leOne_coeffs

/-- Truncation polynomial for `ineq2` used in the `t ≥ 1` part of Appendix A. -/
@[expose]
public noncomputable def ineq2_trunc_geOne : Polynomial ℚ :=
  polyOfCoeffs ineq2_trunc_geOne_coeffs

/-- Truncation polynomial for `ineq2` used in the `t ≤ 1` part of Appendix A. -/
@[expose]
public noncomputable def ineq2_trunc_leOne : Polynomial ℚ :=
  polyOfCoeffs ineq2_trunc_leOne_coeffs

/-- Truncation polynomial for `Bleading` used in Appendix A (Lemma `Bleadingterms`). -/
@[expose]
public noncomputable def Bleading_trunc : Polynomial ℚ :=
  polyOfCoeffs Bleading_trunc_coeffs

end

end SpherePacking.Dim24.AppendixA
