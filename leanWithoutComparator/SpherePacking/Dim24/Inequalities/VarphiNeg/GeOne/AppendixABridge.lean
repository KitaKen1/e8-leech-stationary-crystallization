module
public import SpherePacking.Dim24.Inequalities.VarphiNeg.GeOne.Defs
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.QSeriesHelpers
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Numerators


/-!
# Appendix A bridge

Bridge lemmas between the `VarphiNegGeOne` local model and Appendix A's definitions.

Appendix A contains canonical definitions for `varphi_num`, `q`, and the coefficient function
`coeffVarphiNum`. This file records definitional/rewriting facts so the `VarphiNegGeOne` files can
reuse Appendix A lemmas without duplicating the same constructions.
-/

noncomputable section

namespace SpherePacking.Dim24.VarphiNegGeOne

open AppendixA
open UpperHalfPlane

/-- Rewrite lemma identifying Appendix A's `varphi_num` with `VarphiNegGeOne.varphi_num`. -/
public lemma appendixA_varphi_num_eq (z : ℍ) : AppendixA.varphi_num z = varphi_num z := by
  rfl

/-- Rewrite lemma identifying Appendix A's `q` with `VarphiNegGeOne.q`. -/
public lemma appendixA_q_eq (t : ℝ) : AppendixA.q t = q t := by
  rfl

private lemma appendixA_conv_fun_eq : AppendixA.conv = conv := by
  rfl

private lemma appendixA_coeffE2_fun_eq : AppendixA.coeffE2 = coeffE2 := by
  rfl

private lemma appendixA_coeffE4_fun_eq : AppendixA.coeffE4 = coeffE4 := by
  rfl

private lemma appendixA_coeffE6_fun_eq : AppendixA.coeffE6 = coeffE6 := by
  rfl

private lemma appendixA_coeffE2Sq_fun_eq : AppendixA.coeffE2Sq = coeffE2Sq := by rfl

private lemma appendixA_coeffE4Sq_fun_eq : AppendixA.coeffE4Sq = coeffE4Sq := by rfl

private lemma appendixA_coeffE4Cube_fun_eq : AppendixA.coeffE4Cube = coeffE4Cube := by rfl

private lemma appendixA_coeffE4Fourth_fun_eq : AppendixA.coeffE4Fourth = coeffE4Fourth := by rfl

private lemma appendixA_coeffE6Sq_fun_eq : AppendixA.coeffE6Sq = coeffE6Sq := by rfl

/-- Rewrite lemma identifying Appendix A's `coeffVarphiNum` with `VarphiNegGeOne.coeffVarphiNum`. -/
public lemma appendixA_coeffVarphiNum_eq (n : ℕ) :
    AppendixA.coeffVarphiNum n = coeffVarphiNum n := by
  -- The two definitions differ only by the helper `coeffLin`.
  simp [AppendixA.coeffVarphiNum, coeffVarphiNum, coeffLin_eq_lincomb,
    appendixA_conv_fun_eq, appendixA_coeffE2Sq_fun_eq, appendixA_coeffE4Fourth_fun_eq,
    appendixA_coeffE6Sq_fun_eq, appendixA_coeffE4Cube_fun_eq, appendixA_coeffE4Sq_fun_eq,
    appendixA_coeffE2_fun_eq, appendixA_coeffE4_fun_eq, appendixA_coeffE6_fun_eq]

end SpherePacking.Dim24.VarphiNegGeOne
