/-
Computational certificate (Appendix A): `Bleading_trunc_coeffs` matches the coefficientwise
`LowerBound` construction from `BLeadingCoeffs.lean`.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffQTableRewrites
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Phi2CoreTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Phi1CoreTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.DeltaHatSqTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.VarphiTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffMatchingLemmas
import Mathlib.Tactic.FinCases


/-!
### Certificate for the PARI/GP-style truncation procedure

This file provides `simp` lemmas that rewrite the coefficientwise `LowerBound` construction
(implemented in `BLeadingCoeffs.lean`) to the computable `_Num` variants backed by explicit tables.

The main result is a `fin_cases`/`decide` certificate identifying `Bleading_trunc_coeffs.getD` with
the closed-form coefficient formula.
-/


namespace SpherePacking.Dim24.AppendixA

open scoped BigOperators

-- The pretty-printed form of `List.getD` is `l[n]?.getD d`; we add a helper rewrite lemma so that
-- the `ψI` table lemma can fire under this notation.
/-- Rewrite the `get?`/`getD` notation for `psiInumCoeffs` to the explicit coefficient table. -/
@[simp] public lemma psiInumCoeffs_get?_getD_eq (n : ℕ) :
    (BleadingCoeffs.psiInumCoeffs[n]?).getD 0 = psiInumCoeffs_table.getD n 0 := by
  simpa [List.getD] using! (psiInumCoeffs_getD_eq (n := n))

namespace BleadingCoeffs


/-- Rewrite `Akeep` to its computable `_Num` definition. -/
@[simp] public lemma Akeep_eq_AkeepNum (i : ℕ) : Akeep i = AkeepNum i := by
  simpa using! (AkeepNum_eq_Akeep i).symm

/-- Rewrite `Ashift` to its computable `_Num` definition. -/
@[simp] public lemma Ashift_eq_AshiftNum (i : ℕ) : Ashift i = AshiftNum i := by
  simpa using! (AshiftNum_eq_Ashift i).symm

/-- Rewrite `Bkeep` to its computable `_Num` definition. -/
@[simp] public lemma Bkeep_eq_BkeepNum (i : ℕ) : Bkeep i = BkeepNum i := by
  simpa using! (BkeepNum_eq_Bkeep i).symm

/-- Rewrite `Bshift` to its computable `_Num` definition. -/
@[simp] public lemma Bshift_eq_BshiftNum (i : ℕ) : Bshift i = BshiftNum i := by
  simpa using! (BshiftNum_eq_Bshift i).symm

/-- Rewrite `Ckeep` to its computable `_Num` definition. -/
@[simp] public lemma Ckeep_eq_CkeepNum (i : ℕ) : Ckeep i = CkeepNum i := by
  simpa using! (CkeepNum_eq_Ckeep i).symm

/-!
### Length lemma for `powQ`

We use this to show out-of-range coefficients (`n ≥ QN`) of any `powQ`-constructed list are `0`.
-/

lemma length_powQ (a : List ℚ) (k : ℕ) : (powQ a k).length = QN := by
  cases k <;> simp [powQ, mulQ, QN]

/-!
### Table rewrites for `coeffQ` on the `q`-series lists

We expose them as `simp` lemmas with an `if` guard, so that for concrete indices the guard reduces
by computation.
-/

/-- Rewrite `coeffQ DeltaSqQ n` to the explicit integer table (with an `if n < QN` guard). -/
@[simp] public lemma coeffQ_DeltaSqQ_eq_table (n : ℕ) :
    coeffQ DeltaSqQ n =
      if n < QN then
        (deltaHatSqCoeffsZ_table.getD n 0 : ℚ) * ((1 : ℚ) / (1728 ^ (2 : ℕ)))
      else 0 := by
  by_cases hn : n < QN
  · simpa [hn] using!
      (SpherePacking.Dim24.AppendixA.coeffQ_DeltaSqQ_eq (n := n) hn).trans
        (coeffDeltaSq_eq_table (n := n) (hn := by simpa using! hn))
  · have hlen : DeltaSqQ.length = QN := by
      simpa [DeltaSqQ, QN] using! (length_powQ (a := DeltaQ) 2)
    have : DeltaSqQ.length ≤ n := by simpa [hlen] using! Nat.le_of_not_gt hn
    have hzero : coeffQ DeltaSqQ n = 0 := by
      simpa [coeffQ] using! List.getD_eq_default (l := DeltaSqQ) (d := (0 : ℚ)) (n := n) this
    simp [hn, hzero]

end BleadingCoeffs

/-!
### Main certificate: `Bleading_trunc_coeffs` matches the `LowerBound` coefficient formula
-/

-- Prevent rewriting integer-numerator sign tests back into rational order tests.
attribute [-simp] Rat.num_nonneg Rat.num_neg in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in -- This `fin_cases`/`decide` certificate is expensive.
/-- Certificate: `Bleading_trunc_coeffs.getD` agrees with the closed-form coefficient formula. -/
public lemma Bleading_trunc_coeffs_getD_eq_formula (k : Fin BleadingCoeffs.N) :
    Bleading_trunc_coeffs.getD k.1 0 =
      BleadingCoeffs.Akeep k.1 +
        (if k.1 + 2 < BleadingCoeffs.N then BleadingCoeffs.Ashift (k.1 + 2) else 0) +
        BleadingCoeffs.Bkeep k.1 +
          (if k.1 + 1 < BleadingCoeffs.N then BleadingCoeffs.Bshift (k.1 + 1) else 0) +
          BleadingCoeffs.Ckeep k.1 := by
  fin_cases k <;>
    -- Avoid `simp` on the whole goal (it can rewrite `a*b = 0` into a disjunction);
    -- instead simplify LHS/RHS in place and then close the resulting ground equality by `decide`.
    (conv_lhs => simp [Bleading_trunc_coeffs]
     conv_rhs =>
        simp (config := { maxSteps := 2000000 })
          [BleadingCoeffs.AkeepNum, BleadingCoeffs.AshiftNum, BleadingCoeffs.BkeepNum,
            BleadingCoeffs.BshiftNum, BleadingCoeffs.CkeepNum, BleadingCoeffs.piForANum,
            BleadingCoeffs.invPiForCNum, BleadingCoeffs.choosePiNum, BleadingCoeffs.chooseInvPiNum,
            BleadingCoeffs.Acoeff, BleadingCoeffs.Bcoeff, BleadingCoeffs.Ccoeff,
            BleadingCoeffs.isEven, BleadingCoeffs.qIdx, BleadingCoeffs.deltaIdx,
            BleadingCoeffs.piDiv, BleadingCoeffs.invPiDiv, BleadingCoeffs.phi2Scale,
            BleadingCoeffs.phi1Scale, BleadingCoeffs.leadTScale, BleadingCoeffs.leadInvPiScale,
            BleadingCoeffs.cQ, BleadingCoeffs.N, BleadingCoeffs.QN, BleadingCoeffs.piLower10Q,
            BleadingCoeffs.piUpper10Q, BleadingCoeffs.invPiLower10Q, BleadingCoeffs.invPiUpper10Q,
            varphiNumCoeffsZ_table, phi1CoreCoeffsZ_table, phi2CoreCoeffsZ_table,
            deltaHatSqCoeffsZ_table, psiInumCoeffs_table, psiInumCoeffs_getD_eq,
            psiInumCoeffs_get?_getD_eq, Rat.add_def', Rat.mul_eq_mkRat, Rat.sub_def', Rat.inv_def,
            Rat.div_def', Rat.pow_def]
     decide)

end SpherePacking.Dim24.AppendixA
