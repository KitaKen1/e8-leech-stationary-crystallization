/-
Coefficient model and truncation-polynomial evaluation for the `t ≤ 1` case.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.EvenReindex
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.SeriesSplit
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffMatchingLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffQTableRewrites
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.VarphiTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Phi1CoreTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Phi2CoreTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.VarphiQSeries
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
Coefficient model for the `t ≤ 1` truncation inequality.

This file packages the explicit coefficient model used to compare the PARI/GP truncation
polynomial `varphi_trunc_leOne` against an exact finite head of the `q`-series. The main output is
the rewrite lemma `trunc_eval₂_eq_sum_range_formula`, which expands
`((-varphi_trunc_leOne).eval₂ _ (r t))` as a finite sum of the computable coefficients
`truncCoeffFormula`.

### Computable variants (avoid `<`/`≤` on `ℚ`)

Kernel reduction does not unfold `Rat.blt`, so order tests on `ℚ` do not reduce. We therefore
provide `*_Num` variants that branch on integer numerator comparisons.
-/
open scoped BigOperators

namespace SpherePacking.Dim24.AppendixA

noncomputable section

namespace VarphiLeOne

open BleadingCoeffs

/-
### Coefficient model for the truncation polynomial

We follow `appendix.txt` with:
`c = 1/23`, `tLower = 1`, `tUpper = 1/(23*r)`, and 10-digit bounds for `1/π`.

After substituting `tUpper`, terms with a factor of `t` (resp. `t^2`) shift down by one (resp. two)
powers of `r`, since `tUpper * r = 1/23`.
-/

/-- Coefficient model `A(i)` for the `varphi` numerator term (odd indices vanish). -/
@[expose] public def Acoeff (i : ℕ) : ℚ :=
  if i % 2 = 0 then -coeffQ phinumQ (i / 2) else 0

lemma varphiNumCoeffsZ_table_getD_nonpos_fin :
    ∀ n : Fin BleadingCoeffs.QN, (varphiNumCoeffsZ_table.getD n.1 0 : ℚ) ≤ 0 := by
  intro n; fin_cases n <;> simp [varphiNumCoeffsZ_table]

set_option backward.isDefEq.respectTransparency false in
/-- Nonnegativity of `Acoeff` on the range `i < BleadingCoeffs.N`. -/
public lemma Acoeff_nonneg_fin : ∀ i : Fin BleadingCoeffs.N, 0 ≤ Acoeff i.1 := by
  intro i
  have hi_div : i.1 / 2 < BleadingCoeffs.QN := by
    have : i.1 < 2 * BleadingCoeffs.QN := by
      simp [BleadingCoeffs.N, BleadingCoeffs.QN]
    exact Nat.div_lt_of_lt_mul this
  by_cases hmod : i.1 % 2 = 0
  · have hcoeff :
        coeffQ phinumQ (i.1 / 2) = (varphiNumCoeffsZ_table.getD (i.1 / 2) 0 : ℚ) := by
      simp [BleadingCoeffs.coeffQ_phinumQ_eq_table, hi_div]
    have hnonpos : (coeffQ phinumQ (i.1 / 2)) ≤ 0 := by
      -- Reduce to the (precomputed) table and discharge by finite case split.
      have :=
        varphiNumCoeffsZ_table_getD_nonpos_fin (n := ⟨i.1 / 2, hi_div⟩)
      simpa [hcoeff] using! this
    -- `Acoeff` is `-coeffQ phinumQ (i/2)` for even indices.
    simpa [Acoeff, hmod] using! (neg_nonneg.2 hnonpos)
  · simp [Acoeff, hmod]

/-- Coefficient model `B(i)` for the `phi1` core term (odd indices vanish). -/
@[expose] public def Bcoeff (i : ℕ) : ℚ :=
  if i % 2 = 0 then (6 : ℚ) * coeffQ phi1CoreQ (i / 2) else 0

/-- Coefficient model `C(i)` for the `phi2` core term (odd indices vanish). -/
@[expose] public def Ccoeff (i : ℕ) : ℚ :=
  if i % 2 = 0 then (-36 : ℚ) * coeffQ phi2CoreQ (i / 2) else 0

/-- Choose a rational approximation to `1/π` suitable for bounding the `Bcoeff i` term. -/
@[expose] public def invPiForB (i : ℕ) : ℚ := chooseInvPi (Bcoeff i)

/-- Choose a rational approximation to `1/π^2` (via squaring) suitable for the `Ccoeff i` term. -/
@[expose] public def invPiSqForC (i : ℕ) : ℚ := (chooseInvPi (Ccoeff i)) ^ (2 : ℕ)

/-- Nonnegative part of `Acoeff` kept at the same power of `r`. -/
@[expose] public def Akeep (i : ℕ) : ℚ := if 0 ≤ Acoeff i then Acoeff i else 0

/-- Negative part of `Acoeff` shifted down by two powers of `r` (using the factor `cQ^2`). -/
@[expose] public def Ashift (i : ℕ) : ℚ :=
  if Acoeff i < 0 then (cQ ^ (2 : ℕ)) * Acoeff i else 0

/-- Nonnegative part of `Bcoeff` kept at the same power of `r` (including a `1/π` bound). -/
@[expose] public def Bkeep (i : ℕ) : ℚ := if 0 ≤ Bcoeff i then invPiForB i * Bcoeff i else 0

/-- Negative part of `Bcoeff` shifted down by one power of `r` (using the factor `cQ`). -/
@[expose] public def Bshift (i : ℕ) : ℚ :=
  if Bcoeff i < 0 then cQ * (invPiForB i * Bcoeff i) else 0

/-- Scaled `Ccoeff` using a rational upper/lower bound for `1/π^2`. -/
@[expose] public def Ckeep (i : ℕ) : ℚ := invPiSqForC i * Ccoeff i

/-- Numerator-based version of `invPiForB` (computable under kernel reduction). -/
@[expose] public def invPiForBNum (i : ℕ) : ℚ := chooseInvPiNum (Bcoeff i)

/-- Numerator-based version of `invPiSqForC` (computable under kernel reduction). -/
@[expose] public def invPiSqForCNum (i : ℕ) : ℚ := (chooseInvPiNum (Ccoeff i)) ^ (2 : ℕ)

/-- Numerator-based version of `Akeep`. -/
@[expose] public def AkeepNum (i : ℕ) : ℚ := if 0 ≤ (Acoeff i).num then Acoeff i else 0

/-- Numerator-based version of `Ashift`. -/
@[expose] public def AshiftNum (i : ℕ) : ℚ :=
  if (Acoeff i).num < 0 then cQ ^ 2 * Acoeff i else 0

/-- Numerator-based version of `Bkeep`. -/
@[expose] public def BkeepNum (i : ℕ) : ℚ :=
  if 0 ≤ (Bcoeff i).num then invPiForBNum i * Bcoeff i else 0

/-- Numerator-based version of `Bshift`. -/
@[expose] public def BshiftNum (i : ℕ) : ℚ :=
  if (Bcoeff i).num < 0 then cQ * (invPiForBNum i * Bcoeff i) else 0

/-- Numerator-based version of `Ckeep`. -/
@[expose] public def CkeepNum (i : ℕ) : ℚ := invPiSqForCNum i * Ccoeff i

lemma AkeepNum_eq_Akeep (i : ℕ) : AkeepNum i = Akeep i := by
  unfold AkeepNum Akeep
  by_cases h : 0 ≤ Acoeff i
  · have hnum : 0 ≤ (Acoeff i).num := (Rat.num_nonneg).2 h
    simp [h, hnum]
  · have hnum : ¬ 0 ≤ (Acoeff i).num := by
      intro hnum
      exact h ((Rat.num_nonneg).1 hnum)
    simp [h, hnum]

lemma AshiftNum_eq_Ashift (i : ℕ) : AshiftNum i = Ashift i := by
  unfold AshiftNum Ashift
  by_cases h : Acoeff i < 0
  · have hnum : (Acoeff i).num < 0 := (Rat.num_neg).2 h
    simp [h, hnum]
  · have hnum : ¬ (Acoeff i).num < 0 := by
      intro hnum
      exact h ((Rat.num_neg).1 hnum)
    simp [h, hnum]

lemma BkeepNum_eq_Bkeep (i : ℕ) : BkeepNum i = Bkeep i := by
  unfold BkeepNum Bkeep
  by_cases h : 0 ≤ Bcoeff i
  · have hnum : 0 ≤ (Bcoeff i).num := (Rat.num_nonneg).2 h
    simp [h, hnum, invPiForBNum, invPiForB, BleadingCoeffs.chooseInvPiNum_eq_chooseInvPi]
  · have hnum : ¬ 0 ≤ (Bcoeff i).num := by
      intro hnum
      exact h ((Rat.num_nonneg).1 hnum)
    simp [h, hnum]

lemma BshiftNum_eq_Bshift (i : ℕ) : BshiftNum i = Bshift i := by
  unfold BshiftNum Bshift
  by_cases h : Bcoeff i < 0
  · have hnum : (Bcoeff i).num < 0 := (Rat.num_neg).2 h
    simp [h, hnum, invPiForBNum, invPiForB, BleadingCoeffs.chooseInvPiNum_eq_chooseInvPi]
  · have hnum : ¬ (Bcoeff i).num < 0 := by
      intro hnum
      exact h ((Rat.num_neg).1 hnum)
    simp [h, hnum]

lemma CkeepNum_eq_Ckeep (i : ℕ) : CkeepNum i = Ckeep i := by
  simp [CkeepNum, Ckeep, invPiSqForCNum, invPiSqForC, BleadingCoeffs.chooseInvPiNum_eq_chooseInvPi]

/--
Coefficient formula for the truncation polynomial after splitting into keep/shift parts.

This is the explicit coefficient used in `trunc_eval₂_eq_sum_range_formula`.
-/
@[expose] public def truncCoeffFormula (k : ℕ) : ℚ :=
  Akeep k +
    (if k + 2 < BleadingCoeffs.N then Ashift (k + 2) else 0) +
      Bkeep k +
        (if k + 1 < BleadingCoeffs.N then Bshift (k + 1) else 0) +
          Ckeep k

/-- Computable (numerator-branching) version of `truncCoeffFormula`. -/
@[expose] public def truncCoeffFormulaNum (k : ℕ) : ℚ :=
  AkeepNum k +
    (if k + 2 < BleadingCoeffs.N then AshiftNum (k + 2) else 0) +
      BkeepNum k +
        (if k + 1 < BleadingCoeffs.N then BshiftNum (k + 1) else 0) +
          CkeepNum k

/-- The list of expected coefficients, defined as `List.ofFn truncCoeffFormula`. -/
@[expose] public def truncCoeffsExpected : List ℚ :=
  List.ofFn fun i : Fin BleadingCoeffs.N => truncCoeffFormula i.1

lemma truncCoeffsExpected_length : truncCoeffsExpected.length = BleadingCoeffs.N := by
  -- Avoid `simp` loops on `List.ofFn`.
  unfold truncCoeffsExpected
  exact List.length_ofFn (f := fun i : Fin BleadingCoeffs.N => truncCoeffFormula i.1)

lemma varphi_trunc_leOne_coeffs_length : varphi_trunc_leOne_coeffs.length = BleadingCoeffs.N := by
  decide

lemma invPiForBNum_eq_invPiForB (i : ℕ) : invPiForBNum i = invPiForB i := by
  simp [invPiForBNum, invPiForB, BleadingCoeffs.chooseInvPiNum_eq_chooseInvPi]

lemma invPiSqForCNum_eq_invPiSqForC (i : ℕ) : invPiSqForCNum i = invPiSqForC i := by
  simp [invPiSqForCNum, invPiSqForC, BleadingCoeffs.chooseInvPiNum_eq_chooseInvPi]

lemma truncCoeffFormulaNum_eq_truncCoeffFormula (k : ℕ) :
    truncCoeffFormulaNum k = truncCoeffFormula k := by
  simp [truncCoeffFormulaNum, truncCoeffFormula, AkeepNum_eq_Akeep, AshiftNum_eq_Ashift,
    BkeepNum_eq_Bkeep, BshiftNum_eq_Bshift, CkeepNum_eq_Ckeep]

lemma truncCoeffsExpected_getD_of_lt (k : ℕ) (hk : k < BleadingCoeffs.N) :
    truncCoeffsExpected.getD k 0 = truncCoeffFormula k := by
  -- Unfold `truncCoeffsExpected` as `List.ofFn`.
  let g : Fin BleadingCoeffs.N → ℚ := fun i => truncCoeffFormula i.1
  unfold truncCoeffsExpected
  have hlen : (List.ofFn g).length = BleadingCoeffs.N := List.length_ofFn (f := g)
  have hk' : k < (List.ofFn g).length := lt_of_lt_of_eq hk (Eq.symm hlen)
  let i : Fin (List.ofFn g).length := ⟨k, hk'⟩
  have hgetD : (List.ofFn g).getD k 0 = (List.ofFn g).get i := by
    change (List.ofFn g).getD (i : Nat) 0 = (List.ofFn g).get i
    exact List.getD_eq_get (l := List.ofFn g) (d := (0 : ℚ)) i
  rw [hgetD]
  rw [List.get_ofFn (f := g) (i := i)]
  simp [i, g]

@[simp] lemma truncCoeffsExpected_getD_eq (k : ℕ) :
    truncCoeffsExpected.getD k 0 = if k < BleadingCoeffs.N then truncCoeffFormula k else 0 := by
  by_cases hk : k < BleadingCoeffs.N
  · simpa [hk] using! truncCoeffsExpected_getD_of_lt (k := k) hk
  · rw [if_neg hk]
    have hk' : truncCoeffsExpected.length ≤ k := by
      have : BleadingCoeffs.N ≤ k := Nat.le_of_not_gt hk
      simpa [truncCoeffsExpected_length] using! this
    exact List.getD_eq_default (l := truncCoeffsExpected) (d := (0 : ℚ)) (n := k) hk'

@[simp] lemma List.get_eq_getD0 (l : List ℚ) (n : ℕ) (hn : n < l.length) :
    l.get ⟨n, hn⟩ = l.getD n 0 :=
  by simpa using! (List.getD_eq_get (l := l) (d := (0 : ℚ)) (i := ⟨n, hn⟩)).symm

-- Prevent rewriting integer-numerator sign tests back into rational order tests.
attribute [-simp] Rat.num_nonneg Rat.num_neg

macro "simp_varphi_coeff_goal" : tactic =>
  `(tactic|
    (simp only [AppendixA.varphi_trunc_leOne_coeffs, truncCoeffsExpected,
        truncCoeffsExpected_getD_eq, List.get_eq_getD0, List.getD_map,
        -- rewrite `ℚ`-order tests/choices to numerator comparisons
        ← invPiForBNum_eq_invPiForB, ← invPiSqForCNum_eq_invPiSqForC,
        ← truncCoeffFormulaNum_eq_truncCoeffFormula,
        truncCoeffFormulaNum, AkeepNum, AshiftNum, BkeepNum, BshiftNum, CkeepNum, invPiForBNum,
        invPiSqForCNum, Acoeff, Bcoeff, Ccoeff,
        BleadingCoeffs.chooseInvPiNum, BleadingCoeffs.invPiLower10Q, BleadingCoeffs.invPiUpper10Q,
        BleadingCoeffs.piLower10Q, BleadingCoeffs.piUpper10Q, BleadingCoeffs.N, BleadingCoeffs.QN,
        BleadingCoeffs.cQ, BleadingCoeffs.isEven, BleadingCoeffs.qIdx,
        BleadingCoeffs.coeffQ_phinumQ_eq_table, BleadingCoeffs.coeffQ_phi1CoreQ_eq_table,
        BleadingCoeffs.coeffQ_phi2CoreQ_eq_table, varphiNumCoeffsZ_table, phi1CoreCoeffsZ_table,
        phi2CoreCoeffsZ_table,
        Rat.add_def', Rat.sub_def', Rat.mul_eq_mkRat, Rat.div_def', Rat.inv_def, Rat.pow_def]
      ; decide))

macro "interval_simp_varphi_coeff_goal" x:ident "(" hlo:term "," hhi:term ")" : tactic =>
  `(tactic| (interval_cases $x using $hlo, $hhi <;> simp_varphi_coeff_goal))

set_option backward.isDefEq.respectTransparency false in
lemma varphi_coeffs_eq_expected_get_10_19 (n : ℕ)
    (hn1 : n < (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).length)
    (hn2 : n < truncCoeffsExpected.length) (hn1' : 10 ≤ n) (hn2' : n < 20) :
    (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).get ⟨n, hn1⟩ =
  truncCoeffsExpected.get ⟨n, hn2⟩ := by
  interval_simp_varphi_coeff_goal n (hn1', hn2')

set_option backward.isDefEq.respectTransparency false in
lemma varphi_coeffs_eq_expected_get_20_29 (n : ℕ)
    (hn1 : n < (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).length)
    (hn2 : n < truncCoeffsExpected.length) (hn1' : 20 ≤ n) (hn2' : n < 30) :
    (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).get ⟨n, hn1⟩ =
  truncCoeffsExpected.get ⟨n, hn2⟩ := by
  interval_simp_varphi_coeff_goal n (hn1', hn2')

set_option backward.isDefEq.respectTransparency false in
lemma varphi_coeffs_eq_expected_get_30_39 (n : ℕ)
    (hn1 : n < (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).length)
    (hn2 : n < truncCoeffsExpected.length) (hn1' : 30 ≤ n) (hn2' : n < 40) :
    (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).get ⟨n, hn1⟩ =
  truncCoeffsExpected.get ⟨n, hn2⟩ := by
  interval_simp_varphi_coeff_goal n (hn1', hn2')

set_option backward.isDefEq.respectTransparency false in
lemma varphi_coeffs_eq_expected_get_40_49 (n : ℕ)
    (hn1 : n < (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).length)
    (hn2 : n < truncCoeffsExpected.length) (hn1' : 40 ≤ n) (hn2' : n < 50) :
    (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).get ⟨n, hn1⟩ =
  truncCoeffsExpected.get ⟨n, hn2⟩ := by
  interval_simp_varphi_coeff_goal n (hn1', hn2')

set_option backward.isDefEq.respectTransparency false in
lemma varphi_coeffs_eq_expected_get_50_59 (n : ℕ)
    (hn1 : n < (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).length)
    (hn2 : n < truncCoeffsExpected.length) (hn1' : 50 ≤ n) (hn2' : n < 60) :
    (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).get ⟨n, hn1⟩ =
  truncCoeffsExpected.get ⟨n, hn2⟩ := by
  interval_simp_varphi_coeff_goal n (hn1', hn2')

set_option backward.isDefEq.respectTransparency false in
lemma varphi_coeffs_eq_expected_get_60_69 (n : ℕ)
    (hn1 : n < (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).length)
    (hn2 : n < truncCoeffsExpected.length) (hn1' : 60 ≤ n) (hn2' : n < 70) :
    (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).get ⟨n, hn1⟩ =
  truncCoeffsExpected.get ⟨n, hn2⟩ := by
  interval_simp_varphi_coeff_goal n (hn1', hn2')

set_option backward.isDefEq.respectTransparency false in
lemma varphi_coeffs_eq_expected_get_70_79 (n : ℕ)
    (hn1 : n < (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).length)
    (hn2 : n < truncCoeffsExpected.length) (hn1' : 70 ≤ n) (hn2' : n < 80) :
    (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).get ⟨n, hn1⟩ =
  truncCoeffsExpected.get ⟨n, hn2⟩ := by
  interval_simp_varphi_coeff_goal n (hn1', hn2')

set_option backward.isDefEq.respectTransparency false in
lemma varphi_coeffs_eq_expected_get_80_89 (n : ℕ)
    (hn1 : n < (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).length)
    (hn2 : n < truncCoeffsExpected.length) (hn1' : 80 ≤ n) (hn2' : n < 90) :
    (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).get ⟨n, hn1⟩ =
  truncCoeffsExpected.get ⟨n, hn2⟩ := by
  interval_simp_varphi_coeff_goal n (hn1', hn2')

set_option backward.isDefEq.respectTransparency false in
lemma varphi_coeffs_eq_expected_get_90_99 (n : ℕ)
    (hn1 : n < (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).length)
    (hn2 : n < truncCoeffsExpected.length) (hn1' : 90 ≤ n) (hn2' : n < 100) :
    (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).get ⟨n, hn1⟩ =
  truncCoeffsExpected.get ⟨n, hn2⟩ := by
  interval_simp_varphi_coeff_goal n (hn1', hn2')

set_option backward.isDefEq.respectTransparency false in
lemma varphi_coeffs_eq_expected_get (n : ℕ)
    (hn1 : n < (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).length)
    (hn2 : n < truncCoeffsExpected.length) :
    (varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a)).get ⟨n, hn1⟩ =
      truncCoeffsExpected.get ⟨n, hn2⟩ := by
  have hnN : n < BleadingCoeffs.N := by
    simpa [truncCoeffsExpected_length] using! hn2
  have hn100 : n < 100 := by simpa [BleadingCoeffs.N] using! hnN
  by_cases h10 : n < 10
  · -- `0 ≤ n` for `interval_cases`.
    have hn0 : 0 ≤ n := Nat.zero_le n
    interval_simp_varphi_coeff_goal n (hn0, h10)
  have h10' : 10 ≤ n := Nat.le_of_not_gt h10
  by_cases h20 : n < 20
  · exact varphi_coeffs_eq_expected_get_10_19 n hn1 hn2 h10' h20
  have h20' : 20 ≤ n := Nat.le_of_not_gt h20
  by_cases h30 : n < 30
  · exact varphi_coeffs_eq_expected_get_20_29 n hn1 hn2 h20' h30
  have h30' : 30 ≤ n := Nat.le_of_not_gt h30
  by_cases h40 : n < 40
  · exact varphi_coeffs_eq_expected_get_30_39 n hn1 hn2 h30' h40
  have h40' : 40 ≤ n := Nat.le_of_not_gt h40
  by_cases h50 : n < 50
  · exact varphi_coeffs_eq_expected_get_40_49 n hn1 hn2 h40' h50
  have h50' : 50 ≤ n := Nat.le_of_not_gt h50
  by_cases h60 : n < 60
  · exact varphi_coeffs_eq_expected_get_50_59 n hn1 hn2 h50' h60
  have h60' : 60 ≤ n := Nat.le_of_not_gt h60
  by_cases h70 : n < 70
  · exact varphi_coeffs_eq_expected_get_60_69 n hn1 hn2 h60' h70
  have h70' : 70 ≤ n := Nat.le_of_not_gt h70
  by_cases h80 : n < 80
  · exact varphi_coeffs_eq_expected_get_70_79 n hn1 hn2 h70' h80
  have h80' : 80 ≤ n := Nat.le_of_not_gt h80
  by_cases h90 : n < 90
  · exact varphi_coeffs_eq_expected_get_80_89 n hn1 hn2 h80' h90
  have h90' : 90 ≤ n := Nat.le_of_not_gt h90
  exact varphi_coeffs_eq_expected_get_90_99 n hn1 hn2 h90' hn100

lemma varphi_trunc_leOne_coeffs_map_neg_eq_expected :
    varphi_trunc_leOne_coeffs.map (fun a : ℚ => -a) = truncCoeffsExpected := by
  refine List.ext_get ?_ (fun n hn1 hn2 => ?_)
  · simp [varphi_trunc_leOne_coeffs_length, truncCoeffsExpected_length]
  · -- Discharge each concrete coefficient check by computation (`simp` + `decide`).
    simpa using! varphi_coeffs_eq_expected_get (n := n) hn1 hn2

lemma polyOfCoeffs_map_neg (l : List ℚ) :
    polyOfCoeffs (l.map (fun a => -a)) = -polyOfCoeffs l := by
  induction l with
  | nil => simp [polyOfCoeffs]
  | cons a l ih => simp [polyOfCoeffs, ih, add_comm]

/--
Rewrite the truncation polynomial evaluation as a finite sum over `truncCoeffFormula`.

This turns `(-varphi_trunc_leOne).eval₂ _ (r t)` into an explicit `Finset.sum` over
`Finset.range BleadingCoeffs.N`.
-/
public lemma trunc_eval₂_eq_sum_range_formula (t : ℝ) :
    ((-varphi_trunc_leOne).eval₂ (algebraMap ℚ ℝ) (r t)) =
      ∑ n ∈ Finset.range BleadingCoeffs.N, (truncCoeffFormula n : ℝ) * (r t) ^ n := by
  -- Rewrite `-varphi_trunc_leOne` as `polyOfCoeffs` on the negated coefficient list,
  -- then replace it by the computed `truncCoeffsExpected`.
  have hpoly : (-varphi_trunc_leOne) = polyOfCoeffs truncCoeffsExpected := by
    simpa [varphi_trunc_leOne, varphi_trunc_leOne_coeffs_map_neg_eq_expected] using!
      (polyOfCoeffs_map_neg (l := varphi_trunc_leOne_coeffs)).symm
  -- Expand evaluation into a coefficient sum and rewrite coefficients using `truncCoeffFormula`.
  have hsum := eval₂_polyOfCoeffs_eq_sum_range_getD (l := truncCoeffsExpected) (x := r t)
  have hlen : truncCoeffsExpected.length = BleadingCoeffs.N := truncCoeffsExpected_length
  -- Replace the `getD` terms.
  calc
      ((-varphi_trunc_leOne).eval₂ (algebraMap ℚ ℝ) (r t))
          = (polyOfCoeffs truncCoeffsExpected).eval₂ (algebraMap ℚ ℝ) (r t) := by
            simp [hpoly]
    _ =
        ∑ n ∈ Finset.range BleadingCoeffs.N,
          (algebraMap ℚ ℝ) (truncCoeffsExpected.getD n 0) * (r t) ^ n := by
            simpa [hlen] using! hsum
    _ = ∑ n ∈ Finset.range BleadingCoeffs.N, (truncCoeffFormula n : ℝ) * (r t) ^ n := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hn' : n < BleadingCoeffs.N := Finset.mem_range.1 hn
          have hget : truncCoeffsExpected.getD n 0 = truncCoeffFormula n :=
            truncCoeffsExpected_getD_of_lt (k := n) hn'
          -- Rewrite the coefficient, then simplify the cast.
          calc
            (algebraMap ℚ ℝ) (truncCoeffsExpected.getD n 0) * (r t) ^ n =
                (algebraMap ℚ ℝ) (truncCoeffFormula n) * (r t) ^ n := by
                  rw [hget]
            _ = (truncCoeffFormula n : ℝ) * (r t) ^ n := by
                  simp


end VarphiLeOne

end

end SpherePacking.Dim24.AppendixA
