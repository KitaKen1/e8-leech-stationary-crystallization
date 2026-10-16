-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumCert.VerifyThetaH4
import Mathlib.Tactic.IntervalCases

/-!
# Verify H4 H2

This file proves the remaining staged table equalities needed for the `psiSnumCoeffs_calc_fast`
certificate: the square `H4^2`, the powers `H2^k` (for `k = 2,3,4,5,6,7`), and the composite terms
`termA` and `termB`.

## Main statements
* `psiSnumCoeffs_calc_eq_cert`
-/

namespace SpherePacking.Dim24.Ineq2PsiSnum
lemma powZ_fast_H4_2 :
    powZ_fast Ineq2PsiSnumTables.H4Z_table 2 = Ineq2PsiSnumTables.H4Z_pow2_table := by
  have h0 : powZ_fast Ineq2PsiSnumTables.H4Z_table 0 = oneZ := by rfl
  have h1 : powZ_fast Ineq2PsiSnumTables.H4Z_table 1 = Ineq2PsiSnumTables.H4Z_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.H4Z_table 1
          = mulZ_fast Ineq2PsiSnumTables.H4Z_table (powZ_fast Ineq2PsiSnumTables.H4Z_table 0) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.H4Z_table oneZ := by rw [h0]
      _ = Ineq2PsiSnumTables.H4Z_table := mul_H4_one
  calc
    powZ_fast Ineq2PsiSnumTables.H4Z_table 2
        = mulZ_fast Ineq2PsiSnumTables.H4Z_table (powZ_fast Ineq2PsiSnumTables.H4Z_table 1) := rfl
    _ = mulZ_fast Ineq2PsiSnumTables.H4Z_table Ineq2PsiSnumTables.H4Z_table := by rw [h1]
    _ = Ineq2PsiSnumTables.H4Z_pow2_table := mul_H4_pow2

lemma mul_H2_one :
    mulZ_fast Ineq2PsiSnumTables.H2Z_table oneZ = Ineq2PsiSnumTables.H2Z_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD (l := mulZ_fast Ineq2PsiSnumTables.H2Z_table oneZ) (n := n) hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.H2Z_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.H2Z_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_H2_pow2 :
    mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_table =
      Ineq2PsiSnumTables.H2Z_pow2_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.H2Z_pow2_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.H2Z_pow2_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_H2_pow3 :
    mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow2_table =
      Ineq2PsiSnumTables.H2Z_pow3_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow2_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.H2Z_pow3_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.H2Z_pow3_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_H2_pow4 :
    mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow3_table =
      Ineq2PsiSnumTables.H2Z_pow4_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow3_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.H2Z_pow4_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.H2Z_pow4_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_H2_pow5 :
    mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow4_table =
      Ineq2PsiSnumTables.H2Z_pow5_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow4_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.H2Z_pow5_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.H2Z_pow5_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_H2_pow6 :
    mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow5_table =
      Ineq2PsiSnumTables.H2Z_pow6_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow5_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.H2Z_pow6_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.H2Z_pow6_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_H2_pow7 :
    mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow6_table =
      Ineq2PsiSnumTables.H2Z_pow7_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow6_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.H2Z_pow7_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.H2Z_pow7_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma powZ_fast_H2_5 :
    powZ_fast Ineq2PsiSnumTables.H2Z_table 5 = Ineq2PsiSnumTables.H2Z_pow5_table := by
  have h0 : powZ_fast Ineq2PsiSnumTables.H2Z_table 0 = oneZ := by rfl
  have h1 : powZ_fast Ineq2PsiSnumTables.H2Z_table 1 = Ineq2PsiSnumTables.H2Z_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.H2Z_table 1
          = mulZ_fast Ineq2PsiSnumTables.H2Z_table (powZ_fast Ineq2PsiSnumTables.H2Z_table 0) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.H2Z_table oneZ := by rw [h0]
      _ = Ineq2PsiSnumTables.H2Z_table := mul_H2_one
  have h2 : powZ_fast Ineq2PsiSnumTables.H2Z_table 2 = Ineq2PsiSnumTables.H2Z_pow2_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.H2Z_table 2
          = mulZ_fast Ineq2PsiSnumTables.H2Z_table (powZ_fast Ineq2PsiSnumTables.H2Z_table 1) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_table := by rw [h1]
      _ = Ineq2PsiSnumTables.H2Z_pow2_table := mul_H2_pow2
  have h3 : powZ_fast Ineq2PsiSnumTables.H2Z_table 3 = Ineq2PsiSnumTables.H2Z_pow3_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.H2Z_table 3
          = mulZ_fast Ineq2PsiSnumTables.H2Z_table (powZ_fast Ineq2PsiSnumTables.H2Z_table 2) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow2_table := by rw [h2]
      _ = Ineq2PsiSnumTables.H2Z_pow3_table := mul_H2_pow3
  have h4 : powZ_fast Ineq2PsiSnumTables.H2Z_table 4 = Ineq2PsiSnumTables.H2Z_pow4_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.H2Z_table 4
          = mulZ_fast Ineq2PsiSnumTables.H2Z_table (powZ_fast Ineq2PsiSnumTables.H2Z_table 3) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow3_table := by rw [h3]
      _ = Ineq2PsiSnumTables.H2Z_pow4_table := mul_H2_pow4
  calc
    powZ_fast Ineq2PsiSnumTables.H2Z_table 5
        = mulZ_fast Ineq2PsiSnumTables.H2Z_table (powZ_fast Ineq2PsiSnumTables.H2Z_table 4) := rfl
    _ = mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow4_table := by rw [h4]
    _ = Ineq2PsiSnumTables.H2Z_pow5_table := mul_H2_pow5

lemma powZ_fast_H2_6 :
    powZ_fast Ineq2PsiSnumTables.H2Z_table 6 = Ineq2PsiSnumTables.H2Z_pow6_table := by
  have h5 : powZ_fast Ineq2PsiSnumTables.H2Z_table 5 = Ineq2PsiSnumTables.H2Z_pow5_table :=
    powZ_fast_H2_5
  calc
    powZ_fast Ineq2PsiSnumTables.H2Z_table 6
        = mulZ_fast Ineq2PsiSnumTables.H2Z_table (powZ_fast Ineq2PsiSnumTables.H2Z_table 5) := rfl
    _ = mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow5_table := by rw [h5]
    _ = Ineq2PsiSnumTables.H2Z_pow6_table := mul_H2_pow6

lemma powZ_fast_H2_7 :
    powZ_fast Ineq2PsiSnumTables.H2Z_table 7 = Ineq2PsiSnumTables.H2Z_pow7_table := by
  have h6 : powZ_fast Ineq2PsiSnumTables.H2Z_table 6 = Ineq2PsiSnumTables.H2Z_pow6_table :=
    powZ_fast_H2_6
  calc
    powZ_fast Ineq2PsiSnumTables.H2Z_table 7
        = mulZ_fast Ineq2PsiSnumTables.H2Z_table (powZ_fast Ineq2PsiSnumTables.H2Z_table 6) := rfl
    _ = mulZ_fast Ineq2PsiSnumTables.H2Z_table Ineq2PsiSnumTables.H2Z_pow6_table := by rw [h6]
    _ = Ineq2PsiSnumTables.H2Z_pow7_table := mul_H2_pow7

lemma mul_termA :
    mulZ_fast Ineq2PsiSnumTables.H2Z_pow5_table Ineq2PsiSnumTables.H4Z_pow2_table =
      Ineq2PsiSnumTables.termA_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.H2Z_pow5_table Ineq2PsiSnumTables.H4Z_pow2_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.termA_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.termA_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_termB :
    mulZ_fast Ineq2PsiSnumTables.H2Z_pow6_table Ineq2PsiSnumTables.H4Z_table =
      Ineq2PsiSnumTables.termB_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.H2Z_pow6_table Ineq2PsiSnumTables.H4Z_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.termB_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.termB_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma psiSnumCoeffs_calc_fast_eq_cert :
    psiSnumCoeffs_calc_fast = Ineq2GeOneCoeffs.psiSnumCoeffs := by
  -- Expand the fast computation and rewrite each intermediate list to its table.
  unfold psiSnumCoeffs_calc_fast H2Z_fast H4Z_fast
  -- Rewrite the theta coefficient lists.
  rw [theta01Z_fast_eq_table, theta10Z_fast_eq_table]
  -- Rewrite `H₄Z` and `H₂Z`.
  rw [powZ_fast_theta01_4, powZ_fast_theta10_4, shift1_theta10_pow4]
  -- Rewrite the remaining powers and products.
  rw [powZ_fast_H4_2, powZ_fast_H2_5, powZ_fast_H2_6, powZ_fast_H2_7, mul_termA, mul_termB]
  -- Close the final concrete list equality.
  simp only [Ineq2GeOneCoeffs.psiSnumCoeffs, Ineq2GeOneCoeffs.psiSnumCoeffs_table]
  decide

/-! The main certificate statement in this file. -/

/-- The definitional computation `psiSnumCoeffs_calc` agrees with the hard-coded coefficient table
`Ineq2GeOneCoeffs.psiSnumCoeffs`. -/
public theorem psiSnumCoeffs_calc_eq_cert :
    psiSnumCoeffs_calc = Ineq2GeOneCoeffs.psiSnumCoeffs := by
  -- Transfer from the original computation to the fast one, then to the certificate table.
  have hfast : psiSnumCoeffs_calc_fast = Ineq2GeOneCoeffs.psiSnumCoeffs :=
    psiSnumCoeffs_calc_fast_eq_cert
  have hslow : psiSnumCoeffs_calc_fast = psiSnumCoeffs_calc :=
    psiSnumCoeffs_calc_fast_eq_slow
  simpa [hslow] using! hfast

end SpherePacking.Dim24.Ineq2PsiSnum
