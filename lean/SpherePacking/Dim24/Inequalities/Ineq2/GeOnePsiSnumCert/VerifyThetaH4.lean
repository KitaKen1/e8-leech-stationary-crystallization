-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumCert.SumRange
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumTables.ThetaTables
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumTables.H4Pow2Table
import Mathlib.Tactic.IntervalCases


/-!
# Verifying staged theta and `H4` tables

This file verifies intermediate coefficient lists used in the fast computation
`psiSnumCoeffs_calc_fast` against the explicit tables in `SpherePacking.Dim24.Ineq2PsiSnumTables`.
The proofs are by kernel computation on the concrete lists and by small staged rewrites.

## Main definitions
* `oneZ`
* `get_eq_getD`

## Main statements
* `theta01Z_fast_eq_table`
* `theta10Z_fast_eq_table`
* `powZ_fast_theta01_4`
* `powZ_fast_theta10_4`
* `shift1_theta10_pow4`
* `mul_H4_pow2`
* `mul_H4_one`
-/


namespace SpherePacking.Dim24.Ineq2PsiSnum
/-- The truncated constant series `1` as a list: coefficient `1` at index `0`, and `0` elsewhere. -/
@[expose] public def oneZ : List ℤ :=
  List.ofFn fun i : Fin Ineq2GeOneCoeffs.N => if i.1 = 0 then (1 : ℤ) else 0

/-- Rewrite `l.get ⟨n, hn⟩` as `l.getD n 0`, to avoid proof-dependent indexing in table
computations. -/
public lemma get_eq_getD (l : List ℤ) (n : ℕ) (hn : n < l.length) :
    l.get ⟨n, hn⟩ = l.getD n 0 := by
  simpa using!
    (List.getD_eq_get (l := l) (d := (0 : ℤ)) (i := ⟨n, hn⟩)).symm

/-- The computed list `theta01Z_fast` agrees with the explicit table `theta01Z_table`. -/
public lemma theta01Z_fast_eq_table :
    theta01Z_fast = Ineq2PsiSnumTables.theta01Z_table := by
  decide

/-- The computed list `theta10Z_fast` agrees with the explicit table `theta10Z_table`. -/
public lemma theta10Z_fast_eq_table :
    theta10Z_fast = Ineq2PsiSnumTables.theta10Z_table := by
  decide

lemma mul_theta01_one :
    mulZ_fast Ineq2PsiSnumTables.theta01Z_table oneZ = Ineq2PsiSnumTables.theta01Z_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  -- Avoid proof-dependence in `Fin` indices by switching to `getD`.
  rw [
    get_eq_getD (l := mulZ_fast Ineq2PsiSnumTables.theta01Z_table oneZ) (n := n) hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.theta01Z_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.theta01Z_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_theta01_pow2 :
    mulZ_fast Ineq2PsiSnumTables.theta01Z_table Ineq2PsiSnumTables.theta01Z_table =
      Ineq2PsiSnumTables.theta01Z_pow2_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.theta01Z_table Ineq2PsiSnumTables.theta01Z_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.theta01Z_pow2_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.theta01Z_pow2_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_theta01_pow3 :
    mulZ_fast Ineq2PsiSnumTables.theta01Z_table Ineq2PsiSnumTables.theta01Z_pow2_table =
      Ineq2PsiSnumTables.theta01Z_pow3_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.theta01Z_table Ineq2PsiSnumTables.theta01Z_pow2_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.theta01Z_pow3_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.theta01Z_pow3_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_theta01_pow4 :
    mulZ_fast Ineq2PsiSnumTables.theta01Z_table Ineq2PsiSnumTables.theta01Z_pow3_table =
      Ineq2PsiSnumTables.H4Z_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.theta01Z_table Ineq2PsiSnumTables.theta01Z_pow3_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.H4Z_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.H4Z_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

/-- Verify the staged identity `theta01Z_table ^ 4 = H4Z_table`, computed via `powZ_fast`. -/
public lemma powZ_fast_theta01_4 :
    powZ_fast Ineq2PsiSnumTables.theta01Z_table 4 = Ineq2PsiSnumTables.H4Z_table := by
  -- Expand `powZ_fast` without evaluating the full nested products.
  have h0 : powZ_fast Ineq2PsiSnumTables.theta01Z_table 0 = oneZ := by rfl
  have h1 : powZ_fast Ineq2PsiSnumTables.theta01Z_table 1 = Ineq2PsiSnumTables.theta01Z_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.theta01Z_table 1
          =
            mulZ_fast Ineq2PsiSnumTables.theta01Z_table
              (powZ_fast Ineq2PsiSnumTables.theta01Z_table 0) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.theta01Z_table oneZ := by rw [h0]
      _ = Ineq2PsiSnumTables.theta01Z_table := mul_theta01_one
  have h2 :
      powZ_fast Ineq2PsiSnumTables.theta01Z_table 2 = Ineq2PsiSnumTables.theta01Z_pow2_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.theta01Z_table 2
          =
            mulZ_fast Ineq2PsiSnumTables.theta01Z_table
              (powZ_fast Ineq2PsiSnumTables.theta01Z_table 1) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.theta01Z_table Ineq2PsiSnumTables.theta01Z_table := by
          rw [h1]
      _ = Ineq2PsiSnumTables.theta01Z_pow2_table := mul_theta01_pow2
  have h3 :
      powZ_fast Ineq2PsiSnumTables.theta01Z_table 3 = Ineq2PsiSnumTables.theta01Z_pow3_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.theta01Z_table 3
          =
            mulZ_fast Ineq2PsiSnumTables.theta01Z_table
              (powZ_fast Ineq2PsiSnumTables.theta01Z_table 2) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.theta01Z_table Ineq2PsiSnumTables.theta01Z_pow2_table := by
          rw [h2]
      _ = Ineq2PsiSnumTables.theta01Z_pow3_table := mul_theta01_pow3
  calc
    powZ_fast Ineq2PsiSnumTables.theta01Z_table 4
        =
          mulZ_fast Ineq2PsiSnumTables.theta01Z_table
            (powZ_fast Ineq2PsiSnumTables.theta01Z_table 3) := rfl
    _ = mulZ_fast Ineq2PsiSnumTables.theta01Z_table Ineq2PsiSnumTables.theta01Z_pow3_table := by
          rw [h3]
    _ = Ineq2PsiSnumTables.H4Z_table := mul_theta01_pow4

lemma mul_theta10_one :
    mulZ_fast Ineq2PsiSnumTables.theta10Z_table oneZ = Ineq2PsiSnumTables.theta10Z_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD (l := mulZ_fast Ineq2PsiSnumTables.theta10Z_table oneZ) (n := n) hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.theta10Z_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.theta10Z_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_theta10_pow2 :
    mulZ_fast Ineq2PsiSnumTables.theta10Z_table Ineq2PsiSnumTables.theta10Z_table =
      Ineq2PsiSnumTables.theta10Z_pow2_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.theta10Z_table Ineq2PsiSnumTables.theta10Z_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.theta10Z_pow2_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.theta10Z_pow2_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_theta10_pow3 :
    mulZ_fast Ineq2PsiSnumTables.theta10Z_table Ineq2PsiSnumTables.theta10Z_pow2_table =
      Ineq2PsiSnumTables.theta10Z_pow3_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.theta10Z_table Ineq2PsiSnumTables.theta10Z_pow2_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.theta10Z_pow3_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.theta10Z_pow3_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

lemma mul_theta10_pow4 :
    mulZ_fast Ineq2PsiSnumTables.theta10Z_table Ineq2PsiSnumTables.theta10Z_pow3_table =
      Ineq2PsiSnumTables.theta10Z_pow4_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.theta10Z_table Ineq2PsiSnumTables.theta10Z_pow3_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.theta10Z_pow4_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.theta10Z_pow4_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

/-- Verify the staged identity `theta10Z_table ^ 4 = theta10Z_pow4_table`, computed via
`powZ_fast`. -/
public lemma powZ_fast_theta10_4 :
    powZ_fast Ineq2PsiSnumTables.theta10Z_table 4 = Ineq2PsiSnumTables.theta10Z_pow4_table := by
  have h0 : powZ_fast Ineq2PsiSnumTables.theta10Z_table 0 = oneZ := by rfl
  have h1 : powZ_fast Ineq2PsiSnumTables.theta10Z_table 1 = Ineq2PsiSnumTables.theta10Z_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.theta10Z_table 1
          =
            mulZ_fast Ineq2PsiSnumTables.theta10Z_table
              (powZ_fast Ineq2PsiSnumTables.theta10Z_table 0) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.theta10Z_table oneZ := by rw [h0]
      _ = Ineq2PsiSnumTables.theta10Z_table := mul_theta10_one
  have h2 :
      powZ_fast Ineq2PsiSnumTables.theta10Z_table 2 = Ineq2PsiSnumTables.theta10Z_pow2_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.theta10Z_table 2
          =
            mulZ_fast Ineq2PsiSnumTables.theta10Z_table
              (powZ_fast Ineq2PsiSnumTables.theta10Z_table 1) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.theta10Z_table Ineq2PsiSnumTables.theta10Z_table := by
          rw [h1]
      _ = Ineq2PsiSnumTables.theta10Z_pow2_table := mul_theta10_pow2
  have h3 :
      powZ_fast Ineq2PsiSnumTables.theta10Z_table 3 = Ineq2PsiSnumTables.theta10Z_pow3_table := by
    calc
      powZ_fast Ineq2PsiSnumTables.theta10Z_table 3
          =
            mulZ_fast Ineq2PsiSnumTables.theta10Z_table
              (powZ_fast Ineq2PsiSnumTables.theta10Z_table 2) := rfl
      _ = mulZ_fast Ineq2PsiSnumTables.theta10Z_table Ineq2PsiSnumTables.theta10Z_pow2_table := by
          rw [h2]
      _ = Ineq2PsiSnumTables.theta10Z_pow3_table := mul_theta10_pow3
  calc
    powZ_fast Ineq2PsiSnumTables.theta10Z_table 4
        =
          mulZ_fast Ineq2PsiSnumTables.theta10Z_table
            (powZ_fast Ineq2PsiSnumTables.theta10Z_table 3) := rfl
    _ = mulZ_fast Ineq2PsiSnumTables.theta10Z_table Ineq2PsiSnumTables.theta10Z_pow3_table := by
          rw [h3]
    _ = Ineq2PsiSnumTables.theta10Z_pow4_table := mul_theta10_pow4

/-- Verify that `H2Z_table` is obtained by shifting `theta10Z_pow4_table` by one coefficient. -/
public lemma shift1_theta10_pow4 :
    shift1Z Ineq2PsiSnumTables.theta10Z_pow4_table = Ineq2PsiSnumTables.H2Z_table := by
  decide

/-- Verify the staged product `H4Z_table * H4Z_table = H4Z_pow2_table`, computed via `mulZ_fast`. -/
public lemma mul_H4_pow2 :
    mulZ_fast Ineq2PsiSnumTables.H4Z_table Ineq2PsiSnumTables.H4Z_table =
      Ineq2PsiSnumTables.H4Z_pow2_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD
      (l := mulZ_fast Ineq2PsiSnumTables.H4Z_table Ineq2PsiSnumTables.H4Z_table)
      (n := n)
      hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.H4Z_pow2_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.H4Z_pow2_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide

/-- Verify the identity `H4Z_table * oneZ = H4Z_table`, computed via `mulZ_fast`. -/
public lemma mul_H4_one :
    mulZ_fast Ineq2PsiSnumTables.H4Z_table oneZ = Ineq2PsiSnumTables.H4Z_table := by
  refine List.ext_get (by decide) ?_
  intro n hn1 hn2
  rw [
    get_eq_getD (l := mulZ_fast Ineq2PsiSnumTables.H4Z_table oneZ) (n := n) hn1,
    get_eq_getD (l := Ineq2PsiSnumTables.H4Z_table) (n := n) hn2
  ]
  have hn100 : n < 100 := by
    have hlen100 : Ineq2PsiSnumTables.H4Z_table.length = 100 := by decide
    simpa [hlen100] using! hn2
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn100 <;> decide


end SpherePacking.Dim24.Ineq2PsiSnum
