/-
Verified integer coefficient table for `coeffVarphiNum` (first `50` coefficients).

We avoid expensive kernel evaluation of rational `q`-series coefficients by:
1) rewriting `coeffVarphiNum n` as an `Int`-cast of the explicit `ℤ` coefficient formula
   `coeffVarphiNumZ n` (see `Part08F_CoeffZModel.lean`);
2) computing the first `50` coefficients using truncated list arithmetic in `ℤ`;
3) discharging the finite table comparison by `decide` on small `ℤ` equalities.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffZModel
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ZVArith
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.CoeffsVarphiInt
import Mathlib.Tactic.FinCases


/-!
### Integer table for `coeffVarphiNum`

This file computes the first `QN = 50` coefficients of `coeffVarphiNum` using truncated list
arithmetic in `ℤ`, and records the resulting table as `varphiNumCoeffsZ_table`. The main lemma
`coeffVarphiNum_eq_table` identifies `coeffVarphiNum n` with the `ℚ`-cast of the table entry for
all `n < QN`.
-/

namespace SpherePacking.Dim24.AppendixA

open scoped BigOperators ArithmeticFunction.sigma

-- List arithmetic utilities are shared in `BLeadingNumLowerBound.ZVArith`.

lemma coeffZV_mulZV_trunc (a b : ℕ → ℤ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV (mulZV (truncZV a) (truncZV b)) n = mulFunZ a b n := by
  simpa using! (coeffZV_mulZV_truncZV (a := a) (b := b) (n := n) hn)


def coeffE2ListZV : List ℤ := truncZV coeffE2Z
def coeffE4ListZV : List ℤ := truncZV coeffE4Z
def coeffE6ListZV : List ℤ := truncZV coeffE6Z

def coeffE2SqListZV : List ℤ := mulZV coeffE2ListZV coeffE2ListZV
def coeffE4SqListZV : List ℤ := mulZV coeffE4ListZV coeffE4ListZV
def coeffE6SqListZV : List ℤ := mulZV coeffE6ListZV coeffE6ListZV

def coeffE4CubeListZV : List ℤ := mulZV coeffE4SqListZV coeffE4ListZV
def coeffE4FourthListZV : List ℤ := mulZV coeffE4SqListZV coeffE4SqListZV

def coeffLinListZV : List ℤ :=
  addZV (smulZV (-49) coeffE4CubeListZV) (smulZV 25 coeffE6SqListZV)

def coeffVarphiNumListZV : List ℤ :=
  addZV
    (addZV
      (addZV
        (smulZV 25 coeffE4FourthListZV)
        (smulZV (-49) (mulZV coeffE6SqListZV coeffE4ListZV)))
      (smulZV 48 (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV)))
    (mulZV coeffLinListZV coeffE2SqListZV)

lemma coeffZV_coeffVarphiNumList_eq (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV coeffVarphiNumListZV n = coeffVarphiNumZ n := by
  -- Shorthand: `hn : n < 50`.
  have hE2 (m : ℕ) (hm : m < BleadingCoeffs.QN) : coeffZV coeffE2ListZV m = coeffE2Z m := by
    simpa [coeffE2ListZV] using! coeffZV_truncZV (a := coeffE2Z) (n := m) hm
  have hE4 (m : ℕ) (hm : m < BleadingCoeffs.QN) : coeffZV coeffE4ListZV m = coeffE4Z m := by
    simpa [coeffE4ListZV] using! coeffZV_truncZV (a := coeffE4Z) (n := m) hm
  have hE6 (m : ℕ) (hm : m < BleadingCoeffs.QN) : coeffZV coeffE6ListZV m = coeffE6Z m := by
    simpa [coeffE6ListZV] using! coeffZV_truncZV (a := coeffE6Z) (n := m) hm
  have hE2Sq (m : ℕ) (hm : m < BleadingCoeffs.QN) :
      coeffZV coeffE2SqListZV m = coeffE2SqZ m := by
    -- `coeffE2SqZ m = mulFunZ coeffE2Z coeffE2Z m`.
    have := coeffZV_mulZV_trunc (a := coeffE2Z) (b := coeffE2Z) (n := m) hm
    simpa [coeffE2SqListZV, coeffE2ListZV, coeffE2SqZ] using! this
  have hE4Sq (m : ℕ) (hm : m < BleadingCoeffs.QN) :
      coeffZV coeffE4SqListZV m = coeffE4SqZ m := by
    have := coeffZV_mulZV_trunc (a := coeffE4Z) (b := coeffE4Z) (n := m) hm
    simpa [coeffE4SqListZV, coeffE4ListZV, coeffE4SqZ] using! this
  have hE6Sq (m : ℕ) (hm : m < BleadingCoeffs.QN) :
      coeffZV coeffE6SqListZV m = coeffE6SqZ m := by
    have := coeffZV_mulZV_trunc (a := coeffE6Z) (b := coeffE6Z) (n := m) hm
    simpa [coeffE6SqListZV, coeffE6ListZV, coeffE6SqZ] using! this
  have hE4Cube (m : ℕ) (hm : m < BleadingCoeffs.QN) :
      coeffZV coeffE4CubeListZV m = coeffE4CubeZ m := by
    have hmul :
        coeffZV coeffE4CubeListZV m =
          Finset.sum (Finset.range (m + 1)) fun j =>
            coeffZV coeffE4SqListZV j * coeffZV coeffE4ListZV (m - j) := by
      simpa [coeffE4CubeListZV] using!
        (coeffZV_mulZV (a := coeffE4SqListZV) (b := coeffE4ListZV) (n := m) hm)
    refine hmul.trans ?_
    simp only [coeffE4CubeZ, mulFunZ]
    simpa using! (Finset.sum_congr rfl (fun j hj => by
      have hjle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hjlt : j < BleadingCoeffs.QN := lt_of_le_of_lt hjle hm
      have hsublt : m - j < BleadingCoeffs.QN := lt_of_le_of_lt (Nat.sub_le _ _) hm
      simp [hE4Sq j hjlt, hE4 (m - j) hsublt]))
  have hE4Fourth (m : ℕ) (hm : m < BleadingCoeffs.QN) :
      coeffZV coeffE4FourthListZV m = coeffE4FourthZ m := by
    have hmul :
        coeffZV coeffE4FourthListZV m =
          Finset.sum (Finset.range (m + 1)) fun j =>
            coeffZV coeffE4SqListZV j * coeffZV coeffE4SqListZV (m - j) := by
      simpa [coeffE4FourthListZV] using!
        (coeffZV_mulZV (a := coeffE4SqListZV) (b := coeffE4SqListZV) (n := m) hm)
    refine hmul.trans ?_
    simp only [coeffE4FourthZ, mulFunZ]
    simpa using! (Finset.sum_congr rfl (fun j hj => by
      have hjle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hjlt : j < BleadingCoeffs.QN := lt_of_le_of_lt hjle hm
      have hsublt : m - j < BleadingCoeffs.QN := lt_of_le_of_lt (Nat.sub_le _ _) hm
      simp [hE4Sq j hjlt, hE4Sq (m - j) hsublt]))
  have hLin (m : ℕ) (hm : m < BleadingCoeffs.QN) :
      coeffZV coeffLinListZV m = (-49 : ℤ) * coeffE4CubeZ m + (25 : ℤ) * coeffE6SqZ m := by
    have hadd :=
      coeffZV_addZV (a := smulZV (-49) coeffE4CubeListZV) (b := smulZV 25 coeffE6SqListZV)
        (n := m) hm
    have hs1 := coeffZV_smulZV (-49) coeffE4CubeListZV m hm
    have hs2 := coeffZV_smulZV 25 coeffE6SqListZV m hm
    simp [coeffLinListZV, hadd, hs1, hs2, hE4Cube m hm, hE6Sq m hm]
  -- Main coefficient expansion of `coeffVarphiNumListZV`.
  have hmain :
      coeffZV coeffVarphiNumListZV n =
        (25 : ℤ) * coeffZV coeffE4FourthListZV n +
          (-(49 : ℤ)) * coeffZV (mulZV coeffE6SqListZV coeffE4ListZV) n +
            (48 : ℤ) * coeffZV (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV) n +
              coeffZV (mulZV coeffLinListZV coeffE2SqListZV) n := by
    have hn' : n < BleadingCoeffs.QN := hn
    -- Peel the nested `addZV`/`smulZV` structure coefficientwise.
    have hOuter := coeffZV_addZV
      (a := addZV
        (addZV (smulZV 25 coeffE4FourthListZV) (smulZV (-49) (mulZV coeffE6SqListZV coeffE4ListZV)))
        (smulZV 48 (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV)))
      (b := mulZV coeffLinListZV coeffE2SqListZV) (n := n) hn'
    have hMid :=
      coeffZV_addZV
        (a := addZV (smulZV 25 coeffE4FourthListZV)
          (smulZV (-49) (mulZV coeffE6SqListZV coeffE4ListZV)))
        (b := smulZV 48 (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV)) (n := n)
        hn'
    have hIn := coeffZV_addZV
      (a := smulZV 25 coeffE4FourthListZV)
      (b := smulZV (-49) (mulZV coeffE6SqListZV coeffE4ListZV)) (n := n) hn'
    have hsA := coeffZV_smulZV 25 coeffE4FourthListZV n hn'
    have hsB := coeffZV_smulZV (-49) (mulZV coeffE6SqListZV coeffE4ListZV) n hn'
    have hsC := coeffZV_smulZV 48 (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV) n hn'
    -- Rewrite and normalize using commutativity/associativity in `ℤ`.
    -- `ring_nf` handles the remaining reassociation cleanly.
    -- (We avoid `simp`-heavy normalization, which can be heartbeat-heavy.)
    calc
      coeffZV coeffVarphiNumListZV n
          = coeffZV
              (addZV
                (addZV
                  (addZV (smulZV 25 coeffE4FourthListZV)
                    (smulZV (-49) (mulZV coeffE6SqListZV coeffE4ListZV)))
                  (smulZV 48 (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV)))
                (mulZV coeffLinListZV coeffE2SqListZV))
              n := by rfl
      _ = coeffZV
            (addZV
              (addZV (smulZV 25 coeffE4FourthListZV)
                (smulZV (-49) (mulZV coeffE6SqListZV coeffE4ListZV)))
              (smulZV 48 (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV)))
            n +
          coeffZV (mulZV coeffLinListZV coeffE2SqListZV) n := by
            simpa [coeffVarphiNumListZV] using! hOuter
      _ = (coeffZV (smulZV 25 coeffE4FourthListZV) n +
            coeffZV (smulZV (-49) (mulZV coeffE6SqListZV coeffE4ListZV)) n) +
            coeffZV (smulZV 48 (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV)) n +
          coeffZV (mulZV coeffLinListZV coeffE2SqListZV) n := by
            -- Expand the remaining nested `addZV` and reassociate.
            simp [hMid, hIn, add_left_comm, add_comm]
      _ = (25 : ℤ) * coeffZV coeffE4FourthListZV n +
            (-(49 : ℤ)) * coeffZV (mulZV coeffE6SqListZV coeffE4ListZV) n +
              (48 : ℤ) * coeffZV (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV) n +
                coeffZV (mulZV coeffLinListZV coeffE2SqListZV) n := by
            -- pull out scalars
            -- and normalize the resulting ring expression.
            -- `hsA/hsB/hsC` unfold the three scalar multiplications.
            -- `ring_nf` takes care of the rest.
            simp [hsA, hsB, hsC, add_assoc, add_left_comm, add_comm]
  have hE6SqE4 :
      coeffZV (mulZV coeffE6SqListZV coeffE4ListZV) n = mulFunZ coeffE6SqZ coeffE4Z n := by
    have hmul := coeffZV_mulZV (a := coeffE6SqListZV) (b := coeffE4ListZV) (n := n) hn
    have ha : ∀ j ∈ Finset.range (n + 1), coeffZV coeffE6SqListZV j = coeffE6SqZ j := by
      intro j hj
      have hjle : j ≤ n := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hj)
      exact hE6Sq j (lt_of_le_of_lt hjle hn)
    have hb : ∀ j ∈ Finset.range (n + 1), coeffZV coeffE4ListZV (n - j) = coeffE4Z (n - j) := by
      intro j hj
      have hnsub : n - j ≤ n := Nat.sub_le _ _
      exact hE4 (n - j) (lt_of_le_of_lt hnsub hn)
    simpa [mulFunZ] using!
      (hmul.trans (by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [ha j hj, hb j hj]))
  have hE6E4SqE2 :
      coeffZV (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV) n =
        mulFunZ (fun m => mulFunZ coeffE6Z coeffE4SqZ m) coeffE2Z n := by
    have hmul2 :=
      coeffZV_mulZV (a := mulZV coeffE6ListZV coeffE4SqListZV) (b := coeffE2ListZV) (n := n) hn
    have ha2 :
        ∀ j ∈ Finset.range (n + 1), coeffZV (mulZV coeffE6ListZV coeffE4SqListZV) j =
          mulFunZ coeffE6Z coeffE4SqZ j := by
      intro j hj
      have hjle : j ≤ n := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hj)
      have hj' : j < BleadingCoeffs.QN := lt_of_le_of_lt hjle hn
      have hmul1 := coeffZV_mulZV (a := coeffE6ListZV) (b := coeffE4SqListZV) (n := j) hj'
      have ha1 : ∀ k ∈ Finset.range (j + 1), coeffZV coeffE6ListZV k = coeffE6Z k := by
        intro k hk
        have hkle : k ≤ j := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hk)
        exact hE6 k (lt_of_le_of_lt hkle hj')
      have hb1 :
          ∀ k ∈ Finset.range (j + 1), coeffZV coeffE4SqListZV (j - k) = coeffE4SqZ (j - k) := by
        intro k hk
        have hjsub : j - k ≤ j := Nat.sub_le _ _
        exact hE4Sq (j - k) (lt_of_le_of_lt hjsub hj')
      simpa [mulFunZ] using!
        (hmul1.trans (by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [ha1 k hk, hb1 k hk]))
    have hb2 : ∀ j ∈ Finset.range (n + 1), coeffZV coeffE2ListZV (n - j) = coeffE2Z (n - j) := by
      intro j hj
      have hnsub : n - j ≤ n := Nat.sub_le _ _
      exact hE2 (n - j) (lt_of_le_of_lt hnsub hn)
    simpa [mulFunZ] using!
      (hmul2.trans (by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [ha2 j hj, hb2 j hj, mulFunZ]))
  have hLinE2Sq :
      coeffZV (mulZV coeffLinListZV coeffE2SqListZV) n =
        mulFunZ (fun m => (-49 : ℤ) * coeffE4CubeZ m + (25 : ℤ) * coeffE6SqZ m) coeffE2SqZ n := by
    have hmul := coeffZV_mulZV (a := coeffLinListZV) (b := coeffE2SqListZV) (n := n) hn
    have ha : ∀ j ∈ Finset.range (n + 1), coeffZV coeffLinListZV j =
        (-49 : ℤ) * coeffE4CubeZ j + (25 : ℤ) * coeffE6SqZ j := by
      intro j hj
      have hjle : j ≤ n := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hj)
      exact hLin j (lt_of_le_of_lt hjle hn)
    have hb : ∀ j ∈ Finset.range (n + 1), coeffZV coeffE2SqListZV (n - j) = coeffE2SqZ (n - j) := by
      intro j hj
      have hnsub : n - j ≤ n := Nat.sub_le _ _
      exact hE2Sq (n - j) (lt_of_le_of_lt hnsub hn)
    simpa [mulFunZ] using!
      (hmul.trans (by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [ha j hj, hb j hj]))
  -- Combine with the definition of `coeffVarphiNumZ`.
  calc
    coeffZV coeffVarphiNumListZV n
        = (25 : ℤ) * coeffZV coeffE4FourthListZV n +
            (-(49 : ℤ)) * coeffZV (mulZV coeffE6SqListZV coeffE4ListZV) n +
              (48 : ℤ) * coeffZV (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV) n +
                coeffZV (mulZV coeffLinListZV coeffE2SqListZV) n := hmain
    _ = (25 : ℤ) * coeffE4FourthZ n +
          (-(49 : ℤ)) * (mulFunZ coeffE6SqZ coeffE4Z n) +
            (48 : ℤ) * (mulFunZ (fun m => mulFunZ coeffE6Z coeffE4SqZ m) coeffE2Z n) +
              mulFunZ
                (fun m => (-49 : ℤ) * coeffE4CubeZ m + (25 : ℤ) * coeffE6SqZ m)
                coeffE2SqZ n := by
          simp [hE4Fourth n hn, hE6SqE4, hE6E4SqE2, hLinE2Sq]
    _ = coeffVarphiNumZ n := by
          -- This is definitional: `coeffVarphiNumZ` is exactly the expanded expression.
          -- We just normalize minor associativity/commutativity differences.
          simp [coeffVarphiNumZ, add_assoc]

/-!
### The expected PARI/GP table (as `ℤ`)
-/

/-- Explicit integer table of the first `QN = 50` coefficients of `coeffVarphiNum`. -/
@[expose] public def varphiNumCoeffsZ_table : List ℤ :=
  varphi_trunc_geOne_coeffsZV

-- Coefficientwise comparison (`0..49`).
lemma coeffVarphiNumListZV_eq_getD_fin (i : Fin BleadingCoeffs.QN) :
    coeffZV coeffVarphiNumListZV i.1 = varphiNumCoeffsZ_table.getD i.1 0 := by
  set_option maxRecDepth 20000 in
  fin_cases i <;> decide

lemma coeffVarphiNumZ_eq_table (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffVarphiNumZ n = varphiNumCoeffsZ_table.getD n 0 := by
  simpa using!
    (coeffZV_coeffVarphiNumList_eq (n := n) hn).symm.trans
      (coeffVarphiNumListZV_eq_getD_fin (i := ⟨n, hn⟩))

/--
For `n < QN`, `coeffVarphiNum n` agrees with the `ℚ`-cast of
`varphiNumCoeffsZ_table.getD n 0`. -/
public lemma coeffVarphiNum_eq_table (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffVarphiNum n = (varphiNumCoeffsZ_table.getD n 0 : ℚ) := by
  simpa [coeffVarphiNum_eq_cast] using!
    congrArg (fun z : ℤ => (z : ℚ))
      (coeffVarphiNumZ_eq_table n hn)

end SpherePacking.Dim24.AppendixA
