-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.CoeffsVarphiInt
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2Varphi.CertPrelude

/-!
# Certificate data for `varphi_num` truncation coefficients

This file defines the explicit `ℤ` list `coeffVarphiNumListZV` and proves the coefficientwise
identities needed to compare it with the expected truncation coefficient list from Appendix A.

## Main definitions
* `coeffVarphiNumListZV`

## Main statements
* `coeffZV_coeffVarphiNumList_eq`
* `coeffVarphiNumListZV_eq_expected`
-/

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

open SpherePacking.Dim24.CertificateZV

namespace Ineq2Varphi

/-- Truncated `ℤ` coefficient list used to certify the first `NVarphi = 50` coefficients. -/
@[expose] public def coeffVarphiNumListZV : List ℤ :=
  addZV
      (addZV
          (addZV
            (smulZV 25 coeffE4FourthListZV)
            (smulZV (-49) (mulZV coeffE6SqListZV coeffE4ListZV)))
          (smulZV 48 (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV)))
      (mulZV coeffLinListZV coeffE2SqListZV)

/--
Coefficientwise identification of `coeffVarphiNumListZV` with `coeffVarphiNumZV` below `NVarphi`.
-/
public lemma coeffZV_coeffVarphiNumList_eq (n : ℕ) (hn : n < NVarphi) :
    coeffZV coeffVarphiNumListZV n = coeffVarphiNumZV n := by
  have hE2 : ∀ m : ℕ, m < NVarphi → coeffZV coeffE2ListZV m = coeffE2ZV m := by
    intro m hm; simpa [coeffE2ListZV] using! coeffZV_trunc coeffE2ZV m hm
  have hE4 : ∀ m : ℕ, m < NVarphi → coeffZV coeffE4ListZV m = coeffE4ZV m := by
    intro m hm; simpa [coeffE4ListZV] using! coeffZV_trunc coeffE4ZV m hm
  have hE6 : ∀ m : ℕ, m < NVarphi → coeffZV coeffE6ListZV m = coeffE6ZV m := by
    intro m hm; simpa [coeffE6ListZV] using! coeffZV_trunc coeffE6ZV m hm
  have hE2Sq : ∀ m : ℕ, m < NVarphi → coeffZV coeffE2SqListZV m = coeffE2SqZV m := by
    intro m hm
    simpa [coeffE2SqListZV, coeffE2ListZV, coeffE2SqZV] using!
      (coeffZV_mulZV_trunc (a := coeffE2ZV) (b := coeffE2ZV) (n := m) hm)
  have hE4Sq : ∀ m : ℕ, m < NVarphi → coeffZV coeffE4SqListZV m = coeffE4SqZV m := by
    intro m hm
    simpa [coeffE4SqListZV, coeffE4ListZV, coeffE4SqZV] using!
      (coeffZV_mulZV_trunc (a := coeffE4ZV) (b := coeffE4ZV) (n := m) hm)
  have hE6Sq : ∀ m : ℕ, m < NVarphi → coeffZV coeffE6SqListZV m = coeffE6SqZV m := by
    intro m hm
    simpa [coeffE6SqListZV, coeffE6ListZV, coeffE6SqZV] using!
      (coeffZV_mulZV_trunc (a := coeffE6ZV) (b := coeffE6ZV) (n := m) hm)
  have hE4Cube : ∀ m : ℕ, m < NVarphi → coeffZV coeffE4CubeListZV m = coeffE4CubeZV m := by
    intro m hm
    have hmul := coeffZV_mulZV (a := coeffE4SqListZV) (b := coeffE4ListZV) (n := m) hm
    have ha : ∀ j ∈ Finset.range (m + 1), coeffZV coeffE4SqListZV j = coeffE4SqZV j := by
      intro j hj
      have hjle : j ≤ m := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hj)
      exact hE4Sq j (lt_of_le_of_lt hjle hm)
    have hb : ∀ j ∈ Finset.range (m + 1), coeffZV coeffE4ListZV (m - j) = coeffE4ZV (m - j) := by
      intro j hj
      have hnsub : m - j ≤ m := Nat.sub_le _ _
      exact hE4 (m - j) (lt_of_le_of_lt hnsub hm)
    have : coeffZV (mulZV coeffE4SqListZV coeffE4ListZV) m = mulFunZV coeffE4SqZV coeffE4ZV m := by
      simpa [mulFunZV] using!
        (hmul.trans (by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [ha j hj, hb j hj]))
    simpa [coeffE4CubeListZV, coeffE4CubeZV] using! this
  have hE4Fourth : ∀ m : ℕ, m < NVarphi → coeffZV coeffE4FourthListZV m = coeffE4FourthZV m := by
    intro m hm
    have hmul := coeffZV_mulZV (a := coeffE4SqListZV) (b := coeffE4SqListZV) (n := m) hm
    have ha : ∀ j ∈ Finset.range (m + 1), coeffZV coeffE4SqListZV j = coeffE4SqZV j := by
      intro j hj
      have hjle : j ≤ m := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hj)
      exact hE4Sq j (lt_of_le_of_lt hjle hm)
    have hb : ∀ j ∈ Finset.range (m + 1),
        coeffZV coeffE4SqListZV (m - j) = coeffE4SqZV (m - j) := by
      intro j hj
      have hnsub : m - j ≤ m := Nat.sub_le _ _
      exact hE4Sq (m - j) (lt_of_le_of_lt hnsub hm)
    have : coeffZV (mulZV coeffE4SqListZV coeffE4SqListZV) m =
      mulFunZV coeffE4SqZV coeffE4SqZV m := by
      simpa [mulFunZV] using!
        (hmul.trans (by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [ha j hj, hb j hj]))
    simpa [coeffE4FourthListZV, coeffE4FourthZV] using! this
  have hLin : ∀ m : ℕ, m < NVarphi → coeffZV coeffLinListZV m = coeffLinZV m := by
    intro m hm
    calc
      coeffZV coeffLinListZV m
          = coeffZV (addZV (smulZV (-49) coeffE4CubeListZV) (smulZV 25 coeffE6SqListZV)) m := by
              rfl
      _ = coeffZV (smulZV (-49) coeffE4CubeListZV) m +
            coeffZV (smulZV 25 coeffE6SqListZV) m :=
              coeffZV_addZV (smulZV (-49) coeffE4CubeListZV) (smulZV 25 coeffE6SqListZV) m hm
      _ = (-49 : ℤ) * coeffZV coeffE4CubeListZV m + (25 : ℤ) * coeffZV coeffE6SqListZV m := by
              rw [coeffZV_smulZV (c := (-49 : ℤ)) (a := coeffE4CubeListZV) (n := m) hm,
                coeffZV_smulZV (c := (25 : ℤ)) (a := coeffE6SqListZV) (n := m) hm]
      _ = (-49 : ℤ) * coeffE4CubeZV m + (25 : ℤ) * coeffE6SqZV m := by
              simp [hE4Cube m hm, hE6Sq m hm]
      _ = coeffLinZV m := by
              simp [coeffLinZV]
  -- Now expand `coeffVarphiNumListZV` coefficientwise.
  have hmain :
      coeffZV coeffVarphiNumListZV n =
        (25 : ℤ) * coeffZV coeffE4FourthListZV n +
          (-(49 : ℤ)) * coeffZV (mulZV coeffE6SqListZV coeffE4ListZV) n +
            (48 : ℤ) * coeffZV (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV) n +
              coeffZV (mulZV coeffLinListZV coeffE2SqListZV) n := by
    -- Avoid `simp` on the full expanded definition: it can exceed the heartbeat limit.
    let A : List ℤ := smulZV 25 coeffE4FourthListZV
    let B : List ℤ := smulZV (-49) (mulZV coeffE6SqListZV coeffE4ListZV)
    let C : List ℤ := smulZV 48 (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV)
    let D : List ℤ := mulZV coeffLinListZV coeffE2SqListZV
    have hAB : coeffZV (addZV A B) n = coeffZV A n + coeffZV B n :=
      coeffZV_addZV (a := A) (b := B) (n := n) hn
    have hABC : coeffZV (addZV (addZV A B) C) n = coeffZV (addZV A B) n + coeffZV C n :=
      coeffZV_addZV (a := addZV A B) (b := C) (n := n) hn
    have hABCD :
        coeffZV (addZV (addZV (addZV A B) C) D) n =
          coeffZV (addZV (addZV A B) C) n + coeffZV D n :=
      coeffZV_addZV (a := addZV (addZV A B) C) (b := D) (n := n) hn
    -- Unfold the coefficient list into the `A+B+C+D` form.
    have hdef : coeffZV coeffVarphiNumListZV n = coeffZV (addZV (addZV (addZV A B) C) D) n := by
      rfl
    -- Combine.
    have hA : coeffZV A n = (25 : ℤ) * coeffZV coeffE4FourthListZV n := by
      simpa [A] using! (coeffZV_smulZV (c := (25 : ℤ)) (a := coeffE4FourthListZV) (n := n) hn)
    have hB : coeffZV B n = (-(49 : ℤ)) * coeffZV (mulZV coeffE6SqListZV coeffE4ListZV) n := by
      simpa [B] using!
        (coeffZV_smulZV (c := (-(49 : ℤ))) (a := mulZV coeffE6SqListZV coeffE4ListZV) (n := n) hn)
    have hC : coeffZV C n = (48 : ℤ) *
      coeffZV (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV) n :=
      coeffZV_smulZV 48 (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV) n hn
    grind only
  -- Rewrite each product coefficient to the corresponding `mulFunZV` expression.
  have hE6SqE4 :
      coeffZV (mulZV coeffE6SqListZV coeffE4ListZV) n = mulFunZV coeffE6SqZV coeffE4ZV n := by
    have hmul := coeffZV_mulZV (a := coeffE6SqListZV) (b := coeffE4ListZV) (n := n) hn
    have ha : ∀ j ∈ Finset.range (n + 1), coeffZV coeffE6SqListZV j = coeffE6SqZV j := by
      intro j hj
      have hjle : j ≤ n := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hj)
      exact hE6Sq j (lt_of_le_of_lt hjle hn)
    have hb : ∀ j ∈ Finset.range (n + 1), coeffZV coeffE4ListZV (n - j) = coeffE4ZV (n - j) := by
      intro j hj
      have hnsub : n - j ≤ n := Nat.sub_le _ _
      exact hE4 (n - j) (lt_of_le_of_lt hnsub hn)
    simpa [mulFunZV] using!
      (hmul.trans (by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [ha j hj, hb j hj]))
  have hE6E4SqE2 :
      coeffZV (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV) n =
        mulFunZV (fun m => mulFunZV coeffE6ZV coeffE4SqZV m) coeffE2ZV n := by
    have hmul2 := coeffZV_mulZV (a := mulZV coeffE6ListZV coeffE4SqListZV) (b :=
      coeffE2ListZV) (n :=
      n) hn
    have ha2 : ∀ j ∈ Finset.range (n + 1), coeffZV (mulZV coeffE6ListZV coeffE4SqListZV) j =
        mulFunZV coeffE6ZV coeffE4SqZV j := by
      intro j hj
      have hjle : j ≤ n := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hj)
      have hjlt : j < NVarphi := lt_of_le_of_lt hjle hn
      -- reuse the computation at level `j`
      have hmul1 := coeffZV_mulZV (a := coeffE6ListZV) (b := coeffE4SqListZV) (n := j) hjlt
      have ha1 : ∀ k ∈ Finset.range (j + 1), coeffZV coeffE6ListZV k = coeffE6ZV k := by
        intro k hk
        have hk_le : k ≤ j := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hk)
        exact hE6 k (lt_of_le_of_lt (le_trans hk_le hjle) hn)
      have hb1 : ∀ k ∈ Finset.range (j + 1), coeffZV coeffE4SqListZV (j - k) = coeffE4SqZV (j -
        k) := by
        intro k hk
        have hsub : j - k ≤ j := Nat.sub_le _ _
        exact hE4Sq (j - k) (lt_of_le_of_lt (le_trans hsub hjle) hn)
      simpa [mulFunZV] using!
        (hmul1.trans (by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [ha1 k hk, hb1 k hk]))
    have hb2 : ∀ j ∈ Finset.range (n + 1), coeffZV coeffE2ListZV (n - j) = coeffE2ZV (n - j) := by
      intro j hj
      have hnsub : n - j ≤ n := Nat.sub_le _ _
      exact hE2 (n - j) (lt_of_le_of_lt hnsub hn)
    simpa [mulFunZV] using!
      (hmul2.trans (by
        refine Finset.sum_congr rfl ?_
        intro j hj
        -- Avoid `simp` canceling a common factor (which creates a disjunction); unfold `mulFunZV`
        -- instead.
        simp [ha2 j hj, hb2 j hj, mulFunZV]))
  have hLinE2Sq :
      coeffZV (mulZV coeffLinListZV coeffE2SqListZV) n = mulFunZV coeffLinZV coeffE2SqZV n := by
    have hmul := coeffZV_mulZV (a := coeffLinListZV) (b := coeffE2SqListZV) (n := n) hn
    have ha : ∀ j ∈ Finset.range (n + 1), coeffZV coeffLinListZV j = coeffLinZV j := by
      intro j hj
      have hjle : j ≤ n := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hj)
      exact hLin j (lt_of_le_of_lt hjle hn)
    have hb : ∀ j ∈ Finset.range (n + 1),
        coeffZV coeffE2SqListZV (n - j) = coeffE2SqZV (n - j) := by
      intro j hj
      have hnsub : n - j ≤ n := Nat.sub_le _ _
      exact hE2Sq (n - j) (lt_of_le_of_lt hnsub hn)
    simpa [mulFunZV] using!
      (hmul.trans (by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [ha j hj, hb j hj]))
  calc
    coeffZV coeffVarphiNumListZV n
        = (25 : ℤ) * coeffZV coeffE4FourthListZV n +
            (-(49 : ℤ)) * coeffZV (mulZV coeffE6SqListZV coeffE4ListZV) n +
              (48 : ℤ) * coeffZV (mulZV (mulZV coeffE6ListZV coeffE4SqListZV) coeffE2ListZV) n +
                coeffZV (mulZV coeffLinListZV coeffE2SqListZV) n := hmain
    _ = (25 : ℤ) * coeffE4FourthZV n +
          (-(49 : ℤ)) * (mulFunZV coeffE6SqZV coeffE4ZV n) +
            (48 : ℤ) * (mulFunZV (fun m => mulFunZV coeffE6ZV coeffE4SqZV m) coeffE2ZV n) +
              (mulFunZV coeffLinZV coeffE2SqZV n) := by
          simp [hE4Fourth n hn, hE6SqE4, hE6E4SqE2, hLinE2Sq]
    _ = coeffVarphiNumZV n := by simp [coeffVarphiNumZV]

/--
The computed coefficient list agrees with the expected truncation coefficients from Appendix A.
-/
public lemma coeffVarphiNumListZV_eq_expected :
    coeffVarphiNumListZV = AppendixA.varphi_trunc_geOne_coeffsZV := by
  set_option maxRecDepth 20000 in
  decide

end SpherePacking.Dim24.Ineq2Varphi
