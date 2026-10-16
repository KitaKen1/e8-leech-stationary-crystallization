-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionA
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


/-!
# Construction A: the `4·D₂₄` condition

This file proves the "`4·D₂₄`" part of the Construction-A description of the Leech lattice:
an integer vector whose coordinates are divisible by `4` and whose total sum is divisible by `8`
maps to a vector in `LeechLattice` under `vecOfScaledStd`.

## Main statement
* `Shell4IsometryLeechConstructionA.mem_LeechLattice_vecOfScaledStd_of_fourMul_of_sum_dvd8`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Shell4IsometryLeechConstructionA

open Finset

lemma exists_row0_zDiff_decomp
    (x : Fin 24 → ℤ) (h4 : fourMul x) (h8 : (8 : ℤ) ∣ ∑ i : Fin 24, x i) :
    ∃ t : ℤ, ∃ c : Fin 24 → ℤ,
      x = t • rowInt row0 + ∑ i : Fin 24, (c i) • Shell4IsometryLeechD24.zDiff i := by
  let c : Fin 24 → ℤ := fun i => if i = 0 then 0 else x i / 4
  have hc0 : c 0 = 0 := by simp [c]
  have hci (i : Fin 24) (hi0 : i ≠ 0) : x i = 4 * c i := by
    have h4i : (4 : ℤ) ∣ x i := h4 i
    simpa [c, hi0, mul_comm] using! (Int.ediv_mul_cancel h4i).symm
  let sSet : Finset (Fin 24) := univ.erase (0 : Fin 24)
  let s : ℤ := ∑ i ∈ sSet, c i
  have hsum_x : (∑ i : Fin 24, x i) = x 0 + 4 * s := by
    have hsplit : (∑ i : Fin 24, x i) = x 0 + ∑ i ∈ sSet, x i := by
      rfl
    have hrepl : (∑ i ∈ sSet, x i) = ∑ i ∈ sSet, 4 * c i := by
      refine sum_congr rfl (fun i hi => ?_)
      have hi0 : i ≠ 0 := (mem_erase.1 hi).1
      simp [hci i hi0]
    have hmul : (∑ i ∈ sSet, 4 * c i) = 4 * (∑ i ∈ sSet, c i) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using!
        (Finset.mul_sum (4 : ℤ) (s := sSet) (f := fun i => c i)).symm
    calc
      (∑ i : Fin 24, x i)
          = x 0 + ∑ i ∈ sSet, x i := hsplit
      _ = x 0 + ∑ i ∈ sSet, 4 * c i := by simp [sSet, hrepl]
      _ = x 0 + 4 * (∑ i ∈ sSet, c i) := by simp [hmul]
      _ = x 0 + 4 * s := by simp [s]
  rcases h8 with ⟨t, ht⟩
  refine ⟨t, c, ?_⟩
  funext k
  by_cases hk0 : k = 0
  · subst hk0
    have hx0 : x 0 = 8 * t - 4 * s := by
      nlinarith [hsum_x, ht]
    have hrow0 : (t • rowInt row0) 0 = 8 * t := by
      have hrow0' : rowInt row0 (0 : Fin 24) = (8 : ℤ) := by
        simp [row0_apply]
      simp [Pi.smul_apply, hrow0', mul_comm]
    have hzsum :
        (∑ i : Fin 24, (c i) • Shell4IsometryLeechD24.zDiff i) 0 = -4 * s := by
      have hsplit :
          (∑ i : Fin 24, c i * Shell4IsometryLeechD24.zDiff i 0) =
            c 0 * Shell4IsometryLeechD24.zDiff 0 0 +
              ∑ i ∈ sSet, c i * Shell4IsometryLeechD24.zDiff i 0 := by
        rfl
      have hrepl :
          (∑ i ∈ sSet, c i * Shell4IsometryLeechD24.zDiff i 0) = ∑ i ∈ sSet, c i * (-4 : ℤ) := by
        refine sum_congr rfl (fun i hi => ?_)
        have hi0 : i ≠ 0 := (mem_erase.1 hi).1
        simp [Shell4IsometryLeechD24.zDiff, hi0]
      calc
        (∑ i : Fin 24, (c i) • Shell4IsometryLeechD24.zDiff i) 0 =
            ∑ i : Fin 24, c i * Shell4IsometryLeechD24.zDiff i 0 := by
              simp [Finset.sum_apply, zsmul_eq_mul]
        _ = c 0 * Shell4IsometryLeechD24.zDiff 0 0 +
              ∑ i ∈ sSet, c i * Shell4IsometryLeechD24.zDiff i 0 := hsplit
        _ = ∑ i ∈ sSet, c i * Shell4IsometryLeechD24.zDiff i 0 := by simp [hc0]
        _ = ∑ i ∈ sSet, c i * (-4 : ℤ) := by simp [hrepl]
        _ = (∑ i ∈ sSet, c i) * (-4 : ℤ) := by
              simpa using! (Finset.sum_mul (s := sSet) (f := fun i => c i) (a := (-4 : ℤ))).symm
        _ = -4 * s := by
              simp [s, mul_comm]
    calc
      x (0 : Fin 24) = 8 * t - 4 * s := hx0
      _ = 8 * t + (-4 * s) := by ring
      _ = (t • rowInt row0) 0 + (∑ i : Fin 24, (c i) • Shell4IsometryLeechD24.zDiff i) 0 := by
            rw [hrow0, hzsum]
  · have hk0' : k ≠ 0 := hk0
    have hrow0k : (t • rowInt row0) k = 0 := by
      have : rowInt row0 k = 0 := by
        simp [row0_apply, hk0]
      simp [Pi.smul_apply, this]
    have hzsumk :
        (∑ i : Fin 24, (c i) • Shell4IsometryLeechD24.zDiff i) k = 4 * c k := by
      have hsingle :
          (∑ i : Fin 24, c i * Shell4IsometryLeechD24.zDiff i k) =
            c k * Shell4IsometryLeechD24.zDiff k k := by
        refine sum_eq_single k ?_ ?_
        · intro i _hi hik
          by_cases hi0 : i = 0
          · subst hi0
            simp [Shell4IsometryLeechD24.zDiff]
          · have hki : k ≠ i := by simpa [eq_comm] using! hik
            simp [Shell4IsometryLeechD24.zDiff, hi0, hk0', hki]
        · intro hk_mem
          exact (hk_mem (mem_univ k)).elim
      calc
        (∑ i : Fin 24, (c i) • Shell4IsometryLeechD24.zDiff i) k =
            ∑ i : Fin 24, c i * Shell4IsometryLeechD24.zDiff i k := by
              simp [Finset.sum_apply, zsmul_eq_mul]
        _ = c k * Shell4IsometryLeechD24.zDiff k k := hsingle
        _ = c k * 4 := by simp [Shell4IsometryLeechD24.zDiff, hk0']
        _ = 4 * c k := by ring
    have hxk : x k = 4 * c k := by
      -- `k ≠ 0` so use `hci`
      simpa using! hci k hk0'
    calc
      x k = 4 * c k := hxk
      _ = (t • rowInt row0) k + (∑ i : Fin 24, (c i) • Shell4IsometryLeechD24.zDiff i) k := by
            rw [hrow0k, hzsumk]
            simp

/--
If an integer vector `x` is coordinatewise divisible by `4` and its total sum is divisible by `8`,
then `vecOfScaledStd x` lies in the Leech lattice.
-/
public theorem mem_LeechLattice_vecOfScaledStd_of_fourMul_of_sum_dvd8
    (x : Fin 24 → ℤ) (h4 : fourMul x) (h8 : (8 : ℤ) ∣ ∑ i : Fin 24, x i) :
    vecOfScaledStd x ∈ (LeechLattice : Set _) := by
  rcases exists_row0_zDiff_decomp x h4 h8 with ⟨t, c, rfl⟩
  have hrow0 : vecOfScaledStd (t • rowInt row0) ∈ (LeechLattice : Set _) := by
    have hmem : (t : ℤ) • vecOfScaledStd (rowInt row0) ∈ (LeechLattice : Set _) :=
      (LeechLattice : Submodule ℤ _).smul_mem t mem_LeechLattice_vecOfScaledStd_row0
    rw [vecOfScaledStd_zsmul t (rowInt row0)]
    exact hmem
  have hzDiffMem :
      vecOfScaledStd (∑ i : Fin 24, (c i) • Shell4IsometryLeechD24.zDiff i) ∈
        (LeechLattice : Set _) := by
    let φ : (Fin 24 → ℤ) →+ EuclideanSpace ℝ (Fin 24) :=
      { toFun := vecOfScaledStd
        map_zero' := by
          ext k
          simp [vecOfScaledStd, Shell4IsometryLeechD24.vecOfScaledStd,
            Shell4IsometryLeechD24.vecOfInt]
        map_add' := by intro a b; simpa using! vecOfScaledStd_add a b }
    have hterm (i : Fin 24) :
        vecOfScaledStd ((c i) • Shell4IsometryLeechD24.zDiff i) ∈ (LeechLattice : Set _) := by
      have hmem :
          (c i) • vecOfScaledStd (Shell4IsometryLeechD24.zDiff i) ∈ (LeechLattice : Set _) :=
        (LeechLattice : Submodule ℤ _).smul_mem (c i) (mem_LeechLattice_vecOfScaledStd_zDiff i)
      rw [vecOfScaledStd_zsmul (c i) (Shell4IsometryLeechD24.zDiff i)]
      exact hmem
    have htermSum :
        (∑ i ∈ (Finset.univ : Finset (Fin 24)),
            vecOfScaledStd ((c i) • Shell4IsometryLeechD24.zDiff i)) ∈
          (LeechLattice : Set _) := by
      simpa using!
        (LeechLattice : Submodule ℤ _).sum_mem (t := (Finset.univ : Finset (Fin 24)))
          (fun i _hi => hterm i)
    have hsum :
        vecOfScaledStd (∑ i ∈ (Finset.univ : Finset (Fin 24)),
            (c i) • Shell4IsometryLeechD24.zDiff i) =
          ∑ i ∈ (Finset.univ : Finset (Fin 24)),
            vecOfScaledStd ((c i) • Shell4IsometryLeechD24.zDiff i) := by
      have hsum0 :=
        (map_sum φ (fun i : Fin 24 => (c i) • Shell4IsometryLeechD24.zDiff i)
          (Finset.univ : Finset (Fin 24)))
      dsimp [φ] at hsum0
      exact hsum0
    exact Set.mem_of_eq_of_mem hsum htermSum
  -- add both parts
  have hadd :
      vecOfScaledStd (t • rowInt row0) +
          vecOfScaledStd (∑ i : Fin 24, (c i) • Shell4IsometryLeechD24.zDiff i) ∈
        (LeechLattice : Set _) :=
    (LeechLattice : Submodule ℤ _).add_mem hrow0 hzDiffMem
  simpa [vecOfScaledStd_add] using! hadd

end Shell4IsometryLeechConstructionA

end
end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
