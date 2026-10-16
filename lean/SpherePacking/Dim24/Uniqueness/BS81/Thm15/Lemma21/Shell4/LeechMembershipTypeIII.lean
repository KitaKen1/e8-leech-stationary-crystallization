-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechMembershipDefs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionA
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionAMain

/-!
# Shell4 Isometry Leech Membership Type III

Leech lattice membership (BS81 Lemma 21), Pattern III: `((±1)^23, (±3)^1)`.

## Main statement
* `Shell4IsometryLeechMembership.mem_leechLattice_of_typeIII`

-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Uniqueness.BS81
open Uniqueness.BS81.CodingTheory
open Uniqueness.BS81.Thm15.Lemma21

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace Shell4IsometryLeechMembership

open Set

lemma pattern3_odd (z : Fin 24 → ℤ) (hz : isPattern3 z) : ∀ k, Odd (z k) := by
  intro k
  rcases hz.2 k with hz1 | hzN1 | hz3 | hzN3
  · simp [hz1]
  · simp [hzN1]
  · refine ⟨1, ?_⟩
    simp [hz3]
  · refine ⟨-2, ?_⟩
    simp [hzN3]

lemma pattern3_sub_rowLast_even (z : Fin 24 → ℤ) (hz : isPattern3 z) :
    ∀ k,
      Even (z k -
        Shell4IsometryLeechConstructionA.rowInt Shell4IsometryLeechConstructionA.last k) := by
  intro k
  exact
    Odd.sub_odd (pattern3_odd z hz k) (Shell4IsometryLeechConstructionA.odd_rowInt_last (k := k))

/-! Remaining inputs: residue (`halfWord`) + mod-8 sum for `e := z - rowInt last`. -/

/--
Leech lattice membership for Pattern III: an integer vector `z` with pattern `((±1)^23, (±3)^1)`
defines a Leech lattice vector `vecOfScaledStd z`, provided the Construction-A residue and mod-`8`
sum conditions hold for `z - rowInt last`.
-/
public theorem mem_leechLattice_of_typeIII
    (z : Fin 24 → ℤ)
    (hz : isPattern3 z)
    (hw :
      Shell4IsometryLeechConstructionA.halfWord
          (z - Shell4IsometryLeechConstructionA.rowInt Shell4IsometryLeechConstructionA.last) ∈
      Shell4IsometryLeechParityCode.leechParityCode)
    (hsum :
      (8 : ℤ) ∣
        ∑ k : Fin 24,
          (z k - Shell4IsometryLeechConstructionA.rowInt Shell4IsometryLeechConstructionA.last k)) :
    vecOfScaledStd z ∈ (LeechLattice : Set ℝ²⁴) := by
  let rowLast :=
    Shell4IsometryLeechConstructionA.rowInt Shell4IsometryLeechConstructionA.last
  let e : Fin 24 → ℤ := z - rowLast
  have heEven : ∀ k, Even (e k) := by
    intro k
    simpa [e, rowLast, Pi.sub_apply] using! (pattern3_sub_rowLast_even z hz k)
  have heMem : vecOfScaledStd e ∈ (LeechLattice : Set ℝ²⁴) := by
    have heMemCA :
        Shell4IsometryLeechConstructionA.vecOfScaledStd e ∈ (LeechLattice : Set ℝ²⁴) :=
      Shell4IsometryLeechConstructionA.mem_LeechLattice_vecOfScaledStd_of_even_of_halfWord_mem
        (z := e) heEven
        (by simpa [e, rowLast, Pi.sub_apply] using! hw)
        (by simpa [e, rowLast, Pi.sub_apply] using! hsum)
    simpa [vecOfScaledStd_eq_leechD24_vecOfScaledStd,
      Shell4IsometryLeechConstructionA.vecOfScaledStd] using! heMemCA
  have hrowLast :
      vecOfScaledStd rowLast ∈ (LeechLattice : Set ℝ²⁴) := by
    simpa [rowLast, vecOfScaledStd_leechGeneratorRows] using!
      (Submodule.subset_span ⟨Shell4IsometryLeechConstructionA.last, rfl⟩ :
        leechGeneratorRows Shell4IsometryLeechConstructionA.last ∈ (LeechLattice : Set ℝ²⁴))
  have hzEq : z = rowLast + e := by
    funext k
    simp [e, rowLast, Pi.add_apply, Pi.sub_apply]
  simpa [hzEq, vecOfScaledStd_add] using!
    (LeechLattice : Submodule ℤ ℝ²⁴).add_mem hrowLast heMem
end Shell4IsometryLeechMembership

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
