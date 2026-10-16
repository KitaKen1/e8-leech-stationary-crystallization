-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechMembershipDefs
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionAFourD24


/-!
# Shell4 Isometry Leech Membership Type I

Leech lattice membership (BS81 Lemma 21), Pattern I: `((±4)^2, 0^22)`.

-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Uniqueness.BS81.Thm15.Lemma21

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace Shell4IsometryLeechMembership

open Set

/--
Leech lattice membership for Pattern I: an integer vector `z` with pattern `((±4)^2, 0^22)`
defines a Leech lattice vector `vecOfScaledStd z`.
-/
public theorem mem_leechLattice_of_typeI
    (z : Fin 24 → ℤ)
    (hz : isPattern2 z) :
    vecOfScaledStd z ∈ (LeechLattice : Set ℝ²⁴) := by
  have h4 : Shell4IsometryLeechConstructionA.fourMul z := by
    intro i
    rcases hz.2 i with h | h | h <;> simp [h]
  -- The nonzero support has cardinality `2`.
  let sNZ : Finset (Fin 24) := Finset.univ.filter fun k : Fin 24 => z k ≠ 0
  have hcard_sNZ : sNZ.card = 2 := by
    have hzeros : (Finset.univ.filter fun k : Fin 24 => z k = 0).card = 22 := by simpa using! hz.1
    have hsplit :
        (Finset.univ.filter fun k : Fin 24 => z k = 0).card +
            (Finset.univ.filter fun k : Fin 24 => z k ≠ 0).card =
          (Finset.univ : Finset (Fin 24)).card :=
      Finset.card_filter_add_card_filter_not fun k => z k = 0
    have h' : 22 + (Finset.univ.filter fun k : Fin 24 => z k ≠ 0).card = 24 := by
      simpa [hzeros] using! hsplit
    exact Eq.symm (Nat.add_left_cancel (id (Eq.symm h')))
  rcases Finset.card_eq_two.1 hcard_sNZ with ⟨i, j, hij, hsNZ⟩
  have hi_mem : i ∈ sNZ := by simp [hsNZ]
  have hj_mem : j ∈ sNZ := by simp [hsNZ]
  have hzi0 : z i ≠ 0 := (Finset.mem_filter.1 hi_mem).2
  have hzj0 : z j ≠ 0 := (Finset.mem_filter.1 hj_mem).2
  have hzpm4 {k : Fin 24} (hk0 : z k ≠ 0) : z k = 4 ∨ z k = -4 := by
    rcases hz.2 k with h0 | h4 | hN4
    · exact (hk0 (by simp [h0])).elim
    · exact Or.inl h4
    · exact Or.inr hN4
  have hzi : z i = 4 ∨ z i = -4 := hzpm4 hzi0
  have hzj : z j = 4 ∨ z j = -4 := hzpm4 hzj0
  have hsum : (∑ k : Fin 24, z k) = z i + z j := by
    have hsum_sNZ : (∑ k ∈ sNZ, z k) = z i + z j := by simp [hsNZ, hij]
    have hsplit :
        (∑ k ∈ sNZ, z k) + (∑ k ∈ (Finset.univ.filter fun k : Fin 24 => ¬ z k ≠ 0), z k) =
          ∑ k : Fin 24, z k :=
      Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => z x ≠ 0) z
    have hzero : (∑ k ∈ (Finset.univ.filter fun k : Fin 24 => z k = 0), z k) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hk0 : z k = 0 := (Finset.mem_filter.1 hk).2
      simp [hk0]
    have hsupport : (∑ k ∈ sNZ, z k) = ∑ k : Fin 24, z k := by
      have : (∑ k ∈ sNZ, z k) + 0 = ∑ k : Fin 24, z k := by simpa [hzero] using! hsplit
      simpa using! this
    exact hsupport.symm.trans hsum_sNZ
  have h8 : (8 : ℤ) ∣ ∑ k : Fin 24, z k := by
    rcases hzi with hi | hi <;> rcases hzj with hj | hj <;> simp [hsum, hi, hj]
  have hmem :
      Shell4IsometryLeechConstructionA.vecOfScaledStd z ∈ (LeechLattice : Set ℝ²⁴) :=
    Shell4IsometryLeechConstructionA.mem_LeechLattice_vecOfScaledStd_of_fourMul_of_sum_dvd8 z h4 h8
  simpa [vecOfScaledStd_eq_leechD24_vecOfScaledStd,
    Shell4IsometryLeechConstructionA.vecOfScaledStd] using! hmem

end Shell4IsometryLeechMembership

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
