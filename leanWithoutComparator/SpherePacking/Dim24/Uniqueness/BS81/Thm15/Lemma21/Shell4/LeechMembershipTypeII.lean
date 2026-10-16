-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechMembershipDefs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionA
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionAMain


/-!
# Shell4 Isometry Leech Membership Type II

Leech lattice membership (BS81 Lemma 21), Pattern II: `((±2)^8, 0^16)`.

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

lemma pattern1_even (z : Fin 24 → ℤ) (hz : isPattern1 z) : ∀ k, Even (z k) :=
  fun k => even_of_isPattern1 hz k

/--
Leech lattice membership for Pattern II: an integer vector `z` with pattern `((±2)^8, 0^16)`
whose residue word lies in `leechParityCode` and whose coordinate sum is divisible by `8`
defines a Leech lattice vector `vecOfScaledStd z`.
-/
public theorem mem_leechLattice_of_typeII
    (z : Fin 24 → ℤ)
    (hz : isPattern1 z)
    (hw :
      Shell4IsometryLeechConstructionA.halfWord z ∈ Shell4IsometryLeechParityCode.leechParityCode)
    (hsum : (8 : ℤ) ∣ ∑ k : Fin 24, z k) :
  vecOfScaledStd z ∈ (LeechLattice : Set ℝ²⁴) := by
  have hzEven : ∀ k, Even (z k) := pattern1_even z hz
  simpa [vecOfScaledStd_eq_leechD24_vecOfScaledStd,
    Shell4IsometryLeechConstructionA.vecOfScaledStd] using!
    (Shell4IsometryLeechConstructionA.mem_LeechLattice_vecOfScaledStd_of_even_of_halfWord_mem
      (z := z) hzEven hw hsum)

end Shell4IsometryLeechMembership

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
