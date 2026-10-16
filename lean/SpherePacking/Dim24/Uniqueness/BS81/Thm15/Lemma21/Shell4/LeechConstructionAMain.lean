-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionA
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionAFourD24
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionALiftParity

/-!
# Construction A: an even membership criterion

This file proves the main even form of Construction A used in the shell-4 isometry steps for
BS81 Lemma 21.

## Main statement
* `Shell4IsometryLeechConstructionA.mem_LeechLattice_vecOfScaledStd_of_even_of_halfWord_mem`

## Proof outline
- Use `exists_even_leechVec_of_mem_leechParityCode` to lift the residue word `halfWord z` to an
  even Leech lattice vector `y` with the same residue and correct mod-8 sum.
- Show `z - y` is coordinatewise divisible by `4` using the congruence lemma
  `four_dvd_sub_of_halves_cast_eq`.
- Use the `4·D₂₄` membership lemma `mem_LeechLattice_vecOfScaledStd_of_fourMul_of_sum_dvd8` on
  `z - y`.
- Conclude by closure under addition in the `ℤ`-submodule `LeechLattice`.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Shell4IsometryLeechConstructionA

/--
If an integer vector `z` has even coordinates, residue word `halfWord z` in `leechParityCode`,
and total coordinate sum divisible by `8`, then `vecOfScaledStd z` lies in `LeechLattice`.
-/
public theorem mem_LeechLattice_vecOfScaledStd_of_even_of_halfWord_mem
    (z : Fin 24 → ℤ)
    (hzEven : ∀ k, Even (z k))
    (hw : halfWord z ∈ Shell4IsometryLeechParityCode.leechParityCode)
    (hsum : (8 : ℤ) ∣ ∑ k : Fin 24, z k) :
    vecOfScaledStd z ∈ (LeechLattice : Set _) := by
  rcases exists_even_leechVec_of_mem_leechParityCode (w := halfWord z) hw with
    ⟨y, hyEven, hyHalf, hySum, hyMem⟩
  have h4 : fourMul (z - y) := by
    intro k
    have hcast : ((y k / 2 : ℤ) : ZMod 2) = ((z k / 2 : ℤ) : ZMod 2) := by
      simpa [halfWord] using! congrArg (fun w => w k) hyHalf
    have : (4 : ℤ) ∣ (z k - y k) :=
      four_dvd_sub_of_halves_cast_eq (a := y k) (b := z k) (hyEven k) (hzEven k) hcast
    simpa [Pi.sub_apply] using! this
  have h8 : (8 : ℤ) ∣ ∑ k : Fin 24, (z - y) k := by
    simpa [Pi.sub_apply, Finset.sum_sub_distrib] using! hsum.sub hySum
  have hzDiffMem : vecOfScaledStd (z - y) ∈ (LeechLattice : Set _) :=
    mem_LeechLattice_vecOfScaledStd_of_fourMul_of_sum_dvd8 (x := z - y) h4 h8
  have hzEq : vecOfScaledStd z = vecOfScaledStd y + vecOfScaledStd (z - y) := by
    have : z = y + (z - y) := by
      funext k
      simp
    calc
      vecOfScaledStd z = vecOfScaledStd (y + (z - y)) :=
        congrArg vecOfScaledStd this
      _ = vecOfScaledStd y + vecOfScaledStd (z - y) := vecOfScaledStd_add _ _
  simpa [hzEq] using! (LeechLattice : Submodule ℤ _).add_mem hyMem hzDiffMem

end Shell4IsometryLeechConstructionA

end
end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
