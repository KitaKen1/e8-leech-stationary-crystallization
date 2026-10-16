-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionA
import Mathlib.Tactic.FinCases


/-!
# Construction A: lifting the parity code

This file lifts a word `w` in the Leech parity code to an even integer vector `y : Fin 24 → ℤ`
with `halfWord y = w`, satisfying the mod-`8` sum condition and lying in `LeechLattice` after
applying `vecOfScaledStd`.

## Main statement
* `Shell4IsometryLeechConstructionA.exists_even_leechVec_of_mem_leechParityCode`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.CodingTheory

namespace Shell4IsometryLeechConstructionA

open Finset

lemma even_liftRowInt (i : Fin 24) : ∀ k : Fin 24, Even (liftRowInt i k) := by
  intro k
  fin_cases i <;> fin_cases k <;> decide

lemma halfWord_liftRowInt (i : Fin 24) :
    halfWord (liftRowInt i) = Shell4IsometryLeechParityCode.leechParityVec i := by
  funext k
  fin_cases i <;> fin_cases k <;> decide

lemma sum_liftRowInt_dvd8 (i : Fin 24) : (8 : ℤ) ∣ ∑ k : Fin 24, liftRowInt i k := by
  fin_cases i <;> decide

lemma halfWord_add_of_even
    (y₁ y₂ : Fin 24 → ℤ) (hy₁ : ∀ k, Even (y₁ k)) (hy₂ : ∀ k, Even (y₂ k)) :
    halfWord (y₁ + y₂) = halfWord y₁ + halfWord y₂ := by
  funext k
  have h1 : (2 : ℤ) ∣ y₁ k := (hy₁ k).two_dvd
  have _ : (2 : ℤ) ∣ y₂ k := (hy₂ k).two_dvd
  simp [halfWord, Pi.add_apply, Int.add_ediv_of_dvd_left (a := y₁ k) (b := y₂ k) (c := (2 : ℤ)) h1,
    Int.cast_add]

lemma vecOfScaledStd_zero :
    vecOfScaledStd (0 : Fin 24 → ℤ) = (0 : EuclideanSpace ℝ (Fin 24)) := by
  ext k
  simp [vecOfScaledStd, Shell4IsometryLeechD24.vecOfScaledStd, Shell4IsometryLeechD24.vecOfInt]

private lemma zero_witness :
    ∃ y : Fin 24 → ℤ,
      (∀ k, Even (y k)) ∧
      halfWord y = (0 : BinWord 24) ∧
      (8 : ℤ) ∣ ∑ k : Fin 24, y k ∧
      vecOfScaledStd y ∈ (LeechLattice : Set _) := by
  refine ⟨0, ?_, ?_, ?_, ?_⟩
  · intro k
    simp
  · ext k
    simp [halfWord]
  · simp
  · simp [vecOfScaledStd_zero]

lemma mem_LeechLattice_vecOfScaledStd_row (i : Fin 24) :
    vecOfScaledStd (rowInt i) ∈ (LeechLattice : Set _) := by
  have h : leechGeneratorRows i ∈ (LeechLattice : Set _) := Submodule.subset_span ⟨i, rfl⟩
  simpa [vecOfScaledStd, rowInt, Shell4IsometryLeechD24.vecOfScaledStd,
    Shell4IsometryLeechD24.vecOfInt, leechGeneratorRows, leechGeneratorRowsUnscaled] using! h

lemma mem_LeechLattice_vecOfScaledStd_liftRowInt (i : Fin 24) :
    vecOfScaledStd (liftRowInt i) ∈ (LeechLattice : Set _) := by
  have hmem : liftRowCoeff i • vecOfScaledStd (rowInt i) ∈ (LeechLattice : Set _) :=
    (LeechLattice : Submodule ℤ _).smul_mem (liftRowCoeff i) (mem_LeechLattice_vecOfScaledStd_row i)
  have hEq : vecOfScaledStd (liftRowInt i) = liftRowCoeff i • vecOfScaledStd (rowInt i) := by
    simpa [liftRowInt] using! (vecOfScaledStd_zsmul (n := liftRowCoeff i) (z := rowInt i))
  simpa [hEq] using! hmem

/--
Lift a word in `leechParityCode` to an even integer vector in the Leech lattice with the same
`halfWord`.
-/
public theorem exists_even_leechVec_of_mem_leechParityCode
    (w : BinWord 24) (hw : w ∈ Shell4IsometryLeechParityCode.leechParityCode) :
    ∃ y : Fin 24 → ℤ,
      (∀ k, Even (y k)) ∧
      halfWord y = w ∧
      (8 : ℤ) ∣ ∑ k : Fin 24, y k ∧
      vecOfScaledStd y ∈ (LeechLattice : Set _) := by
  -- Unfold `leechParityCode` to the span definition.
  change w ∈ Shell4IsometryLeechParityCode.leechParitySubmodule at hw
  -- `leechParitySubmodule` is a `span` of the 12 basis vectors.
  -- We induct over that span, carrying along an integer witness.
  have hw' :
      w ∈
        Submodule.span (ZMod 2) (Set.range Shell4IsometryLeechParityCode.leechParityBasisVec) := by
    simpa [Shell4IsometryLeechParityCode.leechParitySubmodule] using! hw
  refine
    Submodule.span_induction
      (p := fun w _ =>
        ∃ y : Fin 24 → ℤ,
          (∀ k, Even (y k)) ∧
          halfWord y = w ∧
          (8 : ℤ) ∣ ∑ k : Fin 24, y k ∧
          vecOfScaledStd y ∈ (LeechLattice : Set _))
      (x := w) ?_ ?_ ?_ ?_ hw'
  · intro x hx
    rcases hx with ⟨t, rfl⟩
    -- For a basis vector, choose the corresponding lifted generator row.
    let i : Fin 24 := Shell4IsometryLeechParityCode.leechParityBasisIdx t
    refine ⟨liftRowInt i, even_liftRowInt i, ?_, ?_, mem_LeechLattice_vecOfScaledStd_liftRowInt i⟩
    · -- `halfWord` matches the basis word.
      simpa [Shell4IsometryLeechParityCode.leechParityBasisVec,
        Shell4IsometryLeechParityCode.leechParityBasisIdx]
        using! (halfWord_liftRowInt i)
    · -- mod-8 sum condition
      simpa using! sum_liftRowInt_dvd8 i
  · -- zero vector
    simpa using! zero_witness
  · -- addition
    intro w₁ w₂ _ _ hw₁ hw₂
    rcases hw₁ with ⟨y₁, hy₁E, hy₁w, hy₁sum, hy₁mem⟩
    rcases hw₂ with ⟨y₂, hy₂E, hy₂w, hy₂sum, hy₂mem⟩
    refine ⟨y₁ + y₂, ?_, ?_, ?_, ?_⟩
    · intro k
      exact (hy₁E k).add (hy₂E k)
    · -- `halfWord` additivity for even vectors
      simpa [hy₁w, hy₂w] using! (halfWord_add_of_even y₁ y₂ hy₁E hy₂E)
    · -- sum divisibility
      simpa [Finset.sum_add_distrib] using! hy₁sum.add hy₂sum
    · -- lattice membership
      simpa [vecOfScaledStd_add] using! (LeechLattice : Submodule ℤ _).add_mem hy₁mem hy₂mem
  · -- scalar multiplication by `a : ZMod 2` (only `0` or `1`)
    intro a w _ hw
    rcases hw with ⟨y, hyE, hyw, hysum, hymem⟩
    rcases (Uniqueness.BS81.CodingTheory.GolayBounds.zmod2_eq_zero_or_eq_one a) with rfl | rfl
    · -- `0 • w = 0`
      simpa using! zero_witness
    · exact ⟨y, hyE, by simpa [one_smul] using! hyw, hysum, hymem⟩

end Shell4IsometryLeechConstructionA

end
end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
