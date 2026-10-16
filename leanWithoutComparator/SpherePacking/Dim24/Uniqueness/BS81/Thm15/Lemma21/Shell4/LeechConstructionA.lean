-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.LeechLattice.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechD24
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechParityCode
public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.InnerProductSpace.PiL2


/-!
# Construction A: basic integer data

This file collects basic integer-valued gadgets used in the Construction-A description of the
Leech lattice, as they appear in the shell-4 isometry steps for BS81 Lemma 21.

We fix notation for the integral Leech generator rows, define the residue map `halfWord`, package
the coordinatewise divisibility-by-`4` condition as `fourMul`, and re-export the standard map
`vecOfScaledStd` turning an integer vector into a vector of `ℝ²⁴`.

## Main definitions
* `Shell4IsometryLeechConstructionA.halfWord`
* `Shell4IsometryLeechConstructionA.rowInt`, `Shell4IsometryLeechConstructionA.row0`,
  `Shell4IsometryLeechConstructionA.last`
* `Shell4IsometryLeechConstructionA.fourMul`
* `Shell4IsometryLeechConstructionA.vecOfScaledStd`
* `Shell4IsometryLeechConstructionA.liftRowInt`

## Main statements
* `Shell4IsometryLeechConstructionA.four_dvd_sub_of_halves_cast_eq`
* `Shell4IsometryLeechConstructionA.mem_LeechLattice_vecOfScaledStd_row0`
* `Shell4IsometryLeechConstructionA.mem_LeechLattice_vecOfScaledStd_zDiff`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.CodingTheory

namespace Shell4IsometryLeechConstructionA

/-! ## Integer vectors associated to binary words -/

def wordToInt (w : BinWord 24) : Fin 24 → ℤ := fun i : Fin 24 => if w i = 0 then 0 else 1

lemma wordToInt_apply_eq_zero {w : BinWord 24} {i : Fin 24} (h : w i = 0) :
    wordToInt w i = 0 := by
  simp [wordToInt, h]

lemma wordToInt_apply_eq_one {w : BinWord 24} {i : Fin 24} (h : w i ≠ 0) :
    wordToInt w i = 1 := by
  simp [wordToInt, h]

/--
The binary word obtained by reducing `z / 2` modulo `2`, coordinatewise.

For even `z`, this records the mod-`4` residue class used in Construction A.
-/
@[expose] public def halfWord (z : Fin 24 → ℤ) : BinWord 24 :=
  fun i : Fin 24 => ((z i / 2 : ℤ) : ZMod 2)

/-- The `i`-th Leech generator row, viewed as an integer vector `Fin 24 → ℤ`. -/
@[expose] public def rowInt (i : Fin 24) : Fin 24 → ℤ :=
  fun k : Fin 24 => leechGeneratorMatrixInt i k

/-- The index `23`, used for the distinguished last generator row. -/
public abbrev last : Fin 24 := 23
/-- The index `0`, used for the distinguished first generator row. -/
public abbrev row0 : Fin 24 := 0

/-- Coordinate description of the distinguished row `rowInt row0`. -/
public lemma row0_apply (k : Fin 24) :
    rowInt row0 k = (if k = 0 then (8 : ℤ) else 0) := by
  fin_cases k <;> rfl

/-- Coordinate description of the distinguished row `rowInt last`. -/
public lemma row_last_apply (k : Fin 24) :
    rowInt last k = (if k = 0 then (-3 : ℤ) else 1) := by
  fin_cases k <;> rfl

/-- Every coordinate of `rowInt last` is an odd integer. -/
public lemma odd_rowInt_last (k : Fin 24) :
    Odd (rowInt last k) := by
  by_cases hk0 : k = 0
  · subst hk0
    refine ⟨-2, ?_⟩
    simp [row_last_apply]
  · refine ⟨0, ?_⟩
    simp [row_last_apply, hk0]

/-! ## A basic `mod 4` congruence lemma -/

/--
If `a` and `b` are even, and their halves coincide modulo `2`, then `b - a` is divisible by `4`.

This is a convenient "mod-2 on halves implies mod-4" upgrade used in the Construction-A argument.
-/
public lemma four_dvd_sub_of_halves_cast_eq {a b : ℤ} (ha : Even a) (hb : Even b)
    (h : ((a / 2 : ℤ) : ZMod 2) = ((b / 2 : ℤ) : ZMod 2)) :
    (4 : ℤ) ∣ (b - a) := by
  have hdvd2 : (2 : ℤ) ∣ (b / 2 - a / 2) := by
    simpa using!
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a := a / 2) (b := b / 2) (c := 2)).1 h
  rcases hdvd2 with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have ha2 : 2 * (a / 2) = a := Int.two_mul_ediv_two_of_even ha
  have hb2 : 2 * (b / 2) = b := Int.two_mul_ediv_two_of_even hb
  calc
    b - a = 2 * (b / 2) - 2 * (a / 2) := by simp [hb2, ha2]
    _ = 2 * (b / 2 - a / 2) := by ring
    _ = 2 * (2 * k) := by simp [hk]
    _ = 4 * k := by ring

/-! ## The `4·D₂₄` sublattice condition -/

/-- The predicate that an integer vector has all coordinates divisible by `4`. -/
@[expose] public def fourMul (x : Fin 24 → ℤ) : Prop :=
  ∀ i : Fin 24, (4 : ℤ) ∣ x i

/-! ## `vecOfScaledStd` (scaled standard basis) -/

/--
The vector of `ℝ²⁴` whose scaled coordinates in the standard basis are the integers `z`.

This is re-exported from `Shell4IsometryLeechD24` to keep the Construction-A files self-contained.
-/
@[expose] public def vecOfScaledStd (z : Fin 24 → ℤ) : EuclideanSpace ℝ (Fin 24) :=
  Shell4IsometryLeechD24.vecOfScaledStd z

/-- Additivity of `vecOfScaledStd`. -/
public lemma vecOfScaledStd_add (z₁ z₂ : Fin 24 → ℤ) :
    vecOfScaledStd (z₁ + z₂) = vecOfScaledStd z₁ + vecOfScaledStd z₂ := by
  ext k
  simp [vecOfScaledStd, Shell4IsometryLeechD24.vecOfScaledStd, Shell4IsometryLeechD24.vecOfInt,
    Pi.add_apply, mul_add]

/-- Compatibility of `vecOfScaledStd` with `ℤ`-scalar multiplication. -/
public lemma vecOfScaledStd_zsmul (n : ℤ) (z : Fin 24 → ℤ) :
    vecOfScaledStd (n • z) = n • vecOfScaledStd z := by
  ext k
  simp [vecOfScaledStd, Shell4IsometryLeechD24.vecOfScaledStd, Shell4IsometryLeechD24.vecOfInt,
    Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, mul_assoc, mul_comm]

/-- The scaled vector associated to the first generator row lies in `LeechLattice`. -/
public lemma mem_LeechLattice_vecOfScaledStd_row0 :
    vecOfScaledStd (rowInt row0) ∈ (LeechLattice : Set _) := by
  have h : leechGeneratorRows row0 ∈ (LeechLattice : Set _) := Submodule.subset_span ⟨row0, rfl⟩
  assumption

/-- The scaled vector associated to each `zDiff i` lies in `LeechLattice`. -/
public lemma mem_LeechLattice_vecOfScaledStd_zDiff (i : Fin 24) :
    vecOfScaledStd (Shell4IsometryLeechD24.zDiff i) ∈ (LeechLattice : Set _) := by
  by_cases hi0 : i = 0
  · subst hi0
    have hz0 :
        vecOfScaledStd (Shell4IsometryLeechD24.zDiff (0 : Fin 24)) =
          (0 : EuclideanSpace ℝ (Fin 24)) := by
      ext k
      simp [Shell4IsometryLeechD24.zDiff, vecOfScaledStd, Shell4IsometryLeechD24.vecOfScaledStd,
        Shell4IsometryLeechD24.vecOfInt]
    simp [hz0]
  · simpa [vecOfScaledStd] using! Shell4IsometryLeechD24.mem_LeechLattice_vecOfScaledStd_zDiff i hi0

/-! ## Parity-code lifting primitives -/

/--
The scalar used to make the Leech generator row `rowInt i` even.

The last row is odd, so we use the factor `2` there and `1` elsewhere.
-/
@[expose] public def liftRowCoeff (i : Fin 24) : ℤ :=
  if i = last then 2 else 1

/--
An even integer vector lifting the `i`-th Leech parity basis vector.

It is defined as `liftRowCoeff i • rowInt i`.
-/
@[expose] public def liftRowInt (i : Fin 24) : Fin 24 → ℤ :=
  (liftRowCoeff i) • rowInt i

end Shell4IsometryLeechConstructionA

end
end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
