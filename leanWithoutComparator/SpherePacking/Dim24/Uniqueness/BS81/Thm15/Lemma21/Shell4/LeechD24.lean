-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.LeechLattice.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases


/-!
# A `4·D₂₄` sublattice of the Leech lattice

This file provides an explicit family of integer vectors generating a copy of `4·D₂₄` inside the
Leech lattice.  The main construction is the map `vecOfScaledStd` turning an integer vector
`z : Fin 24 → ℤ` into a vector of `ℝ²⁴`, together with the basic difference vectors `zDiff i`
with coordinates `(-4 at 0, +4 at i)`.

## Main definitions
* `Shell4IsometryLeechD24.vecOfInt`
* `Shell4IsometryLeechD24.vecOfScaledStd`
* `Shell4IsometryLeechD24.zDiff`

## Main statement
* `Shell4IsometryLeechD24.mem_LeechLattice_vecOfScaledStd_zDiff`

-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps

noncomputable section

open scoped BigOperators

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace Shell4IsometryLeechD24

/-! Integer combinations of generator rows (unscaled). -/

def combInt (c : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun k : Fin 24 => ∑ i : Fin 24, c i * leechGeneratorMatrixInt i k

/-- The vector in `ℝ²⁴` with standard coordinates given by the integers `z`. -/
@[expose] public noncomputable def vecOfInt (z : Fin 24 → ℤ) : ℝ²⁴ :=
  WithLp.toLp 2 fun k : Fin 24 => (z k : ℝ)

/-! `vecOfScaledStd`: scaled standard-basis reconstruction. -/

/-- The vector of `ℝ²⁴` whose scaled coordinates in the standard basis are the integers `z`. -/
@[expose] public noncomputable def vecOfScaledStd (z : Fin 24 → ℤ) : ℝ²⁴ :=
  ((Real.sqrt 8)⁻¹ : ℝ) • vecOfInt z

lemma sum_zsmul_leechGeneratorRows_eq_vecOfScaledStd_combInt (c : Fin 24 → ℤ) :
    (∑ i : Fin 24, c i • leechGeneratorRows i) = vecOfScaledStd (combInt c) := by
  ext k
  simp only [leechGeneratorRows, leechGeneratorRowsUnscaled, vecOfScaledStd, vecOfInt, combInt,
    WithLp.ofLp_sum, WithLp.ofLp_smul, zsmul_eq_mul, smul_eq_mul,
    Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_sum, Int.cast_mul,
    mul_comm]
  simpa [mul_assoc, mul_left_comm, mul_comm] using!
    (Finset.mul_sum ((Real.sqrt 8)⁻¹ : ℝ) (s := (Finset.univ : Finset (Fin 24)))
      (f := fun x : Fin 24 => (c x : ℝ) * (leechGeneratorMatrixInt x k : ℝ))).symm

theorem mem_LeechLattice_vecOfScaledStd_combInt (c : Fin 24 → ℤ) :
    vecOfScaledStd (combInt c) ∈ (LeechLattice : Set ℝ²⁴) := by
  -- `LeechLattice = span ℤ (range leechGeneratorRows)`.
  change vecOfScaledStd (combInt c) ∈ Submodule.span ℤ (Set.range leechGeneratorRows)
  exact
    (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := leechGeneratorRows)
          (x := vecOfScaledStd (combInt c))).2
      ⟨c, by simpa using! sum_zsmul_leechGeneratorRows_eq_vecOfScaledStd_combInt c⟩

/-! The basic `D₂₄` differences `(-4 at 0, +4 at i)`. -/

/--
The basic `D₂₄` difference vector.

For `i ≠ 0`, this has coordinates `-4` at `0`, `4` at `i`, and `0` elsewhere (and is `0` if
`i = 0` by definition).
-/
@[expose] public def zDiff (i : Fin 24) : Fin 24 → ℤ :=
  fun k =>
    if i = 0 then 0 else if k = 0 then (-4 : ℤ) else if k = i then (4 : ℤ) else 0

def coeffDiff_basic (i : Fin 24) : Fin 24 → ℤ :=
  fun j => if j = 0 then (-1 : ℤ) else if j = i then (1 : ℤ) else 0

def coeffDiff (i : Fin 24) : Fin 24 → ℤ :=
  match i.1 with
  | 0 => 0
  | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 9 | 10 | 12 | 16 => coeffDiff_basic i
  | 7 =>
      fun j =>
        if j = 0 then 2 else
        if j = 1 then -1 else
        if j = 2 then -1 else
        if j = 3 then -1 else
        if j = 4 then -1 else
        if j = 5 then -1 else
        if j = 6 then -1 else
        if j = 7 then 2 else 0
  | 11 =>
      fun j =>
        if j = 0 then 2 else
        if j = 1 then -1 else
        if j = 2 then -1 else
        if j = 3 then -1 else
        if j = 8 then -1 else
        if j = 9 then -1 else
        if j = 10 then -1 else
        if j = 11 then 2 else 0
  | 13 =>
      fun j =>
        if j = 0 then 2 else
        if j = 1 then -1 else
        if j = 4 then -1 else
        if j = 5 then -1 else
        if j = 8 then -1 else
        if j = 9 then -1 else
        if j = 12 then -1 else
        if j = 13 then 2 else 0
  | 14 =>
      fun j =>
        if j = 0 then 2 else
        if j = 2 then -1 else
        if j = 4 then -1 else
        if j = 6 then -1 else
        if j = 8 then -1 else
        if j = 10 then -1 else
        if j = 12 then -1 else
        if j = 14 then 2 else 0
  | 15 =>
      fun j =>
        if j = 0 then -4 else
        if j = 1 then 2 else
        if j = 2 then 2 else
        if j = 3 then 1 else
        if j = 5 then 1 else
        if j = 6 then 1 else
        if j = 7 then -2 else
        if j = 9 then 1 else
        if j = 10 then 1 else
        if j = 11 then -2 else
        if j = 12 then -1 else
        if j = 15 then 2 else 0
  | 17 =>
      fun j =>
        if j = 0 then -1 else
        if j = 1 then 1 else
        if j = 3 then 1 else
        if j = 5 then 1 else
        if j = 6 then 1 else
        if j = 7 then -2 else
        if j = 8 then -1 else
        if j = 9 then -1 else
        if j = 16 then -1 else
        if j = 17 then 2 else 0
  | 18 =>
      fun j =>
        if j = 0 then 2 else
        if j = 3 then -1 else
        if j = 4 then -1 else
        if j = 5 then -1 else
        if j = 8 then -1 else
        if j = 10 then -1 else
        if j = 16 then -1 else
        if j = 18 then 2 else 0
  | 19 =>
      fun j =>
        if j = 0 then -1 else
        if j = 2 then 1 else
        if j = 3 then 1 else
        if j = 4 then -1 else
        if j = 6 then -1 else
        if j = 9 then 1 else
        if j = 10 then 1 else
        if j = 11 then -2 else
        if j = 16 then -1 else
        if j = 19 then 2 else 0
  | 20 =>
      fun j =>
        if j = 0 then 3 else
        if j = 1 then -1 else
        if j = 2 then -1 else
        if j = 3 then -1 else
        if j = 4 then -1 else
        if j = 8 then -1 else
        if j = 12 then -1 else
        if j = 16 then -1 else
        if j = 20 then 2 else 0
  | 21 =>
      fun j =>
        if j = 0 then -4 else
        if j = 1 then 1 else
        if j = 2 then 1 else
        if j = 4 then 2 else
        if j = 6 then -1 else
        if j = 7 then 2 else
        if j = 8 then 2 else
        if j = 9 then 1 else
        if j = 12 then 1 else
        if j = 13 then -2 else
        if j = 16 then 1 else
        if j = 17 then -2 else
        if j = 20 then -2 else
        if j = 21 then 2 else 0
  | 22 =>
      fun j =>
        if j = 0 then -7 else
        if j = 1 then 1 else
        if j = 2 then 2 else
        if j = 3 then 2 else
        if j = 4 then 3 else
        if j = 5 then 1 else
        if j = 6 then 1 else
        if j = 8 then 2 else
        if j = 10 then 1 else
        if j = 12 then 1 else
        if j = 14 then -2 else
        if j = 16 then 1 else
        if j = 18 then -2 else
        if j = 20 then -2 else
        if j = 22 then 2 else 0
  | 23 =>
      fun j =>
        if j = 0 then 5 else
        if j = 1 then -2 else
        if j = 2 then -3 else
        if j = 3 then -2 else
        if j = 5 then -1 else
        if j = 8 then 1 else
        if j = 9 then -1 else
        if j = 10 then -1 else
        if j = 11 then 2 else
        if j = 12 then 1 else
        if j = 15 then -2 else
        if j = 16 then 1 else
        if j = 19 then -2 else
        if j = 20 then 2 else
        if j = 21 then -2 else
        if j = 22 then -2 else
        if j = 23 then 4 else 0
  | _ => coeffDiff_basic i

lemma combInt_coeffDiff_eq_zDiff_0 :
    combInt (coeffDiff (0 : Fin 24)) = zDiff (0 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_1 :
    combInt (coeffDiff (1 : Fin 24)) = zDiff (1 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_2 :
    combInt (coeffDiff (2 : Fin 24)) = zDiff (2 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_3 :
    combInt (coeffDiff (3 : Fin 24)) = zDiff (3 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_4 :
    combInt (coeffDiff (4 : Fin 24)) = zDiff (4 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_5 :
    combInt (coeffDiff (5 : Fin 24)) = zDiff (5 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_6 :
    combInt (coeffDiff (6 : Fin 24)) = zDiff (6 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_7 :
    combInt (coeffDiff (7 : Fin 24)) = zDiff (7 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_8 :
    combInt (coeffDiff (8 : Fin 24)) = zDiff (8 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_9 :
    combInt (coeffDiff (9 : Fin 24)) = zDiff (9 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_10 :
    combInt (coeffDiff (10 : Fin 24)) = zDiff (10 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_11 :
    combInt (coeffDiff (11 : Fin 24)) = zDiff (11 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_12 :
    combInt (coeffDiff (12 : Fin 24)) = zDiff (12 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_13 :
    combInt (coeffDiff (13 : Fin 24)) = zDiff (13 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_14 :
    combInt (coeffDiff (14 : Fin 24)) = zDiff (14 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_15 :
    combInt (coeffDiff (15 : Fin 24)) = zDiff (15 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_16 :
    combInt (coeffDiff (16 : Fin 24)) = zDiff (16 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_17 :
    combInt (coeffDiff (17 : Fin 24)) = zDiff (17 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_18 :
    combInt (coeffDiff (18 : Fin 24)) = zDiff (18 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_19 :
    combInt (coeffDiff (19 : Fin 24)) = zDiff (19 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_20 :
    combInt (coeffDiff (20 : Fin 24)) = zDiff (20 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_21 :
    combInt (coeffDiff (21 : Fin 24)) = zDiff (21 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_22 :
    combInt (coeffDiff (22 : Fin 24)) = zDiff (22 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

lemma combInt_coeffDiff_eq_zDiff_23 :
    combInt (coeffDiff (23 : Fin 24)) = zDiff (23 : Fin 24) := by
  ext k
  fin_cases k <;> decide +kernel

/-- For `i ≠ 0`, the scaled vector `vecOfScaledStd (zDiff i)` lies in `LeechLattice`. -/
public theorem mem_LeechLattice_vecOfScaledStd_zDiff (i : Fin 24) (hi : i ≠ 0) :
    vecOfScaledStd (zDiff i) ∈ (LeechLattice : Set ℝ²⁴) := by
  -- discharge by cases on `i` to avoid expensive reduction
  fin_cases i
  · cases hi rfl
  · simpa [combInt_coeffDiff_eq_zDiff_1] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (1 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_2] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (2 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_3] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (3 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_4] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (4 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_5] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (5 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_6] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (6 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_7] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (7 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_8] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (8 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_9] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (9 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_10] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (10 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_11] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (11 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_12] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (12 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_13] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (13 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_14] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (14 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_15] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (15 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_16] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (16 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_17] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (17 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_18] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (18 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_19] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (19 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_20] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (20 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_21] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (21 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_22] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (22 : Fin 24))
  · simpa [combInt_coeffDiff_eq_zDiff_23] using!
      mem_LeechLattice_vecOfScaledStd_combInt (coeffDiff (23 : Fin 24))

end Shell4IsometryLeechD24

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
