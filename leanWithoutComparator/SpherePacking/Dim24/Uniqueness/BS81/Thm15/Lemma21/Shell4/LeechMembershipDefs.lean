-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.LeechLattice.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Patterns
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayConcrete
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechD24
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechParityCode
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Leech lattice membership: shared definitions

This file contains the common definitions and lemmas used by the three shell-4 pattern-membership
proofs (Types I/II/III) in the proof of BS81 Lemma 21.

## Main definitions
* `Shell4IsometryLeechMembership.vecOfScaledStd`

## Main statements
* `Shell4IsometryLeechMembership.scaledCoord_std_vecOfScaledStd`

## References
* Bannai-Sloane (1981), Section 4 and Lemma 21.
* Design notes: `paper/Notes/CodingTheory/leech_minimal_vectors_from_golay.tex`.
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

/-!
### Helper: the vector with prescribed scaled coordinates in the standard basis
-/

/--
The vector of `ℝ²⁴` whose scaled coordinates in the standard basis are the integers `z`.

This is a local re-export of `Shell4IsometryLeechD24.vecOfScaledStd`.
-/
@[expose] public def vecOfScaledStd (z : Fin 24 → ℤ) : ℝ²⁴ :=
  Shell4IsometryLeechD24.vecOfScaledStd z

/-- Unfolding lemma for `Shell4IsometryLeechMembership.vecOfScaledStd`. -/
public lemma vecOfScaledStd_eq_leechD24_vecOfScaledStd (z : Fin 24 → ℤ) :
    vecOfScaledStd z = Shell4IsometryLeechD24.vecOfScaledStd z := by
  rfl

/-- Additivity of `vecOfScaledStd`. -/
public lemma vecOfScaledStd_add (z₁ z₂ : Fin 24 → ℤ) :
    vecOfScaledStd (z₁ + z₂) = vecOfScaledStd z₁ + vecOfScaledStd z₂ := by
  ext k
  simp [vecOfScaledStd, Shell4IsometryLeechD24.vecOfScaledStd, Shell4IsometryLeechD24.vecOfInt,
    Pi.add_apply, mul_add]

/-- The scaled vector associated to generator row `i` is `leechGeneratorRows i`. -/
public lemma vecOfScaledStd_leechGeneratorRows (i : Fin 24) :
    vecOfScaledStd (fun k : Fin 24 => leechGeneratorMatrixInt i k) = leechGeneratorRows i := by
  simp [vecOfScaledStd, Shell4IsometryLeechD24.vecOfScaledStd, Shell4IsometryLeechD24.vecOfInt,
    leechGeneratorRows, leechGeneratorRowsUnscaled]

/--
The `scaledCoord` of `vecOfScaledStd z` in the standard basis recovers the integer coordinate `z`.
-/
public theorem scaledCoord_std_vecOfScaledStd (z : Fin 24 → ℤ) (i : Fin 24) :
    scaledCoord (fun j : Fin 24 => EuclideanSpace.single j 1) i (vecOfScaledStd z) =
      (z i : ℝ) := by
  have hs8 : (Real.sqrt 8 : ℝ) ≠ 0 := by
    have : (0 : ℝ) < 8 := by norm_num
    exact Real.sqrt_ne_zero'.2 this
  have hinner :
      (⟪(EuclideanSpace.basisFun (Fin 24) ℝ) i,
          WithLp.toLp 2 (fun j : Fin 24 => (z j : ℝ))⟫ : ℝ) = (z i : ℝ) := by
    simpa using!
      (EuclideanSpace.basisFun_inner (ι := Fin 24) (𝕜 := ℝ)
        (x := WithLp.toLp 2 (fun j : Fin 24 => (z j : ℝ))) i)
  have hinner' :
      (⟪EuclideanSpace.single i 1,
          WithLp.toLp 2 (fun j : Fin 24 => (z j : ℝ))⟫ : ℝ) = (z i : ℝ) := by
    simpa using! hinner
  -- Unfold `vecOfScaledStd` and cancel the scale factors `√8` and `1/√8`.
  simp [scaledCoord, coord, vecOfScaledStd, Shell4IsometryLeechD24.vecOfScaledStd,
    Shell4IsometryLeechD24.vecOfInt, real_inner_smul_right, hs8, hinner']

end Shell4IsometryLeechMembership

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
