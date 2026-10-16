-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Auxiliary
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Moments.Core

/-!
# The spherical average `11 / 49140`

This file evaluates the spherical average
`sphereAvg24 (fun x => indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫))` for an orthogonal pair `u ⟂ v`,
yielding the value `11 / 49140` (BS81 Lemma 18(ii)).

## Main statements
* `CommonNeighbors44MomentsFinal.sphereAvg24_indPoly_mul_indPoly_eq`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44MomentsFinal

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory Set

open CommonNeighbors44Aux

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Spherical average of `indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫)` for an orthogonal pair `u ⟂ v`. -/
public theorem sphereAvg24_indPoly_mul_indPoly_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ C)
    (huv : (⟪u, v⟫ : ℝ) = 0) :
    sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
      (11 / 49140 : ℝ) := by
  have hu1 : ‖u‖ = (1 : ℝ) := h.code.norm_one hu
  have hv1 : ‖v‖ = (1 : ℝ) := h.code.norm_one hv
  have h22 := sphereAvg24_inner_sq_mul_inner_sq_eq (h := h) (hu := hu) (hv := hv) huv
  have h42 := sphereAvg24_inner_pow_four_mul_inner_sq_eq (h := h) (hu := hu) (hv := hv) huv
  have h44 := sphereAvg24_inner_pow_four_mul_inner_pow_four_eq (h := h) (hu := hu) (hv := hv) huv
  have h24 :
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 2 * (⟪x, v⟫ : ℝ) ^ 4) = (1 / 5824 : ℝ) := by
    have :=
      sphereAvg24_inner_pow_four_mul_inner_sq_eq (h := h) (u := v) (v := u) (hu := hv) (hv := hu)
        (huv := by simpa [real_inner_comm] using! huv)
    simpa [mul_comm, mul_left_comm, mul_assoc] using! this
  have hoddL (i j : ℕ) (hi : Odd i) :
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ) ^ j) = 0 :=
    sphereAvg24_inner_pow_mul_inner_pow_eq_zero_of_odd_left huv hi
  have hoddR (i j : ℕ) (hj : Odd j) :
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ) ^ j) = 0 :=
    sphereAvg24_inner_pow_mul_inner_pow_eq_zero_of_odd_right huv hj
  have havg :
      sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
        indPolyIdx.sum (fun i =>
          indPolyIdx.sum (fun j =>
            (indPolyCoeff i * indPolyCoeff j) * sphereAvg24 (indPolyMon u v i j))) :=
    sphereAvg24_indPoly_mul_indPoly_eq_doubleSum_indPolyMon (u := u) (v := v) hu1 hv1
  have hfinal :
      indPolyIdx.sum (fun i =>
        indPolyIdx.sum (fun j =>
          (indPolyCoeff i * indPolyCoeff j) *
            sphereAvg24 (fun x : ℝ²⁴ => indPolyMon u v i j x))) =
        (11 / 49140 : ℝ) := by
    -- Expand the `range 6` sums; odd mixed moments vanish, leaving only the known even moments.
    have hodd1 : Odd (1 : ℕ) := by decide
    have hodd3 : Odd (3 : ℕ) := by decide
    have hodd5 : Odd (5 : ℕ) := by decide
    have hoddU1 (j : ℕ) :
        sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) * (⟪x, v⟫ : ℝ) ^ j) = 0 := by
      simpa [pow_one] using! hoddL 1 j hodd1
    have hoddV1 (i : ℕ) :
        sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ)) = 0 := by
      simpa [pow_one] using! hoddR i 1 hodd1
    simp [indPolyIdx, Finset.sum_range_succ, indPolyCoeff, indPolyMon, hoddL, hoddR, hoddU1, hoddV1,
      hodd3, hodd5, h22, h42, h24, h44]
    norm_num
  calc
    sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ))
        =
        indPolyIdx.sum (fun i =>
          indPolyIdx.sum (fun j =>
            (indPolyCoeff i * indPolyCoeff j) *
              sphereAvg24 (fun x : ℝ²⁴ => indPolyMon u v i j x))) := havg
    _ = (11 / 49140 : ℝ) := hfinal

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44MomentsFinal
