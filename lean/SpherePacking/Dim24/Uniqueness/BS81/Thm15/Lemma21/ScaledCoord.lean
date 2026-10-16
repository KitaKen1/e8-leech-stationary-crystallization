-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IntegerCoords

/-!
# Basic lemmas about `scaledCoord`

This file relates `coord` and `scaledCoord` and records that, in an orthonormal frame, equality of
all scaled coordinates determines the vector.

## Main statements
* `sqrt8_ne_zero`
* `coord_eq_scaledCoord_div_sqrt8`
* `scaledCoord_sub`
* `eq_of_scaledCoord_eq`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- `Real.sqrt 8` is nonzero. -/
public lemma sqrt8_ne_zero : (Real.sqrt 8 : ℝ) ≠ 0 := by
  have : (0 : ℝ) < 8 := by norm_num
  exact Real.sqrt_ne_zero'.2 this

/-- The coordinate `coord e i x` is `scaledCoord e i x / √8`. -/
public lemma coord_eq_scaledCoord_div_sqrt8
    (e : Fin 24 → ℝ²⁴) (i : Fin 24) (x : ℝ²⁴) :
    coord e i x = scaledCoord e i x / Real.sqrt 8 := by
  simp [scaledCoord]

/-- `scaledCoord` is additive with respect to subtraction. -/
public lemma scaledCoord_sub (e : Fin 24 → ℝ²⁴) (i : Fin 24) (x y : ℝ²⁴) :
    scaledCoord e i (x - y) = scaledCoord e i x - scaledCoord e i y := by
  simp [scaledCoord, coord, inner_sub_right, mul_sub]

/-- In an orthonormal frame, a vector is determined by its `scaledCoord` values. -/
public lemma eq_of_scaledCoord_eq
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) {x y : ℝ²⁴}
    (h : ∀ i : Fin 24, scaledCoord e i x = scaledCoord e i y) :
    x = y := by
  have hcoord : ∀ i : Fin 24, coord e i x = coord e i y := by
    intro i
    have := congrArg (fun t : ℝ => t / Real.sqrt 8) (h i)
    simpa [coord_eq_scaledCoord_div_sqrt8] using! this
  calc
    x = ∑ i : Fin 24, (coord e i x) • e i := coord_eq_of_orthonormal e he x
    _ = ∑ i : Fin 24, (coord e i y) • e i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [hcoord i]
    _ = y := (coord_eq_of_orthonormal e he y).symm

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
