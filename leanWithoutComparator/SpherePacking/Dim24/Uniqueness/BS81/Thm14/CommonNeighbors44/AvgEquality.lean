-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Auxiliary
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Moments.Core
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Moments.IndPoly
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24

/-!
# Design reduction for the indicator sum

The function `x ↦ indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫)` has total degree at most `10` after expansion.
Using the design axiom `EqCase24Pkg.design11`, its finite average over `C` equals the spherical
average over `S23`.

## Main statements
* `CommonNeighbors44Steps.finsetAvg_indPoly_mul_indPoly_eq_sphereAvg`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44Steps

noncomputable section

open scoped RealInnerProductSpace BigOperators

open MeasureTheory Set

open Uniqueness.BS81.Thm14
open CommonNeighbors44Aux

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Design reduction for the common-neighbor indicator product: `finsetAvg = sphereAvg24`. -/
public theorem finsetAvg_indPoly_mul_indPoly_eq_sphereAvg
    (C : Set ℝ²⁴) (h : EqCase24Pkg C)
    {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ C) :
    finsetAvg h.code.finite.toFinset
        (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
      sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) := by
  simpa using!
    (CommonNeighbors44Aux.finsetAvg_indPoly_mul_indPoly_eq_sphereAvg_of_pkg (h := h) hu hv)

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44Steps
