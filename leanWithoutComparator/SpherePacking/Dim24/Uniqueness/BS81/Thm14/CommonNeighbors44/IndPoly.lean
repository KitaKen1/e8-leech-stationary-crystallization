-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvg24Lemmas
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The indicator polynomial `indPoly` and its double-sum expansion

This file isolates the definitions/lemmas around the indicator polynomial
`CommonNeighbors44Aux.indPoly`
used in the 44-common-neighbors count (BS81 Lemma 18(ii)), together with the reusable boilerplate:
* writing `indPoly` as a short monomial sum,
* expanding `indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫)` into a finite double sum,
* commuting `finsetAvg` and `sphereAvg24` with that double sum.
-/

namespace SpherePacking.Dim24

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

open MeasureTheory Set

namespace CommonNeighbors44Aux

/-!
## The indicator polynomial `indPoly`
-/

/-- The indicator polynomial used for the 44-common-neighbors count.

It satisfies `indPoly (1 / 2) = 1` and vanishes at `-1`, `-1 / 2`, `-1 / 4`, `0`, `1 / 4`. -/
@[expose] public def indPoly (t : ℝ) : ℝ :=
  (64 / 9 : ℝ) * t * (t + 1) * (t + (1 / 2 : ℝ)) * (t + (1 / 4 : ℝ)) * (t - (1 / 4 : ℝ))

/-- Normalization: `indPoly (1 / 2) = 1`. -/
@[grind =]
public lemma indPoly_half : indPoly (1 / 2 : ℝ) = 1 := by
  simp [indPoly]
  norm_num

/-- Root: `indPoly (-1) = 0`. -/
@[grind =]
public lemma indPoly_neg_one : indPoly (-1 : ℝ) = 0 := by
  simp [indPoly]

/-- Root: `indPoly (-1 / 2) = 0`. -/
@[grind =]
public lemma indPoly_neg_half : indPoly (-1 / 2 : ℝ) = 0 := by
  have : (-1 / 2 : ℝ) + (2 : ℝ)⁻¹ = 0 := by norm_num
  simp [indPoly, this]

/-- Root: `indPoly (-1 / 4) = 0`. -/
@[grind =]
public lemma indPoly_neg_quarter : indPoly (-1 / 4 : ℝ) = 0 := by
  have : (-1 / 4 : ℝ) + (4 : ℝ)⁻¹ = 0 := by norm_num
  simp [indPoly, this]

/-- Root: `indPoly 0 = 0`. -/
@[grind =]
public lemma indPoly_zero : indPoly (0 : ℝ) = 0 := by
  simp [indPoly]

/-- Root: `indPoly (1 / 4) = 0`. -/
@[grind =]
public lemma indPoly_quarter : indPoly (1 / 4 : ℝ) = 0 := by
  simp [indPoly]

/-- Expanded form of `indPoly`. -/
public lemma indPoly_expand (t : ℝ) :
    indPoly t =
      (64 / 9 : ℝ) * t ^ 5 +
        (32 / 3 : ℝ) * t ^ 4 +
          (28 / 9 : ℝ) * t ^ 3 -
            (2 / 3 : ℝ) * t ^ 2 -
              (2 / 9 : ℝ) * t := by
  simp [indPoly]
  ring

/-!
## `indPoly` as a short sum
-/

/-- The index set `{0,1,2,3,4,5}` used to write `indPoly` as a short monomial sum. -/
@[expose] public def indPolyIdx : Finset ℕ :=
  Finset.range 6

/-- Coefficients for the monomial expansion of `indPoly`. -/
@[expose] public def indPolyCoeff : ℕ → ℝ
  | 0 => 0
  | 1 => -(2 / 9 : ℝ)
  | 2 => -(2 / 3 : ℝ)
  | 3 => (28 / 9 : ℝ)
  | 4 => (32 / 3 : ℝ)
  | 5 => (64 / 9 : ℝ)
  | _ => 0

/-- Write `indPoly` as `∑_{k < 6} indPolyCoeff k * t^k`. -/
public lemma indPoly_eq_sum (t : ℝ) :
    indPoly t = indPolyIdx.sum (fun k => indPolyCoeff k * t ^ k) := by
  simp [indPoly_expand, indPolyIdx, indPolyCoeff, Finset.sum_range_succ]
  ring_nf

/-!
## `indPoly(⟪x,u⟫) * indPoly(⟪x,v⟫)` as a double sum
-/

/-- The monomial `(⟪x,u⟫)^i * (⟪x,v⟫)^j` used in the `indPoly` double-sum expansion. -/
@[expose] public def indPolyMon (u v : ℝ²⁴) (i j : ℕ) (x : ℝ²⁴) : ℝ :=
  (⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ) ^ j

/-- The double-sum term for `indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫)`. -/
@[expose] public def indPolyTerm (u v : ℝ²⁴) (i j : ℕ) (x : ℝ²⁴) : ℝ :=
  (indPolyCoeff i * indPolyCoeff j) * indPolyMon u v i j x

/-- Expand `indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫)` as a finite double sum. -/
public lemma indPoly_mul_indPoly_eq_doubleSum (u v x : ℝ²⁴) :
    indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ) =
      indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => indPolyTerm u v i j x)) := by
  have hu' :
      indPoly (⟪x, u⟫ : ℝ) = indPolyIdx.sum (fun i => indPolyCoeff i * (⟪x, u⟫ : ℝ) ^ i) := by
    simpa using! (indPoly_eq_sum (t := (⟪x, u⟫ : ℝ)))
  have hv' :
      indPoly (⟪x, v⟫ : ℝ) = indPolyIdx.sum (fun j => indPolyCoeff j * (⟪x, v⟫ : ℝ) ^ j) := by
    simpa using! (indPoly_eq_sum (t := (⟪x, v⟫ : ℝ)))
  calc
    indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)
        =
          (indPolyIdx.sum fun i => indPolyCoeff i * (⟪x, u⟫ : ℝ) ^ i) *
            (indPolyIdx.sum fun j => indPolyCoeff j * (⟪x, v⟫ : ℝ) ^ j) := by
          simp [hu', hv']
    _ = indPolyIdx.sum (fun i => indPolyIdx.sum fun j =>
          (indPolyCoeff i * (⟪x, u⟫ : ℝ) ^ i) * (indPolyCoeff j * (⟪x, v⟫ : ℝ) ^ j)) :=
          Finset.sum_mul_sum indPolyIdx indPolyIdx (fun i => indPolyCoeff i * ⟪x, u⟫ ^ i)
              (fun j => indPolyCoeff j * ⟪x, v⟫ ^ j)
    _ = indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => indPolyTerm u v i j x)) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          refine Finset.sum_congr rfl (fun j hj => ?_)
          simp [indPolyTerm, indPolyMon]
          ring_nf

/-- Commute `finsetAvg` with the double-sum expansion of `indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫)`. -/
public lemma finsetAvg_indPoly_mul_indPoly_eq_doubleSum (Cfin : Finset ℝ²⁴) (u v : ℝ²⁴) :
    finsetAvg Cfin (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
      indPolyIdx.sum (fun i =>
        indPolyIdx.sum (fun j => finsetAvg Cfin (indPolyTerm u v i j))) := by
  calc
    finsetAvg Cfin (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
        finsetAvg Cfin
          (fun x : ℝ²⁴ =>
            indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => indPolyTerm u v i j x))) := by
          refine congrArg (fun f => finsetAvg Cfin f) ?_
          funext x
          simpa using! (indPoly_mul_indPoly_eq_doubleSum (u := u) (v := v) (x := x))
    _ =
        indPolyIdx.sum (fun i =>
          indPolyIdx.sum (fun j => finsetAvg Cfin (indPolyTerm u v i j))) :=
          AdditionTheorem.Bridge24.finsetAvg_finset_sum₂
              Cfin indPolyIdx indPolyIdx (indPolyTerm u v)

/-!
## Integrability of the double-sum terms
-/

/-- Integrability of `indPolyMon` on the unit sphere. -/
public lemma integrable_indPolyMon {u v : ℝ²⁴} (hu1 : ‖u‖ = (1 : ℝ)) (hv1 : ‖v‖ = (1 : ℝ))
    (i j : ℕ) :
    Integrable (fun x : S23 => indPolyMon u v i j x.1) sphereMeasure24 := by
  simpa [indPolyMon] using! (Uniqueness.BS81.Thm14.integrable_inner_pow_mul_inner_pow
    (u := u) (v := v) hu1 hv1 i j)

/-- Integrability of `indPolyTerm` on the unit sphere. -/
public lemma integrable_indPolyTerm {u v : ℝ²⁴} (hu1 : ‖u‖ = (1 : ℝ)) (hv1 : ‖v‖ = (1 : ℝ))
    (i j : ℕ) :
    Integrable (fun x : S23 => indPolyTerm u v i j x.1) sphereMeasure24 := by
  have hmon : Integrable (fun x : S23 => indPolyMon u v i j x.1) sphereMeasure24 :=
    integrable_indPolyMon (u := u) (v := v) hu1 hv1 i j
  simpa [indPolyTerm] using! hmon.const_mul (indPolyCoeff i * indPolyCoeff j)

/-!
## Commuting `sphereAvg24` with the `indPoly` double sum
-/

/-- Commute `sphereAvg24` with the double sum defining `indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫)`. -/
public lemma sphereAvg24_doubleSum_indPolyTerm_eq {u v : ℝ²⁴}
    (hu1 : ‖u‖ = (1 : ℝ)) (hv1 : ‖v‖ = (1 : ℝ)) :
    sphereAvg24
        (fun x : ℝ²⁴ =>
          indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => indPolyTerm u v i j x))) =
      indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => sphereAvg24 (indPolyTerm u v i j))) := by
  have hintTerm :
      ∀ i ∈ indPolyIdx, ∀ j ∈ indPolyIdx,
        Integrable (fun x : S23 => indPolyTerm u v i j x.1) sphereMeasure24 := by
    intro i hi j hj
    simpa using! (integrable_indPolyTerm (u := u) (v := v) hu1 hv1 i j)
  exact sphereAvg24_finset_sum₂ indPolyIdx indPolyIdx (indPolyTerm u v) hintTerm

/-- Expand `sphereAvg24 (indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫))` as a finite double sum. -/
public lemma sphereAvg24_indPoly_mul_indPoly_eq_doubleSum {u v : ℝ²⁴}
    (hu1 : ‖u‖ = (1 : ℝ)) (hv1 : ‖v‖ = (1 : ℝ)) :
    sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
      indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => sphereAvg24 (indPolyTerm u v i j))) := by
  have :
      sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
        sphereAvg24
          (fun x : ℝ²⁴ =>
            indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => indPolyTerm u v i j x))) := by
    refine sphereAvg24_congr ?_
    intro x
    simpa using! (indPoly_mul_indPoly_eq_doubleSum (u := u) (v := v) (x := x.1))
  simpa [this] using! (sphereAvg24_doubleSum_indPolyTerm_eq (u := u) (v := v) hu1 hv1)

public lemma finsetAvg_indPoly_mul_indPoly_eq_sphereAvg_of_termwise (Cfin : Finset ℝ²⁴)
    {u v : ℝ²⁴} (hu1 : ‖u‖ = (1 : ℝ)) (hv1 : ‖v‖ = (1 : ℝ))
    (hterm :
      ∀ i ∈ indPolyIdx, ∀ j ∈ indPolyIdx,
        finsetAvg Cfin (indPolyTerm u v i j) = sphereAvg24 (indPolyTerm u v i j)) :
    finsetAvg Cfin (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
      sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) := by
  have hfin :
      finsetAvg Cfin (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
        indPolyIdx.sum (fun i =>
          indPolyIdx.sum (fun j => finsetAvg Cfin (indPolyTerm u v i j))) := by
    simpa using! (finsetAvg_indPoly_mul_indPoly_eq_doubleSum (Cfin := Cfin) (u := u) (v := v))
  have hsphere :
      sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
        indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => sphereAvg24 (indPolyTerm u v i j))) := by
    simpa using! (sphereAvg24_indPoly_mul_indPoly_eq_doubleSum (u := u) (v := v) hu1 hv1)
  have hsumEq :
      indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => finsetAvg Cfin (indPolyTerm u v i j))) =
        indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => sphereAvg24 (indPolyTerm u v i j))) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simpa using! hterm i hi j hj
  calc
    finsetAvg Cfin (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
        indPolyIdx.sum (fun i =>
          indPolyIdx.sum (fun j => finsetAvg Cfin (indPolyTerm u v i j))) := hfin
    _ =
        indPolyIdx.sum (fun i =>
          indPolyIdx.sum (fun j => sphereAvg24 (indPolyTerm u v i j))) := hsumEq
    _ = sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) := hsphere.symm

/-- Pull the scalar coefficient out of `sphereAvg24 (indPolyTerm u v i j)`. -/
public lemma sphereAvg24_indPolyTerm_eq_smul (u v : ℝ²⁴) (i j : ℕ) :
    sphereAvg24 (indPolyTerm u v i j) =
      (indPolyCoeff i * indPolyCoeff j) * sphereAvg24 (indPolyMon u v i j) := by
  change
      sphereAvg24 (fun x : ℝ²⁴ => (indPolyCoeff i * indPolyCoeff j) * indPolyMon u v i j x) =
        (indPolyCoeff i * indPolyCoeff j) * sphereAvg24 (indPolyMon u v i j)
  simpa [mul_assoc] using!
    (sphereAvg24_smul (a := (indPolyCoeff i * indPolyCoeff j)) (f := indPolyMon u v i j))

/-- Rewrite the double sum of `sphereAvg24 (indPolyTerm ...)` using `indPolyMon`. -/
public lemma doubleSum_sphereAvg_indPolyTerm_eq (u v : ℝ²⁴) :
    indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => sphereAvg24 (indPolyTerm u v i j))) =
      indPolyIdx.sum (fun i =>
        indPolyIdx.sum
          (fun j => (indPolyCoeff i * indPolyCoeff j) * sphereAvg24 (indPolyMon u v i j))) := by
  refine Finset.sum_congr rfl (fun i hi => ?_)
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp [sphereAvg24_indPolyTerm_eq_smul]

/-- Rewrite `sphereAvg24 (indPoly (⟪x,u⟫) * indPoly (⟪x,v⟫))` using `indPolyMon`. -/
public lemma sphereAvg24_indPoly_mul_indPoly_eq_doubleSum_indPolyMon {u v : ℝ²⁴}
    (hu1 : ‖u‖ = (1 : ℝ)) (hv1 : ‖v‖ = (1 : ℝ)) :
    sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
      indPolyIdx.sum (fun i =>
        indPolyIdx.sum (fun j =>
          (indPolyCoeff i * indPolyCoeff j) * sphereAvg24 (indPolyMon u v i j))) := by
  calc
    sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
        indPolyIdx.sum (fun i => indPolyIdx.sum (fun j => sphereAvg24 (indPolyTerm u v i j))) :=
      sphereAvg24_indPoly_mul_indPoly_eq_doubleSum (u := u) (v := v) hu1 hv1
    _ =
        indPolyIdx.sum (fun i =>
          indPolyIdx.sum (fun j =>
            (indPolyCoeff i * indPolyCoeff j) * sphereAvg24 (indPolyMon u v i j))) := by
      simpa using! (doubleSum_sphereAvg_indPolyTerm_eq (u := u) (v := v))

end CommonNeighbors44Aux

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
