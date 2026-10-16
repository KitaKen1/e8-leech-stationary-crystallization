-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.AvgEquality
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.SumEqualsCount

/-!
# The 44 common neighbors count

This is an intersection number of the 6-class association scheme in BS81 Theorem 14, but for the
BS81 kissing-uniqueness route we avoid formalizing the full association-scheme package.

Instead, it can be derived directly from:
- the BS81 spherical 11-design identity (equation (14), `h.design11`),
- the explicit distance distribution (equation (11), `h.distCount_eq`),
- and explicit spherical mixed moments on `S^{23}`.

Gap-free LaTeX source (in-repo): `paper/Notes/SphericalLP/bs81_common_neighbors_44.tex`.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Set
open CommonNeighbors44Aux

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- In the BS81 equality case, an orthogonal pair has exactly `44` common neighbors. -/
public theorem commonNeighbors44
    (C : Set ℝ²⁴) (h : EqCase24Pkg C)
    {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ C) (hinner : (⟪u, v⟫ : ℝ) = 0) :
    Set.ncard {w : ℝ²⁴ | w ∈ C ∧ (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) ∧ (⟪v, w⟫ : ℝ) = (1 / 2 : ℝ)} = 44 := by
  let f : ℝ²⁴ → ℝ := fun x => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)
  -- Step 1: identify the finite average with the spherical average.
  have havg :
      finsetAvg h.code.finite.toFinset f = sphereAvg24 f :=
    CommonNeighbors44Steps.finsetAvg_indPoly_mul_indPoly_eq_sphereAvg (C := C) h hu hv
  -- Step 2: evaluate the spherical average explicitly (`11/49140`).
  have hsphere :
      sphereAvg24 f = (11 / 49140 : ℝ) :=
    (Uniqueness.BS81.Thm14.CommonNeighbors44MomentsFinal.sphereAvg24_indPoly_mul_indPoly_eq
      (h := h) (hu := hu) (hv := hv) hinner)
  -- Step 3: convert the average to a sum.
  have hμ :
      finsetAvg h.code.finite.toFinset f = (11 / 49140 : ℝ) := by
    simpa [havg] using! hsphere
  have hsum :
      h.code.finite.toFinset.sum (fun w : ℝ²⁴ =>
        indPoly (⟪u, w⟫ : ℝ) * indPoly (⟪v, w⟫ : ℝ)) =
        (44 : ℝ) := by
    have hcard : (h.code.finite.toFinset.card : ℝ) = 196560 := by
      have := (Set.ncard_eq_toFinset_card (s := C) h.code.finite)
      have : (h.code.finite.toFinset.card : ℝ) = (Set.ncard C : ℝ) := by
        exact_mod_cast this.symm
      simpa [h.card_eq] using! this
    have hne : (h.code.finite.toFinset.card : ℝ) ≠ 0 := by
      nlinarith [hcard]
    have hmul := congrArg (fun r : ℝ => (h.code.finite.toFinset.card : ℝ) * r) hμ
    have hsum' :
        h.code.finite.toFinset.sum (fun w : ℝ²⁴ =>
          indPoly (⟪u, w⟫ : ℝ) * indPoly (⟪v, w⟫ : ℝ)) =
          (196560 : ℝ) * (11 / 49140 : ℝ) := by
      simpa [finsetAvg, f, hne, hcard, real_inner_comm, mul_assoc,
        mul_left_comm, mul_comm] using! hmul
    simpa [hsum'] using! (by norm_num : (196560 : ℝ) * (11 / 49140 : ℝ) = (44 : ℝ))
  -- Step 4: rewrite the sum as the desired count.
  have hcountR :
      (Set.ncard {w : ℝ²⁴ | w ∈ C ∧ (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) ∧ (⟪v, w⟫ : ℝ) = (1 / 2 : ℝ)} : ℝ) =
        44 := by
    have hsumCount :=
      CommonNeighbors44Steps.sum_indPoly_mul_indPoly_eq_commonNeighbors_card (C := C) h hu hv hinner
    linarith [hsumCount, hsum]
  exact_mod_cast hcountR

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
