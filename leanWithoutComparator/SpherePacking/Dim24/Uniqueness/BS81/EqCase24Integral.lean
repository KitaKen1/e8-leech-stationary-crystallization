-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
import SpherePacking.Dim24.Uniqueness.BS81.EqCase24Support

/-!
# Integer-valued inner products after scaling

In the BS81 equality case, the inner products between code vectors lie in the support set
`{1, -1, ±1/2, ±1/4, 0}`. After scaling the code by `2`, all such inner products become integers.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open scoped RealInnerProductSpace Pointwise

/-- Inner products between vectors in `twoCodeVectors C` are integer-valued in the equality case. -/
public theorem inner_twoCodeVectors_int
    (C : Set ℝ²⁴) (hEq : EqCase24 C) {x y : ℝ²⁴}
    (hx : x ∈ twoCodeVectors C) (hy : y ∈ twoCodeVectors C) :
    ∃ m : ℤ, ⟪x, y⟫ = (m : ℝ) := by
  rcases hx with ⟨u, hu, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  have hscale :
      (⟪(2 : ℝ) • u, (2 : ℝ) • v⟫ : ℝ) = (4 : ℝ) * (⟪u, v⟫ : ℝ) := by
    simp [real_inner_smul_left, real_inner_smul_right]
    ring
  have hinner :=
    inner_eq_one_or_eq_neg_one_or_eq_half_or_eq_neg_half_or_eq_quarter_or_eq_neg_quarter_or_eq_zero
      (C := C) hEq (hu := hu) (hv := hv)
  rcases hinner with
    h | h | h | h | h | h | h
  · refine ⟨4, ?_⟩
    simp [hscale, h]
  · refine ⟨-4, ?_⟩
    simp [hscale, h]
  · refine ⟨2, ?_⟩
    simpa [hscale, h] using! (by norm_num : (4 : ℝ) * (1 / 2 : ℝ) = (2 : ℝ))
  · refine ⟨-2, ?_⟩
    simpa [hscale, h] using! (by norm_num : (4 : ℝ) * (-1 / 2 : ℝ) = (-2 : ℝ))
  · refine ⟨1, ?_⟩
    simp [hscale, h]
  · refine ⟨-1, ?_⟩
    simpa [hscale, h] using! (by norm_num : (4 : ℝ) * (-1 / 4 : ℝ) = (-1 : ℝ))
  · refine ⟨0, ?_⟩
    simp [hscale, h]

end SpherePacking.Dim24.Uniqueness.BS81
