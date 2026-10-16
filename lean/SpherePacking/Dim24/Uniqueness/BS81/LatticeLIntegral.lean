-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
import SpherePacking.Dim24.Uniqueness.BS81.EqCase24Integral

/-!
# Integrality of `latticeL`

In the BS81 equality case, the lattice `latticeL C := span_ℤ (2 • C)` is integral: all inner
products between lattice vectors are integers. The key input is that pairwise inner products on
`twoCodeVectors C` are integers and integrality is preserved under taking `ℤ`-linear combinations.

## Main statements
* `Uniqueness.BS81.inner_latticeL_int`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81

noncomputable section

open scoped RealInnerProductSpace Pointwise

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

lemma inner_int_of_mem_span_twoCodeVectors_left
    (C : Set ℝ²⁴) (hEq : EqCase24 C) (x : ℝ²⁴) (hx : x ∈ (latticeL C : Set ℝ²⁴)) :
    ∀ y : ℝ²⁴, y ∈ (latticeL C : Set ℝ²⁴) → ∃ m : ℤ, ⟪x, y⟫ = (m : ℝ) := by
  intro y hy
  -- span induction on `y`
  induction hy using Submodule.span_induction with
  | mem y hyS =>
      -- reduce `x` to the span again by a second induction
      induction hx using Submodule.span_induction with
      | mem x hxS =>
          exact inner_twoCodeVectors_int (C := C) hEq hxS hyS
      | zero =>
          exact ⟨0, by simp⟩
      | add x x' _ _ ih ih' =>
          rcases ih with ⟨m, hm⟩
          rcases ih' with ⟨m', hm'⟩
          refine ⟨m + m', ?_⟩
          simp [inner_add_left, hm, hm']
      | smul n x _ ih =>
          rcases ih with ⟨m, hm⟩
          refine ⟨n * m, ?_⟩
          have hz : (n • x : ℝ²⁴) = (n : ℝ) • x := by
            simpa using! (Int.cast_smul_eq_zsmul ℝ n x).symm
          simp [hz, inner_smul_left, hm]
  | zero =>
      exact ⟨0, by simp⟩
  | add y y' _ _ ih ih' =>
      rcases ih with ⟨m, hm⟩
      rcases ih' with ⟨m', hm'⟩
      refine ⟨m + m', ?_⟩
      simp [inner_add_right, hm, hm']
  | smul n y _ ih =>
      rcases ih with ⟨m, hm⟩
      refine ⟨n * m, ?_⟩
      have hz : (n • y : ℝ²⁴) = (n : ℝ) • y := by
        simpa using! (Int.cast_smul_eq_zsmul ℝ n y).symm
      simp [hz, inner_smul_right, hm]

/-- In the BS81 equality case, `latticeL C` is integral: all inner products are integers. -/
public theorem inner_latticeL_int
    (C : Set ℝ²⁴) (hEq : EqCase24 C) {x y : ℝ²⁴}
    (hx : x ∈ (latticeL C : Set ℝ²⁴)) (hy : y ∈ (latticeL C : Set ℝ²⁴)) :
    ∃ m : ℤ, ⟪x, y⟫ = (m : ℝ) :=
  inner_int_of_mem_span_twoCodeVectors_left (C := C) hEq x hx y hy

end

end SpherePacking.Dim24.Uniqueness.BS81
