-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeLIntegral
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeLShell4
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Half-integrality and value restrictions for BS81 Lemma 16

Let `L = span_ℤ (2 • C)` and suppose `v ∈ L` has `‖v‖ ^ 2 = 2`.
For any `u ∈ C`:
* `⟪2u, v⟫ ∈ ℤ` by integrality of `L`,
* hence `⟪u, v⟫ ∈ (1/2)ℤ`,
* and Cauchy-Schwarz forces `⟪u, v⟫ ∈ {0, ±1/2, ±1}`.

## Main statements
* `inner_twoU_v_halfInteger`
* `inner_mem_values_of_norm_sq_two`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16

noncomputable section

open scoped RealInnerProductSpace Pointwise

open Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- For `u ∈ C` and `v ∈ span_ℤ (2 • C)`, the inner product `⟪u, v⟫` lies in `(1/2)ℤ`. -/
public theorem inner_twoU_v_halfInteger
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ (latticeL C : Set ℝ²⁴)) :
    ∃ m : ℤ, (⟪u, v⟫ : ℝ) = (m : ℝ) / 2 := by
  have hEq : Uniqueness.BS81.EqCase24 C :=
    Uniqueness.BS81.Thm14.EqCase24Pkg.toEqCase24 (C := C) h
  have huL : (2 : ℝ) • u ∈ (latticeL C : Set ℝ²⁴) :=
    Uniqueness.BS81.smul_mem_latticeL (C := C) hu
  rcases Uniqueness.BS81.inner_latticeL_int (C := C) hEq (x := (2 : ℝ) • u)
      (y := v) huL hv with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hm' : (2 : ℝ) * (⟪u, v⟫ : ℝ) = (m : ℝ) := by
    simpa [real_inner_smul_left, mul_assoc, mul_left_comm, mul_comm] using! hm
  nlinarith [hm']

/-- If `‖u‖ = 1` and `‖v‖ ^ 2 = 2`, then `⟪u, v⟫` can only be `0, ±1/2, ±1`. -/
public theorem inner_mem_values_of_norm_sq_two
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ (latticeL C : Set ℝ²⁴))
    (hnormu : ‖u‖ = (1 : ℝ)) (hnormv : ‖v‖ ^ 2 = (2 : ℝ)) :
    (⟪u, v⟫ : ℝ) = 0 ∨ (⟪u, v⟫ : ℝ) = (1 / 2 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 / 2 : ℝ) ∨
      (⟪u, v⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 : ℝ) := by
  rcases inner_twoU_v_halfInteger (C := C) h (hu := hu) (hv := hv) with ⟨m, hm⟩
  have habs : |(⟪u, v⟫ : ℝ)| ≤ ‖u‖ * ‖v‖ := by
    simpa using! (abs_real_inner_le_norm u v)
  have habs2 : |(⟪u, v⟫ : ℝ)| ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    simpa [pow_two] using! mul_le_mul habs habs (abs_nonneg _) (by positivity)
  have habs2' : |(⟪u, v⟫ : ℝ)| ^ 2 ≤ (2 : ℝ) := by
    simp_all
  have hm_abs2 : |((m : ℝ) / 2)| ^ 2 ≤ (2 : ℝ) := by
    simpa [hm] using! habs2'
  have hm_sq : (m : ℝ) ^ 2 ≤ (8 : ℝ) := by
    have hsq : ((m : ℝ) / 2) ^ 2 ≤ (2 : ℝ) := by
      simpa [sq_abs] using! hm_abs2
    nlinarith [hsq]
  have hm_le2 : m ≤ (2 : ℤ) := by
    refine le_of_not_gt ?_
    intro hm_gt2
    have hm_ge3 : (3 : ℤ) ≤ m := Int.add_one_le_of_lt hm_gt2
    have hm_ge3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge3
    have h9 : (9 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hm_ge3R]
    nlinarith [hm_sq, h9]
  have hm_geNeg2 : (-2 : ℤ) ≤ m := by
    refine le_of_not_gt ?_
    intro hm_ltNeg2
    have h1 : m + 1 ≤ (-2 : ℤ) := Int.add_one_le_of_lt hm_ltNeg2
    have hm_leNeg3 : m ≤ (-3 : ℤ) := by
      have := add_le_add_right h1 (-1 : ℤ)
      simpa [add_assoc] using! this
    have hm_leNeg3R : (m : ℝ) ≤ (-3 : ℝ) := by exact_mod_cast hm_leNeg3
    have h9 : (9 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hm_leNeg3R]
    nlinarith [hm_sq, h9]
  interval_cases m using hm_geNeg2, hm_le2
  · right; right; right; right
    rw [hm]
    norm_num
  · right; right; left
    rw [hm]
    norm_num
  · left
    rw [hm]
    norm_num
  · right; left
    rw [hm]
    norm_num
  · right; right; right; left
    rw [hm]
    norm_num

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16
