-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeLIntegral
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16.MinNorm
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Inner products in the norm-4 shell

Let `L₄` be the set of vectors of squared norm `4` in `L = span_ℤ (2 • C)`.
Using Lemma 16 to rule out vectors of squared norm `2` in `L`, we show that for `u,v ∈ L₄` with
`u ≠ v`, one has `⟪u, v⟫ ≠ ±3`. Together with integrality and Cauchy-Schwarz, this yields the
explicit list of possible inner products.

## Main statements
* `inner_ne_three_of_distinct_shell4`
* `inner_ne_neg_three_of_distinct_shell4`
* `inner_mem_set_of_shell4`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- If `‖x‖ ^ 2 = 4`, then `‖x‖ = 2`. -/
public lemma norm_eq_two_of_norm_sq_eq_four {x : ℝ²⁴} (hx : ‖x‖ ^ 2 = (4 : ℝ)) :
    ‖x‖ = (2 : ℝ) := by
  have habs : |‖x‖| = |(2 : ℝ)| :=
    (sq_eq_sq_iff_abs_eq_abs (‖x‖) (2 : ℝ)).1
      (by simpa using! hx.trans (by norm_num : (4 : ℝ) = (2 : ℝ) ^ 2))
  simpa [abs_of_nonneg (norm_nonneg x)] using! habs

/-- Inner products between vectors in `latticeShell4 C` are integers. -/
public theorem inner_mem_int_of_shell4
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    {u v : ℝ²⁴}
    (hu : u ∈ latticeShell4 C) (hv : v ∈ latticeShell4 C) :
    ∃ m : ℤ, ⟪u, v⟫ = (m : ℝ) := by
  -- Project the full Theorem 14 package to the legacy `EqCase24` integrality package.
  have hEq : Uniqueness.BS81.EqCase24 C :=
    Uniqueness.BS81.Thm14.EqCase24Pkg.toEqCase24 (C := C) h
  -- Both `u` and `v` lie in the lattice `latticeL C` by definition of the shell.
  exact
    Uniqueness.BS81.inner_latticeL_int (C := C) (hEq := hEq) (x := u) (y := v)
      hu.1 hv.1

/-- For distinct `u,v ∈ latticeShell4 C`, we have `⟪u, v⟫ ≠ 3`. -/
public theorem inner_ne_three_of_distinct_shell4
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    {u v : ℝ²⁴}
    (hu : u ∈ latticeShell4 C) (hv : v ∈ latticeShell4 C) :
    (⟪u, v⟫ : ℝ) ≠ (3 : ℝ) := by
  intro hinner
  have hmem : u - v ∈ (latticeL C : Set ℝ²⁴) :=
    (latticeL C).sub_mem hu.1 hv.1
  have hnorm_sq : ‖u - v‖ ^ 2 = (2 : ℝ) := by
    have hcalc :
        ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * (⟪u, v⟫ : ℝ) + ‖v‖ ^ 2 := by
      simpa using! (norm_sub_sq_real u v)
    linarith [hcalc, hu.2, hv.2, hinner]
  exact
    (Uniqueness.BS81.Thm15.Lemma16.no_norm_sq_two_vector_in_latticeL C h)
      ⟨u - v, hmem, hnorm_sq⟩

/-- For distinct `u,v ∈ latticeShell4 C`, we have `⟪u, v⟫ ≠ -3`. -/
public theorem inner_ne_neg_three_of_distinct_shell4
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    {u v : ℝ²⁴}
    (hu : u ∈ latticeShell4 C) (hv : v ∈ latticeShell4 C) :
    (⟪u, v⟫ : ℝ) ≠ (-3 : ℝ) := by
  intro hinner
  have hvneg : (-v) ∈ latticeShell4 C := by
    refine ⟨(latticeL C).neg_mem hv.1, ?_⟩
    simpa [norm_neg] using! hv.2
  have : (⟪u, -v⟫ : ℝ) ≠ (3 : ℝ) :=
    inner_ne_three_of_distinct_shell4 (C := C) h (u := u) (v := -v) hu hvneg
  exact this (by simp [inner_neg_right, hinner])

/-- Possible inner products between `u,v ∈ latticeShell4 C` lie in `{0, ±1, ±2, ±4}`. -/
public theorem inner_mem_set_of_shell4
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    {u v : ℝ²⁴}
    (hu : u ∈ latticeShell4 C) (hv : v ∈ latticeShell4 C) :
    (⟪u, v⟫ : ℝ) ∈ ({0, (1 : ℝ), (-1 : ℝ), (2 : ℝ), (-2 : ℝ), (4 : ℝ), (-4 : ℝ)} : Set ℝ) := by
  rcases inner_mem_int_of_shell4 (C := C) h hu hv with ⟨m, hm⟩
  have hnormu : ‖u‖ = (2 : ℝ) := norm_eq_two_of_norm_sq_eq_four hu.2
  have hnormv : ‖v‖ = (2 : ℝ) := norm_eq_two_of_norm_sq_eq_four hv.2
  have habs : |(⟪u, v⟫ : ℝ)| ≤ (4 : ℝ) := by
    have habs' : |(⟪u, v⟫ : ℝ)| ≤ (2 : ℝ) * (2 : ℝ) := by
      simpa [hnormu, hnormv] using! (abs_real_inner_le_norm u v)
    simpa using! (habs'.trans (by norm_num))
  have hmabs : |(m : ℝ)| ≤ (4 : ℝ) := by
    simpa [hm] using! habs
  have hm_le : (m : ℝ) ≤ (4 : ℝ) := (abs_le.mp hmabs).2
  have hm_ge : (-4 : ℝ) ≤ (m : ℝ) := (abs_le.mp hmabs).1
  have hm_le_z : m ≤ 4 := by exact_mod_cast hm_le
  have hm_ge_z : (-4 : ℤ) ≤ m := by exact_mod_cast hm_ge
  by_cases huv : u = v
  · subst huv
    have hinner4 : (⟪u, u⟫ : ℝ) = (4 : ℝ) := by
      calc
        (⟪u, u⟫ : ℝ) = ‖u‖ ^ 2 := by simp
        _ = (4 : ℝ) := hu.2
    rw [hinner4]
    simp
  · have hne3 : (⟪u, v⟫ : ℝ) ≠ (3 : ℝ) :=
      inner_ne_three_of_distinct_shell4 (C := C) h hu hv
    have hneN3 : (⟪u, v⟫ : ℝ) ≠ (-3 : ℝ) :=
      inner_ne_neg_three_of_distinct_shell4 (C := C) h hu hv
    interval_cases m using hm_ge_z, hm_le_z
    all_goals
      first
      | (rw [hm]; norm_num; done)
      | (exfalso; apply hne3; rw [hm]; norm_num; done)
      | (exfalso; apply hneN3; rw [hm]; norm_num; done)

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17
