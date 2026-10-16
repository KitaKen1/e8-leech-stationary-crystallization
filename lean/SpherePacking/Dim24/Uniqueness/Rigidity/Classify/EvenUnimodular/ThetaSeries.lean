-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.FiniteShells
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Theta series coefficients

For a discrete `ℤ`-submodule `L ⊆ ℝ²⁴`, we define the shells
`thetaShell L n = {v ∈ L | ‖v‖^2 = 2n}` and the corresponding counting function `thetaCoeff L n`.

We prove finiteness of each shell and record basic coefficient identities at `n = 0` and `n = 1`
(for rootless lattices).

## Main definitions
* `thetaShell`
* `thetaCoeff`

## Main statements
* `finite_thetaShell`
* `thetaCoeff_zero`
* `thetaCoeff_one_eq_zero_of_rootless`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The `n`-th shell for the theta series: lattice vectors of squared norm `2n`. -/
@[expose]
public def thetaShell (L : Submodule ℤ ℝ²⁴) (n : ℕ) : Set ℝ²⁴ :=
  {v : ℝ²⁴ | v ∈ L ∧ ‖v‖ ^ 2 = (2 : ℝ) * n}

lemma norm_le_two_mul_add_one_of_norm_sq_eq (v : ℝ²⁴) (n : ℕ)
    (h : ‖v‖ ^ 2 = (2 : ℝ) * n) :
    ‖v‖ ≤ (2 : ℝ) * n + 1 := by
  have hR0 : 0 ≤ (2 : ℝ) * n + 1 := by nlinarith
  have hsq : ‖v‖ ^ 2 ≤ ((2 : ℝ) * n + 1) ^ 2 := by
    -- `‖v‖^2 = 2n ≤ (2n+1)^2`.
    nlinarith [h]
  -- Convert the inequality on squares into an inequality on norms.
  exact (sq_le_sq₀ (norm_nonneg v) hR0).1 (by simpa [pow_two] using! hsq)

/-- For a discrete lattice, each shell `thetaShell L n` is finite. -/
public theorem finite_thetaShell (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] (n : ℕ) :
    (thetaShell L n).Finite := by
  -- Compare with the bounded shell `{v ∈ L | ‖v‖ ≤ 2n+1}`.
  refine (finite_shell_norm_le (L := L) (R := (2 : ℝ) * n + 1)).subset ?_
  intro v hv
  rcases hv with ⟨hvL, hvSq⟩
  refine ⟨hvL, ?_⟩
  simpa using! norm_le_two_mul_add_one_of_norm_sq_eq (v := v) (n := n) hvSq

/-- The `n`-th theta coefficient: the number of lattice vectors of squared norm `2n`. -/
@[expose]
public noncomputable def thetaCoeff (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] (n : ℕ) : ℕ :=
  (finite_thetaShell (L := L) n).toFinset.card

/-- The zeroth theta coefficient is `1` (the only vector of squared norm `0` is `0`). -/
@[simp]
public theorem thetaCoeff_zero (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] : thetaCoeff L 0 = 1 := by
  -- `thetaShell L 0 = {0}`.
  have hShell : thetaShell L 0 = ({0} : Set ℝ²⁴) := by
    ext v
    constructor
    · rintro ⟨-, hv⟩
      -- `‖v‖^2 = 0` implies `v = 0`.
      simp_all
    · intro hv
      rcases hv with rfl
      simp [thetaShell]
  simp [thetaCoeff, hShell]

/-- In a rootless lattice, the first theta coefficient vanishes. -/
@[simp]
public theorem thetaCoeff_one_eq_zero_of_rootless (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L]
    (hRootless : Rootless L) :
    thetaCoeff L 1 = 0 := by
  -- `thetaShell L 1` is empty by rootlessness.
  have hEmpty : thetaShell L 1 = (∅ : Set ℝ²⁴) := by
    ext v
    constructor
    · rintro ⟨hvL, hv⟩
      have hv0 : v ≠ 0 := by
        rintro rfl
        simp at hv
      have : ‖v‖ ^ 2 ≠ (2 : ℝ) := by
        simpa [Rootless] using! hRootless v hvL hv0
      -- but `‖v‖^2 = 2` in `thetaShell L 1`
      exact (this (by simpa using! hv)).elim
    · intro hv
      simp at hv
  simp [thetaCoeff, hEmpty]

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
