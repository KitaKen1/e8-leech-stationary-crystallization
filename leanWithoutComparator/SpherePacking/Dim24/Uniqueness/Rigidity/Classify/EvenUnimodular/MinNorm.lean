-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.LatticeInvariants

/-!
# Even lattices: a min-norm bound

We record a simple consequence of the hypotheses `EvenNormSq L` and `Rootless L`: every nonzero
vector in `L` has norm at least `2`.

## Main statements
* `two_le_norm_of_evenNormSq_rootless`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
/-- In an even rootless lattice, every nonzero vector has norm at least `2`. -/
public lemma two_le_norm_of_evenNormSq_rootless (L : Submodule ℤ ℝ²⁴)
    (hEven : EvenNormSq L) (hRootless : Rootless L) :
    ∀ v : ℝ²⁴, v ∈ L → v ≠ 0 → (2 : ℝ) ≤ ‖v‖ := by
  intro v hv hv0
  rcases hEven v hv with ⟨n, hn⟩
  have hn0 : n ≠ 0 := by
    intro hn0
    simp_all
  have hn1 : n ≠ 1 := by
    intro hn1
    have : ‖v‖ ^ 2 = (2 : ℝ) := by simpa [hn1] using! hn
    exact (hRootless v hv hv0) this
  have hn2 : 2 ≤ n := by
    omega
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hsq : (2 : ℝ) ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [hn, hn']
  exact (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg v)).1 hsq

end SpherePacking.Dim24.Uniqueness.RigidityClassify
