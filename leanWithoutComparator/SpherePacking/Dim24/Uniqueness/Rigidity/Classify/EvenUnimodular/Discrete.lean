-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.MinNorm

/-!
# Discreteness from a min-norm bound

If a subgroup of a metric additive group admits a positive lower bound on distances between
distinct points, then it carries the discrete topology.

We specialize this observation to `Submodule ℤ ℝ²⁴`, using the min-norm bound for even rootless
lattices from `EvenUnimodular.MinNorm`.

## Main statements
* `discreteTopology_of_two_le_norm`
* `instDiscreteTopology_of_even_rootless`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
/-- If every nonzero vector in `L` has norm at least `2`, then `L` has the discrete topology. -/
public theorem discreteTopology_of_two_le_norm (L : Submodule ℤ ℝ²⁴)
    (hmin : ∀ v : ℝ²⁴, v ∈ L → v ≠ 0 → (2 : ℝ) ≤ ‖v‖) :
    DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  rw [Metric.isOpen_iff]
  intro y hy
  have hy' : y = x := by simpa [Set.mem_singleton_iff] using! hy
  subst y
  refine ⟨(1 : ℝ), by norm_num, ?_⟩
  intro z hz
  by_cases hzx : z = x
  · simp [Set.mem_singleton_iff, hzx]
  have hsub : ((z : ℝ²⁴) - (x : ℝ²⁴)) ∈ L := sub_mem z.property x.property
  have hsub0 : ((z : ℝ²⁴) - (x : ℝ²⁴)) ≠ 0 := by
    intro h0
    apply hzx
    apply Subtype.ext
    exact sub_eq_zero.mp h0
  have hge : (2 : ℝ) ≤ ‖(z : ℝ²⁴) - (x : ℝ²⁴)‖ := hmin _ hsub hsub0
  have hge' : (2 : ℝ) ≤ dist z x := by simpa [Subtype.dist_eq, dist_eq_norm] using! hge
  have hz' : dist z x < 2 := by
    exact lt_trans (by simpa [Metric.mem_ball] using! hz) (by norm_num)
  exact False.elim ((not_lt_of_ge hge') hz')

/-- An even rootless lattice has the discrete topology. -/
public theorem instDiscreteTopology_of_even_rootless (L : Submodule ℤ ℝ²⁴)
    (hEven : EvenNormSq L) (hRootless : Rootless L) :
    DiscreteTopology L :=
  discreteTopology_of_two_le_norm (L := L)
    (hmin := two_le_norm_of_evenNormSq_rootless (L := L) hEven hRootless)

end SpherePacking.Dim24.Uniqueness.RigidityClassify
