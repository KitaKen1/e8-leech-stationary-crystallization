-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.LatticeInvariants
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.Bases

/-!
# Unimodular implies full rank

In this repo, `Unimodular L` is defined as `ZLattice.covolume L volume = 1`.
Since `ZLattice.covolume` is defined using `MeasureTheory.addCovolume`, and `ENNReal.toReal ⊤ = 0`,
any lattice whose action admits *only* infinite-volume fundamental domains has covolume `0`.

We use this to show: if `L` is discrete and unimodular in `ℝ²⁴`, then it spans `ℝ²⁴` over `ℝ`.

## Main definitions
* `IsZLatticeOfUnimodular.spanR`

## Main statements
* `IsZLatticeOfUnimodular.countable_of_discrete`
* `IsZLatticeOfUnimodular.volume_univ_orthogonal_eq_top`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace Topology
open MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace IsZLatticeOfUnimodular

variable (L : Submodule ℤ ℝ²⁴)

/-- The real span of `L`, as an `ℝ`-subspace of `ℝ²⁴`. -/
@[expose]
public abbrev spanR : Submodule ℝ ℝ²⁴ :=
  Submodule.span ℝ (L : Set ℝ²⁴)

/-- The underlying set of `L` is contained in its real span `spanR L`. -/
public lemma subset_spanR : (L : Set ℝ²⁴) ⊆ (spanR (L := L)) := by
  intro x hx
  exact Submodule.subset_span hx

/-! ### Countability -/

/-- A discrete `ℤ`-submodule of `ℝ²⁴` is countable. -/
public lemma countable_of_discrete [DiscreteTopology L] : Countable L := by
  -- A discrete separable space is countable; `L` is separable as a subspace of `ℝ²⁴`.
  haveI : TopologicalSpace.SeparableSpace L := by infer_instance
  exact (TopologicalSpace.separableSpace_iff_countable (α := L)).1 (by infer_instance)

/-! ### Orthogonal complement nontriviality -/

/-- If `spanR L` is not all of `ℝ²⁴`, then its orthogonal complement is nontrivial. -/
public lemma orthogonal_ne_bot_of_spanR_ne_top (h : spanR (L := L) ≠ ⊤) :
    (spanR (L := L))ᗮ ≠ ⊥ := by
  intro hbot
  exact h (by simpa [Submodule.orthogonal_eq_bot_iff] using! hbot)

/-- If `spanR L` is not all of `ℝ²⁴`, then the orthogonal complement has infinite volume. -/
public lemma volume_univ_orthogonal_eq_top (h : spanR (L := L) ≠ ⊤) :
    volume (Set.univ : Set (↥((spanR (L := L))ᗮ))) = ⊤ := by
  have hne : (spanR (L := L))ᗮ ≠ ⊥ := orthogonal_ne_bot_of_spanR_ne_top (L := L) h
  haveI : Nontrivial ((spanR (L := L))ᗮ) :=
    Submodule.nontrivial_iff_ne_bot.mpr hne
  simp_all

end IsZLatticeOfUnimodular

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
