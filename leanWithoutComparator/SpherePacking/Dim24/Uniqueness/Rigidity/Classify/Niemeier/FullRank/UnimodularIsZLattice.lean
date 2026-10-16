-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.FundamentalDomain
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.FullRank.InfiniteVolume
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Unimodular lattices have full rank

We show that a discrete unimodular `ℤ`-submodule `L ⊆ ℝ²⁴` has full real span `spanR L = ⊤`,
using the infinite-volume lemma from `Niemeier.FullRank.InfiniteVolume`. This yields an
`IsZLattice` structure on `L`.

## Main statements
* `IsZLatticeOfUnimodular.spanR_eq_top_of_unimodular_work`
* `IsZLatticeOfUnimodular.isZLattice_of_unimodular_work`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace IsZLatticeOfUnimodular

variable (L : Submodule ℤ ℝ²⁴)

/-- A discrete unimodular lattice has full real span `spanR L = ⊤`. -/
public theorem spanR_eq_top_of_unimodular_work [DiscreteTopology L] (hUnimod : Unimodular L) :
    spanR (L := L) = ⊤ := by
  by_contra hW
  -- Obtain a (measurable) fundamental domain from unimodularity.
  have hHas : MeasureTheory.HasAddFundamentalDomain L ℝ²⁴ volume :=
    hasAddFundamentalDomain_of_unimodular (L := L) hUnimod
  haveI : Countable L := countable_of_discrete (L := L)
  let F0 : Set ℝ²⁴ := hHas.ExistsIsAddFundamentalDomain.choose
  have hF0 : IsAddFundamentalDomain L F0 (volume : Measure ℝ²⁴) :=
    hHas.ExistsIsAddFundamentalDomain.choose_spec
  have hVolTop0 : (volume : Measure ℝ²⁴) F0 = ⊤ :=
    volume_eq_top_of_isAddFundamentalDomain_of_spanR_ne_top (L := L) hF0 hW
  -- Since `addCovolume` chooses some fundamental domain and `toReal ⊤ = 0`, we get
  -- `ZLattice.covolume L volume = 0`, contradicting `hUnimod : ... = 1`.
  have hcov0 : ZLattice.covolume L volume = 0 := by
    have hadd :
        MeasureTheory.addCovolume L ℝ²⁴ (volume : Measure ℝ²⁴) =
          (volume : Measure ℝ²⁴) F0 := by
      -- By definition, `addCovolume` is the volume of the chosen fundamental domain.
      simp [MeasureTheory.addCovolume, hHas, F0]
    -- Conclude `covolume = toReal ⊤ = 0`.
    simp [ZLattice.covolume, hadd, hVolTop0]
  exact (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa [Unimodular, hcov0] using! hUnimod.symm)

/-- A discrete unimodular `ℤ`-submodule of `ℝ²⁴` is a `ℤ`-lattice (`IsZLattice`). -/
public theorem isZLattice_of_unimodular_work [DiscreteTopology L] (hUnimod : Unimodular L) :
    IsZLattice ℝ L :=
  ⟨spanR_eq_top_of_unimodular_work (L := L) hUnimod⟩

end IsZLatticeOfUnimodular

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
