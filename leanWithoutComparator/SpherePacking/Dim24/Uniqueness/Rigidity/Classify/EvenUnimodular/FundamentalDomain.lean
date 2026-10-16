module
public import SpherePacking.Dim24.Uniqueness.LatticeInvariants

/-!
# Fundamental domains from unimodularity

In this repo `Unimodular L` is the ad-hoc assertion `ZLattice.covolume L volume = 1`.
Since `ZLattice.covolume` is the real part of `MeasureTheory.addCovolume`, which is `0` when no
fundamental domain exists, unimodularity forces the existence of an additive fundamental domain.

## Main statements
* `hasAddFundamentalDomain_of_unimodular`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

open MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
/-- A unimodular lattice admits an additive fundamental domain. -/
public theorem hasAddFundamentalDomain_of_unimodular (L : Submodule ℤ ℝ²⁴)
    (hUnimod : Unimodular L) :
    MeasureTheory.HasAddFundamentalDomain L ℝ²⁴ volume := by
  by_contra hFD
  have h0 : ZLattice.covolume L volume = 0 := by
    simp [ZLattice.covolume, MeasureTheory.addCovolume, hFD]
  exact zero_ne_one ((show (0 : ℝ) = 1 from h0.symm.trans hUnimod))

end SpherePacking.Dim24.Uniqueness.RigidityClassify
