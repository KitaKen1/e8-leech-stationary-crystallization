module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.Discrete
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.FundamentalDomain

/-!
# Setup objects for the Niemeier/Leech step

This file introduces a small structure bundling the ad-hoc predicates used in this repo
(`EvenNormSq`, `Unimodular`, `Rootless`) together with the basic typeclass consequences needed
for later analytic/combinatorial arguments (e.g. discreteness, existence of a fundamental domain).

No classification results are proved here.

## Main definitions
* `EvenUnimodularRootlessLattice`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
/-- A rank-24 candidate for the Niemeier/Leech classification step. -/
public structure EvenUnimodularRootlessLattice where
  /-- The underlying `ℤ`-submodule of `ℝ²⁴`. -/
  L : Submodule ℤ ℝ²⁴
  /-- Evenness of squared norms (ad-hoc predicate used throughout this repo). -/
  hEven : EvenNormSq L
  /-- Unimodularity, expressed as `ZLattice.covolume L volume = 1`. -/
  hUnimod : Unimodular L
  /-- Rootlessness: no vectors of squared norm `2`. -/
  hRootless : Rootless L

namespace EvenUnimodularRootlessLattice

variable (X : EvenUnimodularRootlessLattice)

/-- An even rootless lattice has the discrete topology. -/
public instance instDiscreteTopology : DiscreteTopology X.L :=
  instDiscreteTopology_of_even_rootless (L := X.L) X.hEven X.hRootless

/-- A unimodular lattice admits an additive fundamental domain. -/
public theorem hasAddFundamentalDomain :
    MeasureTheory.HasAddFundamentalDomain X.L ℝ²⁴ MeasureTheory.volume :=
  hasAddFundamentalDomain_of_unimodular (L := X.L) X.hUnimod

/-- Evenness of squared norms implies integrality of inner products. -/
public theorem integral : Integral X.L :=
  integral_of_evenNormSq (L := X.L) X.hEven

end SpherePacking.Dim24.Uniqueness.RigidityClassify.EvenUnimodularRootlessLattice
