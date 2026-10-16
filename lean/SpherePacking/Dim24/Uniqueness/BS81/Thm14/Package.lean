module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs

/-!
# BS81 Theorem 14 package

BS81 Theorem 14 asserts that if `C` is an optimal `(24, 196560, 1/2)` code, then:
* `C` is a tight spherical `11`-design in `Ω₂₄`,
* the distance distribution is given explicitly by equation (11),
* and `C` carries a `6`-class association scheme.

For the kissing-uniqueness route in this development, the association-scheme portion is not used.
Instead we derive the only required intersection number (the `44` common-neighbors count) directly
from the design and distance-distribution package, via spherical mixed moments; see
`paper/Notes/SphericalLP/bs81_common_neighbors_44.tex`.

This file packages the needed conclusions as the structure `EqCase24Pkg`.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The full conclusion package of BS81 Theorem 14. -/
public structure EqCase24Pkg (C : Set ℝ²⁴) : Prop extends Uniqueness.BS81.EqCase24 C where
  /-- BS81 design property (equation (14)) with `t=11`, stated for the `Finset` of `C`. -/
  design11 : IsBS81SphericalDesign24 11 code.finite.toFinset

attribute [grind cases] EqCase24Pkg

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
