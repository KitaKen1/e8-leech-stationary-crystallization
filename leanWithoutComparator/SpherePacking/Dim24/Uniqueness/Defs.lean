module
public import SpherePacking.Dim24.Packing


/-!
# Definitions for the dimension-24 uniqueness statement

These are separated from `SpherePacking/Dim24/Uniqueness.lean` so that supporting modules can
`public import` them without creating import cycles.

## Main definitions
* `PeriodicSpherePacking.Isometric`
* `IsometricToScaledLeech`
* `HasLeechDistanceSpectrum`
-/


namespace SpherePacking.Dim24

open scoped ENNReal

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

section
variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

/-- Isometry equivalence for periodic packings: same sphere configuration up to an ambient isometry.

Faithfulness note:
In our `SpherePacking` structure, `separation` is part of the data (it fixes the sphere radius
`separation/2`). Equality of center sets alone would not rule out choosing a smaller separation
than the true minimal distance, so we include `separation` in the equivalence.
-/
@[expose] public def PeriodicSpherePacking.Isometric (S T : PeriodicSpherePacking d) : Prop :=
  S.separation = T.separation ∧
    ∃ e : V ≃ᵢ V, e '' S.centers = T.centers


end

/-- The "scaled-isometric to the Leech packing" conclusion appearing in Theorem 1.1. -/
@[expose] public def IsometricToScaledLeech (S : PeriodicSpherePacking 24) : Prop :=
  ∃ c : ℝ, ∃ hc : 0 < c,
    PeriodicSpherePacking.Isometric S (PeriodicSpherePacking.scale (S := LeechPacking) (d := 24) hc)

/-- A convenient intermediate invariant: the set of squared interpoint distances is contained in
`{2k | k ≥ 2}` (the Leech "even norm" spectrum), after suitable normalization.

This is the kind of constraint produced by the equality case analysis in Cohn-Elkies, Section 8,
combined with the root structure of the auxiliary function `f`.
-/
@[expose] public def HasLeechDistanceSpectrum (S : PeriodicSpherePacking 24) : Prop :=
  ∀ x y : S.centers, x ≠ y → ∃ k : ℕ, 2 ≤ k ∧ ‖(x : ℝ²⁴) - (y : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * k

end SpherePacking.Dim24
