-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Scale
public import SpherePacking.Dim24.Uniqueness.Input.Roots
import SpherePacking.Dim24.MagicFunction.F.RealValued
import SpherePacking.Dim24.Uniqueness.Input.EqualityCase

/-!
# Reduction to the Leech distance spectrum

This file reduces optimality (attaining the Leech density) to the constraint that the squared
interpoint distances lie in the Leech distance spectrum, after scaling to normalize
`separation = 2`.

It packages the equality-case input from the Cohn-Elkies LP bound and the root structure of the
auxiliary function `f`.
-/

namespace SpherePacking.Dim24

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
Equality-case input for the Cohn-Elkies linear programming bound (dimension 24).
-/

/-- Equality case (Cohn-Elkies, Section 8): in the normalized setting `separation = 2`,
attaining the Leech density forces `f(x-y)=0` for every pair of distinct centers.

This is the precise "slack vanishes pointwise" statement used to extract the distance spectrum.
-/
public theorem optimality_normalized_forces_f_of_sub_eq_zero (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2) (hS : S.density = LeechPacking.density) :
    ∀ x y : S.centers, x ≠ y → f ((x : ℝ²⁴) - (y : ℝ²⁴)) = 0 := by
  intro x y hxy
  have hre : (f ((x : ℝ²⁴) - (y : ℝ²⁴))).re = 0 :=
    optimality_normalized_forces_f_of_sub_re_eq_zero (S := S) hSep hS x y hxy
  simpa [f_real ((x : ℝ²⁴) - (y : ℝ²⁴))] using! congrArg (fun r : ℝ => (r : ℂ)) hre

/-!
Elementary geometric lemmas converting separation bounds into norm bounds, used in the
uniqueness-distance-spectrum reduction.
-/

/-- `S.separation` bounds below the distance between any two distinct centers. -/
public theorem PeriodicSpherePacking.separation_le_norm_sub {d : ℕ} (S : PeriodicSpherePacking d)
    {x y : S.centers} (hxy : x ≠ y) :
    S.separation ≤ ‖(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))‖ := by
  simpa [dist_eq_norm] using! (S.centers_dist hxy)

/-- If `S.separation = 2`, then any two distinct centers are at distance at least `2`. -/
public theorem PeriodicSpherePacking.two_le_norm_sub_of_separation_eq_two
    (S : PeriodicSpherePacking 24) (hSep : S.separation = 2) {x y : S.centers} (hxy : x ≠ y) :
    (2 : ℝ) ≤ ‖(x : ℝ²⁴) - (y : ℝ²⁴)‖ := by
  simpa [hSep] using! (PeriodicSpherePacking.separation_le_norm_sub (S := S) (hxy := hxy))

/-- Root structure of `f` for `‖x‖ ≥ 2`:
if `f(x)=0` and `‖x‖ ≥ 2`, then `‖x‖^2 = 2k` for some
integer `k ≥ 2`.

Paper reference: `dim_24.tex`, end of Section 4 (just before the appendix). -/
public theorem norm_sq_eq_two_mul_of_f_eq_zero_of_two_le_norm (x : ℝ²⁴)
    (hx : (2 : ℝ) ≤ ‖x‖) (hf : f x = 0) :
    ∃ k : ℕ, 2 ≤ k ∧ ‖x‖ ^ 2 = (2 : ℝ) * k := by
  have hfAxis : f (axisVec ‖x‖) = 0 := by
    simpa [f_eq_f_axisVec_norm (x := x)] using! hf
  exact norm_sq_eq_two_mul_of_f_axisVec_eq_zero_of_two_le ‖x‖ hx hfAxis

/-- Equality case input (Cohn-Elkies, Section 8): once the packing is normalized to have
`separation = 2`, attaining the Leech density forces the Leech distance spectrum.

This is where the argument connects:
- equality in the LP bound to vanishing of slack terms,
- vanishing to membership in the zero set of the auxiliary function,
- the explicit root structure of `f` for `r ≥ 2`.
-/
public theorem optimal_periodic_has_leech_distance_spectrum_normalized
    (S : PeriodicSpherePacking 24) (hSep : S.separation = 2)
    (hS : S.density = LeechPacking.density) :
    HasLeechDistanceSpectrum S := by
  intro x y hxy
  refine norm_sq_eq_two_mul_of_f_eq_zero_of_two_le_norm (x - y) ?_ ?_
  · exact PeriodicSpherePacking.two_le_norm_sub_of_separation_eq_two (S := S) hSep hxy
  · exact optimality_normalized_forces_f_of_sub_eq_zero (S := S) hSep hS x y hxy

/-- From optimality, deduce the Leech distance spectrum after an appropriate scaling.

Paper reference: `dim_24.tex`, Introduction + the discussion citing Cohn-Elkies, Section 8.
-/
public theorem optimal_periodic_has_leech_distance_spectrum (S : PeriodicSpherePacking 24)
    (hS : S.density = LeechPacking.density) :
    ∃ c : ℝ, ∃ hc : 0 < c,
  (S.scale hc).separation = 2 ∧ HasLeechDistanceSpectrum (S.scale hc) := by
  -- Normalize to separation `2` by scaling.
  rcases PeriodicSpherePacking.exists_scale_separation_eq_two (S := S) with ⟨c, hc, hSep⟩
  refine ⟨c, hc, hSep, ?_⟩
  have hDens : (S.scale hc).density = LeechPacking.density := by
    simpa [PeriodicSpherePacking.scale_density (S := S) (hc := hc)] using! hS
  exact optimal_periodic_has_leech_distance_spectrum_normalized (S := S.scale hc) hSep hDens

end SpherePacking.Dim24
