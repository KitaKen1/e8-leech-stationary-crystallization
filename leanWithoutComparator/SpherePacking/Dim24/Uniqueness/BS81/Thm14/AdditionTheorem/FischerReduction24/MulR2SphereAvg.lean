-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.FischerReduction24.MulR2Pointwise

/-!
# Fischer reduction: averaging `mulR2Pk` on the sphere

This step file records the `sphereAvg24` version of the `mulR2Pk` restriction lemma.

## Main statements
* `FischerReduction24Steps.sphereAvg24_eval_mulR2Pk_eq_sphereAvg24_eval_step`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24.FischerReduction24Steps

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.LP Uniqueness.BS81.Thm14.AdditionTheorem Uniqueness.BS81.LP.Gegenbauer24.PSD

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- On the unit sphere, averaging `mulR2Pk q` agrees with averaging `q` (step `k → k+2`). -/
public theorem sphereAvg24_eval_mulR2Pk_eq_sphereAvg24_eval_step
    (k : ℕ) (q : Fischer.Pk k) :
    sphereAvg24 (fun x : ℝ²⁴ =>
      evalPk24 (k := k + 2) (y := x) (Fischer.mulR2Pk (k := k) q)) =
      sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) q) := by
  -- Unfold `sphereAvg24` and use integral congruence on the sphere.
  unfold sphereAvg24
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro u
  -- `u` lies on the unit sphere, hence `‖u‖ = 1`, so `mulR2Pk` does not change evaluation.
  have hu1 : ‖(u.1 : ℝ²⁴)‖ = (1 : ℝ) := by
    rw [← dist_zero_right]
    exact Metric.mem_sphere.1 u.2
  simpa using!
    (FischerReduction24Steps.evalPk24_mulR2Pk_of_norm_eq_one_step (k := k) (q := q) (x := u.1) hu1)

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24.FischerReduction24Steps
