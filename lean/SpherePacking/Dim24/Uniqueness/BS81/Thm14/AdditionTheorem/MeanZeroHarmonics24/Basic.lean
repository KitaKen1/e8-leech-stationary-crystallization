-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DoubleSumsToHarmonics24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.MeanZeroHarmonics24.AtZero
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.MeanZeroHarmonics24.MeanValue

/-!
# Mean-zero for harmonic polynomials

This file proves the analytic input for the BS81 design bridge in dimension `24`: a nonconstant
harmonic homogeneous polynomial has mean `0` on the unit sphere.

The proof uses the mean-value property for harmonic functions on `ℝ²⁴` at the origin, together
with the fact that a homogeneous polynomial of positive degree vanishes at `0`.

## Main statements
* `AdditionTheorem.Bridge24.sphereAvg24_harmonic_degree_pos_eq_zero`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.LP

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
### Step 1: evaluation at `0` vanishes for positive degrees
-/

/-!
### Step 2: mean value property at the origin (harmonic ⇒ average over sphere = value at `0`)

The key statement we ultimately need is phrased directly in terms of `sphereAvg24` and `evalPk24`.
-/

/-!
### Consequence: mean-zero for `k ≥ 1`

This is the exact lemma the main bridge file needs.
-/

/-- Nonconstant harmonic homogeneous polynomials have mean `0` on the unit sphere (`n = 24`). -/
public theorem sphereAvg24_harmonic_degree_pos_eq_zero
    (k : ℕ) (hk : 1 ≤ k)
    (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic.Harm k) :
    sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x)
      (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k)) = 0 := by
  calc
    sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x)
        (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k))
        =
        evalPk24 (k := k) (y := (0 : ℝ²⁴))
          (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k) := by
          simpa using!
            (MeanZeroHarmonics24Steps.sphereAvg24_eq_evalPk24_at_zero_of_harmonic_step (k := k) h)
    _ = 0 := by
          simpa using!
            MeanZeroHarmonics24Steps.evalPk24_at_zero_eq_zero_of_degree_pos_step (k := k) hk (h : _)

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24
