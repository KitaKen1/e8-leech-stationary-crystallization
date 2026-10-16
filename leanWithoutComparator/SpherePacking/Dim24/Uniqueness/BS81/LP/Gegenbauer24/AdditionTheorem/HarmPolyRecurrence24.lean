-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.ZonalPolynomial24
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Kernel

/-!
# Gegenbauer recurrence for the harmonic zonal kernel (dimension 24)

This file completes the addition-theorem bridge: the zonal polynomial `harmPoly24` extracted from
harmonic projection agrees with the normalized Gegenbauer polynomial `Gegenbauer24`. As a result,
the harmonic Gram kernel `harmKernel24` is a scalar multiple of
`(Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)`.

## Main statements
* `harmKernel24_eq_gegenbauer_eval`
* `zonalKernel24_eq_inv_harmKernelScalar24_mul_harmKernel24`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem
noncomputable section

open scoped RealInnerProductSpace

open Polynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Express `harmKernel24` as a scalar multiple of the normalized Gegenbauer kernel. -/
public theorem harmKernel24_eq_gegenbauer_eval
    (k : ℕ) {u v : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) (hv : ‖v‖ = (1 : ℝ)) :
    PSD.ZonalKernel.harmKernel24 k u v =
      (harmKernelScalar24 k) *
        (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ) := by
  simpa [harmPoly24, mul_assoc, mul_left_comm, mul_comm] using!
    (harmKernel24_eq_harmPoly24_eval (k := k) (u := u) (v := v) hu hv)

theorem harmKernel24_eq_zonalKernel24
    (k : ℕ) {u v : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) (hv : ‖v‖ = (1 : ℝ)) :
    PSD.ZonalKernel.harmKernel24 k u v =
      (harmKernelScalar24 k) *
        zonalKernel24 k u v := by
  simpa [zonalKernel24, mul_assoc] using!
    (harmKernel24_eq_gegenbauer_eval (k := k) (u := u) (v := v) hu hv)

/-- Solve for `zonalKernel24` in terms of `harmKernel24` and `harmKernelScalar24`. -/
public theorem zonalKernel24_eq_inv_harmKernelScalar24_mul_harmKernel24
    (k : ℕ) {u v : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) (hv : ‖v‖ = (1 : ℝ)) :
    zonalKernel24 k u v =
      (harmKernelScalar24 k)⁻¹ *
        PSD.ZonalKernel.harmKernel24 k u v := by
  have hs : harmKernelScalar24 k ≠ 0 := harmKernelScalar24_ne_zero (k := k)
  have h :=
    (harmKernel24_eq_zonalKernel24 (k := k) (u := u) (v := v) hu hv)
  exact (eq_inv_mul_iff_mul_eq₀ hs).mpr (id (Eq.symm h))

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem
