-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.HarmPolyRecurrence24
import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.NormalizedRecurrence

/-!
# Normalized recurrence for `harmPoly24`

This file lives in the Theorem 14 design namespace and re-exports the addition-theorem bridge from
the LP layer. In particular, it provides the kernel identity
`harmKernel24 k u v = harmKernelScalar24 k * (Gegenbauer24 k).eval ⟪u, v⟫` for unit vectors.

It also records the normalized three-term recurrence and initial values for `harmPoly24`.

## Main statements
* `AdditionTheorem.harmKernel24_eq_gegenbauer_eval`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Polynomial
open Uniqueness.BS81.LP

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open Uniqueness.BS81.LP
open Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem
open Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalKernel

/-!
## Re-export from the LP layer

The LP folder `.../LP/Gegenbauer24/AdditionTheorem/` contains the addition-theorem bridge in the
namespace `Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem`.

This file lives in the Theorem 14 design layer. To avoid duplicating the entire bridge, we
re-export the core definitions and statements in the current namespace.

This provides convenient access to the core definitions and statements in the current namespace.
-/

/-- Recurrence coefficient `α_k` for the normalized Gegenbauer recurrence in dimension `24`. -/
abbrev α (k : ℕ) : ℝ :=
  (k + 22 : ℝ) / (2 * k + 22 : ℝ)

/-- Recurrence coefficient `β_k` for the normalized Gegenbauer recurrence in dimension `24`. -/
abbrev β (k : ℕ) : ℝ :=
  (k : ℝ) / (2 * k + 22 : ℝ)

/-!
## Recurrence coefficients

For `n = 24`, the normalized recurrence (as in `LP/Gegenbauer24/NormalizedRecurrence.lean`) is:

`t P_k(t) = α_k P_{k+1}(t) + β_k P_{k-1}(t)` for `k ≥ 1`,
with `α_k = (k+22)/(2k+22)` and `β_k = k/(2k+22)`.
-/

/-!
## Initial values

`harmPoly24 0 = 1`, `harmPoly24 1 = X`.

These are normalization conventions for the harmonic reproducing kernel at degrees `0,1`.
-/

theorem harmPoly24_zero : harmPoly24 0 = (1 : Polynomial ℝ) := by
  simp [Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.harmPoly24]

theorem harmPoly24_one : harmPoly24 1 = (X : Polynomial ℝ) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h11 : (11 : ℝ) ≠ 0 := by norm_num
  -- Unfold `harmPoly24` as the normalized Gegenbauer polynomial, then simplify at index `1`.
  simp only [harmPoly24, Gegenbauer24, gegenbauer, gegenbauer24Param, map_mul, mul_comm, eval_mul,
    eval_X, eval_C, one_mul, mul_inv_rev, mul_left_comm, ne_eq, X_ne_zero, not_false_eq_true,
    mul_eq_left₀]
  -- Remaining goal: scalar cancellation in the constant polynomial ring.
  rw [(mul_assoc (C (2 : ℝ) : Polynomial ℝ) (C (2⁻¹ : ℝ) : Polynomial ℝ)
    ((C (11 : ℝ) : Polynomial ℝ) * C (11⁻¹ : ℝ))).symm]
  rw [← (Polynomial.C_mul (R := ℝ) (a := (2 : ℝ)) (b := (2⁻¹ : ℝ)))]
  rw [← (Polynomial.C_mul (R := ℝ) (a := (11 : ℝ)) (b := (11⁻¹ : ℝ)))]
  rw [← (Polynomial.C_mul (R := ℝ) (a := (2 : ℝ) * (2⁻¹ : ℝ)) (b := (11 : ℝ) * (11⁻¹ : ℝ)))]
  simp [h2, h11]

/-!
## Normalized three-term recurrence

This is the central lemma of the bridge note, specialized to `n = 24`.

Paper reference:
`paper/Notes/SphericalLP/gegenbauer_addition_theorem_bridge.tex`, Corollary `cor:Pk_recur`.
-/

theorem harmPoly24_normalized_recurrence (k : ℕ) (hk : 1 ≤ k) :
    (X : Polynomial ℝ) * harmPoly24 k =
      (C (α k)) * harmPoly24 (k + 1) + (C (β k)) * harmPoly24 (k - 1) := by
  -- Reduce to the normalized Gegenbauer recurrence.
  cases k with
  | zero =>
      cases (Nat.not_succ_le_zero 0 hk)
  | succ n =>
      -- Work by evaluation extensionality.
      refine Polynomial.funext ?_
      intro t
      have hrec :=
        Uniqueness.BS81.LP.Gegenbauer24_eval_recurrence_succ (n := n) (t := t)
      have hden : (2 + ((n : ℝ) * 2 + 22)) = (n : ℝ) * 2 + 24 := by ring
      have hnum : (n : ℝ) + (1 + 22) = (n : ℝ) + 23 := by ring
      simpa [Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.harmPoly24, α, β,
        Nat.succ_eq_add_one, hden, hnum, add_assoc, add_left_comm, add_comm,
        mul_add, add_mul, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using! hrec

/-!
## Identification with recurrence-defined `Gegenbauer24`

Once the recurrence and initial values are established, identification is a routine induction.

Paper reference:
`paper/Notes/SphericalLP/gegenbauer_addition_theorem_bridge.tex`, Theorem `thm:identify`.
-/

theorem harmPoly24_eq_Gegenbauer24 (k : ℕ) : harmPoly24 k = Gegenbauer24 k := by
  rfl

/-!
## Kernel-level identification

Combining the reduction lemma from `ZonalKernelReduction24.lean` with the polynomial equality
`harmPoly24 = Gegenbauer24` yields the pointwise kernel identity on the unit sphere:

`harmKernel24 k u v = Gegenbauer24 k (⟪u,v⟫)`.

This is the exact addition theorem conclusion used by the Delsarte LP method.
-/

/-- Pointwise identification of `harmKernel24` with the Gegenbauer kernel on the unit sphere. -/
public theorem harmKernel24_eq_gegenbauer_eval
    (k : ℕ) {u v : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) (hv : ‖v‖ = (1 : ℝ)) :
    harmKernel24 k u v =
      (Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.harmKernelScalar24 k) *
        (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ) :=
  Gegenbauer24.AdditionTheorem.harmKernel24_eq_gegenbauer_eval k hu hv

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem
