-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Module.Pi

/-!
# Zonal Gegenbauer kernels on `Ω₂₄`

This file introduces the kernel-level API used by the Delsarte linear programming method.
The normalized Gegenbauer zonal kernel is

`zonalKernel24 k u v = (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)`,

and `IsPSDKernel24 K` expresses the nonnegativity of the double sum
`∑ u in C, ∑ v in C, K u v` for every finite `C ⊆ Ω₂₄` of unit vectors.

The proof that `zonalKernel24 k` is PSD (Schoenberg / addition theorem) is in
`.../LP/Gegenbauer24/KernelPSD.lean`.

## Main definitions
* `zonalKernel24`
* `IsPSDKernel24`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.LP
noncomputable section

open scoped RealInnerProductSpace BigOperators

open Polynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The normalized Gegenbauer zonal kernel on `Ω₂₄`. -/
@[expose] public def zonalKernel24 (k : ℕ) (u v : ℝ²⁴) : ℝ :=
  (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)

/-- The PSD inequality we need for a zonal kernel. -/
@[expose] public def IsPSDKernel24 (K : ℝ²⁴ → ℝ²⁴ → ℝ) : Prop :=
  ∀ C : Finset ℝ²⁴,
    (∀ u ∈ C, ‖u‖ = (1 : ℝ)) →
      0 ≤ C.sum (fun u => C.sum (fun v => K u v))

/-!
Positivity of the Gegenbauer zonal kernels (Schoenberg / addition theorem).

This is the key analytic input behind the Delsarte dual certificate.

Reference: CK06 §2.2 (positive-definite kernels on spheres).

The corresponding Lean lemma is `Uniqueness.BS81.LP.zonalKernel24_psd` in
`.../LP/Gegenbauer24/KernelPSD.lean`.
-/

/-- PSD kernels are closed under nonnegative linear combinations. -/
lemma IsPSDKernel24.add_nonneg_smul
    {K₁ K₂ : ℝ²⁴ → ℝ²⁴ → ℝ}
    (h₁ : IsPSDKernel24 K₁) (h₂ : IsPSDKernel24 K₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsPSDKernel24 (fun u v => a * K₁ u v + b * K₂ u v) := by
  intro C hC
  have hsum₁ : 0 ≤ C.sum (fun u => C.sum (fun v => K₁ u v)) := h₁ C hC
  have hsum₂ : 0 ≤ C.sum (fun u => C.sum (fun v => K₂ u v)) := h₂ C hC
  have hlin :
      C.sum (fun u => C.sum (fun v => a * K₁ u v + b * K₂ u v)) =
        a * C.sum (fun u => C.sum (fun v => K₁ u v)) +
          b * C.sum (fun u => C.sum (fun v => K₂ u v)) := by
    -- Expand both sums using `Finset.sum_add_distrib` and pull out scalars using `Finset.mul_sum`.
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  -- Conclude by nonnegativity of each scalar multiple.
  have hnonneg₁ : 0 ≤ a * C.sum (fun u => C.sum (fun v => K₁ u v)) := mul_nonneg ha hsum₁
  have hnonneg₂ : 0 ≤ b * C.sum (fun u => C.sum (fun v => K₂ u v)) := mul_nonneg hb hsum₂
  -- Rewrite the goal using `hlin`.
  simpa [hlin] using! add_nonneg hnonneg₁ hnonneg₂

end

end SpherePacking.Dim24.Uniqueness.BS81.LP
