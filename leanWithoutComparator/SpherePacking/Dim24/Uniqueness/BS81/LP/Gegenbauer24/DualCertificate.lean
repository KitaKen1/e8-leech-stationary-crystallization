-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Delsarte
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.KernelPSD
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Dual certificates from Gegenbauer expansions

This file is the bridge between:
* positivity of the Gegenbauer zonal kernels `Gegenbauer24 k (⟪u,v⟫)` (kernel-level PSD), and
* the Delsarte dual-certificate inequality
  `a0 * |C|^2 ≤ ∑ u in C, ∑ v in C, f.eval (⟪u,v⟫)` for a polynomial `f` with nonnegative
  Gegenbauer coefficients.

## Main definitions
* `gegenbauerExpansion`

## Main statements
* `isDelsarteDual24_of_gegenbauerExpansion`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP
noncomputable section

open scoped RealInnerProductSpace BigOperators

open Polynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- A finite Gegenbauer expansion (normalized by `Gegenbauer24 k (1) = 1`). -/
@[expose] public def gegenbauerExpansion (N : ℕ) (a : ℕ → ℝ) : Polynomial ℝ :=
  (Finset.range (N + 1)).sum (fun k => (C (a k)) * Gegenbauer24 k)

/-- The PSD inequality for each Gegenbauer term, in the form used by `IsDelsarteDual24`. -/
lemma sum_sum_gegenbauer24_nonneg (k : ℕ) (C : Finset ℝ²⁴)
    (hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ)) :
    0 ≤ C.sum (fun u => C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ))) := by
  -- Immediate from `zonalKernel24_psd`.
  have hpsd : IsPSDKernel24 (zonalKernel24 k) := zonalKernel24_psd k
  simpa [IsPSDKernel24, zonalKernel24] using! hpsd C hC

/-- Expand the double sum of a Gegenbauer expansion term-by-term. -/
lemma sum_sum_eval_gegenbauerExpansion
    (N : ℕ) (a : ℕ → ℝ) (C : Finset ℝ²⁴) :
    C.sum (fun u => C.sum (fun v => (gegenbauerExpansion N a).eval (⟪u, v⟫ : ℝ))) =
      (Finset.range (N + 1)).sum (fun k =>
        (a k) * C.sum (fun u => C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := by
  let R : Finset ℕ := Finset.range (N + 1)
  have hEval (u v : ℝ²⁴) :
      (gegenbauerExpansion N a).eval (⟪u, v⟫ : ℝ) =
        R.sum (fun k => (a k) * (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)) := by
    -- Use the ring-hom viewpoint on evaluation to make `Finset.sum` rewriting robust.
    let t : ℝ := (⟪u, v⟫ : ℝ)
    change Polynomial.evalRingHom t (gegenbauerExpansion N a) =
        R.sum (fun k => (a k) * Polynomial.evalRingHom t (Gegenbauer24 k))
    -- Expand `gegenbauerExpansion` and push `evalRingHom` through sums/products.
    simp [gegenbauerExpansion, R, t]
  -- Expand the eval inside the double sum.
  have hExpand :
      C.sum (fun u => C.sum (fun v => (gegenbauerExpansion N a).eval (⟪u, v⟫ : ℝ))) =
        C.sum (fun u => C.sum (fun v => R.sum (fun k =>
          (a k) * (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    refine Finset.sum_congr rfl ?_
    intro v hv
    exact hEval u v
  -- Swap summations to pull `R` outside.
  -- `∑ u ∈ C, ∑ v ∈ C, ∑ k ∈ R, ... = ∑ k ∈ R, ∑ u ∈ C, ∑ v ∈ C, ...`.
  calc
    C.sum (fun u => C.sum (fun v => (gegenbauerExpansion N a).eval (⟪u, v⟫ : ℝ)))
        = C.sum (fun u => C.sum (fun v => R.sum (fun k =>
            (a k) * (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := hExpand
    _ = C.sum (fun u => R.sum (fun k => C.sum (fun v =>
            (a k) * (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := by
          refine Finset.sum_congr rfl ?_
          exact fun x a_1 => Finset.sum_comm
    _ = R.sum (fun k => C.sum (fun u => C.sum (fun v =>
            (a k) * (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := by
          -- swap the `u` and `k` sums
          exact Finset.sum_comm
    _ = R.sum (fun k => (a k) * C.sum (fun u => C.sum (fun v =>
            (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          -- Pull `a k` out of the double sum.
          simp [Finset.mul_sum]
    _ = (Finset.range (N + 1)).sum (fun k =>
          (a k) * C.sum (fun u => C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := by
          simp [R]

lemma sum_sum_gegenbauer24_zero (C : Finset ℝ²⁴) :
    C.sum (fun u => C.sum (fun v => (Gegenbauer24 0).eval (⟪u, v⟫ : ℝ))) =
      (C.card : ℝ) ^ 2 := by
  -- `Gegenbauer24 0 = 1`, so the summand is identically `1`.
  simp [Gegenbauer24_zero, pow_two]

/-- If `f` has a nonnegative Gegenbauer expansion, then it is a Delsarte dual certificate. -/
public lemma isDelsarteDual24_of_gegenbauerExpansion
    (N : ℕ) (a : ℕ → ℝ)
    (ha_nonneg : ∀ k ≤ N, 0 ≤ a k) :
    Uniqueness.BS81.IsDelsarteDual24 (gegenbauerExpansion N a) (a 0) := by
  intro C hC
  -- Expand the double sum term-by-term in the expansion.
  have hexpand :
      C.sum (fun u => C.sum (fun v => (gegenbauerExpansion N a).eval (⟪u, v⟫ : ℝ))) =
        (Finset.range (N + 1)).sum (fun k =>
          (a k) * C.sum (fun u => C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) :=
    sum_sum_eval_gegenbauerExpansion (N := N) (a := a) (C := C)
  -- Let `g k` be the `k`-th contribution.
  let g : ℕ → ℝ := fun k =>
    (a k) * C.sum (fun u => C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))
  have hmem0 : (0 : ℕ) ∈ Finset.range (N + 1) := by
    simp [Finset.mem_range]
  -- Split off the `k=0` term in the expanded sum.
  have hsplit :
      (Finset.range (N + 1)).sum g =
        g 0 + ((Finset.range (N + 1)).erase 0).sum g :=
    (Finset.add_sum_erase (s := Finset.range (N + 1)) (f := g) (a := 0) hmem0).symm
  have hrest_nonneg : 0 ≤ ((Finset.range (N + 1)).erase 0).sum g := by
    refine Finset.sum_nonneg ?_
    intro k hk
    have hk' : k ≠ 0 ∧ k ∈ Finset.range (N + 1) := by
      simpa [Finset.mem_erase] using! hk
    have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk'.2)
    have hak : 0 ≤ a k := ha_nonneg k hk_le
    have hSk :
        0 ≤ C.sum (fun u => C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ))) :=
      sum_sum_gegenbauer24_nonneg (k := k) (C := C) hC
    exact mul_nonneg hak hSk
  have hg0 :
      g 0 = (a 0) * (C.card : ℝ) ^ 2 := by
    simpa [g, mul_assoc] using! congrArg (fun r => (a 0) * r) (sum_sum_gegenbauer24_zero (C := C))
  have hmain :
      (a 0) * (C.card : ℝ) ^ 2 ≤ (Finset.range (N + 1)).sum g := by
    -- Rewrite `∑ g` by splitting off `g 0`, then use `g 0 ≤ g 0 + rest`.
    rw [hsplit, ← hg0]
    exact le_add_of_nonneg_right hrest_nonneg
  -- Transport back through the expansion identity.
  -- `hmain` is about `sum g`, and `hexpand` identifies `sum g` with the original double sum.
  exact le_of_le_of_eq hmain (id (Eq.symm hexpand))
end

end SpherePacking.Dim24.Uniqueness.BS81.LP
