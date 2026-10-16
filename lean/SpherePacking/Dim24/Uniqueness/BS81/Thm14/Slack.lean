-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Delsarte
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs
import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.DualCertificate
import Mathlib.Data.Set.Basic
public import SpherePacking.ForMathlib.CancelDenomsCompat

/-!
# Complementary slackness for the Delsarte LP bound

This file records the complementary-slackness consequences of sharpness in the Delsarte LP bound.
When the bound is sharp, every inequality in the LP proof is an equality, forcing:
* off-diagonal inner products lie in the root set of the dual polynomial, and
* each PSD Gegenbauer constraint with positive coefficient is tight.

These are the inputs used later to deduce the design property (via vanishing Gegenbauer sums) and
the explicit distance distribution (equation (11)).

## Main statement
* `isGegenbauerDesign24_of_sharp_expansion`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Polynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Root set
-/

private def rootSet (f : Polynomial ℝ) : Set ℝ :=
  {t : ℝ | f.eval t = 0}

private lemma mem_rootSet_iff (f : Polynomial ℝ) (t : ℝ) : t ∈ rootSet f ↔ f.eval t = 0 := Iff.rfl

attribute [grind =] mem_rootSet_iff

/-!
## Sharp bound forces roots on off-diagonal inner products
-/

private theorem offDiag_inner_in_rootSet_of_sharp
    (C : Set ℝ²⁴) (s : ℝ) (f : Polynomial ℝ) (a0 : ℝ)
    (hC : IsSphericalCode 24 C s)
    (ha0 : 0 < a0)
    (hneg : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) s → f.eval t ≤ 0)
    (hdual : Uniqueness.BS81.IsDelsarteDual24 f a0)
    (hsharp : (Set.ncard C : ℝ) = f.eval 1 / a0) :
    ∀ ⦃u v : ℝ²⁴⦄, u ∈ C → v ∈ C → u ≠ v → (⟪u, v⟫ : ℝ) ∈ rootSet f := by
  intro u v hu hv huv
  -- Use the algebraic equality-case lemma from the Delsarte framework.
  have hzero :
      f.eval (⟪u, v⟫ : ℝ) = 0 :=
    Uniqueness.BS81.sharp_bound_forces_inner_in_rootSet
      (C := C) (s := s) (f := f) (a0 := a0) hC ha0 hneg hdual hsharp hu hv huv
  simp [rootSet, hzero]

/-!
## Tightness of PSD constraints

Assume `f` has a Gegenbauer expansion `f = ∑_{k=0..N} a_k P_k` with `a_k ≥ 0`.
Then:
- the dual certificate is the sum of the per-`k` PSD certificates,
- sharpness forces the `k≥1` quadratic forms to vanish.

We use `Finset.sum_eq_zero_iff_of_nonneg` after splitting off the `k=0` term.
-/

/-!
## Tightness implies design (via Gegenbauer sums)
-/

/-- Sharpness of a Gegenbauer expansion forces the corresponding code to be a Gegenbauer design. -/
public theorem isGegenbauerDesign24_of_sharp_expansion
    (t : ℕ) (N : ℕ) (a : ℕ → ℝ) (f : Polynomial ℝ)
    (hExp :
      f =
        (Finset.range (N + 1)).sum (fun k =>
          (Polynomial.C (a k)) * (Uniqueness.BS81.LP.Gegenbauer24 k)))
    (ht_le : t ≤ N)
    (ha_pos : ∀ k : ℕ, 1 ≤ k → k ≤ t → 0 < a k)
    (Cfin : Finset ℝ²⁴)
    (hgegen_nonneg : ∀ k : ℕ, k ≤ N → 0 ≤ gegenbauerDoubleSum24 k Cfin)
    (ha_nonneg : ∀ k ≤ N, 0 ≤ a k)
    (hsharp :
      (a 0) * (Cfin.card : ℝ) ^ 2 =
        Cfin.sum (fun u => Cfin.sum (fun v => f.eval (⟪u, v⟫ : ℝ)))) :
    IsGegenbauerDesign24 t Cfin := by
  -- Paper/LP idea: expand `f` in the Gegenbauer basis. Equality forces the weighted sum of
  -- nonnegative Gegenbauer double sums (for degrees `1..t` with `a_k>0`) to vanish.
  have hExp' : f = Uniqueness.BS81.LP.gegenbauerExpansion N a := by
    simpa [Uniqueness.BS81.LP.gegenbauerExpansion] using! hExp
  have hsharp' :
      (a 0) * (Cfin.card : ℝ) ^ 2 =
        (Finset.range (N + 1)).sum (fun k => (a k) * gegenbauerDoubleSum24 k Cfin) := by
    have hsharp_exp :
        (a 0) * (Cfin.card : ℝ) ^ 2 =
          Cfin.sum (fun u => Cfin.sum (fun v =>
            (Uniqueness.BS81.LP.gegenbauerExpansion N a).eval (⟪u, v⟫ : ℝ))) := by
      simpa [hExp'] using! hsharp
    have hexpand :
        Cfin.sum (fun u => Cfin.sum (fun v =>
          (Uniqueness.BS81.LP.gegenbauerExpansion N a).eval (⟪u, v⟫ : ℝ))) =
          (Finset.range (N + 1)).sum (fun k => (a k) * gegenbauerDoubleSum24 k Cfin) := by
      let R : Finset ℕ := Finset.range (N + 1)
      have hEval (u v : ℝ²⁴) :
          (Uniqueness.BS81.LP.gegenbauerExpansion N a).eval (⟪u, v⟫ : ℝ) =
            R.sum (fun k => (a k) * (Uniqueness.BS81.LP.Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)) := by
        let t : ℝ := (⟪u, v⟫ : ℝ)
        change Polynomial.evalRingHom t (Uniqueness.BS81.LP.gegenbauerExpansion N a) =
          R.sum (fun k => (a k) * Polynomial.evalRingHom t (Uniqueness.BS81.LP.Gegenbauer24 k))
        simp [Uniqueness.BS81.LP.gegenbauerExpansion, R, t]
      have hExpand :
          Cfin.sum (fun u => Cfin.sum (fun v =>
            (Uniqueness.BS81.LP.gegenbauerExpansion N a).eval (⟪u, v⟫ : ℝ))) =
            Cfin.sum (fun u => Cfin.sum (fun v =>
              R.sum (fun k => (a k) * (Uniqueness.BS81.LP.Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := by
        refine Finset.sum_congr rfl ?_
        intro u hu
        refine Finset.sum_congr rfl ?_
        intro v hv
        exact hEval u v
      calc
        Cfin.sum (fun u => Cfin.sum (fun v =>
            (Uniqueness.BS81.LP.gegenbauerExpansion N a).eval (⟪u, v⟫ : ℝ))) =
            Cfin.sum (fun u => Cfin.sum (fun v =>
              R.sum (fun k =>
                (a k) * (Uniqueness.BS81.LP.Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := hExpand
        _ = Cfin.sum (fun u => R.sum (fun k => Cfin.sum (fun v =>
              (a k) * (Uniqueness.BS81.LP.Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := by
            refine Finset.sum_congr rfl ?_
            exact fun x a_1 => Finset.sum_comm
        _ = R.sum (fun k => Cfin.sum (fun u => Cfin.sum (fun v =>
              (a k) * (Uniqueness.BS81.LP.Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))) := by
            exact Finset.sum_comm
        _ = R.sum (fun k => (a k) * gegenbauerDoubleSum24 k Cfin) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [gegenbauerDoubleSum24, Finset.mul_sum]
        _ = (Finset.range (N + 1)).sum (fun k => (a k) * gegenbauerDoubleSum24 k Cfin) := by
            simp [R]
    exact hsharp_exp.trans hexpand
  have hG0 : gegenbauerDoubleSum24 0 Cfin = (Cfin.card : ℝ) ^ 2 := by
    simp [gegenbauerDoubleSum24, pow_two, mul_comm]
  -- Isolate the `k=0` term from the RHS sum.
  let s : Finset ℕ := Finset.range (N + 1)
  let g : ℕ → ℝ := fun k => (a k) * gegenbauerDoubleSum24 k Cfin
  have hs0 : (0 : ℕ) ∈ s := by
    -- `0 < N+1`.
    exact Finset.mem_range.mpr (Nat.succ_pos _)
  have hsum_erase0 : (s.erase 0).sum g = 0 := by
    have hs_eq : s.sum g = g 0 := by
      exact Eq.symm (CancelDenoms.derive_trans hG0 hsharp')
    have hsplit : g 0 + (s.erase 0).sum g = s.sum g :=
      Finset.add_sum_erase (s := s) (f := g) (a := (0 : ℕ)) hs0
    have hcancel : g 0 + (s.erase 0).sum g = g 0 := by
      simpa [hs_eq] using! hsplit
    exact left_eq_add.mp (id (Eq.symm hcancel))
  -- Each term in the erased sum is nonnegative, hence must be `0`.
  have hterm_zero :
      ∀ k ∈ s.erase 0, g k = 0 := by
    have hnonneg :
        ∀ k ∈ s.erase 0, 0 ≤ g k := by
      intro k hk
      have hk' : k ≤ N := by
        -- `k ∈ range (N+1)` implies `k ≤ N`.
        have hk_range : k < N + 1 := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
        exact Nat.le_of_lt_succ hk_range
      exact mul_nonneg (ha_nonneg k hk') (hgegen_nonneg k hk')
    have hall :
        ∀ k ∈ s.erase 0, g k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum_erase0
    exact hall
  -- Conclude `gegenbauerDoubleSum24 k Cfin = 0` for all `1 ≤ k ≤ t`.
  intro k hk1 hkt
  have hkN : k ≤ N := le_trans hkt ht_le
  have hk_mem : k ∈ s.erase 0 := by
    refine Finset.mem_erase.2 ?_
    refine ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk1), ?_⟩
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hkN)
  have hgk : g k = 0 := hterm_zero k hk_mem
  have hak : 0 < a k := ha_pos k hk1 hkt
  -- From `a k * DS = 0` and `a k ≠ 0`, deduce `DS = 0`.
  have : gegenbauerDoubleSum24 k Cfin = 0 := by
    have hak0 : a k ≠ 0 := ne_of_gt hak
    -- `mul_eq_zero` gives `a k = 0 ∨ DS = 0`.
    exact (mul_eq_zero_iff_left hak0).mp (hterm_zero k hk_mem)
  exact this

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
