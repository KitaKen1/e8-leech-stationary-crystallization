-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

/-!
# Odd-degree vanishing for antipodal sets

For any antipodal finite set `C` on the unit sphere and any *odd* `k`,
`gegenbauerDoubleSum24 k C = 0`.

This is used to upgrade vanishing for `k=1..10` into vanishing for `k=1..11` (since `11` is odd).
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.BuildSteps
open Finset

/-- Antipodality predicate for finsets: closed under negation. -/
@[expose] public def IsAntipodalFinset {α : Type*} [Neg α] (C : Finset α) : Prop :=
  ∀ u ∈ C, -u ∈ C

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.BuildSteps


namespace SpherePacking.Dim24

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace Uniqueness.BS81.LP
noncomputable section

open Polynomial

lemma gegenbauerVal_neg (lam : ℝ) :
    ∀ n x, gegenbauerVal lam n (-x) = ((-1 : ℝ) ^ n) * gegenbauerVal lam n x
  | 0, x => by
      simp [gegenbauerVal]
  | 1, x => by
      simp [gegenbauerVal]
  | n + 2, x => by
      simp [gegenbauerVal, gegenbauerVal_neg lam n x, gegenbauerVal_neg lam (n + 1) x,
        pow_succ, sub_eq_add_neg, div_eq_mul_inv]
      ring

lemma Gegenbauer24Val_neg (n : ℕ) (x : ℝ) :
    Gegenbauer24Val n (-x) = ((-1 : ℝ) ^ n) * Gegenbauer24Val n x := by
  -- Normalization divides by the constant `C_n(1)`, so parity is unchanged.
  simp [Gegenbauer24Val, gegenbauerVal_neg, mul_assoc, mul_comm]

/-- Parity of `Gegenbauer24`: evaluation at `-x` picks up the factor `(-1)^n`. -/
public lemma Gegenbauer24_eval_neg (n : ℕ) (x : ℝ) :
    (Gegenbauer24 n).eval (-x) = ((-1 : ℝ) ^ n) * (Gegenbauer24 n).eval x := by
  simp [Gegenbauer24_eval_eq, Gegenbauer24Val_neg]

lemma Gegenbauer24_eval_neg_11 (x : ℝ) :
    (Gegenbauer24 11).eval (-x) = - (Gegenbauer24 11).eval x := by
  have hodd : Odd (11 : ℕ) := by decide
  simpa [hodd.neg_one_pow] using! (Gegenbauer24_eval_neg (n := 11) (x := x))

end

end Uniqueness.BS81.LP

namespace Uniqueness.BS81.Thm14.BuildSteps.Design11

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Finset
open Uniqueness.BS81.Thm14

open Uniqueness.BS81.LP

lemma gegenbauer24_eval_neg_of_odd (k : ℕ) (hk : Odd k) (x : ℝ) :
    (Gegenbauer24 k).eval (-x) = - (Gegenbauer24 k).eval x := by
  simp [Gegenbauer24_eval_neg, hk.neg_one_pow]

lemma gegenbauer24_eval_inner_neg_right_of_odd (k : ℕ) (hk : Odd k) (u v : ℝ²⁴) :
    (Gegenbauer24 k).eval (⟪u, -v⟫ : ℝ) = - (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ) := by
  simpa [inner_neg_right] using!
    (gegenbauer24_eval_neg_of_odd (k := k) hk (x := (⟪u, v⟫ : ℝ)))

lemma sum_gegenbauer24_eval_inner_eq_zero_of_antipodal_of_odd
    (k : ℕ) (hk : Odd k) (C : Finset ℝ²⁴) (hanti : IsAntipodalFinset C) (u : ℝ²⁴) :
    C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)) = 0 := by
  have hpair (v : ℝ²⁴) :
      (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ) + (Gegenbauer24 k).eval (⟪u, -v⟫ : ℝ) = 0 := by
    rw [gegenbauer24_eval_inner_neg_right_of_odd (k := k) hk (u := u) (v := v)]
    simp
  -- Pair terms in the sum over `v ∈ C` using the involution `v ↦ -v`.
  simpa using!
    (Finset.sum_involution (s := C)
      (f := fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ))
      (g := fun v _hv => -v)
      (hg₁ := fun v _hv => by
        simpa using! hpair v)
      (hg₃ := fun v _hv hv0 => by
        -- If `-v = v`, then the cancellation identity forces the term to be zero.
        intro hvfix
        apply hv0
        exact add_self_eq_zero.mp (by simpa [hvfix] using! hpair v))
      (g_mem := fun v hv => hanti v hv)
      (hg₄ := fun v _hv => by simp))

/-- If `C` is antipodal and `k` is odd, then `gegenbauerDoubleSum24 k C = 0`. -/
public theorem gegenbauerDoubleSum24_eq_zero_of_antipodal_of_odd
    (k : ℕ) (hk : Odd k) (C : Finset ℝ²⁴) (hanti : IsAntipodalFinset C) :
    gegenbauerDoubleSum24 k C = 0 := by
  simp [gegenbauerDoubleSum24,
    sum_gegenbauer24_eval_inner_eq_zero_of_antipodal_of_odd (k := k) hk (C := C) hanti]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.BuildSteps.Design11
