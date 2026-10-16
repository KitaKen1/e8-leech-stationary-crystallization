-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Normalized three-term recurrence for `Gegenbauer24`

This file proves the three-term recurrence for the normalized basis `Gegenbauer24`.
In evaluation form (for `n ≥ 0`) it reads:

`t * P_{n+1}(t) = α_n * P_{n+2}(t) + β_n * P_n(t)`,

with `α_n = (n+23)/(2n+24)` and `β_n = (n+1)/(2n+24)`.

## Main statements
* `Gegenbauer24_eval_recurrence_succ`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.LP
noncomputable section

open Polynomial

private def c (n : ℕ) : ℝ :=
  (gegenbauer gegenbauer24Param n).eval (1 : ℝ)

private lemma c_succ :
    ∀ n : ℕ, c (n + 1) = ((2 * gegenbauer24Param + (n : ℝ)) / (n + 1 : ℝ)) * c n := by
  intro n
  simpa [c] using! (gegenbauer24_eval_one_succ (n := n))

private lemma c_ne_zero (n : ℕ) : c n ≠ 0 := by
  intro h0
  have hc0 : (gegenbauer gegenbauer24Param n).eval (1 : ℝ) = 0 := by
    simpa [c] using! h0
  have hc0' : (gegenbauer (11 : ℝ) n).eval (1 : ℝ) = 0 := by
    simpa [gegenbauer24Param] using! hc0
  have hzero : (Gegenbauer24 n).eval (1 : ℝ) = 0 := by
    simp [Gegenbauer24, gegenbauer24Param, hc0']
  have hone : (Gegenbauer24 n).eval (1 : ℝ) = 1 := Gegenbauer24_eval_one n
  have h1 : (1 : ℝ) = 0 := hone.symm.trans hzero
  exact one_ne_zero h1

private lemma gegenbauer_eval_eq_c_mul_Gegenbauer24_eval (n : ℕ) (t : ℝ) :
    (gegenbauer gegenbauer24Param n).eval t = c n * (Gegenbauer24 n).eval t := by
  have hc : c n ≠ 0 := c_ne_zero (n := n)
  -- `Gegenbauer24 n = (C (c n)⁻¹) * gegenbauer gegenbauer24Param n`.
  have h :
      (Gegenbauer24 n).eval t = (c n)⁻¹ * (gegenbauer gegenbauer24Param n).eval t := by
    simp [Gegenbauer24, c, gegenbauer24Param]
  -- Rearrange.
  exact (inv_mul_eq_iff_eq_mul₀ hc).mp (id (Eq.symm h))

private lemma c_ratio_succ (n : ℕ) :
    c (n + 1) / c n = (2 * gegenbauer24Param + (n : ℝ)) / (n + 1 : ℝ) := by
  have hc : c n ≠ 0 := c_ne_zero (n := n)
  simp [div_eq_mul_inv, c_succ (n := n), hc, mul_assoc, mul_comm]

private lemma c_ratio_pred (n : ℕ) :
    c n / c (n + 1) = (n + 1 : ℝ) / (2 * gegenbauer24Param + (n : ℝ)) := by
  have hc : c n ≠ 0 := c_ne_zero (n := n)
  have hsucc := c_succ (n := n)
  -- `c (n+1) = ((2*gegenbauer24Param + n)/(n+1)) * c n`, so divide both sides by `c n`.
  -- Then invert.
  -- We keep the algebra in `ℝ`.
  calc
    c n / c (n + 1)
        = c n / (((2 * gegenbauer24Param + (n : ℝ)) / (n + 1 : ℝ)) * c n) := by
            simp [hsucc]
    _ = (n + 1 : ℝ) / (2 * gegenbauer24Param + (n : ℝ)) := by
            field_simp [hc]

/-- Normalized three-term recurrence for `Gegenbauer24` (evaluation form). -/
public lemma Gegenbauer24_eval_recurrence_succ (n : ℕ) (t : ℝ) :
    t * (Gegenbauer24 (n + 1)).eval t =
      ((n + 23 : ℝ) / (2 * n + 24 : ℝ)) * (Gegenbauer24 (n + 2)).eval t +
        ((n + 1 : ℝ) / (2 * n + 24 : ℝ)) * (Gegenbauer24 n).eval t := by
  -- Shorthands for the unnormalized Gegenbauer evaluations.
  set C0 : ℝ := (gegenbauer gegenbauer24Param n).eval t
  set C1 : ℝ := (gegenbauer gegenbauer24Param (n + 1)).eval t
  set C2 : ℝ := (gegenbauer gegenbauer24Param (n + 2)).eval t
  -- Coefficients in the recurrence.
  let a : ℝ := (2 * ((n : ℝ) + 1 + gegenbauer24Param) / ((n + 2 : ℕ) : ℝ))
  let b : ℝ := (((n : ℝ) + 2 * gegenbauer24Param) / ((n + 2 : ℕ) : ℝ))
  -- The defining recurrence for `gegenbauer` at index `n+2`, evaluated at `t`.
  have hrec : C2 = a * (t * C1) - b * C0 := by
    -- Unfold only the `n+2` clause of `gegenbauer` and evaluate at `t`.
    -- Leave recursive calls untouched.
    simp [C0, C1, C2, a, b, gegenbauer, gegenbauer24Param, div_eq_mul_inv, sub_eq_add_neg,
      mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm]
  have ha : a ≠ 0 := by
    have hn2 : 0 < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (n + 1)
    have hnum : 0 < 2 * ((n : ℝ) + 1 + gegenbauer24Param) := by
      have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      have : 0 < ((n : ℝ) + 1 + gegenbauer24Param) := by
        norm_num [gegenbauer24Param] at *
        linarith
      nlinarith
    exact ne_of_gt (div_pos hnum hn2)
  have htC1 : t * C1 = a⁻¹ * C2 + a⁻¹ * b * C0 := by
    -- From `hrec`: `C2 + b*C0 = a*(t*C1)`.
    grind only
  -- Convert `C0,C1,C2` to normalized evaluations.
  have hc0 : C0 = c n * (Gegenbauer24 n).eval t := by
    simpa [C0] using! (gegenbauer_eval_eq_c_mul_Gegenbauer24_eval (n := n) (t := t))
  have hc1 : C1 = c (n + 1) * (Gegenbauer24 (n + 1)).eval t := by
    simpa [C1] using! (gegenbauer_eval_eq_c_mul_Gegenbauer24_eval (n := n + 1) (t := t))
  have hc2 : C2 = c (n + 2) * (Gegenbauer24 (n + 2)).eval t := by
    simpa [C2] using! (gegenbauer_eval_eq_c_mul_Gegenbauer24_eval (n := n + 2) (t := t))
  have hcn1 : c (n + 1) ≠ 0 := c_ne_zero (n := n + 1)
  -- Start from `t * Gegenbauer24 (n+1).eval t = (c(n+1))⁻¹ * (t*C1)`.
  have hL :
      t * (Gegenbauer24 (n + 1)).eval t = (c (n + 1))⁻¹ * (t * C1) := by
    simp [hc1, hcn1, mul_assoc, mul_comm]
  -- Rewrite `t*C1` using `htC1`, then substitute `hc0`/`hc2`, and compute the coefficients.
  have hcoef1 :
      (c (n + 1))⁻¹ * (a⁻¹ * c (n + 2)) = ((n + 23 : ℝ) / (2 * n + 24 : ℝ)) := by
    have hn2 : (n + 2 : ℝ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (n + 1)
    have hratio :
        c (n + 2) / c (n + 1) =
          (2 * gegenbauer24Param + ((n + 1 : ℕ) : ℝ)) / (n + 2 : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, one_add_one_eq_two]
        using! (c_ratio_succ (n := n + 1))
    -- Rewrite as `a⁻¹ * (c(n+2)/c(n+1))` and compute.
    calc
      (c (n + 1))⁻¹ * (a⁻¹ * c (n + 2))
          = a⁻¹ * (c (n + 2) / c (n + 1)) := by
              simp [div_eq_mul_inv, mul_left_comm, mul_comm]
      _ =
          a⁻¹ * ((2 * gegenbauer24Param + ((n + 1 : ℕ) : ℝ)) / (n + 2 : ℝ)) := by
            simp [hratio]
      _ = ((n + 23 : ℝ) / (2 * n + 24 : ℝ)) := by
            -- Pure arithmetic in `ℝ`.
            have hn12 : (↑n + 12 : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.succ_ne_zero (n + 11))
            have h2hn12 : (2 * (↑n + 12 : ℝ)) ≠ 0 :=
              mul_ne_zero (by norm_num) hn12
            -- Unfold `a`, then clear denominators.
            simp [a, gegenbauer24Param, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
            field_simp [hn2, h2hn12]
            ring_nf
  have hcoef0 :
      (c (n + 1))⁻¹ * (a⁻¹ * b * c n) = ((n + 1 : ℝ) / (2 * n + 24 : ℝ)) := by
    have hn2 : (n + 2 : ℝ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (n + 1)
    have hratio :
        c n / c (n + 1) =
          (n + 1 : ℝ) / (2 * gegenbauer24Param + (n : ℝ)) := c_ratio_pred (n := n)
    have hn22 : (2 * gegenbauer24Param + (n : ℝ)) ≠ 0 := by
      have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      have : 0 < 2 * gegenbauer24Param + (n : ℝ) := by
        norm_num [gegenbauer24Param] at *
        linarith
      exact ne_of_gt this
    calc
      (c (n + 1))⁻¹ * (a⁻¹ * b * c n)
          = a⁻¹ * b * (c n / c (n + 1)) := by
              simp [div_eq_mul_inv, mul_assoc, mul_comm]
      _ =
          a⁻¹ * b * ((n + 1 : ℝ) / (2 * gegenbauer24Param + (n : ℝ))) := by
            simp [hratio]
      _ = ((n + 1 : ℝ) / (2 * n + 24 : ℝ)) := by
            have hn12 : (↑n + 12 : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.succ_ne_zero (n + 11))
            have h2hn12 : (2 * (↑n + 12 : ℝ)) ≠ 0 :=
              mul_ne_zero (by norm_num) hn12
            simp [a, b, gegenbauer24Param, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
            -- `field_simp` may leave side-goals about nonzero denominators.
            field_simp [hn2, hn22, h2hn12]
            left
            ring_nf
  -- Finish.
  calc
    t * (Gegenbauer24 (n + 1)).eval t
        = (c (n + 1))⁻¹ * (t * C1) := hL
    _ = (c (n + 1))⁻¹ * (a⁻¹ * C2 + a⁻¹ * b * C0) := by
          simp [htC1]
    _ = ((n + 23 : ℝ) / (2 * n + 24 : ℝ)) * (Gegenbauer24 (n + 2)).eval t +
          ((n + 1 : ℝ) / (2 * n + 24 : ℝ)) * (Gegenbauer24 n).eval t := by
          -- Substitute `C2` and `C0` and expand the LHS into the two contributions.
          have hrewrite :
              (c (n + 1))⁻¹ * (a⁻¹ * C2 + a⁻¹ * b * C0) =
                ((c (n + 1))⁻¹ * (a⁻¹ * c (n + 2))) * (Gegenbauer24 (n + 2)).eval t +
                  ((c (n + 1))⁻¹ * (a⁻¹ * b * c n)) * (Gegenbauer24 n).eval t := by
            -- Use `hc2` and `hc0` to replace `C2` and `C0`, then distribute and reassociate.
            simp [hc2, hc0, mul_add, mul_assoc, mul_left_comm, mul_comm]
          rw [hrewrite]
          have hterm2 :
              ((c (n + 1))⁻¹ * (a⁻¹ * c (n + 2))) * (Gegenbauer24 (n + 2)).eval t =
                ((n + 23 : ℝ) / (2 * n + 24 : ℝ)) * (Gegenbauer24 (n + 2)).eval t := by
            simpa [mul_assoc] using!
              congrArg (fun r => r * (Gegenbauer24 (n + 2)).eval t) hcoef1
          have hterm0 :
              ((c (n + 1))⁻¹ * (a⁻¹ * b * c n)) * (Gegenbauer24 n).eval t =
                ((n + 1 : ℝ) / (2 * n + 24 : ℝ)) * (Gegenbauer24 n).eval t := by
            simpa [mul_assoc] using! congrArg (fun r => r * (Gegenbauer24 n).eval t) hcoef0
          have hterm0' :
              (c (n + 1))⁻¹ * (a⁻¹ * (b * (c n * (Gegenbauer24 n).eval t))) =
                ((n + 1 : ℝ) / (2 * n + 24 : ℝ)) * (Gegenbauer24 n).eval t := by
            simpa [mul_assoc] using! hterm0
          simp [mul_assoc, hterm2, hterm0', add_comm]

end

end SpherePacking.Dim24.Uniqueness.BS81.LP
