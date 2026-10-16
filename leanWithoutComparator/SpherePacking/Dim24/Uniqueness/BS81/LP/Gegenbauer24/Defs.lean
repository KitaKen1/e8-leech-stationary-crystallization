-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Gegenbauer polynomials in dimension 24

We define the (unnormalized) Gegenbauer polynomials `gegenbauer lam n` by a three-term recurrence,
and then normalize them at `t = 1` to obtain the basis `Gegenbauer24 n` used for the Delsarte
linear programming method on the unit sphere in `ℝ²⁴` (i.e. `S^{23}`).

## Main definitions
* `gegenbauer`
* `gegenbauer24Param`
* `Gegenbauer24`
* `gegenbauerVal`, `Gegenbauer24Val`

## Main statements
* `Gegenbauer24_eval_one`
* `gegenbauer_eval_eq_gegenbauerVal`
* `Gegenbauer24_eval_eq`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP
noncomputable section

open Polynomial

/-- The (unnormalized) Gegenbauer polynomial `C_n^{(λ)}` as a polynomial over `ℝ`. -/
@[expose] public def gegenbauer (lam : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => (C (2 * lam)) * X
  | n + 2 =>
      let nR : ℝ := n
      let denom : ℝ := (n + 2 : ℝ)
      let a : ℝ := (2 * (nR + 1 + lam)) / denom
      let b : ℝ := (nR + 2 * lam) / denom
      (C a) * X * gegenbauer lam (n + 1) - (C b) * gegenbauer lam n

/-- Parameter `λ` for the unit sphere in `ℝ²⁴` (i.e. `S^{23}`): `λ = (24-2)/2 = 11`. -/
@[expose] public def gegenbauer24Param : ℝ := 11

/-- The normalized Gegenbauer polynomial basis used for `Ω₂₄`, normalized by `P_n(1) = 1`. -/
@[expose] public def Gegenbauer24 (n : ℕ) : Polynomial ℝ :=
  let lam : ℝ := gegenbauer24Param
  (C ((gegenbauer lam n).eval (1 : ℝ))⁻¹) * gegenbauer lam n

/-- The normalized basis starts at `Gegenbauer24 0 = 1`. -/
@[simp] public lemma Gegenbauer24_zero : Gegenbauer24 0 = (1 : Polynomial ℝ) := by
  simp [Gegenbauer24, gegenbauer]

/-- Recurrence for the unnormalized values `gegenbauer gegenbauer24Param n` at `t = 1`. -/
public lemma gegenbauer24_eval_one_succ (n : ℕ) :
    (gegenbauer gegenbauer24Param (n + 1)).eval (1 : ℝ) =
      ((2 * gegenbauer24Param + (n : ℝ)) / (n + 1 : ℝ)) *
        (gegenbauer gegenbauer24Param n).eval (1 : ℝ) := by
  let c : ℕ → ℝ := fun m => (gegenbauer gegenbauer24Param m).eval (1 : ℝ)
  have crec :
      ∀ m : ℕ,
        c (m + 2) =
          (2 * ((m : ℝ) + 1 + gegenbauer24Param) / ((m + 2 : ℕ) : ℝ)) * c (m + 1) -
            (((m : ℝ) + 2 * gegenbauer24Param) / ((m + 2 : ℕ) : ℝ)) * c m := by
    intro m
    simp [c, gegenbauer, mul_assoc, sub_eq_add_neg, add_assoc, div_eq_mul_inv]
  have hsucc :
      ∀ m : ℕ, c (m + 1) = ((2 * gegenbauer24Param + (m : ℝ)) / (m + 1 : ℝ)) * c m := by
    intro m
    induction m with
    | zero =>
        simp [c, gegenbauer, gegenbauer24Param, div_eq_mul_inv, mul_comm]
    | succ n ih =>
        have hbase := crec n
        have hsub :
            c (n + 2) =
              (2 * ((n : ℝ) + 1 + gegenbauer24Param) / ((n + 2 : ℕ) : ℝ)) *
                    (((2 * gegenbauer24Param + (n : ℝ)) / (n + 1 : ℝ)) * c n) -
                  (((n : ℝ) + 2 * gegenbauer24Param) / ((n + 2 : ℕ) : ℝ)) * c n := by
          simpa [ih] using! hbase
        have hfact :
            c (n + 2) =
              ((2 * ((n : ℝ) + 1 + gegenbauer24Param) / ((n + 2 : ℕ) : ℝ)) *
                    ((2 * gegenbauer24Param + (n : ℝ)) / (n + 1 : ℝ)) -
                  (((n : ℝ) + 2 * gegenbauer24Param) / ((n + 2 : ℕ) : ℝ))) * c n := by
          refine hsub.trans ?_
          ring_nf
        have hn1 : (n + 1 : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.succ_ne_zero n)
        grind only
  simpa [c] using! (hsucc n)

/-- Normalization: `Gegenbauer24 n` evaluates to `1` at `t = 1`. -/
@[simp] public lemma Gegenbauer24_eval_one (n : ℕ) : (Gegenbauer24 n).eval (1 : ℝ) = 1 := by
  -- Definitional: `(C ((p.eval 1)⁻¹) * p).eval 1 = (p.eval 1)⁻¹ * p.eval 1`,
  -- so it suffices to show `p.eval 1 ≠ 0`. We prove strict positivity of `p.eval 1`.
  let a : ℕ → ℝ := fun m => (gegenbauer gegenbauer24Param m).eval (1 : ℝ)
  have hsucc :
      ∀ m : ℕ, a (m + 1) = ((2 * gegenbauer24Param + (m : ℝ)) / (m + 1 : ℝ)) * a m := by
    intro m
    simpa [a] using! (gegenbauer24_eval_one_succ (n := m))
  have hpos : 0 < a n := by
    induction n with
    | zero =>
        simp [a, gegenbauer, gegenbauer24Param]
    | succ n ih =>
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have h22 : (0 : ℝ) < (2 * gegenbauer24Param) := by norm_num [gegenbauer24Param]
        have hnum : 0 < (2 * gegenbauer24Param + (n : ℝ)) := by linarith
        have hden : 0 < (n + 1 : ℝ) := by
          linarith
        have hcoef : 0 < ((2 * gegenbauer24Param + (n : ℝ)) / (n + 1 : ℝ)) := div_pos hnum hden
        simpa [hsucc n] using! mul_pos hcoef ih
  have hne : (gegenbauer gegenbauer24Param n).eval (1 : ℝ) ≠ 0 := by
    simpa [a] using! (ne_of_gt hpos)
  calc
    (Gegenbauer24 n).eval (1 : ℝ) =
        ((gegenbauer gegenbauer24Param n).eval (1 : ℝ))⁻¹ *
          (gegenbauer gegenbauer24Param n).eval (1 : ℝ) := by
          simp [Gegenbauer24, gegenbauer24Param, mul_comm]
    _ = 1 := by simpa using! (inv_mul_cancel₀ hne)

/-!
### Evaluation helpers

Value-level recursion for `gegenbauer` / `Gegenbauer24`, used to avoid unfolding large polynomials.
-/

/-- Value-level recursion for the (unnormalized) Gegenbauer polynomials `C_n^{(λ)}(x)`. -/
@[expose]
public def gegenbauerVal (lam : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun x => (2 * lam) * x
  | n + 2 =>
      fun x =>
        let nR : ℝ := n
        let denom : ℝ := (n + 2 : ℝ)
        let a : ℝ := (2 * (nR + 1 + lam)) / denom
        let b : ℝ := (nR + 2 * lam) / denom
        a * x * gegenbauerVal lam (n + 1) x - b * gegenbauerVal lam n x

/-- Evaluation of `gegenbauer lam n` agrees with the value-level recursion `gegenbauerVal`. -/
public lemma gegenbauer_eval_eq_gegenbauerVal (lam : ℝ) :
    ∀ n x, (gegenbauer lam n).eval x = gegenbauerVal lam n x
  | 0, x => by simp [gegenbauer, gegenbauerVal]
  | 1, x => by simp [gegenbauer, gegenbauerVal]
  | n + 2, x => by
      simp [gegenbauer, gegenbauerVal, gegenbauer_eval_eq_gegenbauerVal lam (n + 1) x,
        gegenbauer_eval_eq_gegenbauerVal lam n x, mul_assoc]

/-- Value-level version of the normalized basis `Gegenbauer24`, i.e. `P_n(x) = C_n(x)/C_n(1)`. -/
@[expose]
public def Gegenbauer24Val (n : ℕ) (x : ℝ) : ℝ :=
  let lam : ℝ := gegenbauer24Param
  (gegenbauerVal lam n (1 : ℝ))⁻¹ * gegenbauerVal lam n x

/-- Evaluation of `Gegenbauer24` agrees with the value-level normalization `Gegenbauer24Val`. -/
public lemma Gegenbauer24_eval_eq (n : ℕ) (x : ℝ) :
    (Gegenbauer24 n).eval x = Gegenbauer24Val n x := by
  simp [Gegenbauer24, Gegenbauer24Val, gegenbauer_eval_eq_gegenbauerVal]

end

end SpherePacking.Dim24.Uniqueness.BS81.LP
