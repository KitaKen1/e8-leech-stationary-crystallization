-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The BS81 polynomial `f24` for the `(24, 1/2)` LP bound

This file defines the polynomial `f24` used in BS81 Theorem 13 and records basic evaluations and
the sign condition `f24.eval t ≤ 0` for `t ∈ [-1, 1/2]`.

## Main definitions
* `f24`

## Main statements
* `f24_eval`
* `f24_eval_one`
* `f24_eval_nonpos_of_mem_Icc`

## References
* `paper/BS81/sources.tex`, §4, Theorem 13
-/


namespace SpherePacking.Dim24.Uniqueness.BS81
noncomputable section

open Polynomial

/-- The BS81 polynomial used for the `(24, 1/2)` LP bound. -/
@[expose] public def f24 : Polynomial ℝ :=
  (X + C 1) *
    (X + C (1 / 2 : ℝ)) ^ 2 *
      (X + C (1 / 4 : ℝ)) ^ 2 *
        X ^ 2 *
          (X - C (1 / 4 : ℝ)) ^ 2 *
            (X - C (1 / 2 : ℝ))

/-- Expanded evaluation formula for `f24`. -/
@[simp] public lemma f24_eval (t : ℝ) :
    f24.eval t =
      (t + 1) *
        (t + (1 / 2 : ℝ)) ^ 2 *
          (t + (1 / 4 : ℝ)) ^ 2 *
            t ^ 2 *
              (t - (1 / 4 : ℝ)) ^ 2 *
                (t - (1 / 2 : ℝ)) := by
  simp [f24, mul_assoc, mul_left_comm, mul_comm]

/-- Evaluate the BS81 polynomial at `t = 1`. -/
public lemma f24_eval_one : f24.eval (1 : ℝ) = (2025 / 1024 : ℝ) := by
  -- `2 * (3/2)^2 * (5/4)^2 * 1^2 * (3/4)^2 * (1/2) = 2025/1024`.
  simp [f24_eval]
  norm_num

/-- The BS81 polynomial satisfies `f24.eval t ≤ 0` for all `t ∈ [-1, 1/2]`. -/
public lemma f24_eval_nonpos_of_mem_Icc (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) (1 / 2 : ℝ)) :
    f24.eval t ≤ 0 := by
  have ht1 : 0 ≤ t + 1 := by nlinarith [ht.1]
  have htHalf : t - (1 / 2 : ℝ) ≤ 0 := by nlinarith [ht.2]
  -- All factors except the last are nonnegative, and the last is nonpositive on `[-1,1/2]`.
  have h2 : 0 ≤ (t + (1 / 2 : ℝ)) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (t + (1 / 4 : ℝ)) ^ 2 := sq_nonneg _
  have h4 : 0 ≤ t ^ 2 := sq_nonneg _
  have h5 : 0 ≤ (t - (1 / 4 : ℝ)) ^ 2 := sq_nonneg _
  have h12 : 0 ≤ (t + 1) * (t + (1 / 2 : ℝ)) ^ 2 := mul_nonneg ht1 h2
  have h123 : 0 ≤ (t + 1) * (t + (1 / 2 : ℝ)) ^ 2 * (t + (1 / 4 : ℝ)) ^ 2 := by
    simpa [mul_assoc] using! mul_nonneg h12 h3
  have h1234 :
      0 ≤ (t + 1) * (t + (1 / 2 : ℝ)) ^ 2 * (t + (1 / 4 : ℝ)) ^ 2 * t ^ 2 := by
    simpa [mul_assoc] using! mul_nonneg h123 h4
  have hnonneg :
      0 ≤
        (t + 1) *
          (t + (1 / 2 : ℝ)) ^ 2 *
            (t + (1 / 4 : ℝ)) ^ 2 *
              t ^ 2 *
                (t - (1 / 4 : ℝ)) ^ 2 := by
    simpa [mul_assoc] using! mul_nonneg h1234 h5
  -- Multiply a nonnegative number by a nonpositive number.
  simpa [f24_eval, mul_assoc] using! (mul_nonpos_of_nonneg_of_nonpos hnonneg htHalf)

end

end SpherePacking.Dim24.Uniqueness.BS81
