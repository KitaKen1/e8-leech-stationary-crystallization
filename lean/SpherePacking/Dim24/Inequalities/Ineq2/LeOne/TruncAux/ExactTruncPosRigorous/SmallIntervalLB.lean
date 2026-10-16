-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTruncPosRigorous.SmallDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum


/-!
# Interval lower bounds for polynomial evaluation

Given a coefficient list `l : List ℚ` and an interval `a ≤ x ≤ b` with `0 ≤ a` and `|x| ≤ b`, this
file defines computable lower bounds `intervalLB l a b K` and `intervalLBWeak l a b K` for the real
evaluation of `polyOfCoeffs l` at `x`. The bounds split the polynomial into a head of length `K`
and a tail controlled by a norm estimate on `l.drop K`.

These interval bounds are used to certify that the small-`t` polynomial `polySmall` is positive on
`x ∈ [1 / 30, 1 / 23]` in the proof of Appendix A, Lemma `ineq2`.

## Main definitions
* `intervalLB`, `intervalLBWeak`

## Main statements
* `eval₂_polyOfCoeffs_ge_intervalLB`
* `intervalLBWeak_le_intervalLB`

-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open CoeffModel

namespace ExactTruncPosRigorous

/-- Sum of absolute values of a list of rationals. -/
@[expose] public def absSumQ : List ℚ → ℚ
  | [] => 0
  | a :: l => |a| + absSumQ l

lemma absBoundQ_nonneg (l : List ℚ) (b : ℚ) (hb0 : 0 ≤ b) : 0 ≤ absBoundQ l b := by
  induction l with
  | nil =>
      simp [absBoundQ]
  | cons a l ih =>
      have ih' : 0 ≤ absBoundQ l b := ih
      have habs : 0 ≤ |a| := abs_nonneg a
      have hmul : 0 ≤ b * absBoundQ l b := mul_nonneg hb0 ih'
      simpa [absBoundQ, add_assoc] using! add_nonneg habs hmul

lemma absBoundQ_le_absSumQ (l : List ℚ) (b : ℚ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    absBoundQ l b ≤ absSumQ l := by
  induction l with
  | nil =>
      simp [absBoundQ, absSumQ]
  | cons a l ih =>
      have hnonneg : 0 ≤ absBoundQ l b := absBoundQ_nonneg (l := l) (b := b) hb0
      calc
        absBoundQ (a :: l) b = |a| + b * absBoundQ l b := by simp [absBoundQ]
        _ ≤ |a| + absBoundQ l b := by
              have hmul : b * absBoundQ l b ≤ 1 * absBoundQ l b :=
                mul_le_mul_of_nonneg_right hb1 hnonneg
              simpa [one_mul, add_assoc, add_left_comm, add_comm] using! add_le_add_left hmul |a|
        _ ≤ |a| + absSumQ l :=
              add_le_add_right ih |a|
        _ = absSumQ (a :: l) := by simp [absSumQ]

/-- Wrapper for `x ^ n` used in the interval bound definitions. -/
@[expose] public def powQ (x : ℚ) (n : ℕ) : ℚ := x ^ n

/-- A lower bound for the head sum `∑_{n < K} c_n x^n` on an interval `a ≤ x ≤ b`, obtained by
using `a^n` for nonnegative coefficients and `b^n` for negative coefficients. -/
@[expose] public def headLB (l : List ℚ) (a b : ℚ) (K : ℕ) : ℚ :=
  (Finset.range K).sum (fun n =>
    let c := l.getD n 0
    if 0 ≤ c then c * powQ a n else c * powQ b n)

/-- Primitive-recursive version of `headLB`, used to keep kernel reduction small. -/
@[expose] public def headLBRec (l : List ℚ) (a b : ℚ) : ℕ → ℚ
  | 0 => 0
  | K + 1 =>
      headLBRec l a b K +
        let c := l.getD K 0
        if 0 ≤ c then c * powQ a K else c * powQ b K

lemma headLBRec_eq_headLB (l : List ℚ) (a b : ℚ) (K : ℕ) :
    headLBRec l a b K = headLB l a b K := by
  induction K with
  | zero =>
      simp [headLBRec, headLB]
  | succ K ih =>
      simp [headLBRec, headLB, Finset.sum_range_succ, ih]

/-- Interval lower bound for `polyOfCoeffs l`:
head bound `headLB l a b K` minus a certified tail bound using `absBoundQ`. -/
@[expose] public def intervalLB (l : List ℚ) (a b : ℚ) (K : ℕ) : ℚ :=
  headLB l a b K - (powQ b K) * absBoundQ (l.drop K) b

/-- Weaker interval lower bound for `polyOfCoeffs l`, replacing `absBoundQ` by the simpler
`absSumQ` on the tail. -/
@[expose] public def intervalLBWeak (l : List ℚ) (a b : ℚ) (K : ℕ) : ℚ :=
  headLB l a b K - (powQ b K) * absSumQ (l.drop K)

/-- Definition of `intervalLBWeak` using the recursive head bound `headLBRec`. -/
@[expose] public def intervalLBWeakRec (l : List ℚ) (a b : ℚ) (K : ℕ) : ℚ :=
  headLBRec l a b K - (powQ b K) * absSumQ (l.drop K)

/-- The recursive definition `intervalLBWeakRec` agrees with `intervalLBWeak`. -/
public lemma intervalLBWeakRec_eq_intervalLBWeak (l : List ℚ) (a b : ℚ) (K : ℕ) :
    intervalLBWeakRec l a b K = intervalLBWeak l a b K := by
  simp [intervalLBWeakRec, intervalLBWeak, headLBRec_eq_headLB]

/-- On `0 ≤ b ≤ 1`, the weak bound `intervalLBWeak` is below the stronger bound `intervalLB`. -/
public lemma intervalLBWeak_le_intervalLB (l : List ℚ) (a b : ℚ) (K : ℕ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    intervalLBWeak l a b K ≤ intervalLB l a b K := by
  dsimp [intervalLBWeak, intervalLB]
  have hle : absBoundQ (l.drop K) b ≤ absSumQ (l.drop K) :=
    absBoundQ_le_absSumQ (l := l.drop K) (b := b) hb0 hb1
  have hbK0 : 0 ≤ powQ b K := by
    -- `powQ b K` is a nonnegative power when `0 ≤ b`.
    simpa [powQ] using! (pow_nonneg hb0 K)
  -- Multiply the tail bound by `b^K` and subtract.
  have hmul : (powQ b K) * absBoundQ (l.drop K) b ≤ (powQ b K) * absSumQ (l.drop K) :=
    mul_le_mul_of_nonneg_left hle hbK0
  linarith

macro "simp_intervalLBWeak_goal" : tactic =>
  `(tactic|
    (simp [intervalLBWeakRec, headLBRec, powQ, absSumQ, coeffsSmall] <;> try norm_num))

/-! ## Evaluation lower bound -/

/-- If `a ≤ x ≤ b` and `0 ≤ x`, then the real evaluation of `polyOfCoeffs l` at `x` is bounded
below by `intervalLB l a b K`. -/
public lemma eval₂_polyOfCoeffs_ge_intervalLB (l : List ℚ) (a b : ℚ) (K : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (ha0 : 0 ≤ (a : ℝ)) (hb0 : 0 ≤ (b : ℝ)) (hKlen : K ≤ l.length)
    (hxa : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) :
    (AppendixA.polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x ≥ (intervalLB l a b K : ℝ) := by
  have hxabs : |x| ≤ (b : ℝ) := by simpa [abs_of_nonneg hx0] using! hxb
  -- Expand `eval₂` as a finite sum.
  have heval :
      (AppendixA.polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x =
        ∑ n ∈ Finset.range l.length, (algebraMap ℚ ℝ) (l.getD n 0) * x ^ n :=
    AppendixA.eval₂_polyOfCoeffs_eq_sum_range_getD (l := l) (x := x)
  -- Split the sum at `K`.
  have hsplit :
      (∑ n ∈ Finset.range l.length, (algebraMap ℚ ℝ) (l.getD n 0) * x ^ n) =
        (∑ n ∈ Finset.range K, (algebraMap ℚ ℝ) (l.getD n 0) * x ^ n) +
          ∑ n ∈ Finset.range (l.length - K), (algebraMap ℚ ℝ) (l.getD (K + n) 0) * x ^ (K + n) := by
    have hK : K + (l.length - K) = l.length := Nat.add_sub_of_le hKlen
    have :=
      Finset.sum_range_add
        (f := fun n => (algebraMap ℚ ℝ) (l.getD n 0) * x ^ n)
        K
        (l.length - K)
    simpa [hK, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using! this
  -- Head lower bound: `headLB ≤ headSum`.
  have hhead_le :
      (headLB l a b K : ℝ) ≤ ∑ n ∈ Finset.range K, (algebraMap ℚ ℝ) (l.getD n 0) * x ^ n := by
    let bound : ℕ → ℝ := fun n =>
      let cQ : ℚ := l[n]?.getD 0
      ((if 0 ≤ cQ then cQ * a ^ n else cQ * b ^ n) : ℚ)
    have hbound :
        (headLB l a b K : ℝ) = ∑ n ∈ Finset.range K, bound n := by
      -- Push the cast inside the finite sum and simplify `powQ`.
      simp [headLB, bound, powQ, List.getD]
      rfl
    rw [hbound]
    refine Finset.sum_le_sum ?_
    intro n hn
    dsimp [bound]
    set cQ : ℚ := l[n]?.getD 0 with hcQ
    by_cases hc : 0 ≤ cQ
    · have hxpow : (a : ℝ) ^ n ≤ x ^ n := pow_le_pow_left₀ ha0 hxa n
      have hcR : 0 ≤ (cQ : ℝ) := by exact_mod_cast hc
      have hmul : (a : ℝ) ^ n * (cQ : ℝ) ≤ x ^ n * (cQ : ℝ) :=
        mul_le_mul_of_nonneg_right hxpow hcR
      have hcoefQ : l.getD n 0 = cQ := by
        rfl
      have hcoefR : (algebraMap ℚ ℝ) (l.getD n 0) = (cQ : ℝ) := by
        simpa using! congrArg (algebraMap ℚ ℝ) hcoefQ
      -- Rewrite the RHS coefficient to `cQ`, simplify the `if` using `hc`, then use `hmul`.
      rw [hcoefR]
      have hmul' : (a : ℝ) ^ n * (cQ : ℝ) ≤ (cQ : ℝ) * x ^ n := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! hmul
      simpa [hc, mul_assoc, mul_left_comm, mul_comm] using! hmul'
    · have hc' : cQ < 0 := lt_of_not_ge hc
      have hxpow : x ^ n ≤ (b : ℝ) ^ n := pow_le_pow_left₀ hx0 hxb n
      have hcR : (cQ : ℝ) ≤ 0 := by exact_mod_cast hc'.le
      have hmul : (b : ℝ) ^ n * (cQ : ℝ) ≤ x ^ n * (cQ : ℝ) :=
        -- `x^n ≤ b^n` and `cQ ≤ 0`.
        mul_le_mul_of_nonpos_right hxpow hcR
      have hcoefQ : l.getD n 0 = cQ := by
        rfl
      have hcoefR : (algebraMap ℚ ℝ) (l.getD n 0) = (cQ : ℝ) := by
        simpa using! congrArg (algebraMap ℚ ℝ) hcoefQ
      -- Rewrite the RHS coefficient to `cQ`, simplify the `if` using `hc`, then use `hmul`.
      rw [hcoefR]
      have hmul' : (b : ℝ) ^ n * (cQ : ℝ) ≤ (cQ : ℝ) * x ^ n := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! hmul
      simpa [hc, mul_assoc, mul_left_comm, mul_comm] using! hmul'
  have hhead_ge :
      (∑ n ∈ Finset.range K, (algebraMap ℚ ℝ) (l.getD n 0) * x ^ n) ≥ (headLB l a b K : ℝ) := by
    simpa [ge_iff_le] using! hhead_le
  -- Tail bound: `|tail| ≤ b^K * absBound (drop K l) b`.
  have htail_abs :
      |∑ n ∈ Finset.range (l.length - K), (algebraMap ℚ ℝ) (l.getD (K + n) 0) * x ^ (K + n)| ≤
        (b : ℝ) ^ K * AppendixA.absBound (l.drop K) (b : ℝ) := by
    have hxKle : x ^ K ≤ (b : ℝ) ^ K := pow_le_pow_left₀ hx0 hxb K
    -- Rewrite the tail sum as `x^K * eval₂ (drop K l) x`.
    have htail_eq :
        (∑ n ∈ Finset.range (l.length - K), (algebraMap ℚ ℝ) (l.getD (K + n) 0) * x ^ (K + n)) =
          x ^ K * (AppendixA.polyOfCoeffs (l.drop K)).eval₂ (algebraMap ℚ ℝ) x := by
      have hdrop :
          (AppendixA.polyOfCoeffs (l.drop K)).eval₂ (algebraMap ℚ ℝ) x =
            ∑ n ∈ Finset.range (l.drop K).length, (algebraMap ℚ ℝ) ((l.drop K).getD n 0) * x ^ n :=
        AppendixA.eval₂_polyOfCoeffs_eq_sum_range_getD (l := l.drop K) (x := x)
      have hlen : (l.drop K).length = l.length - K := by
        simp [List.length_drop]
      -- Replace `getD` on `drop`.
      have hgetD : ∀ n : ℕ, n < l.length - K → (l.drop K).getD n 0 = l.getD (K + n) 0 := by
        norm_num
      -- Expand.
      rw [hdrop]
      -- Rewrite the index range.
      simp only [List.getD_eq_getElem?_getD, eq_ratCast, List.length_drop, List.getElem?_drop]
      -- Pull out `x^K`.
      have :
          x ^ K *
              (∑ n ∈ Finset.range (l.length - K),
                (algebraMap ℚ ℝ) (l.getD (K + n) 0) * x ^ n) =
            ∑ n ∈ Finset.range (l.length - K),
              (algebraMap ℚ ℝ) (l.getD (K + n) 0) * x ^ (K + n) := by
        set term : ℕ → ℝ := fun n => (algebraMap ℚ ℝ) (l.getD (K + n) 0) * x ^ n
        calc
          x ^ K * (∑ n ∈ Finset.range (l.length - K), term n) =
              ∑ n ∈ Finset.range (l.length - K), x ^ K * term n :=
                Finset.mul_sum (Finset.range (l.length - K)) term (x ^ K)
          _ = ∑ n ∈ Finset.range (l.length - K),
                (algebraMap ℚ ℝ) (l.getD (K + n) 0) * x ^ (K + n) := by
                refine Finset.sum_congr rfl ?_
                intro n hn
                simp [term, pow_add, mul_assoc, mul_comm]
      -- Conclude.
      simpa [this, hgetD] using! this.symm
    have htail_bound :
        |(AppendixA.polyOfCoeffs (l.drop K)).eval₂ (algebraMap ℚ ℝ) x| ≤
          AppendixA.absBound (l.drop K) (b : ℝ) :=
      AppendixA.abs_eval₂_polyOfCoeffs_le_absBound (l := l.drop K) (x := x) (c := (b : ℝ)) hb0 hxabs
    have habs :
        |x ^ K * (AppendixA.polyOfCoeffs (l.drop K)).eval₂ (algebraMap ℚ ℝ) x| ≤
          (b : ℝ) ^ K * AppendixA.absBound (l.drop K) (b : ℝ) := by
      -- Use `|ab| = |a|*|b|` and bound each factor separately.
      have hxKabs : |x ^ K| ≤ (b : ℝ) ^ K := by
        have hxK0 : 0 ≤ x ^ K := pow_nonneg hx0 _
        simpa [abs_of_nonneg hxK0] using! hxKle
      have hmul :
          |x ^ K| * |(AppendixA.polyOfCoeffs (l.drop K)).eval₂ (algebraMap ℚ ℝ) x| ≤
            (b : ℝ) ^ K * AppendixA.absBound (l.drop K) (b : ℝ) :=
        mul_le_mul hxKabs htail_bound (abs_nonneg _) (pow_nonneg hb0 _)
      -- Turn this into an inequality about `|x^K * eval|` without rewriting `|x^K|`.
      rw [abs_mul]
      exact hmul
    -- Rewrite the tail sum as `x^K * eval₂ (drop K l) x`.
    -- Avoid `simp` here to prevent rewriting `|x^K|` to `|x|^K`.
    rw [htail_eq]
    exact habs
  have htail_ge :
      (∑ n ∈ Finset.range (l.length - K), (algebraMap ℚ ℝ) (l.getD (K + n) 0) * x ^ (K + n)) ≥
        -((b : ℝ) ^ K * AppendixA.absBound (l.drop K) (b : ℝ)) := by
    -- `|S| ≤ M` implies `-M ≤ S`.
    exact (neg_le_of_abs_le htail_abs)
  have hmain :
      (AppendixA.polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x ≥
        (headLB l a b K : ℝ) - (b : ℝ) ^ K * AppendixA.absBound (l.drop K) (b : ℝ) := by
    rw [heval, hsplit]
    nlinarith [hhead_ge, htail_ge]
  have hcast :
      (headLB l a b K : ℝ) - (b : ℝ) ^ K * AppendixA.absBound (l.drop K) (b : ℝ) =
        (intervalLB l a b K : ℝ) := by
    have habs : AppendixA.absBound (l.drop K) (b : ℝ) = (absBoundQ (l.drop K) b : ℝ) :=
      absBoundQ_cast (l := l.drop K) b
    simp [intervalLB, habs, headLB, powQ, sub_eq_add_neg]
  simpa [hcast] using! hmain

end SpherePacking.Dim24.Ineq2LeOneTruncAux.ExactTruncPosRigorous
