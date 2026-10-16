/- Identifying the series head with the exact truncation sum. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.EvenReindex
public import
  SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PiBoundsAndTruncCompare
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.SeriesSplit
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import Mathlib.Data.Complex.BigOperators


/-!
# Identify the series head with `Bleading_exact_trunc`

In the `BleadingNum` expansion, we split each `q`/`r`-series into a finite head plus a tail.
The head term `headS` is built from the explicit coefficient lists in `BleadingCoeffs`.

This file shows that the finite head agrees with the analytic truncation expression
`Bleading_exact_trunc`.

## Main definitions
* `aA`, `aB`, `aC`, `aΔ`, `aψ`
* `headS`

## Main statements
* `headS_eq_exact_trunc`
-/


open scoped BigOperators
open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA


/-- Coefficients `aA n` for the `varphi` numerator head, from the list `phinumQ`. -/
@[expose] public def aA : ℕ → ℚ := fun n => BleadingCoeffs.coeffQ BleadingCoeffs.phinumQ n

/-- Coefficients `aB n` for the `phi1` numerator head, from the list `phi1CoreQ`. -/
@[expose] public def aB : ℕ → ℚ := fun n => BleadingCoeffs.coeffQ BleadingCoeffs.phi1CoreQ n

/-- Coefficients `aC n` for the `phi2` numerator head, from the list `phi2CoreQ`. -/
@[expose] public def aC : ℕ → ℚ := fun n => BleadingCoeffs.coeffQ BleadingCoeffs.phi2CoreQ n

/-- Coefficients `aΔ n` for the `Δ^2` head, from the list `DeltaSqQ`. -/
@[expose] public def aΔ : ℕ → ℚ := fun n => BleadingCoeffs.coeffQ BleadingCoeffs.DeltaSqQ n

/-- Coefficients `aψ n` for the `psiI` numerator `r`-series head, from `psiInumCoeffs`. -/
@[expose] public def aψ : ℕ → ℤ := fun n => BleadingCoeffs.psiInumCoeffs.getD n 0

private lemma qterm_it_eq_rC_pow (t : ℝ) (ht0 : 0 < t) (n : ℕ) :
    qterm (it t ht0) n = (rC t) ^ (2 * n) := by
  have hqr : (q t : ℂ) = (rC t) ^ (2 : ℕ) := by
    simpa [rC] using! congrArg (fun x : ℝ => (x : ℂ)) (q_eq_r_sq (t := t))
  simpa [hqr, pow_mul] using! (qterm_it (t := t) (ht := ht0) (n := n))

private lemma qhead_it_eq_sum_rC_even (t : ℝ) (ht0 : 0 < t) (a : ℕ → ℂ) (N : ℕ) :
    qhead a (it t ht0) N = ∑ n ∈ Finset.range N, a n * (rC t) ^ (2 * n) := by
  simp [qhead, qterm_it_eq_rC_pow]

private lemma qhead_to_even_guard_sum (t : ℝ) (ht0 : 0 < t) (a : ℕ → ℂ) :
    qhead a (it t ht0) BleadingCoeffs.QN =
      ∑ i ∈ Finset.range BleadingCoeffs.N,
        (if i % 2 = 0 then a (i / 2) * (rC t) ^ i else 0) := by
  have hsum :
      (∑ i ∈ Finset.range BleadingCoeffs.N, (if i % 2 = 0 then a (i / 2) * (rC t) ^ i else 0)) =
        ∑ n ∈ Finset.range BleadingCoeffs.QN, a n * (rC t) ^ (2 * n) := by
    simpa [BleadingCoeffs.N, BleadingCoeffs.QN, Nat.mul_comm] using!
      (sum_range_even_ite (N := BleadingCoeffs.QN) (c := a) (x := rC t))
  exact (qhead_it_eq_sum_rC_even (t := t) (ht0 := ht0) (a := a) (N := BleadingCoeffs.QN)).trans
    hsum.symm

private lemma rhead_eq_sum (t : ℝ) (a : ℕ → ℤ) (N : ℕ) :
    rhead a t N = ∑ n ∈ Finset.range N, (a n : ℂ) * (rC t) ^ n := by
  simp [rhead]

/--
The finite head term in the `BleadingNum` expansion at `z = it t`.

This is the sum of the `qhead`/`rhead` pieces that match the explicit truncation polynomial
`Bleading_exact_trunc`.
-/
@[expose] public def headS (t : ℝ) (ht0 : 0 < t) : ℂ :=
  let z : ℍ := it t ht0
  ((Real.pi : ℂ) / (28304640 : ℂ)) *
      ((t : ℂ) ^ (2 : ℕ) * qhead (fun n : ℕ => (aA n : ℂ)) z BleadingCoeffs.QN +
        (t : ℂ) *
            (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
              qhead (fun n : ℕ => (aB n : ℂ)) z BleadingCoeffs.QN) -
          ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
            qhead (fun n : ℕ => (aC n : ℂ)) z BleadingCoeffs.QN)) +
    (1 / ((65520 : ℂ) * Real.pi)) * rhead aψ t BleadingCoeffs.N +
      (-(1 / 39 : ℂ) * (t : ℂ) + (10 / (117 : ℂ)) * (1 / (Real.pi : ℂ))) *
        qhead (fun n : ℕ => (aΔ (n + 1) : ℂ)) z BleadingCoeffs.QN

/-- The finite head term `headS` agrees with the explicit truncation `Bleading_exact_trunc`. -/
public lemma headS_eq_exact_trunc (t : ℝ) (ht0 : 0 < t) :
    headS t ht0 = (Bleading_exact_trunc t : ℂ) := by
  -- Put `headS` and `Bleading_exact_trunc` into the same normal form over `x = r(t)`.
  set x : ℂ := rC t
  have hx :
      (Bleading_exact_trunc t : ℂ) =
        ∑ i ∈ Finset.range BleadingCoeffs.N, (Bleading_exact_coeff t i : ℂ) * x ^ i := by
    -- `Bleading_exact_trunc` is a real finite sum; push the coercion through the sum.
    dsimp [Bleading_exact_trunc]
    simp [x, rC]
  -- Rewrite each `qhead`/`rhead` into the corresponding guarded/un-guarded sum.
  let sA : ℂ :=
    ∑ i ∈ Finset.range BleadingCoeffs.N, if i % 2 = 0 then (aA (i / 2) : ℂ) * x ^ i else 0
  let sB : ℂ :=
    ∑ i ∈ Finset.range BleadingCoeffs.N, if i % 2 = 0 then (aB (i / 2) : ℂ) * x ^ i else 0
  let sC : ℂ :=
    ∑ i ∈ Finset.range BleadingCoeffs.N, if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0
  let sΔ : ℂ :=
    ∑ i ∈ Finset.range BleadingCoeffs.N, if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0
  let sψ : ℂ := ∑ i ∈ Finset.range BleadingCoeffs.N, (aψ i : ℂ) * x ^ i
  have hqA' : qhead (fun n : ℕ => (aA n : ℂ)) (it t ht0) BleadingCoeffs.QN = sA := by
    simpa [sA, x] using!
      qhead_to_even_guard_sum (t := t) (ht0 := ht0) (a := fun n : ℕ => (aA n : ℂ))
  have hqB' : qhead (fun n : ℕ => (aB n : ℂ)) (it t ht0) BleadingCoeffs.QN = sB := by
    simpa [sB, x] using!
      qhead_to_even_guard_sum (t := t) (ht0 := ht0) (a := fun n : ℕ => (aB n : ℂ))
  have hqC' : qhead (fun n : ℕ => (aC n : ℂ)) (it t ht0) BleadingCoeffs.QN = sC := by
    simpa [sC, x] using!
      qhead_to_even_guard_sum (t := t) (ht0 := ht0) (a := fun n : ℕ => (aC n : ℂ))
  have hqΔ' : qhead (fun n : ℕ => (aΔ (n + 1) : ℂ)) (it t ht0) BleadingCoeffs.QN = sΔ := by
    simpa [sΔ, x, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using!
      qhead_to_even_guard_sum (t := t) (ht0 := ht0) (a := fun n : ℕ => (aΔ (n + 1) : ℂ))
  have hrψ' : rhead aψ t BleadingCoeffs.N = sψ := by
    simpa [sψ, x] using! (rhead_eq_sum (t := t) (a := aψ) (N := BleadingCoeffs.N))
  -- Define the common normal form (in terms of the guarded sums).
  -- This form is chosen to match the `A/B/C` decomposition of `Bleading_exact_coeff`.
  let E : ℂ :=
    (Real.pi : ℂ) * (t : ℂ) ^ (2 : ℕ) * ((BleadingCoeffs.piDiv : ℂ) * sA) +
      (t : ℂ) * ((BleadingCoeffs.phi1Scale : ℂ) * sB + (BleadingCoeffs.leadTScale : ℂ) * sΔ) +
        (1 / (Real.pi : ℂ)) *
          ((BleadingCoeffs.phi2Scale : ℂ) * sC +
            (BleadingCoeffs.leadInvPiScale : ℂ) * sΔ +
              (BleadingCoeffs.invPiDiv : ℂ) * sψ)
  have hL : headS t ht0 = E := by
    -- Unfold and rewrite the head sums.
    dsimp [headS]
    rw [hqA', hqB', hqC', hqΔ', hrψ']
    dsimp [E]
    simp [BleadingCoeffs.piDiv, BleadingCoeffs.invPiDiv, BleadingCoeffs.phi1Scale,
      BleadingCoeffs.phi2Scale, BleadingCoeffs.leadTScale, BleadingCoeffs.leadInvPiScale,
      div_eq_mul_inv, sub_eq_add_neg, mul_add, add_mul, mul_assoc, add_assoc]
    ring_nf
    have hπ : (Real.pi : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hπ]
    ring
  have hR : (Bleading_exact_trunc t : ℂ) = E := by
    -- Start from the definition.
    rw [hx]
    -- Split the sum using the `A/B/C` decomposition, then rewrite each coefficient sum as guarded.
    have hsum_decomp :
        (∑ i ∈ Finset.range BleadingCoeffs.N, (Bleading_exact_coeff t i : ℂ) * x ^ i) =
          (Real.pi : ℂ) * (t : ℂ) ^ (2 : ℕ) *
              (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Acoeff i : ℂ) * x ^ i) +
            (t : ℂ) *
              (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bcoeff i : ℂ) * x ^ i) +
            (1 / (Real.pi : ℂ)) *
              (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Ccoeff i : ℂ) * x ^ i) := by
      -- Expand the summand, split the sum into the `A/B/C` parts,
      -- then factor out the common scalars.
      have hsplit :
          (∑ i ∈ Finset.range BleadingCoeffs.N, (Bleading_exact_coeff t i : ℂ) * x ^ i) =
            (∑ i ∈ Finset.range BleadingCoeffs.N,
                ((BleadingCoeffs.Acoeff i : ℂ) * (Real.pi : ℂ) * (t : ℂ) ^ (2 : ℕ)) * x ^ i) +
              (∑ i ∈ Finset.range BleadingCoeffs.N,
                  ((BleadingCoeffs.Bcoeff i : ℂ) * (t : ℂ)) * x ^ i) +
                (∑ i ∈ Finset.range BleadingCoeffs.N,
                    ((BleadingCoeffs.Ccoeff i : ℂ) * (1 / (Real.pi : ℂ))) * x ^ i) := by
        -- Termwise expansion of `Bleading_exact_coeff`, then linearity of `Finset.sum`.
        simp [Bleading_exact_coeff, mul_add, add_assoc, div_eq_mul_inv, mul_left_comm, mul_comm,
          Finset.sum_add_distrib]
      -- Factor `π * t^2`.
      have hA :
          (∑ i ∈ Finset.range BleadingCoeffs.N,
                ((BleadingCoeffs.Acoeff i : ℂ) * (Real.pi : ℂ) * (t : ℂ) ^ (2 : ℕ)) * x ^ i) =
            (Real.pi : ℂ) * (t : ℂ) ^ (2 : ℕ) *
              (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Acoeff i : ℂ) * x ^ i) := by
        have hcongr :
            (∑ i ∈ Finset.range BleadingCoeffs.N,
                  ((BleadingCoeffs.Acoeff i : ℂ) * (Real.pi : ℂ) * (t : ℂ) ^ (2 : ℕ)) * x ^ i) =
              ∑ i ∈ Finset.range BleadingCoeffs.N,
                ((Real.pi : ℂ) * (t : ℂ) ^ (2 : ℕ)) * ((BleadingCoeffs.Acoeff i : ℂ) * x ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [mul_assoc, mul_left_comm, mul_comm]
        rw [hcongr]
        simpa [mul_assoc] using!
          (Finset.mul_sum (a := (Real.pi : ℂ) * (t : ℂ) ^ (2 : ℕ))
            (s := Finset.range BleadingCoeffs.N)
            (f := fun i : ℕ => (BleadingCoeffs.Acoeff i : ℂ) * x ^ i)).symm
      -- Factor `t`.
      have hB :
          (∑ i ∈ Finset.range BleadingCoeffs.N,
                ((BleadingCoeffs.Bcoeff i : ℂ) * (t : ℂ)) * x ^ i) =
            (t : ℂ) *
              (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bcoeff i : ℂ) * x ^ i) := by
        have hcongr :
            (∑ i ∈ Finset.range BleadingCoeffs.N,
                  ((BleadingCoeffs.Bcoeff i : ℂ) * (t : ℂ)) * x ^ i) =
              ∑ i ∈ Finset.range BleadingCoeffs.N,
                (t : ℂ) * ((BleadingCoeffs.Bcoeff i : ℂ) * x ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [mul_left_comm, mul_comm]
        rw [hcongr]
        simpa [mul_assoc] using!
          (Finset.mul_sum (a := (t : ℂ)) (s := Finset.range BleadingCoeffs.N)
            (f := fun i : ℕ => (BleadingCoeffs.Bcoeff i : ℂ) * x ^ i)).symm
      -- Factor `1/π`.
      have hC :
          (∑ i ∈ Finset.range BleadingCoeffs.N,
                ((BleadingCoeffs.Ccoeff i : ℂ) * (1 / (Real.pi : ℂ))) * x ^ i) =
            (1 / (Real.pi : ℂ)) *
              (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Ccoeff i : ℂ) * x ^ i) := by
        have hcongr :
            (∑ i ∈ Finset.range BleadingCoeffs.N,
                  ((BleadingCoeffs.Ccoeff i : ℂ) * (1 / (Real.pi : ℂ))) * x ^ i) =
              ∑ i ∈ Finset.range BleadingCoeffs.N,
                (1 / (Real.pi : ℂ)) * ((BleadingCoeffs.Ccoeff i : ℂ) * x ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [mul_left_comm, mul_comm]
        rw [hcongr]
        simpa [mul_assoc] using!
          (Finset.mul_sum (a := (1 / (Real.pi : ℂ))) (s := Finset.range BleadingCoeffs.N)
            (f := fun i : ℕ => (BleadingCoeffs.Ccoeff i : ℂ) * x ^ i)).symm
      -- Assemble.
      calc
        (∑ i ∈ Finset.range BleadingCoeffs.N, (Bleading_exact_coeff t i : ℂ) * x ^ i)
            =
            (∑ i ∈ Finset.range BleadingCoeffs.N,
                ((BleadingCoeffs.Acoeff i : ℂ) * (Real.pi : ℂ) * (t : ℂ) ^ (2 : ℕ)) * x ^ i) +
              (∑ i ∈ Finset.range BleadingCoeffs.N,
                  ((BleadingCoeffs.Bcoeff i : ℂ) * (t : ℂ)) * x ^ i) +
                (∑ i ∈ Finset.range BleadingCoeffs.N,
                    ((BleadingCoeffs.Ccoeff i : ℂ) * (1 / (Real.pi : ℂ))) * x ^ i) := hsplit
        _ =
            (Real.pi : ℂ) * (t : ℂ) ^ (2 : ℕ) *
                (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Acoeff i : ℂ) * x ^ i) +
              (t : ℂ) *
                (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bcoeff i : ℂ) * x ^ i) +
                (1 / (Real.pi : ℂ)) *
                  (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Ccoeff i : ℂ) * x ^ i) := by
              rw [hA, hB, hC]
    -- Now compute each coefficient sum in terms of `sA/sB/sC/sΔ/sψ`.
    have hsumA :
        (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Acoeff i : ℂ) * x ^ i) =
          (BleadingCoeffs.piDiv : ℂ) * sA := by
      -- Expand the RHS and compare summands.
      have :
          (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Acoeff i : ℂ) * x ^ i) =
            ∑ i ∈ Finset.range BleadingCoeffs.N,
              (BleadingCoeffs.piDiv : ℂ) * (if i % 2 = 0 then (aA (i / 2) : ℂ) * x ^ i else 0) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases h : i % 2 = 0
        · have hisEven : BleadingCoeffs.isEven i = true := by
            simp [BleadingCoeffs.isEven, h]
          -- Unfold `Acoeff` without rewriting `coeffQ` into tables.
          rw [BleadingCoeffs.Acoeff, hisEven, BleadingCoeffs.qIdx]
          -- Reduce the guard on the RHS.
          rw [if_pos h]
          dsimp [aA]
          -- Reassociate and push the `ℚ`-cast through multiplication.
          simp only [Rat.cast_mul, mul_assoc]
        · have hisEven : BleadingCoeffs.isEven i = false := by
            simp [BleadingCoeffs.isEven, h]
          rw [BleadingCoeffs.Acoeff, hisEven]
          rw [if_neg h]
          simp
      -- Pull out the scalar `piDiv`.
      calc
        (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Acoeff i : ℂ) * x ^ i)
            = ∑ i ∈ Finset.range BleadingCoeffs.N,
                (BleadingCoeffs.piDiv : ℂ) *
                  (if i % 2 = 0 then (aA (i / 2) : ℂ) * x ^ i else 0) := this
        _ = (BleadingCoeffs.piDiv : ℂ) *
              ∑ i ∈ Finset.range BleadingCoeffs.N,
                (if i % 2 = 0 then (aA (i / 2) : ℂ) * x ^ i else 0) :=
              (Finset.mul_sum (a := (BleadingCoeffs.piDiv : ℂ))
                  (s := Finset.range BleadingCoeffs.N)
                  (f := fun i : ℕ => if i % 2 = 0 then (aA (i / 2) : ℂ) * x ^ i else 0)).symm
        _ = (BleadingCoeffs.piDiv : ℂ) * sA := by simp [sA]
    have hsumB :
        (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bcoeff i : ℂ) * x ^ i) =
          (BleadingCoeffs.phi1Scale : ℂ) * sB + (BleadingCoeffs.leadTScale : ℂ) * sΔ := by
      -- Expand `Bcoeff` and split the sum.
      have :
          (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bcoeff i : ℂ) * x ^ i) =
            ∑ i ∈ Finset.range BleadingCoeffs.N,
              ((BleadingCoeffs.phi1Scale : ℂ) *
                    (if i % 2 = 0 then (aB (i / 2) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.leadTScale : ℂ) *
                    (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases h : i % 2 = 0
        · have hisEven : BleadingCoeffs.isEven i = true := by
            simp [BleadingCoeffs.isEven, h]
          -- Unfold `Bcoeff` without rewriting `coeffQ` into tables.
          rw [BleadingCoeffs.Bcoeff, hisEven, BleadingCoeffs.qIdx, BleadingCoeffs.deltaIdx]
          -- Reduce the guards on the RHS only (avoid rewriting `coeffQ` on the LHS).
          have hrhs :
              ((BleadingCoeffs.phi1Scale : ℂ) *
                    (if i % 2 = 0 then (aB (i / 2) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.leadTScale : ℂ) *
                    (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0)) =
                (BleadingCoeffs.phi1Scale : ℂ) * ((aB (i / 2) : ℂ) * x ^ i) +
                  (BleadingCoeffs.leadTScale : ℂ) * ((aΔ (i / 2 + 1) : ℂ) * x ^ i) := by
            simp [h]
          rw [hrhs]
          dsimp [aB, aΔ]
          -- Distribute `* x^i` over the sum and reassociate.
          simp only [Rat.cast_add, Rat.cast_mul, add_mul, mul_assoc]
        · have hisEven : BleadingCoeffs.isEven i = false := by
            simp [BleadingCoeffs.isEven, h]
          rw [BleadingCoeffs.Bcoeff, hisEven]
          -- Reduce the guards on the RHS only.
          have hrhs :
              ((BleadingCoeffs.phi1Scale : ℂ) *
                    (if i % 2 = 0 then (aB (i / 2) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.leadTScale : ℂ) *
                    (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0)) = 0 := by
            simp [h]
          rw [hrhs]
          simp
      calc
        (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bcoeff i : ℂ) * x ^ i) =
            ∑ i ∈ Finset.range BleadingCoeffs.N,
              ((BleadingCoeffs.phi1Scale : ℂ) *
                    (if i % 2 = 0 then (aB (i / 2) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.leadTScale : ℂ) *
                    (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0)) := this
        _ =
            (∑ i ∈ Finset.range BleadingCoeffs.N,
                (BleadingCoeffs.phi1Scale : ℂ) *
                  (if i % 2 = 0 then (aB (i / 2) : ℂ) * x ^ i else 0)) +
              ∑ i ∈ Finset.range BleadingCoeffs.N,
                (BleadingCoeffs.leadTScale : ℂ) *
                  (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0) := by
            simp [Finset.sum_add_distrib]
        _ =
            (BleadingCoeffs.phi1Scale : ℂ) * sB + (BleadingCoeffs.leadTScale : ℂ) * sΔ := by
            simp [sB, sΔ, Finset.mul_sum]
    have hsumC :
        (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Ccoeff i : ℂ) * x ^ i) =
          (BleadingCoeffs.phi2Scale : ℂ) * sC +
            (BleadingCoeffs.leadInvPiScale : ℂ) * sΔ +
            (BleadingCoeffs.invPiDiv : ℂ) * sψ := by
      have hterm :
          (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Ccoeff i : ℂ) * x ^ i) =
            ∑ i ∈ Finset.range BleadingCoeffs.N,
              ((BleadingCoeffs.phi2Scale : ℂ) *
                    (if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.leadInvPiScale : ℂ) *
                    (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.invPiDiv : ℂ) * ((aψ i : ℂ) * x ^ i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases h : i % 2 = 0
        · have hisEven : BleadingCoeffs.isEven i = true := by
            simp [BleadingCoeffs.isEven, h]
          -- Unfold `Ccoeff` without rewriting `coeffQ` into tables.
          rw [BleadingCoeffs.Ccoeff, hisEven, BleadingCoeffs.qIdx, BleadingCoeffs.deltaIdx]
          -- Reduce the guards on the RHS only (avoid rewriting `coeffQ` on the LHS).
          have hrhs :
              ((BleadingCoeffs.phi2Scale : ℂ) *
                    (if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.leadInvPiScale : ℂ) *
                    (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.invPiDiv : ℂ) * ((aψ i : ℂ) * x ^ i)) =
                (BleadingCoeffs.phi2Scale : ℂ) * ((aC (i / 2) : ℂ) * x ^ i) +
                  (BleadingCoeffs.leadInvPiScale : ℂ) * ((aΔ (i / 2 + 1) : ℂ) * x ^ i) +
                  (BleadingCoeffs.invPiDiv : ℂ) * ((aψ i : ℂ) * x ^ i) := by
            simp [h]
          rw [hrhs]
          dsimp [aC, aΔ, aψ]
          -- Distribute `* x^i` over sums and reassociate; reconcile `ℤ → ℚ → ℂ` casts.
          simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_intCast, add_mul, mul_assoc]
        · have hisEven : BleadingCoeffs.isEven i = false := by
            simp [BleadingCoeffs.isEven, h]
          rw [BleadingCoeffs.Ccoeff, hisEven]
          -- Reduce the guards on the RHS only (avoid rewriting `coeffQ` on the LHS).
          have hrhs :
              ((BleadingCoeffs.phi2Scale : ℂ) *
                    (if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.leadInvPiScale : ℂ) *
                    (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.invPiDiv : ℂ) * ((aψ i : ℂ) * x ^ i)) =
                (BleadingCoeffs.invPiDiv : ℂ) * ((aψ i : ℂ) * x ^ i) := by
            simp [h]
          rw [hrhs]
          dsimp [aψ]
          -- Only the `ψ`-term remains; reconcile casts and reassociate.
          simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_intCast, add_mul, mul_assoc]
          simp
      have hsplit :
          (∑ i ∈ Finset.range BleadingCoeffs.N,
                ((BleadingCoeffs.phi2Scale : ℂ) *
                    (if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.leadInvPiScale : ℂ) *
                    (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0) +
                  (BleadingCoeffs.invPiDiv : ℂ) * ((aψ i : ℂ) * x ^ i))) =
          (∑ i ∈ Finset.range BleadingCoeffs.N,
              (BleadingCoeffs.phi2Scale : ℂ) *
                (if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0)) +
              (∑ i ∈ Finset.range BleadingCoeffs.N,
                  (BleadingCoeffs.leadInvPiScale : ℂ) *
                    (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0)) +
                (∑ i ∈ Finset.range BleadingCoeffs.N,
                  (BleadingCoeffs.invPiDiv : ℂ) * ((aψ i : ℂ) * x ^ i)) := by
        simp [Finset.sum_add_distrib, add_assoc]
      rw [hterm, hsplit]
      have hphi2 :
          (∑ i ∈ Finset.range BleadingCoeffs.N,
                (BleadingCoeffs.phi2Scale : ℂ) *
                  (if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0)) =
            (BleadingCoeffs.phi2Scale : ℂ) * sC := by
        simpa [sC] using!
          (Finset.mul_sum (a := (BleadingCoeffs.phi2Scale : ℂ))
            (s := Finset.range BleadingCoeffs.N)
            (f := fun i : ℕ => if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0)).symm
      have hlead :
          (∑ i ∈ Finset.range BleadingCoeffs.N,
                (BleadingCoeffs.leadInvPiScale : ℂ) *
                  (if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0)) =
            (BleadingCoeffs.leadInvPiScale : ℂ) * sΔ := by
        simpa [sΔ] using!
          (Finset.mul_sum (a := (BleadingCoeffs.leadInvPiScale : ℂ))
            (s := Finset.range BleadingCoeffs.N)
            (f := fun i : ℕ => if i % 2 = 0 then (aΔ (i / 2 + 1) : ℂ) * x ^ i else 0)).symm
      have hinvPi :
          (∑ i ∈ Finset.range BleadingCoeffs.N,
              (BleadingCoeffs.invPiDiv : ℂ) * ((aψ i : ℂ) * x ^ i)) =
            (BleadingCoeffs.invPiDiv : ℂ) * sψ := by
        simpa [sψ] using!
          (Finset.mul_sum (a := (BleadingCoeffs.invPiDiv : ℂ))
            (s := Finset.range BleadingCoeffs.N)
            (f := fun i : ℕ => (aψ i : ℂ) * x ^ i)).symm
      -- Rewrite the three pieces and close by associativity.
      rw [hphi2, hlead, hinvPi]
    -- Assemble using the algebraic decomposition.
    rw [hsum_decomp, hsumA, hsumB, hsumC]
    -- This is now exactly `E`.
    -- The previous rewrites close the goal.
  -- Conclude via the shared normal form `E`.
  calc
    headS t ht0 = E := hL
    _ = (Bleading_exact_trunc t : ℂ) := hR.symm

end SpherePacking.Dim24.AppendixA
