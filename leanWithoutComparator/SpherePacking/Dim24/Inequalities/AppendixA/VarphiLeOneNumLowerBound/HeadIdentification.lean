/-
Identify the `q`-series head with `exactTrunc`.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import
  SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.ExactTruncTail.ExactTruncation
/-!
### Head identification and final lower bound

We identify the finite head in `q`-series form with the explicit `r`-polynomial `exactTrunc`,
and then control the tails using `Part13E_TailBounds`.
-/

open scoped BigOperators
open UpperHalfPlane

namespace SpherePacking.Dim24.AppendixA

noncomputable section

namespace VarphiLeOne

open BleadingCoeffs


/-- Coefficients of the `varphi` numerator `q`-series, as a function `ℕ → ℚ`. -/
@[expose] public def aA : ℕ → ℚ := fun n => BleadingCoeffs.coeffQ BleadingCoeffs.phinumQ n

/-- Coefficients of the `phi1` core `q`-series, as a function `ℕ → ℚ`. -/
@[expose] public def aB : ℕ → ℚ := fun n => BleadingCoeffs.coeffQ BleadingCoeffs.phi1CoreQ n

/-- Coefficients of the `phi2` core `q`-series, as a function `ℕ → ℚ`. -/
@[expose] public def aC : ℕ → ℚ := fun n => BleadingCoeffs.coeffQ BleadingCoeffs.phi2CoreQ n

lemma qhead_congr {t : ℝ} {ht0 : 0 < t} {a b : ℕ → ℂ}
    (h : ∀ n < BleadingCoeffs.QN, a n = b n) :
    qhead a (it t ht0) BleadingCoeffs.QN = qhead b (it t ht0) BleadingCoeffs.QN := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn' : n < BleadingCoeffs.QN := by simpa [Finset.mem_range] using! hn
  simp [h n hn']

/-- Replace `coeffVarphiNum` by the cached rational coefficient function `aA` in `qhead`. -/
public lemma qhead_coeffVarphiNum_eq (t : ℝ) (ht0 : 0 < t) :
    qhead (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN =
      qhead (fun n : ℕ => (aA n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
  refine qhead_congr (t := t) (ht0 := ht0) (a := fun n => (coeffVarphiNum n : ℂ))
    (b := fun n => (aA n : ℂ)) ?_
  intro n hn
  simpa [aA] using!
    (congrArg (fun q : ℚ => (q : ℂ)) (coeffQ_phinumQ_eq (n := n) hn)).symm

/-- Replace `coeffPhi1Core` by the cached rational coefficient function `aB` in `qhead`. -/
public lemma qhead_coeffPhi1Core_eq (t : ℝ) (ht0 : 0 < t) :
    qhead (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN =
      qhead (fun n : ℕ => (aB n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
  refine qhead_congr (t := t) (ht0 := ht0) (a := fun n => (coeffPhi1Core n : ℂ))
    (b := fun n => (aB n : ℂ)) ?_
  intro n hn
  simpa [aB] using!
    (congrArg (fun q : ℚ => (q : ℂ)) (coeffQ_phi1CoreQ_eq (n := n) hn)).symm

/-- Replace `coeffPhi2Core` by the cached rational coefficient function `aC` in `qhead`. -/
public lemma qhead_coeffPhi2Core_eq (t : ℝ) (ht0 : 0 < t) :
    qhead (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN =
      qhead (fun n : ℕ => (aC n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
  refine qhead_congr (t := t) (ht0 := ht0) (a := fun n => (coeffPhi2Core n : ℂ))
    (b := fun n => (aC n : ℂ)) ?_
  intro n hn
  simpa [aC] using!
    (congrArg (fun q : ℚ => (q : ℂ)) (coeffQ_phi2CoreQ_eq (n := n) hn)).symm

/--
The complex "head" term built from `qhead` and the coefficient model at `z = it t`.

This is the finite head part of `-t^2 * varphi_num - t * phi1_num + phi2_num` after rewriting into
`q`-series form and restricting to the first `BleadingCoeffs.QN` coefficients.
-/
@[expose] public def headS (t : ℝ) (ht0 : 0 < t) : ℂ :=
  let z : ℍ := it t ht0
  (-((t : ℂ) ^ (2 : ℕ))) * qhead (fun n : ℕ => (aA n : ℂ)) z BleadingCoeffs.QN +
    (t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
        qhead (fun n : ℕ => (aB n : ℂ)) z BleadingCoeffs.QN +
      ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
        qhead (fun n : ℕ => (aC n : ℂ)) z BleadingCoeffs.QN

/-- Identify `headS` with the real-valued truncation polynomial `exactTrunc`. -/
public lemma headS_eq_exactTrunc (t : ℝ) (ht0 : 0 < t) : headS t ht0 = (exactTrunc t : ℂ) := by
  have qterm_it_eq_rC_pow (n : ℕ) : qterm (it t ht0) n = (rC t) ^ (2 * n) := by
    have hq : qterm (it t ht0) n = (q t : ℂ) ^ n := by
      simpa using! (qterm_it (t := t) (ht := ht0) (n := n))
    have hqr : (q t : ℂ) = (rC t) ^ (2 : ℕ) := by
      simpa [rC] using! congrArg (fun x : ℝ => (x : ℂ)) (q_eq_r_sq (t := t))
    have hqpow : (q t : ℂ) ^ n = (rC t) ^ (2 * n) := by
      simp [hqr, pow_mul]
    simpa [hq] using! hqpow
  have qhead_to_even_guard_sum (a : ℕ → ℂ) :
      qhead a (it t ht0) BleadingCoeffs.QN =
        ∑ i ∈ Finset.range BleadingCoeffs.N,
          if i % 2 = 0 then a (i / 2) * (rC t) ^ i else 0 := by
    have hqhead :
        qhead a (it t ht0) BleadingCoeffs.QN =
          ∑ n ∈ Finset.range BleadingCoeffs.QN, a n * (rC t) ^ (2 * n) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      simp [qterm_it_eq_rC_pow (n := n)]
    have :
        (∑ i ∈ Finset.range BleadingCoeffs.N,
            if i % 2 = 0 then a (i / 2) * (rC t) ^ i else 0) =
          ∑ n ∈ Finset.range BleadingCoeffs.QN, a n * (rC t) ^ (2 * n) := by
      simpa [BleadingCoeffs.N, BleadingCoeffs.QN, Nat.mul_comm] using!
        (sum_range_even_ite (N := BleadingCoeffs.QN) (c := a) (x := rC t))
    simpa [this] using! hqhead.trans this.symm
  set x : ℂ := rC t
  have hx :
      (exactTrunc t : ℂ) =
        ∑ i ∈ Finset.range BleadingCoeffs.N, (exactCoeff t i : ℂ) * x ^ i := by
    dsimp [exactTrunc]
    simp [x, rC]
  have hqA :
      qhead (fun n : ℕ => (aA n : ℂ)) (it t ht0) BleadingCoeffs.QN =
        ∑ i ∈ Finset.range BleadingCoeffs.N,
          if i % 2 = 0 then (aA (i / 2) : ℂ) * x ^ i else 0 := by
    simpa [x] using! qhead_to_even_guard_sum (a := fun n : ℕ => (aA n : ℂ))
  have hqB :
      qhead (fun n : ℕ => (aB n : ℂ)) (it t ht0) BleadingCoeffs.QN =
        ∑ i ∈ Finset.range BleadingCoeffs.N,
          if i % 2 = 0 then (aB (i / 2) : ℂ) * x ^ i else 0 := by
    simpa [x] using! qhead_to_even_guard_sum (a := fun n : ℕ => (aB n : ℂ))
  have hqC :
      qhead (fun n : ℕ => (aC n : ℂ)) (it t ht0) BleadingCoeffs.QN =
        ∑ i ∈ Finset.range BleadingCoeffs.N,
          if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0 := by
    simpa [x] using! qhead_to_even_guard_sum (a := fun n : ℕ => (aC n : ℂ))
  -- Put `headS` into the same normal form as `exactTrunc`.
  have hhead :
      headS t ht0 =
        ∑ i ∈ Finset.range BleadingCoeffs.N, (exactCoeff t i : ℂ) * x ^ i := by
    dsimp [headS]
    rw [hqA, hqB, hqC]
    have hmerge :
        (-((t : ℂ) ^ (2 : ℕ))) *
              (∑ i ∈ Finset.range BleadingCoeffs.N,
                if i % 2 = 0 then (aA (i / 2) : ℂ) * x ^ i else 0) +
            (t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
              (∑ i ∈ Finset.range BleadingCoeffs.N,
                if i % 2 = 0 then (aB (i / 2) : ℂ) * x ^ i else 0) +
            ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
              (∑ i ∈ Finset.range BleadingCoeffs.N,
                if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0)
            =
            ∑ i ∈ Finset.range BleadingCoeffs.N,
              ((-((t : ℂ) ^ (2 : ℕ))) *
                    (if i % 2 = 0 then (aA (i / 2) : ℂ) * x ^ i else 0) +
                  ((t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
                      (if i % 2 = 0 then (aB (i / 2) : ℂ) * x ^ i else 0) +
                    ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
                      (if i % 2 = 0 then (aC (i / 2) : ℂ) * x ^ i else 0))) := by
      simp [Finset.mul_sum, Finset.sum_add_distrib, add_assoc, mul_assoc]
    -- Reduce to termwise simplification of `exactCoeff`.
    rw [hmerge]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hpar : i % 2 = 0
    · have hAdef : (Acoeff i : ℂ) = -(aA (i / 2) : ℂ) := by
        simp [Acoeff, aA, hpar]
      have hBdef : (Bcoeff i : ℂ) = (6 : ℂ) * (aB (i / 2) : ℂ) := by
        by_cases hq : i / 2 < BleadingCoeffs.QN <;> simp [Bcoeff, aB, hpar, hq, mul_comm]
      have hCdef : (Ccoeff i : ℂ) = (-36 : ℂ) * (aC (i / 2) : ℂ) := by
        by_cases hq : i / 2 < BleadingCoeffs.QN <;> simp [Ccoeff, aC, hpar, hq, mul_comm]
      simp [exactCoeff, hAdef, hBdef, hCdef, hpar, x, div_eq_mul_inv]
      ring_nf
    · have hAdef : (Acoeff i : ℂ) = 0 := by simp [Acoeff, hpar]
      have hBdef : (Bcoeff i : ℂ) = 0 := by simp [Bcoeff, hpar]
      have hCdef : (Ccoeff i : ℂ) = 0 := by simp [Ccoeff, hpar]
      simp [exactCoeff, hAdef, hBdef, hCdef, hpar, x]
  -- Conclude by comparing to the complex form of `exactTrunc`.
  have : headS t ht0 = (exactTrunc t : ℂ) := by
    -- `hhead` is already the desired normal form; rewrite the RHS using `hx`.
    simpa [hx] using! hhead.trans hx.symm
  exact this


end VarphiLeOne

end

end SpherePacking.Dim24.AppendixA
