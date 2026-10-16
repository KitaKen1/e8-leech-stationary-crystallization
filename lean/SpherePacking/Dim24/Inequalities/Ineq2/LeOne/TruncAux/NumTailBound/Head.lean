-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiCoeffMatch
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiTable

/-!
# Head part equals the exact truncation

This file identifies the head series `ineq2_num_head` from `NumTailBound.Defs` with the explicit
exact truncation `ExactTrunc.ineq2_exact_trunc` (as a real number, after taking real parts).

## Main statements
* `ineq2_num_head_re_eq_exact_trunc`
-/

open scoped BigOperators
open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open ExactTrunc
open BleadingCoeffs

namespace NumTailBound

lemma div_two_lt_QN_of_lt_exactN {i : ℕ} (hi : i < CoeffModel.N) : i / 2 < QN := by
  -- Here `CoeffModel.N = 100` and `QN = 50`.
  exact Nat.div_lt_of_lt_mul (by simpa [CoeffModel.N, QN] using! hi)

lemma coeffVarphiNum_cast_eq_phinumCoeffQ (n : ℕ) (hn : n < QN) :
    (AppendixA.coeffVarphiNum n : ℂ) = (CoeffModel.phinumCoeffQ n : ℂ) := by
  have h := AppendixA.coeffVarphiNum_eq_table (n := n) (hn := by simpa [QN] using! hn)
  simpa [CoeffModel.phinumCoeffQ] using! congrArg (fun q : ℚ => (q : ℂ)) h

lemma coeffPhi1Core_cast_eq_phi1CoreCoeffQ (n : ℕ) (hn : n < QN) :
    (AppendixA.coeffPhi1Core n : ℂ) = (CoeffModel.phi1CoreCoeffQ n : ℂ) := by
  have h := AppendixA.coeffPhi1Core_eq_table (n := n) (hn := by simpa [QN] using! hn)
  simpa [CoeffModel.phi1CoreCoeffQ] using! congrArg (fun q : ℚ => (q : ℂ)) h

lemma coeffPhi2Core_cast_eq_phi2CoreCoeffQ (n : ℕ) (hn : n < QN) :
    (AppendixA.coeffPhi2Core n : ℂ) = (CoeffModel.phi2CoreCoeffQ n : ℂ) := by
  have h := AppendixA.coeffPhi2Core_eq_table (n := n) (hn := by simpa [QN] using! hn)
  simpa [CoeffModel.phi2CoreCoeffQ] using! congrArg (fun q : ℚ => (q : ℂ)) h

lemma psiCoeffFun_cast_eq_psiInumCoeffQ (n : ℕ) (hn : n < CoeffModel.N) :
    (AppendixA.psiCoeffFun n : ℂ) = (CoeffModel.psiInumCoeffQ n : ℂ) := by
  have hn' : n < AppendixA.BleadingCoeffs.N := by
    simpa [CoeffModel.N, N] using! hn
  have hψ : AppendixA.psiCoeffFun n = AppendixA.BleadingCoeffs.psiInumCoeffs.getD n 0 :=
    AppendixA.psiCoeffFun_eq_psiInumCoeffs_getD (n := n) hn'
  have hψ' : AppendixA.psiCoeffFun n = AppendixA.psiInumCoeffs_table.getD n 0 := by
    calc
      AppendixA.psiCoeffFun n = AppendixA.BleadingCoeffs.psiInumCoeffs.getD n 0 := hψ
      _ = AppendixA.psiInumCoeffs_table.getD n 0 := by
          simpa using! (AppendixA.psiInumCoeffs_getD_eq n)
  have hcastZ : (AppendixA.psiCoeffFun n : ℂ) = (AppendixA.psiInumCoeffs_table.getD n 0 : ℂ) :=
    congrArg (fun z : ℤ => (z : ℂ)) hψ'
  assumption

lemma ineq2_num_head_eq_exact_trunc_complex (t : ℝ) (ht0 : 0 < t) :
    ineq2_num_head t ht0 = (ExactTrunc.ineq2_exact_trunc t : ℂ) := by
  set xC : ℂ := (AppendixA.r t : ℂ)
  have hxC : AppendixA.rC t = xC := by rfl
  have hqterm : ∀ n : ℕ, AppendixA.qterm (it t ht0) n = xC ^ (2 * n) := by
    intro n
    have h1 := AppendixA.qterm_it (t := t) (ht := ht0) (n := n)
    have hq : (AppendixA.q t : ℂ) = xC ^ (2 : ℕ) := by
      have hqR : AppendixA.q t = (AppendixA.r t) ^ (2 : ℕ) := AppendixA.q_eq_r_sq (t := t)
      simp_all only [Complex.ofReal_pow, xC]
    calc
      AppendixA.qterm (it t ht0) n = (AppendixA.q t : ℂ) ^ n := by simpa using! h1
      _ = (xC ^ (2 : ℕ)) ^ n := by simp [hq]
      _ = xC ^ (2 * n) := by simpa using! (pow_mul xC 2 n).symm
  have h2 : Finset.range (2 * QN) = Finset.range CoeffModel.N := by
    rfl
  have hqhead_varphi :
      AppendixA.qhead (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) (it t ht0) QN =
        ∑ i ∈ Finset.range CoeffModel.N,
          (if i % 2 = 0 then (AppendixA.coeffVarphiNum (i / 2) : ℂ) * xC ^ i else 0) := by
    have :
        ∑ n ∈ Finset.range QN, (AppendixA.coeffVarphiNum n : ℂ) * xC ^ (2 * n) =
          ∑ i ∈ Finset.range (2 * QN),
            (if i % 2 = 0 then (AppendixA.coeffVarphiNum (i / 2) : ℂ) * xC ^ i else 0) := by
      simpa using!
        (AppendixA.sum_range_even_ite (N := QN) (c := fun n => (AppendixA.coeffVarphiNum n : ℂ)) (x
          := xC)).symm
    simp [AppendixA.qhead, hqterm, this, h2, xC]
  have hqhead_phi1 :
      AppendixA.qhead (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN =
        ∑ i ∈ Finset.range CoeffModel.N,
          (if i % 2 = 0 then (AppendixA.coeffPhi1Core (i / 2) : ℂ) * xC ^ i else 0) := by
    have :
        ∑ n ∈ Finset.range QN, (AppendixA.coeffPhi1Core n : ℂ) * xC ^ (2 * n) =
          ∑ i ∈ Finset.range (2 * QN),
            (if i % 2 = 0 then (AppendixA.coeffPhi1Core (i / 2) : ℂ) * xC ^ i else 0) := by
      simpa using!
        (AppendixA.sum_range_even_ite (N := QN) (c := fun n => (AppendixA.coeffPhi1Core n : ℂ)) (x
          := xC)).symm
    simp [AppendixA.qhead, hqterm, this, h2, xC]
  have hqhead_phi2 :
      AppendixA.qhead (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN =
        ∑ i ∈ Finset.range CoeffModel.N,
          (if i % 2 = 0 then (AppendixA.coeffPhi2Core (i / 2) : ℂ) * xC ^ i else 0) := by
    have :
        ∑ n ∈ Finset.range QN, (AppendixA.coeffPhi2Core n : ℂ) * xC ^ (2 * n) =
          ∑ i ∈ Finset.range (2 * QN),
            (if i % 2 = 0 then (AppendixA.coeffPhi2Core (i / 2) : ℂ) * xC ^ i else 0) := by
      simpa using!
        (AppendixA.sum_range_even_ite (N := QN) (c := fun n => (AppendixA.coeffPhi2Core n : ℂ)) (x
          := xC)).symm
    simp [AppendixA.qhead, hqterm, this, h2, xC]
  have hrhead_psi :
      AppendixA.rhead AppendixA.psiCoeffFun t N =
        ∑ i ∈ Finset.range CoeffModel.N, (AppendixA.psiCoeffFun i : ℂ) * xC ^ i := by
    simp [AppendixA.rhead, AppendixA.rC, xC, CoeffModel.N, N, AppendixA.BleadingCoeffs.N]
  have hExact :
      (ExactTrunc.ineq2_exact_trunc t : ℂ) =
        ∑ i ∈ Finset.range CoeffModel.N, (ExactTrunc.ineq2_exact_coeff t i : ℂ) * xC ^ i := by
    dsimp [ExactTrunc.ineq2_exact_trunc]
    simp [xC, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [hExact]
  dsimp [ineq2_num_head]
  rw [hqhead_varphi, hqhead_phi1, hqhead_phi2, hrhead_psi]
  set s : Finset ℕ := Finset.range CoeffModel.N
  have hA :
      ((t : ℂ) ^ (2 : ℕ)) * (∑ i ∈ s, if i % 2 = 0 then (AppendixA.coeffVarphiNum (i / 2) : ℂ) * xC
        ^ i else 0) =
        ∑ i ∈ s, ((t : ℂ) ^ (2 : ℕ)) * (if i % 2 = 0 then (AppendixA.coeffVarphiNum (i / 2) : ℂ) *
          xC ^ i else 0) :=
    Finset.mul_sum s
        (fun i => if i % 2 = 0 then ↑(coeffVarphiNum (i / 2)) * xC ^ i else 0) (↑t ^ 2)
  have hB :
      (t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
          (∑ i ∈ s, if i % 2 = 0 then (AppendixA.coeffPhi1Core (i / 2) : ℂ) * xC ^ i else 0) =
        ∑ i ∈ s,
          (t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
            (if i % 2 = 0 then (AppendixA.coeffPhi1Core (i / 2) : ℂ) * xC ^ i else 0) := by
    simpa [s, mul_assoc] using!
      (Finset.mul_sum (a := (t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ))) (s := s)
        (f := fun i : ℕ => if i % 2 = 0 then (AppendixA.coeffPhi1Core (i / 2) : ℂ) * xC ^ i else 0))
  have hC :
      ((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
          (∑ i ∈ s, if i % 2 = 0 then (AppendixA.coeffPhi2Core (i / 2) : ℂ) * xC ^ i else 0) =
        ∑ i ∈ s,
          ((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
            (if i % 2 = 0 then (AppendixA.coeffPhi2Core (i / 2) : ℂ) * xC ^ i else 0) := by
    simpa [s, mul_assoc] using!
      (Finset.mul_sum (a := (36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) (s := s)
        (f := fun i : ℕ => if i % 2 = 0 then (AppendixA.coeffPhi2Core (i / 2) : ℂ) * xC ^ i else 0))
  have hψ :
      (432 / (Real.pi ^ 2) : ℂ) * (∑ i ∈ s, (AppendixA.psiCoeffFun i : ℂ) * xC ^ i) =
        ∑ i ∈ s, (432 / (Real.pi ^ 2) : ℂ) * ((AppendixA.psiCoeffFun i : ℂ) * xC ^ i) :=
    Finset.mul_sum s (fun i => ↑(psiCoeffFun i) * xC ^ i) (432 / ↑Real.pi ^ 2)
  rw [hA, hB, hC, hψ]
  -- Combine the four head sums into one sum over `s`.
  let a : ℕ → ℂ := fun i =>
    ((t : ℂ) ^ (2 : ℕ)) * (if i % 2 = 0 then (AppendixA.coeffVarphiNum (i / 2) : ℂ) * xC ^ i else 0)
  let b : ℕ → ℂ := fun i =>
    (t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
      (if i % 2 = 0 then (AppendixA.coeffPhi1Core (i / 2) : ℂ) * xC ^ i else 0)
  let c : ℕ → ℂ := fun i =>
    ((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
      (if i % 2 = 0 then (AppendixA.coeffPhi2Core (i / 2) : ℂ) * xC ^ i else 0)
  let d : ℕ → ℂ := fun i =>
    (432 / (Real.pi ^ 2) : ℂ) * ((AppendixA.psiCoeffFun i : ℂ) * xC ^ i)
  -- Rewrite the goal so the left-hand side is explicitly a sum of four `Finset.sum`s.
  change ((∑ i ∈ s, a i) + (∑ i ∈ s, b i) + (∑ i ∈ s, c i) + (∑ i ∈ s, d i)) =
      ∑ i ∈ s, (ExactTrunc.ineq2_exact_coeff t i : ℂ) * xC ^ i
  have hab : (∑ i ∈ s, a i) + (∑ i ∈ s, b i) = ∑ i ∈ s, (a i + b i) := by
    simpa using! (Finset.sum_add_distrib (s := s) (f := a) (g := b)).symm
  have habc :
      (∑ i ∈ s, (a i + b i)) + (∑ i ∈ s, c i) = ∑ i ∈ s, ((a i + b i) + c i) := by
    simpa using! (Finset.sum_add_distrib (s := s) (f := fun i => a i + b i) (g := c)).symm
  have habcd :
      (∑ i ∈ s, ((a i + b i) + c i)) + (∑ i ∈ s, d i) =
        ∑ i ∈ s, (((a i + b i) + c i) + d i) := by
    simpa using! (Finset.sum_add_distrib (s := s) (f := fun i => (a i + b i) + c i) (g := d)).symm
  -- Apply the combination equalities to turn the left side into one sum.
  -- (Only reassociate; no commutativity.)
  rw [hab]
  rw [habc]
  rw [habcd]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hiRange : i ∈ Finset.range CoeffModel.N := by simpa [s] using! hi
  have hi' : i < CoeffModel.N := Finset.mem_range.1 hiRange
  have hn : i / 2 < QN := div_two_lt_QN_of_lt_exactN (i := i) hi'
  by_cases h : i % 2 = 0
  · have hVarphi : (AppendixA.coeffVarphiNum (i / 2) : ℂ) = (CoeffModel.phinumCoeffQ (i / 2) : ℂ) :=
      coeffVarphiNum_cast_eq_phinumCoeffQ (n := i / 2) hn
    have hPhi1 : (AppendixA.coeffPhi1Core (i / 2) : ℂ) = (CoeffModel.phi1CoreCoeffQ (i / 2) : ℂ) :=
      coeffPhi1Core_cast_eq_phi1CoreCoeffQ (n := i / 2) hn
    have hPhi2 : (AppendixA.coeffPhi2Core (i / 2) : ℂ) = (CoeffModel.phi2CoreCoeffQ (i / 2) : ℂ) :=
      coeffPhi2Core_cast_eq_phi2CoreCoeffQ (n := i / 2) hn
    have hPsi : (AppendixA.psiCoeffFun i : ℂ) = (CoeffModel.psiInumCoeffQ i : ℂ) :=
      psiCoeffFun_cast_eq_psiInumCoeffQ (n := i) hi'
    simp [a, b, c, d, ExactTrunc.ineq2_exact_coeff, CoeffModel.A0, CoeffModel.B0, CoeffModel.C0, h,
      hVarphi, hPhi1, hPhi2, hPsi,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
    ring_nf
  · have hPsi : (AppendixA.psiCoeffFun i : ℂ) = (CoeffModel.psiInumCoeffQ i : ℂ) :=
      psiCoeffFun_cast_eq_psiInumCoeffQ (n := i) hi'
    simp [a, b, c, d, ExactTrunc.ineq2_exact_coeff, CoeffModel.A0, CoeffModel.B0, CoeffModel.C0, h,
      hPsi,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The real part of `ineq2_num_head t ht0` is exactly `ExactTrunc.ineq2_exact_trunc t`. -/
public lemma ineq2_num_head_re_eq_exact_trunc (t : ℝ) (ht0 : 0 < t) :
    (ineq2_num_head t ht0).re = ExactTrunc.ineq2_exact_trunc t := by
  have h := congrArg Complex.re (ineq2_num_head_eq_exact_trunc_complex (t := t) (ht0 := ht0))
  simpa using! h

end SpherePacking.Dim24.Ineq2LeOneTruncAux.NumTailBound
