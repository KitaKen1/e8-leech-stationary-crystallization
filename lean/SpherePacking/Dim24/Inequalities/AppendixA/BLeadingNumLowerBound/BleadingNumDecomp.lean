/- Decomposing `BleadingNum` into truncation head and tail. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.HeadEqualsExactTrunc
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.FinalLowerBound
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.SeriesSplit
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Numerators
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffBounds
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.SparseCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffMatchingLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiCoeffMatch
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.DeltaCoeffBounds

/-!
# Decompose `BleadingNum` into truncation and remainder

We expand `BleadingNum` into `q`/`r`-series, split each series into a finite head plus a tail,
match the heads with the explicit coefficient lists used in `headS`, and isolate the remaining
tails. The `Δ^2` term contributes one "missing" coefficient (`coeffDeltaSq 50`) that does not fit
into the uniform tail package, so we keep it separate in the remainder.

The final output is the decomposition
`BleadingNum t - Bleading_exact_trunc t = BleadingNumRemainder t`,
which is the algebraic starting point for the analytic remainder estimate.

## Main definitions
* `BleadingNumRemainder`
* `leadingScale`
* `coeffDeltaSqShift`

## Main statements
* `BleadingNum_sub_exact_trunc_eq_remainder`
-/

open scoped BigOperators
open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA

/-- If `1 ≤ t` then `0 < t` (used to build the point `it t`). -/
public lemma t_pos_of_one_le {t : ℝ} (ht : 1 ≤ t) : 0 < t :=
  lt_of_lt_of_le zero_lt_one ht

private lemma summable_qseries_of_coeffBound (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) (a : ℕ → ℚ)
    (C : ℝ) (k : ℕ) (habs : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    Summable (fun n : ℕ => (a n : ℂ) * qterm (it t ht0) n) := by
  refine Summable.of_norm ?_
  exact summable_norm_qseries_of_coeffBound t ht0 ht a C k habs

private lemma summable_rseries_of_coeffBound (t : ℝ) (ht0 : 0 < t) (a : ℕ → ℤ)
    (C : ℝ) (k : ℕ) (habs : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    Summable (fun n : ℕ => (a n : ℂ) * (rC t) ^ n) := by
  refine Summable.of_norm ?_
  simpa using!
    (summable_norm_rseries_of_coeffBound (t := t) (ht0 := ht0) (a := a) (C := C) (k := k) habs)

/-!
### Remainder definitions
-/

/-- Shifted coefficient function `n ↦ coeffDeltaSq (n+1)`, cast to `ℂ`. -/
@[expose] public def coeffDeltaSqShift (n : ℕ) : ℂ := (coeffDeltaSq (n + 1) : ℂ)

/-- Scalar multiplying the `Δ^2` tail in the `BleadingNum` expansion. -/
@[expose] public def leadingScale (t : ℝ) : ℂ :=
  (-(1 / 39 : ℂ) * (t : ℂ) + (10 / (117 : ℂ)) * (1 / (Real.pi : ℂ)))

/--
The remainder term in the decomposition of `BleadingNum`.

It consists of the `q`/`r`-series tails (beyond the truncation cutoffs) together with the single
extra `Δ^2` coefficient `coeffDeltaSq 50`.
-/
@[expose] public def BleadingNumRemainder (t : ℝ) (ht : 1 ≤ t) : ℂ :=
  let ht0 : 0 < t := t_pos_of_one_le ht
  let z : ℍ := it t ht0
  ((Real.pi : ℂ) / (28304640 : ℂ)) *
        ((t : ℂ) ^ (2 : ℕ) *
              qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN +
          (t : ℂ) *
                (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
                    qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN) -
              ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
                  qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN)) +
    (1 / ((65520 : ℂ) * Real.pi)) * rtail psiCoeffFun t BleadingCoeffs.N +
      (leadingScale t) *
          qtail (fun n : ℕ => coeffDeltaSqShift n) z BleadingCoeffs.QN +
      (leadingScale t) * ((coeffDeltaSq 50 : ℂ) * qterm z 49)

/-- Summability of the `varphi` numerator `q`-series at `z = it t` for `t ≥ 1`. -/
public lemma summable_coeffVarphiNum (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := t_pos_of_one_le ht
    Summable (fun n : ℕ => (coeffVarphiNum n : ℂ) * qterm (it t ht0) n) := by
  intro ht0
  simpa using!
    (summable_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht) (a := coeffVarphiNum)
      (C := Cvarphi) (k := 20) abs_coeffVarphiNum_le)

/-- Summability of the `phi1` core `q`-series at `z = it t` for `t ≥ 1`. -/
public lemma summable_coeffPhi1Core (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := t_pos_of_one_le ht
    Summable (fun n : ℕ => (coeffPhi1Core n : ℂ) * qterm (it t ht0) n) := by
  intro ht0
  simpa using!
    (summable_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht) (a := coeffPhi1Core)
      (C := Cvarphi) (k := 20) abs_coeffPhi1Core_le_Cvarphi)

/-- Summability of the `phi2` core `q`-series at `z = it t` for `t ≥ 1`. -/
public lemma summable_coeffPhi2Core (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := t_pos_of_one_le ht
    Summable (fun n : ℕ => (coeffPhi2Core n : ℂ) * qterm (it t ht0) n) := by
  intro ht0
  simpa using!
    (summable_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht) (a := coeffPhi2Core)
      (C := Cvarphi) (k := 20) abs_coeffPhi2Core_le_Cvarphi)

lemma summable_coeffDeltaSqShift (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := t_pos_of_one_le ht
    Summable (fun n : ℕ => coeffDeltaSqShift n * qterm (it t ht0) n) := by
  intro ht0
  simpa [coeffDeltaSqShift] using!
    (summable_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
      (a := fun n : ℕ => coeffDeltaSq (n + 1)) (C := CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) (k := 29)
      (fun n => abs_coeffDeltaSq_shift_le (n := n)))

lemma summable_psiCoeffFun (t : ℝ) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => (psiCoeffFun n : ℂ) * (rC t) ^ n) := by
  have ht0 : 0 < t := t_pos_of_one_le ht
  simpa using!
    (summable_rseries_of_coeffBound (t := t) (ht0 := ht0) (a := psiCoeffFun)
      (C := (16 : ℝ) ^ (8 : ℕ)) (k := 27) (fun n => abs_psiCoeffFun_le (n := n)))

lemma qhead_coeffVarphiNum_eq (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := t_pos_of_one_le ht
    qhead (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN =
      qhead (fun n : ℕ => (aA n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
  intro ht0
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn' : n < BleadingCoeffs.QN := Finset.mem_range.1 hn
  simp [aA, coeffQ_phinumQ_eq (n := n) hn']

lemma qhead_coeffPhi1Core_eq (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := t_pos_of_one_le ht
    qhead (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN =
      qhead (fun n : ℕ => (aB n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
  intro ht0
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn' : n < BleadingCoeffs.QN := Finset.mem_range.1 hn
  simp [aB, coeffQ_phi1CoreQ_eq (n := n) hn']

lemma qhead_coeffPhi2Core_eq (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := t_pos_of_one_le ht
    qhead (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN =
      qhead (fun n : ℕ => (aC n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
  intro ht0
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn' : n < BleadingCoeffs.QN := Finset.mem_range.1 hn
  simp [aC, coeffQ_phi2CoreQ_eq (n := n) hn']

lemma rhead_psiCoeffFun_eq (t : ℝ) :
    rhead psiCoeffFun t BleadingCoeffs.N = rhead aψ t BleadingCoeffs.N := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn' : n < BleadingCoeffs.N := Finset.mem_range.1 hn
  simp [aψ, psiCoeffFun_eq_psiInumCoeffs_getD (n := n) hn']

lemma aΔ_out_of_range :
    aΔ 50 = 0 := by
  have hle : BleadingCoeffs.DeltaSqQ.length ≤ 50 := by
    simp [BleadingCoeffs.DeltaSqQ, BleadingCoeffs.powQ, BleadingCoeffs.mulQ, BleadingCoeffs.QN]
  simpa [aΔ, BleadingCoeffs.coeffQ] using!
    (List.getD_eq_default (l := BleadingCoeffs.DeltaSqQ) (d := (0 : ℚ)) (n := 50) hle)

lemma qhead_coeffDeltaSqShift_eq_add_missing (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := t_pos_of_one_le ht
    let z : ℍ := it t ht0
    qhead (fun n : ℕ => coeffDeltaSqShift n) z BleadingCoeffs.QN =
      qhead (fun n : ℕ => (aΔ (n + 1) : ℂ)) z BleadingCoeffs.QN +
          (coeffDeltaSq 50 : ℂ) * qterm z 49 := by
  intro ht0 z
  -- Split the head sum at the last index `49`.
  have hsplit :
      qhead (fun n : ℕ => coeffDeltaSqShift n) z BleadingCoeffs.QN
          =
        qhead (fun n : ℕ => coeffDeltaSqShift n) z 49 +
          coeffDeltaSqShift 49 * qterm z 49 := by
    -- `∑_{n<50} = ∑_{n<49} + (n=49)`.
    simpa [qhead, BleadingCoeffs.QN] using!
      (Finset.sum_range_succ (f := fun n : ℕ => coeffDeltaSqShift n * qterm z n) 49)
  have hsplitA :
      qhead (fun n : ℕ => (aΔ (n + 1) : ℂ)) z BleadingCoeffs.QN
          =
        qhead (fun n : ℕ => (aΔ (n + 1) : ℂ)) z 49 +
          (aΔ (49 + 1) : ℂ) * qterm z 49 := by
    simpa [qhead, BleadingCoeffs.QN] using!
      (Finset.sum_range_succ (f := fun n : ℕ => (aΔ (n + 1) : ℂ) * qterm z n) 49)
  -- Match indices `< 49` using `coeffQ_DeltaSqQ_eq` on `n+1 < 50`.
  have hmatch49 :
      qhead (fun n : ℕ => coeffDeltaSqShift n) z 49 =
        qhead (fun n : ℕ => (aΔ (n + 1) : ℂ)) z 49 := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn49 : n < 49 := Finset.mem_range.1 hn
    have hn' : n + 1 < BleadingCoeffs.QN := by
      simpa [BleadingCoeffs.QN] using! (Nat.succ_lt_succ hn49)
    have hcoeff : aΔ (n + 1) = coeffDeltaSq (n + 1) := by
      simpa [aΔ] using! (coeffQ_DeltaSqQ_eq (n := n + 1) hn')
    simp [coeffDeltaSqShift, hcoeff]
  -- Assemble and use `aΔ 50 = 0`.
  have hlast : (aΔ (49 + 1) : ℂ) * qterm z 49 = 0 := by
    simp [aΔ_out_of_range]
  -- `coeffDeltaSqShift 49 = coeffDeltaSq 50`.
  have hshift49 : coeffDeltaSqShift 49 = (coeffDeltaSq 50 : ℂ) := by
    simp [coeffDeltaSqShift]
  calc
    qhead (fun n : ℕ => coeffDeltaSqShift n) z BleadingCoeffs.QN
        = qhead (fun n : ℕ => coeffDeltaSqShift n) z 49 +
            coeffDeltaSqShift 49 * qterm z 49 := hsplit
    _ = qhead (fun n : ℕ => (aΔ (n + 1) : ℂ)) z 49 +
            (coeffDeltaSq 50 : ℂ) * qterm z 49 := by
          simp [hmatch49, hshift49]
    _ = qhead (fun n : ℕ => (aΔ (n + 1) : ℂ)) z BleadingCoeffs.QN +
            (coeffDeltaSq 50 : ℂ) * qterm z 49 := by
          -- rewrite the `aΔ` head at `QN` and cancel the (zero) last coefficient
          simp [hsplitA, hlast, add_comm]

private lemma BleadingNum_eq_headS_add_remainder (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := t_pos_of_one_le ht
    BleadingNum t ht0 = headS t ht0 + BleadingNumRemainder t ht := by
  intro ht0
  set z : ℍ := it t ht0
  -- Expand `BleadingNum` into the explicit numerators and the leading term.
  have hbase := BleadingNum_eq_num_expr (t := t) (ht0 := ht0)
  -- Rewrite each numerator as a `q`/`r`-series.
  have hvarphi : varphi_num z = qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) z := by
    simpa [z] using! (varphi_num_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  have hphi1 :
      phi1_num z =
        (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) * qseries (fun n : ℕ => (coeffPhi1Core n : ℂ)) z) :=
    phi1_num_it_eq_qseries t ht0 ht
  have hphi2 :
      phi2_num z =
        (((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
            qseries (fun n : ℕ => (coeffPhi2Core n : ℂ)) z) := by
    have h := phi2_num_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht)
    simpa [z, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! h
  have hpsi : psiI_num z = rseries psiCoeffFun t := by
    -- The lemma is stated with a `let ht0`; use the same definitional `ht0`.
    have := psiI_num_it_eq_rseries_psiCoeffFun (t := t) (ht := ht)
    simpa [z] using! this
  have hlead' :
      -((BleadingLeadingTerm t : ℂ)) * (Δ z) ^ (2 : ℕ)
          = (leadingScale t) * qseries (fun n : ℕ => coeffDeltaSqShift n) z := by
    have hleadC :
        (BleadingLeadingTerm t : ℂ) =
          (Real.exp (2 * Real.pi * t) : ℂ) *
            ((1 / 39 : ℂ) * (t : ℂ) - (10 / (117 : ℂ)) * (1 / (Real.pi : ℂ))) := by
      simp [BleadingLeadingTerm, sub_eq_add_neg, div_eq_mul_inv, mul_add,
        mul_assoc, mul_left_comm, mul_comm]
    have hshift := exp_two_pi_mul_Delta_sq_eq_qseries_shift (t := t) (ht0 := ht0) (ht := ht)
    calc
      -((BleadingLeadingTerm t : ℂ)) * (Δ z) ^ (2 : ℕ)
          =
            -((Real.exp (2 * Real.pi * t) : ℂ) *
                ((1 / 39 : ℂ) * (t : ℂ) - (10 / (117 : ℂ)) * (1 / (Real.pi : ℂ)))) *
              (Δ z) ^ (2 : ℕ) := by
              simp [hleadC, mul_assoc]
      _ = (leadingScale t) * ((Real.exp (2 * Real.pi * t) : ℂ) * (Δ z) ^ (2 : ℕ)) := by
            simp
              [leadingScale, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm,
                mul_add, add_mul, add_comm]
      _ = (leadingScale t) * qseries (fun n : ℕ => coeffDeltaSqShift n) z := by
            simpa [z] using! congrArg (fun w => (leadingScale t) * w) hshift
  have hlead :
      -((BleadingLeadingTerm t : ℂ) * (Δ z) ^ (2 : ℕ))
          = (leadingScale t) * qseries (fun n : ℕ => coeffDeltaSqShift n) z := by
    simpa [neg_mul, mul_assoc] using! hlead'
  -- Split each `q`/`r`-series into head + tail.
  have hsplit_q (a : ℕ → ℂ) (hs : Summable fun n : ℕ => a n * qterm z n) :
      qseries a z = qhead a z BleadingCoeffs.QN + qtail a z BleadingCoeffs.QN := by
    simpa [z] using! qseries_eq_qhead_add_qtail (a := a) (z := z) (N := BleadingCoeffs.QN) hs
  have hsplit_varphi :
      qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) z =
        qhead (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN +
          qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN := by
    refine hsplit_q (a := fun n : ℕ => (coeffVarphiNum n : ℂ)) ?_
    simpa [z] using! (summable_coeffVarphiNum (t := t) (ht := ht))
  have hsplit_phi1 :
      qseries (fun n : ℕ => (coeffPhi1Core n : ℂ)) z =
        qhead (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN +
          qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN := by
    refine hsplit_q (a := fun n : ℕ => (coeffPhi1Core n : ℂ)) ?_
    simpa [z] using! (summable_coeffPhi1Core (t := t) (ht := ht))
  have hsplit_phi2 :
      qseries (fun n : ℕ => (coeffPhi2Core n : ℂ)) z =
        qhead (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN +
          qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN := by
    refine hsplit_q (a := fun n : ℕ => (coeffPhi2Core n : ℂ)) ?_
    simpa [z] using! (summable_coeffPhi2Core (t := t) (ht := ht))
  have hsplit_deltaShift :
      qseries (fun n : ℕ => coeffDeltaSqShift n) z =
        qhead (fun n : ℕ => coeffDeltaSqShift n) z BleadingCoeffs.QN +
          qtail (fun n : ℕ => coeffDeltaSqShift n) z BleadingCoeffs.QN := by
    refine hsplit_q (a := fun n : ℕ => coeffDeltaSqShift n) ?_
    simpa [z] using! (summable_coeffDeltaSqShift (t := t) (ht := ht))
  have hsplit_psi :
      rseries psiCoeffFun t =
        rhead psiCoeffFun t BleadingCoeffs.N + rtail psiCoeffFun t BleadingCoeffs.N := by
    have hs : Summable (fun n : ℕ => (psiCoeffFun n : ℂ) * (rC t) ^ n) := by
      simpa using! (summable_psiCoeffFun (t := t) (ht := ht))
    simpa using! rseries_eq_rhead_add_rtail (a := psiCoeffFun) (t := t) (N := BleadingCoeffs.N) hs
  -- Match all heads with the explicit head `headS`, isolating the tails.
  have hmatch_varphi :
      qhead (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN =
        qhead (fun n : ℕ => (aA n : ℂ)) z BleadingCoeffs.QN := by
    simpa [z] using! qhead_coeffVarphiNum_eq (t := t) (ht := ht)
  have hmatch_phi1 :
      qhead (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN =
        qhead (fun n : ℕ => (aB n : ℂ)) z BleadingCoeffs.QN := by
    simpa [z] using! qhead_coeffPhi1Core_eq (t := t) (ht := ht)
  have hmatch_phi2 :
      qhead (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN =
        qhead (fun n : ℕ => (aC n : ℂ)) z BleadingCoeffs.QN := by
    simpa [z] using! qhead_coeffPhi2Core_eq (t := t) (ht := ht)
  have hmatch_psi :
      rhead psiCoeffFun t BleadingCoeffs.N = rhead aψ t BleadingCoeffs.N :=
    rhead_psiCoeffFun_eq (t := t)
  have hmatch_delta :
      qhead (fun n : ℕ => coeffDeltaSqShift n) z BleadingCoeffs.QN =
        qhead (fun n : ℕ => (aΔ (n + 1) : ℂ)) z BleadingCoeffs.QN +
          (coeffDeltaSq 50 : ℂ) * qterm z 49 := by
    simpa [z] using! qhead_coeffDeltaSqShift_eq_add_missing (t := t) (ht := ht)
  -- Put everything together.
  -- Avoid one huge `simp`/`ring_nf` call to stay within heartbeat budgets.
  calc
    BleadingNum t ht0
        =
          ((Real.pi : ℂ) / (28304640 : ℂ)) *
              ((t : ℂ) ^ (2 : ℕ) * varphi_num z + (t : ℂ) * phi1_num z - phi2_num z) +
            (1 / ((65520 : ℂ) * Real.pi)) * psiI_num z -
              (BleadingLeadingTerm t : ℂ) * (Δ z) ^ (2 : ℕ) := by
              simpa [z] using! hbase
    _ =
          ((Real.pi : ℂ) / (28304640 : ℂ)) *
              ((t : ℂ) ^ (2 : ℕ) * qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) z +
                (t : ℂ) * ((((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
                    qseries (fun n : ℕ => (coeffPhi1Core n : ℂ)) z)) -
                  (((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
                    qseries (fun n : ℕ => (coeffPhi2Core n : ℂ)) z)) +
            (1 / ((65520 : ℂ) * Real.pi)) * rseries psiCoeffFun t +
              (leadingScale t) * qseries (fun n : ℕ => coeffDeltaSqShift n) z := by
              simp [hvarphi, hphi1, hphi2, hpsi, hlead, sub_eq_add_neg, z]
    _ =
          headS t ht0 + BleadingNumRemainder t ht := by
              simp [headS, BleadingNumRemainder, leadingScale, z,
                hsplit_varphi, hsplit_phi1, hsplit_phi2, hsplit_deltaShift, hsplit_psi,
                hmatch_varphi, hmatch_phi1, hmatch_phi2, hmatch_psi, hmatch_delta,
                sub_eq_add_neg]
              ring_nf

/--
Decompose `BleadingNum` into the explicit truncation `Bleading_exact_trunc` plus the remainder
`BleadingNumRemainder`.
-/
public lemma BleadingNum_sub_exact_trunc_eq_remainder (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := t_pos_of_one_le ht
    BleadingNum t ht0 - (Bleading_exact_trunc t : ℂ) = BleadingNumRemainder t ht := by
  intro ht0
  have h : BleadingNum t ht0 = headS t ht0 + BleadingNumRemainder t ht := by
    simpa using! (BleadingNum_eq_headS_add_remainder (t := t) (ht := ht))
  have hhead : headS t ht0 = (Bleading_exact_trunc t : ℂ) :=
    headS_eq_exact_trunc (t := t) (ht0 := ht0)
  simp [h, hhead, sub_eq_add_neg, add_assoc, add_comm]

end SpherePacking.Dim24.AppendixA
