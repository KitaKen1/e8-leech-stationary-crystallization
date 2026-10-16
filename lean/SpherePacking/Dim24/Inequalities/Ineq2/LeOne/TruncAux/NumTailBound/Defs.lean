-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.Denom
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTrunc
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.VarphiQSeries
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PhiDeltaQSeries.Identities
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.SeriesSplit
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.TailBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.EvenReindex
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PowerBounds
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffBounds
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Splitting `ineq2_num` into head and tail

For the `t ≤ 1` case of Appendix A, Lemma `ineq2`, we work with the cleared numerator
`Ineq2LeOneTruncAux.ineq2_num t ht0` (see `TruncAux.Denom`). This file splits the underlying `q`-
and `r`-series at the truncation cutoffs `BleadingCoeffs.QN` and `BleadingCoeffs.N`, defining the
head part `ineq2_num_head` and the tail part `ineq2_num_tail`.

## Main definitions
* `ineq2_num_head`
* `ineq2_num_tail`

## Main statements
* `ineq2_num_eq_head_add_tail`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open ExactTrunc

namespace NumTailBound

/-- Head part of the `ineq2` cleared numerator: truncate the underlying `q`/`r`-series. -/
@[expose] public def ineq2_num_head (t : ℝ) (ht0 : 0 < t) : ℂ :=
  let z : ℍ := it t ht0
  ((t : ℂ) ^ (2 : ℕ)) *
      AppendixA.qhead (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN
    + (t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
        AppendixA.qhead (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN
    + ((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
        AppendixA.qhead (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN
    + (432 / (Real.pi ^ 2) : ℂ) * AppendixA.rhead AppendixA.psiCoeffFun t BleadingCoeffs.N

/-- Tail part of the `ineq2` cleared numerator: the remaining `q`/`r`-series tails. -/
@[expose] public def ineq2_num_tail (t : ℝ) (ht0 : 0 < t) : ℂ :=
  let z : ℍ := it t ht0
  ((t : ℂ) ^ (2 : ℕ)) *
      AppendixA.qtail (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN
    + (t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
        AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN
    + ((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
        AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN
    + (432 / (Real.pi ^ 2) : ℂ) * AppendixA.rtail AppendixA.psiCoeffFun t BleadingCoeffs.N

/-- Split `ineq2_num` into its truncated head and tail parts (`ineq2_num_head + ineq2_num_tail`). -/
public lemma ineq2_num_eq_head_add_tail (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    ineq2_num t ht0 = ineq2_num_head t ht0 + ineq2_num_tail t ht0 := by
  intro ht0
  -- Split each defining series at the truncation cutoff.
  have hvarphi :
      AppendixA.varphi_num (it t ht0) =
        AppendixA.qseries (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) (it t ht0) := by
    simpa using! (AppendixA.varphi_num_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  have hphi1 :
      AppendixA.phi1_num (it t ht0) =
        ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
          AppendixA.qseries (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) := by
    simpa using! (AppendixA.phi1_num_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  have hphi2 :
      AppendixA.phi2_num (it t ht0) =
        (-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
          AppendixA.qseries (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) := by
    simpa using! (AppendixA.phi2_num_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  have hpsi : AppendixA.psiI_num (it t ht0) = AppendixA.rseries AppendixA.psiCoeffFun t := by
    simpa using! (AppendixA.psiI_num_it_eq_rseries_psiCoeffFun (t := t) ht)
  -- Summability for splitting `qseries`/`rseries` into heads and tails.
  have hsVarphi :
      Summable (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ) * AppendixA.qterm (it t ht0) n) := by
    refine Summable.of_norm ?_
    simpa using!
      (AppendixA.summable_norm_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
        (a := AppendixA.coeffVarphiNum) (C := AppendixA.Cvarphi) (k := 20)
        AppendixA.abs_coeffVarphiNum_le)
  have hsPhi1 :
      Summable (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ) * AppendixA.qterm (it t ht0) n) := by
    refine Summable.of_norm ?_
    exact summable_norm_qseries_coeffPhi1Core t ht0 ht
  have hsPhi2 :
      Summable (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ) * AppendixA.qterm (it t ht0) n) := by
    refine Summable.of_norm ?_
    exact summable_norm_qseries_coeffPhi2Core t ht0 ht
  have hsPsi :
      Summable (fun n : ℕ => (AppendixA.psiCoeffFun n : ℂ) * (AppendixA.rC t) ^ n) := by
    refine Summable.of_norm ?_
    simpa using!
      (AppendixA.summable_norm_rseries_of_coeffBound (t := t) (ht0 := ht0)
        (a := AppendixA.psiCoeffFun) (C := (16 : ℝ) ^ (8 : ℕ)) (k := 27)
        (fun n => AppendixA.abs_psiCoeffFun_le (n := n)))
  have hqsplitVarphi :
      qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) =
        qhead (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN +
          qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN :=
    qseries_eq_qhead_add_qtail (fun n => ↑(coeffVarphiNum n)) (it t ht0) BleadingCoeffs.QN
        hsVarphi
  have hqsplitPhi1 :
      qseries (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) =
        qhead (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN +
          qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN :=
    qseries_eq_qhead_add_qtail (fun n => ↑(coeffPhi1Core n)) (it t ht0) BleadingCoeffs.QN
        hsPhi1
  have hqsplitPhi2 :
      qseries (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) =
        qhead (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN +
          qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN :=
    qseries_eq_qhead_add_qtail (fun n => ↑(coeffPhi2Core n)) (it t ht0) BleadingCoeffs.QN
        hsPhi2
  have hrsplit :
      rseries psiCoeffFun t =
        rhead psiCoeffFun t BleadingCoeffs.N + rtail psiCoeffFun t BleadingCoeffs.N := by
    simpa using!
      (rseries_eq_rhead_add_rtail (a := psiCoeffFun) (t := t) (N := BleadingCoeffs.N) hsPsi)
  -- Put everything together.
  dsimp [ineq2_num, ineq2_num_head, ineq2_num_tail]
  rw [hvarphi, hphi1, hphi2, hpsi]
  rw [hqsplitVarphi, hqsplitPhi1, hqsplitPhi2, hrsplit]
  -- Normalize `-phi2_num` into `+ (36/π^2) * (...)`.
  ring_nf


end SpherePacking.Dim24.Ineq2LeOneTruncAux.NumTailBound
