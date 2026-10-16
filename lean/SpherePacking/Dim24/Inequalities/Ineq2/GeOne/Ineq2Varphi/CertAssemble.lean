-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable
import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
import SpherePacking.Dim24.Inequalities.AppendixA.AbsBoundQ
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.QSeriesHelpers
import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumCert.SumRange
import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumCert.VerifyThetaH4
import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumCert.VerifyH4H2
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.List.GetD
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import SpherePacking.Dim24.Inequalities.Certificate.ZVArith
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2Varphi.CertData
import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.CoeffsVarphiInt


/-!
# Assembling the `varphi_num` truncation certificate

This file packages the list-based certificate identities needed to evaluate the truncation
polynomial `varphi_trunc_geOne` as a finite sum of the certified coefficients `coeffVarphiNum`.

## Main statements
* `varphi_trunc_geOne_eval_eq_sum`
-/

noncomputable section

namespace SpherePacking.Dim24

open SpherePacking.Dim24.CertificateZV

namespace Ineq2Varphi
open AppendixA

lemma coeffVarphiNum_first50 :
    List.ofFn (fun i : Fin 50 => coeffVarphiNum i.1) = AppendixA.varphi_trunc_geOne_coeffs := by
  have hlenL : coeffVarphiNumListZV.length = 50 := by
    simp [coeffVarphiNumListZV, addZV, NVarphi]
  have hcoeff :
      List.ofFn (fun i : Fin 50 => coeffVarphiNum i.1) =
        List.map (fun z : ℤ => (z : ℚ)) coeffVarphiNumListZV := by
    refine List.ext_getElem (by simp [hlenL]) ?_
    intro n hn1 hn2
    have hn : n < NVarphi := by simpa [NVarphi] using! hn1
    have hlhs : (List.ofFn (fun i : Fin 50 => coeffVarphiNum i.1))[n] = coeffVarphiNum n := by
      simpa using! (List.getElem_ofFn (f := fun i : Fin 50 => coeffVarphiNum i.1) (i := n) hn1)
    have hrhs :
        (List.map (fun z : ℤ => (z : ℚ)) coeffVarphiNumListZV)[n] =
          ((coeffVarphiNumListZV[n]) : ℚ) := by
      exact List.getElem_map _
    have hcast : (coeffVarphiNum n) = (coeffVarphiNumZV n : ℚ) := coeffVarphiNum_eq_cast n
    have hZ : coeffVarphiNumZV n = coeffVarphiNumListZV[n] := by
      have hnlen : n < coeffVarphiNumListZV.length := by simpa [hlenL, NVarphi] using! hn
      have hgetD :
          coeffZV coeffVarphiNumListZV n = coeffVarphiNumListZV[n] := by
        simpa [coeffZV] using!
          (List.getD_eq_getElem (l := coeffVarphiNumListZV) (d := (0 : ℤ)) hnlen)
      have hcoeffZ : coeffZV coeffVarphiNumListZV n = coeffVarphiNumZV n :=
        (coeffZV_coeffVarphiNumList_eq (n := n) hn)
      -- eliminate `coeffZV` and conclude
      exact hcoeffZ.symm.trans hgetD
    -- Finish without expanding the `ofFn` list into 50 explicit elements.
    grind only
  calc
    List.ofFn (fun i : Fin 50 => coeffVarphiNum i.1)
        = List.map (fun z : ℤ => (z : ℚ)) coeffVarphiNumListZV := hcoeff
    _ = List.map (fun z : ℤ => (z : ℚ)) varphi_trunc_geOne_coeffsZV := by
          simpa using! congrArg (List.map (fun z : ℤ => (z : ℚ))) coeffVarphiNumListZV_eq_expected
    _ = AppendixA.varphi_trunc_geOne_coeffs := by
          simpa using! (AppendixA.varphi_trunc_geOne_coeffs_eq_map).symm

/-- Evaluate `varphi_trunc_geOne` at `q t` as a finite sum over the first 50 coefficients. -/
public lemma varphi_trunc_geOne_eval_eq_sum (t : ℝ) :
    (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) =
      Finset.sum (Finset.range 50) (fun n => (coeffVarphiNum n : ℝ) * (q t) ^ n) := by
  -- Evaluate the truncation polynomial as a finite sum over its coefficient list.
  have hbase :
      (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) =
        Finset.sum (Finset.range AppendixA.varphi_trunc_geOne_coeffs.length) (fun n =>
          (algebraMap ℚ ℝ) (AppendixA.varphi_trunc_geOne_coeffs.getD n 0) * (q t) ^ n) := by
    simpa [AppendixA.varphi_trunc_geOne] using!
      (AppendixA.eval₂_polyOfCoeffs_eq_sum_range_getD
        (l := AppendixA.varphi_trunc_geOne_coeffs) (x := q t))
  have hlen : AppendixA.varphi_trunc_geOne_coeffs.length = 50 := by
    simp [AppendixA.varphi_trunc_geOne_coeffs]
  have hcoeffs :
      AppendixA.varphi_trunc_geOne_coeffs = List.ofFn (fun i : Fin 50 => coeffVarphiNum i.1) := by
    simpa using! coeffVarphiNum_first50.symm
  -- Rewrite the coefficient list to `List.ofFn` and simplify the `getD` coefficients.
  have hbase' :
      (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) =
        Finset.sum (Finset.range 50) (fun n =>
          (algebraMap ℚ ℝ)
              ((List.ofFn (fun i : Fin 50 => coeffVarphiNum i.1)).getD n 0) *
            (q t) ^ n) := by
    simpa [hlen, hcoeffs] using! hbase
  -- Replace each `getD` coefficient with `coeffVarphiNum n`.
  have hgetD :
      (Finset.sum (Finset.range 50) fun n =>
          (algebraMap ℚ ℝ)
              ((List.ofFn (fun i : Fin 50 => coeffVarphiNum i.1)).getD n 0) *
            (q t) ^ n)
        =
        Finset.sum (Finset.range 50) (fun n => (coeffVarphiNum n : ℝ) * (q t) ^ n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn' : n < 50 := by simpa [Finset.mem_range] using! hn
    have hnlen : n < (List.ofFn (fun i : Fin 50 => coeffVarphiNum i.1)).length :=
      lt_of_lt_of_eq hn' (Eq.symm (List.length_ofFn (f := fun i : Fin 50 => coeffVarphiNum i.1)))
    have hget :
        (List.ofFn (fun i : Fin 50 => coeffVarphiNum i.1)).getD n 0 = coeffVarphiNum n := by
      grind only [= List.getD_eq_getElem?_getD, = List.getElem?_ofFn, = Option.getD_some]
    -- Cast to `ℝ` and conclude the termwise equality.
    have hcast : (algebraMap ℚ ℝ) ((List.ofFn (fun i : Fin 50 => coeffVarphiNum i.1)).getD n 0) =
        (coeffVarphiNum n : ℝ) := by
      simpa [hget]
    exact congrArg (fun c : ℝ => c * (q t) ^ n) hcast
  exact hbase'.trans hgetD


end SpherePacking.Dim24.Ineq2Varphi
