module
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
public import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.AbsBoundQ
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.List.GetD
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesTailBounds
import SpherePacking.Dim24.Inequalities.AppendixA.RSeriesTailBounds


/-!
# Geometric ratio bounds for tail estimates

This file provides a small interface for the geometric-ratio bounds used downstream in the
`GeOne` tail numerics, mostly as wrappers around the canonical Appendix A lemmas.
-/

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

/-! ## Geometric ratio bounds -/

/-- Wrapper for the Appendix A bound `powGeomRatio q 20 50 ≤ 1/2` under `q ≤ 1/535`. -/
public lemma powGeomRatio_q_le_half_of_q_le_one_div_535 {q' : ℝ}
    (hq : q' ≤ (1 : ℝ) / 535) :
    AppendixA.powGeomRatio q' 20 50 ≤ (1 : ℝ) / 2 := by
  exact AppendixA.powGeomRatio_q_le_half_of_q_le_one_div_535 (q' := q') hq

/-- Wrapper for the Appendix A bound `powGeomRatio r 20 100 ≤ 1/2` under `r ≤ 1/23`. -/
public lemma powGeomRatio_r_le_half_of_r_le_one_div_23 {r' : ℝ}
    (hr : r' ≤ (1 : ℝ) / 23) :
    AppendixA.powGeomRatio r' 20 100 ≤ (1 : ℝ) / 2 :=
  AppendixA.powGeomRatio_r_le_half_of_r_le_one_div_23 (r' := r') hr

lemma powGeomRatio_one_div_23_27_100_le_half :
    AppendixA.powGeomRatio ((1 : ℝ) / 23) 27 100 ≤ (1 : ℝ) / 2 := by
  norm_num [AppendixA.powGeomRatio]

/-- Variant of the geometric ratio bound for exponent `27`, under `r ≤ 1/23`. -/
public lemma powGeomRatio_r_le_half_of_r_le_one_div_23_27 {r' : ℝ}
    (hr : r' ≤ (1 : ℝ) / 23) :
    AppendixA.powGeomRatio r' 27 100 ≤ (1 : ℝ) / 2 := by
  exact (AppendixA.powGeomRatio_mono_left (q := r') (q' := (1 : ℝ) / 23) hr 27 100).trans
    powGeomRatio_one_div_23_27_100_le_half

/--
Certified rational inequality used in the `varphi` tail estimate: the explicit constant is
`< eps/2`.
-/
public lemma const_varphi_tail_lt_half_eps :
    ((2 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 535) ^ (44 : ℕ)) <
      ((10 : ℚ) ^ (-50 : ℤ)) / 2 := by
  set_option maxRecDepth 6000 in
  norm_num

/--
Certified rational inequality used in the `ψS` tail estimate (exponent `20`): the explicit constant
is `< eps/2`.
-/
public lemma const_psi_tail_lt_half_eps :
    ((2 : ℚ) * ((44 : ℚ) * (16 : ℚ) * (24 : ℚ) ^ (7 : ℕ)) * (101 : ℚ) ^ (20 : ℕ) *
        ((1 : ℚ) / 23) ^ (88 : ℕ)) <
      ((10 : ℚ) ^ (-50 : ℤ)) / 2 := by
  set_option maxRecDepth 6000 in
  norm_num

/--
Certified rational inequality used in the `ψS` tail estimate (exponent `27`): the explicit constant
is `< eps/2`.
-/
public lemma const_psi27_tail_lt_half_eps :
    ((2 : ℚ) * ((44 : ℚ) * (16 : ℚ) ^ (8 : ℕ)) * (101 : ℚ) ^ (27 : ℕ) *
        ((1 : ℚ) / 23) ^ (88 : ℕ)) <
      ((10 : ℚ) ^ (-50 : ℤ)) / 2 := by
  set_option maxRecDepth 6000 in
  norm_num


end SpherePacking.Dim24
