-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.DenomReduction.Numerators
import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable
import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.VarphiQSeries
import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
import SpherePacking.Dim24.Inequalities.AppendixA.AbsBoundQ
import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumCert.SumRange
import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumCert.VerifyThetaH4
import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumCert.VerifyH4H2
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.List.GetD
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.TailNumerics.GeomRatio
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2Varphi.CertAssemble
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.TailNumerics.Majorant
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffBounds

/-!
# Tail bound for truncating `varphi_num` (`1 ≤ t` case)

This file bounds the `q`-series tail of `varphi_num (it t)` after truncating at order `50`, in the
case `1 ≤ t`.

## Main statements
* `varphi_num_trunc_geOne_norm_sub_le`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

namespace Ineq2Varphi

open scoped BigOperators

/-!
## Tail bound for `varphi_num`
-/

/--
Tail bound for truncating the `varphi_num` `q`-series at order `50`, for `1 ≤ t`.

This controls `‖varphi_num (it t) - varphi_trunc_geOne.eval₂ _ (q t)‖` by `(eps/2) * q(t)^6`.
-/
public lemma varphi_num_trunc_geOne_norm_sub_le (t : ℝ) (ht : 1 ≤ t) :
    ‖varphi_num (it t (lt_of_lt_of_le (by norm_num) ht)) -
        ((AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t) : ℝ) : ℂ)‖
      ≤ (eps / 2) * (q t) ^ (6 : ℕ) := by
  set ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  set z : ℍ := it t ht0
  set a : ℝ := AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)
  -- Abbreviate the series terms.
  set f : ℕ → ℂ := fun n => (AppendixA.coeffVarphiNum n : ℂ) * AppendixA.qterm z n
  have hs_norm :
      Summable (fun n : ℕ => ‖f n‖) := by
    -- Use the coefficient majorant `Cvarphi * (n+1)^20`.
    simpa [f, z] using!
      (AppendixA.summable_norm_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
        (a := AppendixA.coeffVarphiNum) (C := Cvarphi) (k := 20)
        (fun n => by
          simpa [Cvarphi] using! (AppendixA.abs_coeffVarphiNum_le (n := n))))
  have hs : Summable f := Summable.of_norm hs_norm
  have hvarphi : varphi_num z = ∑' n : ℕ, f n := by
    -- `varphi_num z` is exactly this `qseries`.
    simpa [z, f, Dim24.varphi_num, AppendixA.varphi_num, AppendixA.qseries] using!
      (AppendixA.varphi_num_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  -- Identify the truncation polynomial `a` with the finite sum of the first 50 terms.
  have ha :
      ((a : ℝ) : ℂ) = (∑ n ∈ Finset.range 50, f n) := by
    have hsumR :
        a = ∑ n ∈ Finset.range 50, (AppendixA.coeffVarphiNum n : ℝ) * (q t) ^ n := by
      simpa [a] using! (varphi_trunc_geOne_eval_eq_sum (t := t))
    -- Rewrite the RHS as a complex finite sum, then show termwise equality with `f`.
    calc
      ((a : ℝ) : ℂ)
          = ((∑ n ∈ Finset.range 50, (AppendixA.coeffVarphiNum n : ℝ) * (q t) ^ n : ℝ) : ℂ) := by
              simp [hsumR]
      _ = ∑ n ∈ Finset.range 50, ((AppendixA.coeffVarphiNum n : ℝ) * (q t) ^ n : ℂ) := by
            simp
      _ = ∑ n ∈ Finset.range 50, f n := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hqterm : AppendixA.qterm z n = (q t : ℂ) ^ n := by
              simpa [z] using! (AppendixA.qterm_it (t := t) (ht := ht0) (n := n))
            -- `f n` is a real scalar times a real power, hence equal to the real-coerced term.
            simp [f, hqterm]
  -- Split the full `tsum` into the first 50 terms and the tail.
  have hsplit :
      (∑' n : ℕ, f n) = (∑ n ∈ Finset.range 50, f n) + ∑' n : ℕ, f (n + 50) := by
    -- Standard `tsum` decomposition over `ℕ`.
    simpa using! (Summable.sum_add_tsum_nat_add 50 hs).symm
  -- The tail is controlled by the coefficient majorant and the geometric tail bound.
  have htail_le :
      ‖∑' n : ℕ, f (n + 50)‖ ≤ (eps / 2) * (q t) ^ (6 : ℕ) := by
    have hs_norm_tail : Summable (fun n : ℕ => ‖f (n + 50)‖) :=
      hs_norm.comp_injective (add_left_injective 50)
    have hnorm_le :
        ‖∑' n : ℕ, f (n + 50)‖ ≤ ∑' n : ℕ, ‖f (n + 50)‖ :=
      norm_tsum_le_tsum_norm hs_norm_tail
    -- Bound each term using `abs_coeffVarphiNum_le` and `‖qterm(it)‖ = q^n`.
    have hterm_le : ∀ n : ℕ, ‖f (n + 50)‖ ≤ Cvarphi * AppendixA.powGeomTerm (q t) 20 (50 + n) := by
      intro n
      have hq0 : 0 ≤ q t := (Real.exp_pos _).le
      have hqterm : ‖AppendixA.qterm z (n + 50)‖ = (q t) ^ (n + 50) := by
        simpa [z] using! (AppendixA.norm_qterm_it (t := t) (ht := ht0) (n := n + 50))
      have hcoeff := AppendixA.abs_coeffVarphiNum_le (n := n + 50)
      have hpow0 : 0 ≤ (q t) ^ (n + 50) := pow_nonneg hq0 _
      have hnorm_a :
          ‖(AppendixA.coeffVarphiNum (n + 50) : ℂ)‖ =
            |(AppendixA.coeffVarphiNum (n + 50) : ℝ)| := by
        simp
      calc
        ‖f (n + 50)‖ =
            ‖(AppendixA.coeffVarphiNum (n + 50) : ℂ)‖ * ‖AppendixA.qterm z (n + 50)‖ := by
              simp [f]
        _ = |(AppendixA.coeffVarphiNum (n + 50) : ℝ)| * (q t) ^ (n + 50) := by
              rw [hnorm_a, hqterm]
        _ ≤ (Cvarphi * (((n + 50 + 1 : ℕ) : ℝ) ^ 20)) * (q t) ^ (n + 50) :=
              mul_le_mul_of_nonneg_right hcoeff hpow0
        _ = Cvarphi * ((((n + 50 + 1 : ℕ) : ℝ) ^ 20) * (q t) ^ (n + 50)) := by ring
        _ = Cvarphi * AppendixA.powGeomTerm (q t) 20 (n + 50) := by
              dsimp [AppendixA.powGeomTerm]
              norm_num
        _ = Cvarphi * AppendixA.powGeomTerm (q t) 20 (50 + n) := by
              simp [Nat.add_comm]
    -- Sum the termwise bounds.
    have hsum_le :
        (∑' n : ℕ, ‖f (n + 50)‖) ≤
          Cvarphi * (∑' n : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + n)) := by
      -- Summability of the majorant tail `powGeomTerm`.
      have hs_pow :
          Summable (fun n : ℕ => AppendixA.powGeomTerm (q t) 20 (50 + n)) := by
        have hq0 : 0 ≤ q t := (Real.exp_pos _).le
        have hqle : q t ≤ (1 : ℝ) / 535 := by
          simpa [q, AppendixA.q, mul_assoc] using! (AppendixA.q_le_one_div_535_of_one_le (t := t) ht)
        have hρ_le_half : AppendixA.powGeomRatio (q t) 20 50 ≤ (1 : ℝ) / 2 :=
          powGeomRatio_q_le_half_of_q_le_one_div_535 (q' := q t) hqle
        have hρ_lt_one : AppendixA.powGeomRatio (q t) 20 50 < 1 :=
          lt_of_le_of_lt hρ_le_half (by norm_num)
        set ρ : ℝ := AppendixA.powGeomRatio (q t) 20 50
        have hρ0 : 0 ≤ ρ := by
          dsimp [ρ, AppendixA.powGeomRatio]
          exact mul_nonneg hq0 (pow_nonneg (by positivity) _)
        have hdom :
            ∀ n : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + n) ≤ AppendixA.powGeomTerm (q t) 20 50 *
              ρ ^ n :=
              by
          intro n
          simpa [ρ] using! (AppendixA.powGeomTerm_add_le (q := q t) (k := 20) (N := 50) (m := n) hq0)
        have hgeom_summable :
            Summable (fun n : ℕ => AppendixA.powGeomTerm (q t) 20 50 * ρ ^ n) := by
          exact
            (summable_geometric_of_lt_one hρ0 hρ_lt_one).mul_left
              (AppendixA.powGeomTerm (q t) 20 50)
        have hnonneg : ∀ n : ℕ, 0 ≤ AppendixA.powGeomTerm (q t) 20 (50 + n) := by
          intro n
          exact AppendixA.powGeomTerm_nonneg (q := q t) (k := 20) (n := 50 + n) hq0
        exact Summable.of_nonneg_of_le hnonneg hdom hgeom_summable
      have hs_powC :
          Summable (fun n : ℕ => Cvarphi * AppendixA.powGeomTerm (q t) 20 (50 + n)) :=
        hs_pow.mul_left Cvarphi
      have hs_norm_tail' : Summable (fun n : ℕ => ‖f (n + 50)‖) :=
        hs_norm.comp_injective (add_left_injective 50)
      have hmono :
          (∑' n : ℕ, ‖f (n + 50)‖) ≤ ∑' n : ℕ, Cvarphi * AppendixA.powGeomTerm (q t) 20 (50 + n) :=
        hs_norm_tail'.tsum_le_tsum (fun n => hterm_le n) hs_powC
      -- Pull out the constant from the RHS.
      have hconst :
          (∑' n : ℕ, Cvarphi * AppendixA.powGeomTerm (q t) 20 (50 + n)) =
            Cvarphi * (∑' n : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + n)) := by
        exact tsum_mul_left
      exact le_trans hmono (le_of_eq hconst)
    have hmajor :
        Cvarphi * (∑' n : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + n)) ≤ (eps / 2) *
          (q t) ^ (6 : ℕ) :=
      varphi_majorant_tail_bound (t := t) ht
    exact le_trans (le_trans hnorm_le hsum_le) hmajor
  -- Assemble the estimate `‖varphi_num z - a‖ ≤ ...`.
  simp_all

end SpherePacking.Dim24.Ineq2Varphi
