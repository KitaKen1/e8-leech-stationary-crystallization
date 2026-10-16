-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.VarphiQSeries
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesTailBounds
public import SpherePacking.Dim24.Inequalities.VarphiNeg.GeOne.AppendixABridge
public import SpherePacking.Dim24.Inequalities.VarphiNeg.GeOne.TailBound.Geometric
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2Varphi.CertAssemble

/-!
# Tail bound for `t ≥ 1`

Tail bound after truncating the `q`-series at order 50.

## Main statements
* `varphi_tail_bound_geOne`
-/

open scoped BigOperators
open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.VarphiNegGeOne
open AppendixA

/-- Tail bound after truncating the `q`-series at order 50 for `t ≥ 1`.

Paper reference: Appendix A, proof of Lemma `phinonpos`, first case. -/
public theorem varphi_tail_bound_geOne (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    |(varphi_num (it t ht0)).re
        - (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t))|
      ≤ eps * (q t) ^ 6 := by
  set z : ℍ := it t ht0
  set qt : ℝ := q t
  have hqt0 : 0 ≤ qt := (Real.exp_pos _).le
  have hmain :
      |(varphi_num z).re - (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) qt)| ≤
        eps * qt ^ (6 : ℕ) := by
    -- `varphi_num` has the expected `q`-series expansion.
    have hqseries :
        varphi_num z = qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) z := by
      simpa [z, appendixA_varphi_num_eq, appendixA_coeffVarphiNum_eq] using!
        (AppendixA.varphi_num_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
    -- Work with the complex term function `s n = aₙ q^n`.
    let s : ℕ → ℂ := fun n => (coeffVarphiNum n : ℂ) * qterm z n
    have hsNorm : Summable (fun n : ℕ => ‖s n‖) := by
      simpa [s, z] using!
        (AppendixA.summable_norm_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
          (a := coeffVarphiNum) (C := (513200655360 : ℝ)) (k := 20) (fun n => by
            simpa [AppendixA.Cvarphi, appendixA_coeffVarphiNum_eq] using!
              (AppendixA.abs_coeffVarphiNum_le (n := n))))
    have hs : Summable s := Summable.of_norm hsNorm
    have hvarphi : varphi_num z = ∑' n : ℕ, s n := by
      simpa [qseries, s] using! hqseries
    -- Evaluate the truncation polynomial as the finite sum of the first 50 coefficients.
    have hpoly :
        (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) qt) =
          Finset.sum (Finset.range 50) (fun n => (coeffVarphiNum n : ℝ) * qt ^ n) := by
      simpa [qt, appendixA_coeffVarphiNum_eq] using!
        (SpherePacking.Dim24.Ineq2Varphi.varphi_trunc_geOne_eval_eq_sum (t := t))
    -- Define the partial sum at order 50.
    -- Identify its real part with the polynomial evaluation.
    set S50 : ℂ := Finset.sum (Finset.range 50) (fun n => s n)
    have hS50_re :
        S50.re = (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) qt) := by
      calc
        S50.re = Finset.sum (Finset.range 50) (fun n => (coeffVarphiNum n : ℝ) * qt ^ n) := by
          -- Reduce to the termwise fact `((q t : ℂ) ^ n).re = q t ^ n`.
          calc
            S50.re =
                Finset.sum (Finset.range 50) (fun n => (s n).re) := by
                  simp [S50]
            _ = Finset.sum (Finset.range 50) (fun n => (coeffVarphiNum n : ℝ) * qt ^ n) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  have hre : (↑(q t) ^ x : ℂ).re = q t ^ x := by
                    have h := congrArg Complex.re (Complex.ofReal_pow (q t) x).symm
                    refine h.trans ?_
                    simpa using! (Complex.ofReal_re (q t ^ x))
                  simp [s, z, qt, AppendixA.qterm_it, hre]
        _ = (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) qt) := by
          simpa using! hpoly.symm
    -- Split the `q`-series after 50 terms.
    have hsplit : (∑' n : ℕ, s n) = S50 + ∑' m : ℕ, s (m + 50) := by
      simpa [S50] using! (hs.sum_add_tsum_nat_add 50).symm
    have hdiff : varphi_num z - S50 = ∑' m : ℕ, s (m + 50) := by
      grind only
    -- Bound the tail norm by a geometric majorant and use the precomputed `eps` bound.
    have hsNormTail : Summable (fun m : ℕ => ‖s (m + 50)‖) := by
      simpa using! (summable_nat_add_iff 50 (f := fun n : ℕ => ‖s n‖)).2 hsNorm
    have hqt_le : qt ≤ (1 : ℝ) / 535 := by
      simpa [qt] using! q_le_one_div_535 (t := t) ht
    have hρ_le_half :
        AppendixA.powGeomRatio qt 20 50 ≤ (1 : ℝ) / 2 :=
      powGeomRatio_q_le_half_of_q_le_one_div_535 (q' := qt) hqt_le
    have hρ_lt_one : AppendixA.powGeomRatio qt 20 50 < 1 :=
      lt_of_le_of_lt hρ_le_half (by norm_num)
    set ρ : ℝ := AppendixA.powGeomRatio qt 20 50
    have hρ0 : 0 ≤ ρ := by
      dsimp [ρ, AppendixA.powGeomRatio]
      exact mul_nonneg hqt0 (pow_nonneg (by positivity) _)
    have hsPowGeom :
        Summable (fun m : ℕ => AppendixA.powGeomTerm qt 20 (m + 50)) := by
      have hdom :
          ∀ m : ℕ,
            AppendixA.powGeomTerm qt 20 (m + 50) ≤ AppendixA.powGeomTerm qt 20 50 * ρ ^ m := by
        intro m
        simpa [ρ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
          (AppendixA.powGeomTerm_add_le (q := qt) (k := 20) (N := 50) (m := m) hqt0)
      have hgeom_summable : Summable (fun m : ℕ => AppendixA.powGeomTerm qt 20 50 * ρ ^ m) := by
        refine (summable_geometric_of_lt_one hρ0 (by simpa [ρ] using! hρ_lt_one)).mul_left
          (AppendixA.powGeomTerm qt 20 50)
      refine
        Summable.of_nonneg_of_le
          (fun m => AppendixA.powGeomTerm_nonneg (q := qt) (k := 20) (n := m + 50) hqt0) hdom
          hgeom_summable
    have hsMajor :
        Summable (fun m : ℕ => (513200655360 : ℝ) * AppendixA.powGeomTerm qt 20 (m + 50)) :=
      hsPowGeom.mul_left (513200655360 : ℝ)
    have hdomNorm :
        ∀ m : ℕ, ‖s (m + 50)‖ ≤ (513200655360 : ℝ) * AppendixA.powGeomTerm qt 20 (m + 50) := by
      intro m
      have hcoeff :
          |(coeffVarphiNum (m + 50) : ℝ)| ≤
            (513200655360 : ℝ) * (((m + 50 + 1 : ℕ) : ℝ) ^ 20) := by
        simpa [AppendixA.Cvarphi, appendixA_coeffVarphiNum_eq] using!
          (AppendixA.abs_coeffVarphiNum_le (n := m + 50))
      have hpow0 : 0 ≤ qt ^ (m + 50) := pow_nonneg hqt0 _
      have hnorm_q : ‖qterm z (m + 50)‖ = qt ^ (m + 50) := by
        simpa [z, qt, appendixA_q_eq] using!
          (AppendixA.norm_qterm_it (t := t) (ht := ht0) (n := m + 50))
      have hnorm_a :
          ‖(coeffVarphiNum (m + 50) : ℂ)‖ = |(coeffVarphiNum (m + 50) : ℝ)| := by
        simp
      calc
        ‖s (m + 50)‖
            = ‖(coeffVarphiNum (m + 50) : ℂ)‖ * ‖qterm z (m + 50)‖ := by
                simp [s]
        _ = |(coeffVarphiNum (m + 50) : ℝ)| * qt ^ (m + 50) := by
              rw [hnorm_a, hnorm_q]
        _ ≤ (513200655360 * (((m + 50 + 1 : ℕ) : ℝ) ^ 20)) * qt ^ (m + 50) := by
              exact mul_le_mul_of_nonneg_right hcoeff hpow0
        _ = (513200655360 : ℝ) * ((((m + 50 + 1 : ℕ) : ℝ) ^ 20) * qt ^ (m + 50)) := by ring
        _ = (513200655360 : ℝ) * AppendixA.powGeomTerm qt 20 (m + 50) := by
              dsimp [AppendixA.powGeomTerm]
              norm_num
    have h2 :
        (∑' m : ℕ, ‖s (m + 50)‖) ≤
          ∑' m : ℕ, (513200655360 : ℝ) * AppendixA.powGeomTerm qt 20 (m + 50) :=
      hasSum_le hdomNorm hsNormTail.hasSum hsMajor.hasSum
    have h3 :
        (∑' m : ℕ, (513200655360 : ℝ) * AppendixA.powGeomTerm qt 20 (m + 50)) =
          (513200655360 : ℝ) * (∑' m : ℕ, AppendixA.powGeomTerm qt 20 (m + 50)) := by
      simp [tsum_mul_left]
    have h4 :
        (513200655360 : ℝ) * (∑' m : ℕ, AppendixA.powGeomTerm qt 20 (m + 50)) ≤
          eps * qt ^ (6 : ℕ) := by
      -- The precomputed bound is stated with index `(50 + m)`.
      simpa [qt, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
        powGeomTail_bound_eps_scaled (t := t) ht
    have htail_norm :
        ‖∑' m : ℕ, s (m + 50)‖ ≤ eps * qt ^ (6 : ℕ) := by
      have h1 : ‖∑' m : ℕ, s (m + 50)‖ ≤ ∑' m : ℕ, ‖s (m + 50)‖ :=
        norm_tsum_le_tsum_norm hsNormTail
      exact le_trans (le_trans h1 (le_trans h2 (le_of_eq h3))) h4
    have hS50_re' :
        (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) qt) = S50.re := hS50_re.symm
    have hrewrite :
        (varphi_num z).re - (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) qt) =
          (varphi_num z - S50).re := by
      simp [Complex.sub_re, hS50_re']
    calc
      |(varphi_num z).re - (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) qt)|
          = |(varphi_num z - S50).re| := by simp [hrewrite]
      _ ≤ ‖varphi_num z - S50‖ := Complex.abs_re_le_norm _
      _ = ‖∑' m : ℕ, s (m + 50)‖ := by simp [hdiff]
      _ ≤ eps * qt ^ (6 : ℕ) := htail_norm
  simpa [z, qt] using! hmain

end SpherePacking.Dim24.VarphiNegGeOne
