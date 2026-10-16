-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.RBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.AppendixA.Trunc
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.TruncRewrite
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.DenomReduction.Numerators
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.TailNumerics.GeomRatio
import Mathlib.Data.List.GetD
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2PsiSnum.RSeriesOps
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2PsiSnum.SummabilityReindex

/-!
# Truncation evaluation rewrites

For the `t ≥ 1` case of Appendix A, Lemma `ineq2`, we rewrite the evaluation of the truncation
polynomial `ineq2_trunc_geOne` at `r t` in terms of the `varphi` truncation (in `q t`) and a finite
sum `psiSnum_trunc_eval` built from the first `N = 100` coefficients of `psiS_num`.

## Main statements
* `ineq2_trunc_geOne_eval_eq_varphi_sub_cPiLower10_mul_psiSnum_trunc`
* `psiS_num_trunc_geOne_norm_sub_le`
-/

open UpperHalfPlane

noncomputable section
namespace SpherePacking.Dim24
open AppendixA

private lemma sum_range_two_mul (M : ℕ) (x : ℝ) (f : ℕ → ℝ) :
    (Finset.sum (Finset.range (2 * M)) fun n =>
          (if n % 2 = 0 then f (n / 2) else 0) * x ^ n) =
      Finset.sum (Finset.range M) fun m => f m * x ^ (2 * m) := by
  induction M with
  | zero =>
      simp
  | succ M ih =>
      set g : ℕ → ℝ := fun n => (if n % 2 = 0 then f (n / 2) else 0) * x ^ n
      have ih' :
          Finset.sum (Finset.range (2 * M)) g =
            Finset.sum (Finset.range M) (fun m => f m * x ^ (2 * m)) := by
        simpa [g] using! ih
      have hR :
          Finset.sum (Finset.range (Nat.succ M)) (fun m => f m * x ^ (2 * m)) =
            Finset.sum (Finset.range M) (fun m => f m * x ^ (2 * m)) + f M * x ^ (2 * M) := by
        simp [Finset.sum_range_succ]
      have h2 : 2 * Nat.succ M = 2 * M + 2 := by
        simpa using! (Nat.mul_succ 2 M)
      calc
        Finset.sum (Finset.range (2 * Nat.succ M)) g
            = Finset.sum (Finset.range (2 * M + 2)) g := by
                simp [h2]
        _ = Finset.sum (Finset.range (2 * M + 1)) g + g (2 * M + 1) := by
              simp [Finset.sum_range_succ]
        _ = (Finset.sum (Finset.range (2 * M)) g + g (2 * M)) + g (2 * M + 1) := by
              simp [Finset.sum_range_succ]
        _ = Finset.sum (Finset.range (2 * M)) g + g (2 * M) + g (2 * M + 1) := by
              simp [add_assoc]
        _ = Finset.sum (Finset.range (2 * M)) g + f M * x ^ (2 * M) := by
              simp [g]
        _ = Finset.sum (Finset.range (Nat.succ M)) (fun m => f m * x ^ (2 * m)) := by
              -- Rewrite the first sum using `ih'`, then fold back using `sum_range_succ`.
              rw [hR]
              simp [ih']

private lemma ineq2_trunc_geOne_eval₂_eq_sum_expected (t : ℝ) :
    (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)) =
      ∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
        (algebraMap ℚ ℝ) (Ineq2GeOneCoeffs.ineq2_trunc_geOne_coeffs_expected.getD n 0) *
          (r t) ^ n := by
  have hlen : AppendixA.ineq2_trunc_geOne_coeffs.length = Ineq2GeOneCoeffs.N := by
    decide
  simpa [ineq2_trunc_geOne, AppendixA.ineq2_trunc_geOne, hlen,
    Ineq2GeOneCoeffs.ineq2_trunc_geOne_coeffs_eq_expected] using!
    (AppendixA.eval₂_polyOfCoeffs_eq_sum_range_getD
      (l := AppendixA.ineq2_trunc_geOne_coeffs) (x := r t))

private lemma sum_expected_decompose (t : ℝ) :
    (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
          (algebraMap ℚ ℝ) (Ineq2GeOneCoeffs.ineq2_trunc_geOne_coeffs_expected.getD n 0) *
            (r t) ^ n)
      =
      (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
            ((algebraMap ℚ ℝ)
                (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0)) *
              (r t) ^ n)
        -
        (Ineq2GeOneCoeffs.cPiLower10Q : ℝ) *
          (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
              ((Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 : ℚ) : ℝ) * (r t) ^ n) := by
  have hrewrite :
      (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
            (algebraMap ℚ ℝ)
                (Ineq2GeOneCoeffs.ineq2_trunc_geOne_coeffs_expected.getD n 0) *
              (r t) ^ n)
        =
        ∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
          (((algebraMap ℚ ℝ)
                  (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0)) -
              (Ineq2GeOneCoeffs.cPiLower10Q : ℝ) *
                ((Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 : ℚ) : ℝ)) *
            (r t) ^ n := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn' : n < Ineq2GeOneCoeffs.N := by simpa [Finset.mem_range] using! hn
    have hget :
        Ineq2GeOneCoeffs.ineq2_trunc_geOne_coeffs_expected.getD n 0 =
          (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0) -
            Ineq2GeOneCoeffs.cPiLower10Q * (Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 : ℚ) :=
      Ineq2GeOneCoeffs.ineq2_trunc_geOne_coeffs_expected_getD (n := n) hn'
    have hmap := congrArg (algebraMap ℚ ℝ) hget
    have hcast :
        (algebraMap ℚ ℝ)
            (Ineq2GeOneCoeffs.ineq2_trunc_geOne_coeffs_expected.getD n 0) =
          (algebraMap ℚ ℝ)
              (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0) -
            (Ineq2GeOneCoeffs.cPiLower10Q : ℝ) *
              ((Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 : ℚ) : ℝ) := by
      simpa [map_sub, map_mul, mul_assoc] using! hmap
    exact congrArg (fun c : ℝ => c * (r t) ^ n) hcast
  have hdist :
      (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
          (((algebraMap ℚ ℝ)
                    (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0)) -
                (Ineq2GeOneCoeffs.cPiLower10Q : ℝ) *
                  ((Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 : ℚ) : ℝ)) *
              (r t) ^ n)
        =
        (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
            (algebraMap ℚ ℝ)
                  (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0) *
                (r t) ^ n)
          -
          (Ineq2GeOneCoeffs.cPiLower10Q : ℝ) *
            (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
                ((Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 : ℚ) : ℝ) * (r t) ^ n) := by
    simp [sub_mul, mul_assoc, Finset.sum_sub_distrib, Finset.mul_sum]
  exact hrewrite.trans hdist

private lemma varphi_part_sum_eq_eval₂ (t : ℝ) :
    (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
          ((algebraMap ℚ ℝ)
              (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0)) *
            (r t) ^ n)
      =
      (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) := by
  have hq : q t = (r t) ^ (2 : ℕ) := by
    exact q_eq_r_sq t
  have hlen50 : AppendixA.varphi_trunc_geOne_coeffs.length = 50 := by
    decide
  -- Reindex by even indices using the generic lemma `sum_range_two_mul`.
  have hN : Ineq2GeOneCoeffs.N = 2 * 50 := by simp [Ineq2GeOneCoeffs.N]
  set f₀ : ℕ → ℝ := fun m => (algebraMap ℚ ℝ) (AppendixA.varphi_trunc_geOne_coeffs.getD m 0)
  have hsum0 :
      (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
            (algebraMap ℚ ℝ)
                (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0) *
              (r t) ^ n)
        =
        Finset.sum (Finset.range (2 * 50)) (fun n =>
            (if n % 2 = 0 then f₀ (n / 2) else 0) * (r t) ^ n) := by
    grind only [= map_zero]
  have hsum1 :
      Finset.sum (Finset.range (2 * 50)) (fun n =>
            (if n % 2 = 0 then f₀ (n / 2) else 0) * (r t) ^ n)
        =
        Finset.sum (Finset.range 50) (fun m => f₀ m * (r t) ^ (2 * m)) :=
    sum_range_two_mul (M := 50) (x := r t) (f := f₀)
  have hpow : ∀ m : ℕ, (q t) ^ m = (r t) ^ (2 * m) := by
    intro m
    rw [hq]
    simp [pow_mul]
  have hRHS :
      (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) =
        ∑ m ∈ Finset.range 50,
          (algebraMap ℚ ℝ) (AppendixA.varphi_trunc_geOne_coeffs.getD m 0) * (q t) ^ m := by
    simpa [AppendixA.varphi_trunc_geOne, hlen50] using!
      (AppendixA.eval₂_polyOfCoeffs_eq_sum_range_getD
        (l := AppendixA.varphi_trunc_geOne_coeffs) (x := q t))
  calc
    (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
          (algebraMap ℚ ℝ)
              (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0) *
            (r t) ^ n)
        =
        Finset.sum (Finset.range (2 * 50)) (fun n =>
            (if n % 2 = 0 then f₀ (n / 2) else 0) * (r t) ^ n) := hsum0
    _ =
        Finset.sum (Finset.range 50) (fun m => f₀ m * (r t) ^ (2 * m)) := hsum1
    _ =
        ∑ m ∈ Finset.range 50,
          (algebraMap ℚ ℝ) (AppendixA.varphi_trunc_geOne_coeffs.getD m 0) * (q t) ^ m := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          simp [f₀, hpow]
    _ = (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) := by
          exact hRHS.symm

/-- Rewrite `ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)` as the `varphi` truncation in `q t`
minus `cPiLower10` times the truncated `psiS_num` sum `psiSnum_trunc_eval t`. -/
public lemma ineq2_trunc_geOne_eval_eq_varphi_sub_cPiLower10_mul_psiSnum_trunc (t : ℝ) :
    (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t)) =
      (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) -
        cPiLower10 * psiSnum_trunc_eval (t := t) := by
  have hpsi_def :
      (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
          ((Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 : ℚ) : ℝ) * (r t) ^ n)
        = psiSnum_trunc_eval (t := t) := by
    simp [psiSnum_trunc_eval]
  calc
    (ineq2_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (r t))
        =
        (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
            (algebraMap ℚ ℝ)
                (Ineq2GeOneCoeffs.ineq2_trunc_geOne_coeffs_expected.getD n 0) *
              (r t) ^ n) := ineq2_trunc_geOne_eval₂_eq_sum_expected (t := t)
    _ =
        (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
            ((algebraMap ℚ ℝ)
                (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0)) *
              (r t) ^ n)
          -
          (Ineq2GeOneCoeffs.cPiLower10Q : ℝ) *
            (∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
                ((Ineq2GeOneCoeffs.psiSnumCoeffs.getD n 0 : ℚ) : ℝ) * (r t) ^ n) :=
          sum_expected_decompose (t := t)
    _ =
        (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) -
          (Ineq2GeOneCoeffs.cPiLower10Q : ℝ) * psiSnum_trunc_eval (t := t) := by
          rw [varphi_part_sum_eq_eval₂ (t := t), hpsi_def]
    _ =
        (AppendixA.varphi_trunc_geOne.eval₂ (algebraMap ℚ ℝ) (q t)) -
          cPiLower10 * psiSnum_trunc_eval (t := t) := by
          simp [cPiLower10Q_cast]

private lemma summable_powGeomTerm_tail_r_27_100 (t : ℝ) (ht : 1 ≤ t) :
    Summable (fun m : ℕ => AppendixA.powGeomTerm (r t) 27 (100 + m)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hs : Summable (fun n : ℕ => AppendixA.powGeomTerm (r t) 27 n) := by
    simpa using!
      (SpherePacking.Dim24.AppendixA.summable_powGeomTerm_r (t := t) (ht0 := ht0) (k := 27))
  simpa [Nat.add_comm] using! (summable_nat_add_iff 100 (f := fun n : ℕ =>
    AppendixA.powGeomTerm (r t) 27 n)).2 hs

private lemma psiSnum_trunc_eval_eq_sum_coeffFunC (t : ℝ) :
    (psiSnum_trunc_eval (t := t) : ℂ) =
      ∑ n ∈ Finset.range Ineq2GeOneCoeffs.N,
        (Ineq2PsiSnum.psiSnumCoeffFun n : ℂ) * ((r t : ℂ) ^ n) := by
  rw [psiSnum_trunc_eval_eq_sum_coeffFun (t := t)]
  simp

/-- For `1 ≤ t`, bound the norm of the tail
`psiS_num (it t ...) - (psiSnum_trunc_eval t : ℂ)` by a geometric majorant. -/
public lemma psiS_num_trunc_geOne_norm_sub_le (t : ℝ) (ht : 1 ≤ t) :
    ‖psiS_num (it t (lt_of_lt_of_le (by norm_num) ht)) - (psiSnum_trunc_eval (t := t) : ℂ)‖
      ≤ (16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  set z : ℍ := it t ht0
  have hpsi : psiS_num z = Ineq2PsiSnum.rseries Ineq2PsiSnum.psiSnumCoeffFun t := by
    simpa [z] using! (Ineq2PsiSnum.psiS_num_it_eq_rseries_psiSnumCoeffFun (t := t) ht)
  let f : ℕ → ℂ := fun n =>
    (Ineq2PsiSnum.psiSnumCoeffFun n : ℂ) * ((r t : ℂ) ^ n)
  have hs_norm : Summable (fun n : ℕ => ‖f n‖) := by
    have hcoeff :
        ∀ n : ℕ, |(Ineq2PsiSnum.psiSnumCoeffFun n : ℝ)| ≤
          (16 : ℝ) ^ (8 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ 27) := by
      intro n
      simpa using! (Ineq2PsiSnum.abs_psiSnumCoeffFun_le (n := n))
    exact
      Ineq2PsiSnum.summable_norm_rseries_of_coeffBound t ht
        Ineq2PsiSnum.psiSnumCoeffFun (16 ^ 8) 27 hcoeff
  have hs : Summable f := Summable.of_norm hs_norm
  have hsplit :
      (∑' n : ℕ, f n) =
        (∑ n ∈ Finset.range 100, f n) + ∑' n : ℕ, f (n + 100) := by
    simpa using! (Summable.sum_add_tsum_nat_add 100 hs).symm
  have htrunc : (psiSnum_trunc_eval (t := t) : ℂ) = ∑ n ∈ Finset.range 100, f n := by
    simpa [f, Ineq2GeOneCoeffs.N] using! (psiSnum_trunc_eval_eq_sum_coeffFunC (t := t))
  have hdiff :
        (∑' n : ℕ, f n) - (∑ n ∈ Finset.range 100, f n) = ∑' n : ℕ, f (n + 100) :=
      sub_eq_of_eq_add' hsplit
  have hpsi_sub :
      psiS_num z - (psiSnum_trunc_eval (t := t) : ℂ) = ∑' n : ℕ, f (n + 100) := by
    have : Ineq2PsiSnum.rseries Ineq2PsiSnum.psiSnumCoeffFun t = (∑' n : ℕ, f n) := by
      simp [Ineq2PsiSnum.rseries, f]
    calc
      psiS_num z - (psiSnum_trunc_eval (t := t) : ℂ)
          = (∑' n : ℕ, f n) - (∑ n ∈ Finset.range 100, f n) := by
              simp [hpsi, this, htrunc]
      _ = ∑' n : ℕ, f (n + 100) := hdiff
  have hs_norm_tail : Summable (fun n : ℕ => ‖f (n + 100)‖) :=
    (summable_nat_add_iff 100 (f := fun n : ℕ => ‖f n‖)).2 hs_norm
  have htail_norm_le :
      ‖∑' n : ℕ, f (n + 100)‖ ≤ ∑' n : ℕ, ‖f (n + 100)‖ :=
    norm_tsum_le_tsum_norm hs_norm_tail
  have hterm :
      ∀ n : ℕ, ‖f (n + 100)‖ ≤ (16 : ℝ) ^ (8 : ℕ) * AppendixA.powGeomTerm (r t) 27 (100 + n) := by
    intro n
    have hr0 : 0 ≤ r t := (Real.exp_pos _).le
    have hnorm_a :
        ‖(Ineq2PsiSnum.psiSnumCoeffFun (n + 100) : ℂ)‖ =
          |(Ineq2PsiSnum.psiSnumCoeffFun (n + 100) : ℝ)| := by
      simp
    have hnorm_r : ‖((r t : ℂ) ^ (n + 100))‖ = (r t) ^ (n + 100) := by
      simp [norm_pow, abs_of_nonneg hr0]
    have hcoeff := Ineq2PsiSnum.abs_psiSnumCoeffFun_le (n := n + 100)
    dsimp [f]
    calc
      ‖(Ineq2PsiSnum.psiSnumCoeffFun (n + 100) : ℂ) * ((r t : ℂ) ^ (n + 100))‖
          = ‖(Ineq2PsiSnum.psiSnumCoeffFun (n + 100) : ℂ)‖ *
              ‖((r t : ℂ) ^ (n + 100))‖ := by simp
      _ = |(Ineq2PsiSnum.psiSnumCoeffFun (n + 100) : ℝ)| * (r t) ^ (n + 100) := by
          rw [hnorm_a, hnorm_r]
      _ ≤ ((16 : ℝ) ^ (8 : ℕ) * (((n + 100 + 1 : ℕ) : ℝ) ^ 27)) * (r t) ^ (n + 100) := by
            have hrpow : 0 ≤ (r t) ^ (n + 100) := pow_nonneg hr0 _
            exact mul_le_mul_of_nonneg_right hcoeff hrpow
      _ = (16 : ℝ) ^ (8 : ℕ) * AppendixA.powGeomTerm (r t) 27 (100 + n) := by
            dsimp [AppendixA.powGeomTerm]
            have hn : (100 + n : ℕ) = n + 100 := Nat.add_comm 100 n
            -- Rewrite `100+n` to `n+100`, and cast `(n+100+1)` as `(↑(n+100)+1)`.
            rw [hn]
            have hcast : ((n + 100 + 1 : ℕ) : ℝ) = (n + 100 : ℝ) + 1 := by simp
            rw [hcast]
            simp [mul_assoc]
  have hs_powGeom : Summable (fun n : ℕ => AppendixA.powGeomTerm (r t) 27 (100 + n)) :=
    summable_powGeomTerm_tail_r_27_100 (t := t) ht
  have hs_major :
      Summable (fun n : ℕ => (16 : ℝ) ^ (8 : ℕ) * AppendixA.powGeomTerm (r t) 27 (100 + n)) :=
    hs_powGeom.mul_left ((16 : ℝ) ^ (8 : ℕ))
  have hsum_norm_le :
      (∑' n : ℕ, ‖f (n + 100)‖) ≤
        ∑' n : ℕ, (16 : ℝ) ^ (8 : ℕ) * AppendixA.powGeomTerm (r t) 27 (100 + n) :=
    hasSum_le hterm hs_norm_tail.hasSum hs_major.hasSum
  have htail :
      ‖psiS_num z - (psiSnum_trunc_eval (t := t) : ℂ)‖ ≤
          ∑' n : ℕ, (16 : ℝ) ^ (8 : ℕ) * AppendixA.powGeomTerm (r t) 27 (100 + n) := by
    simpa [hpsi_sub] using! (le_trans htail_norm_le hsum_norm_le)
  simpa [tsum_mul_left, mul_assoc] using! htail


end SpherePacking.Dim24
