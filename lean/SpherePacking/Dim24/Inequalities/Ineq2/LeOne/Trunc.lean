/-
Truncation and Sturm-style checks for the `t ≤ 1` case of Lemma `ineq2`.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.AbsBoundQ
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.Denom
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.PariCoeffs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Real.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.RBounds
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTrunc
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.Defs
import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTruncPosRigorous.LargeEvalLe
import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTruncPosRigorous.SmallEvalLe
import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.Head
import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.TailNormBound
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Truncation bounds for `ineq2` (`t ≤ 1` case)

After the modular substitution `t ↦ 1 / t`, the `t ≤ 1` case of Appendix A, Lemma `ineq2` is
reduced to estimates for `t ≥ 1` on the imaginary axis.

This file defines the truncation polynomial `ineq2_trunc_leOne` and proves certified bounds
showing that the cleared numerator is bounded below by the explicit truncation
`ExactTrunc.ineq2_exact_trunc` minus an error term `eps * r(t)^12`. It also provides tail bounds
for the geometric-series sums appearing in the PARI/GP computations of `appendix.txt`.

## Main definitions
* `ineq2_trunc_leOne`

## Main statements
* `Ineq2LeOneTruncAux.NumTailBound.ineq2_exact_trunc_sub_eps_le_num_re`
* `Ineq2LeOneTruncAux.ExactTruncPosRigorous.ineq2_exact_trunc_sub_eps_pos`
* `ineq2_tail_bound_leOne`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

open AppendixA


/-- Truncated polynomial approximation for the `t ≤ 1` reduction in Lemma `ineq2`.
Paper reference: Appendix A, proof of Lemma `ineq2`, second case. -/
noncomputable def ineq2_trunc_leOne : Polynomial ℚ :=
  AppendixA.polyOfCoeffs Ineq2LeOneTruncAux.ineq2_trunc_leOne_coeffs_pari

namespace Ineq2LeOneTruncAux.TruncProofAux

open AppendixA

def horner : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: l, x => a + x * horner l x

set_option maxRecDepth 20000 in
lemma horner_ineq2_qcoeffs_one_div_23_gt_one :
    (1 : ℚ) <
      horner (Ineq2LeOneTruncAux.ineq2_trunc_leOne_coeffs_pari.drop 1) ((1 : ℚ) / 23) := by
  simp [horner, Ineq2LeOneTruncAux.ineq2_trunc_leOne_coeffs_pari]
  norm_num

lemma eval₂_polyOfCoeffs_eq_horner (l : List ℚ) (x : ℚ) :
    (polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) (x : ℝ) = (horner l x : ℝ) := by
  induction l with
  | nil =>
      simp [polyOfCoeffs, horner]
  | cons a l ih =>
      simp [polyOfCoeffs, horner, ih]
def derivCoeffsAux : ℕ → List ℚ → List ℚ
  | _n, [] => []
  | n, a :: l => ((n : ℚ) * a) :: derivCoeffsAux (n + 1) l

def derivCoeffs : List ℚ → List ℚ
  | [] => []
  | _a :: l => derivCoeffsAux 1 l

lemma derivCoeffsAux_getD (n0 : ℕ) (l : List ℚ) (k : ℕ) :
    (derivCoeffsAux n0 l).getD k 0 = ((n0 + k : ℕ) : ℚ) * l.getD k 0 := by
  induction l generalizing n0 k with
  | nil =>
      simp [derivCoeffsAux]
  | cons a l ih =>
      cases k with
      | zero =>
          simp [derivCoeffsAux]
      | succ k =>
          -- `getD` on a `cons` shifts to the tail.
          have h := ih (n0 := n0 + 1) (k := k)
          -- Normalize `Nat` additions on the index coefficient.
          simpa [derivCoeffsAux, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using! h

lemma derivCoeffs_getD (l : List ℚ) (k : ℕ) :
    (derivCoeffs l).getD k 0 = ((k + 1 : ℕ) : ℚ) * l.getD (k + 1) 0 := by
  cases l with
  | nil =>
      simp [derivCoeffs]
  | cons a l =>
      have haux := derivCoeffsAux_getD (n0 := 1) (l := l) (k := k)
      -- Rewrite `l.getD k` as the shifted `getD` on `(a :: l)`.
      have hshift : l.getD k 0 = (a :: l).getD (k + 1) 0 := by
        cases k <;> rfl
      -- And `1 + k = k + 1` in `ℕ`.
      have hone : ((1 + k : ℕ) : ℚ) = ((k + 1 : ℕ) : ℚ) := by
        simp [Nat.add_comm]
      -- Put everything together.
      simpa [derivCoeffs, hshift, hone] using! haux

lemma polyOfCoeffs_derivative (l : List ℚ) :
    (polyOfCoeffs l).derivative = polyOfCoeffs (derivCoeffs l) := by
  ext k
  simpa [Polynomial.coeff_derivative, polyOfCoeffs_coeff_getD, mul_comm] using!
    (derivCoeffs_getD (l := l) (k := k)).symm

set_option maxRecDepth 20000 in
lemma deriv_absBoundQ_ineq2_qcoeffs_one_div_23_neg :
    let qcoeffs : List ℚ := Ineq2LeOneTruncAux.ineq2_trunc_leOne_coeffs_pari.drop 1
    let dcoeffs : List ℚ := derivCoeffs qcoeffs
    let d0Q : ℚ := dcoeffs.getD 0 0
    let dTail : List ℚ := dcoeffs.drop 1
    d0Q + ((1 : ℚ) / 23) * absBoundQ dTail ((1 : ℚ) / 23) < 0 := by
  simp [derivCoeffs, derivCoeffsAux, absBoundQ, Ineq2LeOneTruncAux.ineq2_trunc_leOne_coeffs_pari]
  norm_num

end Ineq2LeOneTruncAux.TruncProofAux
/-- Sturm-style sign check for the `t ≤ 1` truncated polynomial (strict positivity). -/
theorem ineq2_trunc_leOne_pos (t : ℝ) (ht : 1 ≤ t) :
    0 < (ineq2_trunc_leOne.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ) := by
  -- The truncation polynomial is in `r = exp(-π t)` with `t ≥ 1`, so `0 < r ≤ 1/23`.
  have hxpos : 0 < r t := Real.exp_pos _
  have hx0 : 0 ≤ r t := hxpos.le
  have hxle : r t ≤ (1 / 23 : ℝ) := by
    simpa [r, AppendixA.r] using! (AppendixA.r_le_one_div_23 (t := t) ht)
  -- `eps = 10^(-50) < 1`.
  have heps_pos : 0 < eps := by
    have : (0 : ℝ) < (10 : ℝ) := by norm_num
    simpa [eps, AppendixA.eps] using! (zpow_pos this (-50 : ℤ))
  have heps_lt_one : eps < 1 := by
    have h10 : (1 : ℝ) < (10 : ℝ) := by norm_num
    have : (10 : ℝ) ^ (-50 : ℤ) < 1 :=
      zpow_lt_one_of_neg₀ h10 (by decide : (-50 : ℤ) < 0)
    simpa [eps, AppendixA.eps] using! this
  -- Work with the explicit coefficient list, and factor out an `X` to get
  -- `ineq2_trunc_leOne = X * Q`.
  set qcoeffs : List ℚ := Ineq2LeOneTruncAux.ineq2_trunc_leOne_coeffs_pari.drop 1
  set Qpoly : Polynomial ℚ := AppendixA.polyOfCoeffs qcoeffs
  have hcoeffs : Ineq2LeOneTruncAux.ineq2_trunc_leOne_coeffs_pari = (0 : ℚ) :: qcoeffs := by
    simp [qcoeffs, Ineq2LeOneTruncAux.ineq2_trunc_leOne_coeffs_pari]
  have hfactor : ineq2_trunc_leOne = (Polynomial.X : Polynomial ℚ) * Qpoly := by
    dsimp [ineq2_trunc_leOne, Qpoly]
    rw [hcoeffs]
    -- `polyOfCoeffs (0 :: l) = X * polyOfCoeffs l`.
    simp [AppendixA.polyOfCoeffs_zero_cons]
  -- Show `Qpoly(1/23) > 1` by a certified computation in `ℚ`.
  let cQ : ℚ := (1 : ℚ) / 23
  have hQ_cQ : (1 : ℚ) < Ineq2LeOneTruncAux.TruncProofAux.horner qcoeffs cQ := by
    simpa [qcoeffs, cQ] using!
      Ineq2LeOneTruncAux.TruncProofAux.horner_ineq2_qcoeffs_one_div_23_gt_one
  have hQ_c : (1 : ℝ) < (Qpoly.eval₂ (algebraMap ℚ ℝ) (cQ : ℝ)) := by
    -- Rewrite `Qpoly` as `polyOfCoeffs qcoeffs`.
    have :
        (Qpoly.eval₂ (algebraMap ℚ ℝ) (cQ : ℝ)) =
          (Ineq2LeOneTruncAux.TruncProofAux.horner qcoeffs cQ : ℝ) := by
      simpa [Qpoly] using!
        (Ineq2LeOneTruncAux.TruncProofAux.eval₂_polyOfCoeffs_eq_horner qcoeffs cQ)
    -- Cast the certified `ℚ` inequality.
    have hQ_cQ' : (1 : ℝ) < (Ineq2LeOneTruncAux.TruncProofAux.horner qcoeffs cQ : ℝ) := by
      exact_mod_cast hQ_cQ
    simpa [this] using! hQ_cQ'
  -- Show `Qpoly` is strictly antitone on `Icc 0 (1/23)` by an explicit uniform derivative bound.
  set c : ℝ := (1 : ℝ) / 23
  let QR : Polynomial ℝ := Qpoly.map (algebraMap ℚ ℝ)
  let f : ℝ → ℝ := fun x => QR.eval x
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) c) := (QR.continuous).continuousOn
  -- Derivative bound: for `0 ≤ x ≤ c`, `deriv f x < 0`.
  have hf_deriv_neg : ∀ x ∈ interior (Set.Icc (0 : ℝ) c), deriv f x < 0 := by
    intro x hx
    have hxI : x ∈ Set.Ioo (0 : ℝ) c := by simpa [interior_Icc] using! hx
    have hx0' : 0 ≤ x := hxI.1.le
    have hxc : x ≤ c := le_of_lt hxI.2
    have hxabs : |x| ≤ c := by simpa [abs_of_nonneg hx0'] using! hxc
    -- `deriv f x = QR.derivative.eval x`.
    have hderiv : deriv f x = QR.derivative.eval x := by
      simp [f, QR]
    -- Express `QR.derivative` as the mapped derivative of `polyOfCoeffs`.
    have hQpoly_eval : ∀ y : ℝ, f y = (Qpoly.eval₂ (algebraMap ℚ ℝ) y) := by
      intro y
      simp [f, QR, Polynomial.eval₂_eq_eval_map]
    have hQR_deriv :
        QR.derivative =
          (AppendixA.polyOfCoeffs (Ineq2LeOneTruncAux.TruncProofAux.derivCoeffs qcoeffs)).map
            (algebraMap ℚ ℝ) := by
      -- `QR = map (polyOfCoeffs qcoeffs)`, so take derivatives and rewrite using
      -- `polyOfCoeffs_derivative`.
      have :
          QR.derivative = (Qpoly.derivative).map (algebraMap ℚ ℝ) := by
        simp [QR]
      -- Replace `Qpoly.derivative` by `polyOfCoeffs (derivCoeffs qcoeffs)`.
      simpa [Qpoly, Ineq2LeOneTruncAux.TruncProofAux.polyOfCoeffs_derivative qcoeffs] using! this
    -- Bound `QR.derivative.eval x` above by a negative rational constant.
    set dcoeffs : List ℚ := Ineq2LeOneTruncAux.TruncProofAux.derivCoeffs qcoeffs
    set d0Q : ℚ := dcoeffs.getD 0 0
    set dTail : List ℚ := dcoeffs.drop 1
    have hDpoly :
        (AppendixA.polyOfCoeffs dcoeffs).eval₂ (algebraMap ℚ ℝ) x =
          (d0Q : ℝ) + x * (AppendixA.polyOfCoeffs dTail).eval₂ (algebraMap ℚ ℝ) x := by
      cases hds : dcoeffs with
      | nil =>
          simp [d0Q, dTail, hds, AppendixA.polyOfCoeffs]
      | cons a l =>
          simp [d0Q, dTail, hds, AppendixA.eval₂_polyOfCoeffs_cons]
    have habs : |(polyOfCoeffs dTail).eval₂ (algebraMap ℚ ℝ) x| ≤ absBound dTail c :=
      abs_eval₂_polyOfCoeffs_le_absBound (l := dTail) (x := x) (c := c)
        (by
          have : (0 : ℝ) < c := by norm_num [c]
          exact this.le)
        (by
          -- `|x| ≤ c`.
          simpa [c] using! hxabs)
    have habs0 : 0 ≤ AppendixA.absBound dTail c :=
      AppendixA.absBound_nonneg (l := dTail) (by
        have : (0 : ℝ) < c := by norm_num [c]
        exact this.le)
    have hterm_le :
        x * (AppendixA.polyOfCoeffs dTail).eval₂ (algebraMap ℚ ℝ) x ≤
          c * AppendixA.absBound dTail c := by
      have h1 :
          x * (AppendixA.polyOfCoeffs dTail).eval₂ (algebraMap ℚ ℝ) x ≤
            x * |(AppendixA.polyOfCoeffs dTail).eval₂ (algebraMap ℚ ℝ) x| := by
        have := le_abs_self ((AppendixA.polyOfCoeffs dTail).eval₂ (algebraMap ℚ ℝ) x)
        exact mul_le_mul_of_nonneg_left this hx0'
      have h2 :
          x * |(AppendixA.polyOfCoeffs dTail).eval₂ (algebraMap ℚ ℝ) x| ≤
            x * AppendixA.absBound dTail c := by
        exact mul_le_mul_of_nonneg_left habs hx0'
      have h3 : x * AppendixA.absBound dTail c ≤ c * AppendixA.absBound dTail c :=
        mul_le_mul_of_nonneg_right hxc habs0
      exact le_trans (le_trans h1 h2) h3
    have hupper :
        (AppendixA.polyOfCoeffs dcoeffs).eval₂ (algebraMap ℚ ℝ) x ≤
          (d0Q : ℝ) + c * AppendixA.absBound dTail c := by
      linarith [hDpoly, hterm_le]
    -- Certified negativity of `(d0Q : ℝ) + c * absBound dTail c`.
    let cQ' : ℚ := (1 : ℚ) / 23
    have habs_cast :
        AppendixA.absBound dTail (cQ' : ℝ) = (AppendixA.absBoundQ dTail cQ' : ℝ) :=
      AppendixA.absBoundQ_cast (l := dTail) cQ'
    have hconst_neg : d0Q + cQ' * AppendixA.absBoundQ dTail cQ' < 0 := by
      simpa [qcoeffs, dcoeffs, d0Q, dTail, cQ'] using!
        (Ineq2LeOneTruncAux.TruncProofAux.deriv_absBoundQ_ineq2_qcoeffs_one_div_23_neg : _)
    have hconst_negR :
        (d0Q : ℝ) + (cQ' : ℝ) * (AppendixA.absBoundQ dTail cQ' : ℝ) < 0 := by
      exact_mod_cast hconst_neg
    have hc_eq : (cQ' : ℝ) = c := by norm_num [cQ', c]
    have habs_cast' : (absBoundQ dTail cQ' : ℝ) = absBound dTail (cQ' : ℝ) := by
      simpa using! habs_cast.symm
    have hneg :
        (d0Q : ℝ) + c * AppendixA.absBound dTail c < 0 := by
      simpa [hc_eq, habs_cast'] using! hconst_negR
    -- Connect `QR.derivative.eval x` to the `polyOfCoeffs` evaluation and conclude.
    have hDpoly_eval :
        QR.derivative.eval x = (AppendixA.polyOfCoeffs dcoeffs).eval₂ (algebraMap ℚ ℝ) x := by
      -- Use `hQR_deriv` and `eval₂_eq_eval_map`.
      simp [hQR_deriv, Polynomial.eval₂_eq_eval_map, dcoeffs]
    have hDlt : QR.derivative.eval x < 0 :=
      lt_of_le_of_lt (by simpa [hDpoly_eval] using! hupper) hneg
    simpa [hderiv] using! hDlt
  have hanti : StrictAntiOn f (Set.Icc (0 : ℝ) c) :=
    strictAntiOn_of_deriv_neg (D := Set.Icc (0 : ℝ) c) (hD := convex_Icc (0 : ℝ) c) hf_cont
      hf_deriv_neg
  -- Apply strict antitonicity at `x = r t` and `c = 1/23` to get `Q(r t) ≥ Q(c) > 1`.
  have hx_mem : (r t) ∈ Set.Icc (0 : ℝ) c := ⟨hx0, hxle⟩
  have hc_mem : c ∈ Set.Icc (0 : ℝ) c := by exact ⟨by simp [c], le_rfl⟩
  have hQ_ge_c :
      (Qpoly.eval₂ (algebraMap ℚ ℝ) c) ≤ (Qpoly.eval₂ (algebraMap ℚ ℝ) (r t)) := by
    by_cases hEq : r t = c
    · simp [hEq]
    · have hx_lt_c : r t < c :=
        lt_of_le_of_ne hxle hEq
      have hlt : f c < f (r t) := hanti hx_mem hc_mem hx_lt_c
      simpa [f, QR, Polynomial.eval₂_eq_eval_map] using! hlt.le
  have hQ_pos : 0 < (Qpoly.eval₂ (algebraMap ℚ ℝ) (r t)) := by
    have hQ_pos_c : 0 < (Qpoly.eval₂ (algebraMap ℚ ℝ) c) := by
      -- `1 < Qpoly(c)`.
      have hcQ : (cQ : ℝ) = c := by norm_num [cQ, c]
      have : (1 : ℝ) < (Qpoly.eval₂ (algebraMap ℚ ℝ) c) := by simpa [hcQ] using! hQ_c
      exact lt_trans (by norm_num) this
    exact lt_of_lt_of_le hQ_pos_c hQ_ge_c
  -- Now `ineq2_trunc_leOne(r t) = (r t) * Qpoly(r t)`.
  have hP_eval :
      (ineq2_trunc_leOne.eval₂ (algebraMap ℚ ℝ) (r t)) =
        (r t) * (Qpoly.eval₂ (algebraMap ℚ ℝ) (r t)) := by
    -- Evaluate the factorization at `r t`.
    simp [hfactor, Polynomial.eval₂_mul, Polynomial.eval₂_X]
  have hP_pos : 0 < (ineq2_trunc_leOne.eval₂ (algebraMap ℚ ℝ) (r t)) := by
    simpa [hP_eval] using! mul_pos hxpos hQ_pos
  -- Strengthen to a concrete lower bound `r t < P(r t)` using `Qpoly(r t) > 1`.
  have hQ_gt_one : (1 : ℝ) < (Qpoly.eval₂ (algebraMap ℚ ℝ) (r t)) := by
    have hcQ : (cQ : ℝ) = c := by norm_num [cQ, c]
    exact lt_of_lt_of_le (by simpa [hcQ] using! hQ_c) hQ_ge_c
  have hP_gt_r : r t < (ineq2_trunc_leOne.eval₂ (algebraMap ℚ ℝ) (r t)) := by
    have : (r t) * (1 : ℝ) < (r t) * (Qpoly.eval₂ (algebraMap ℚ ℝ) (r t)) :=
      mul_lt_mul_of_pos_left hQ_gt_one hxpos
    simpa [hP_eval, mul_one] using! this
  -- Now show `0 < r t - eps * (r t)^12`, hence `0 < P(r t) - eps*(r t)^12`.
  have hx1 : r t ≤ 1 := hxle.trans (by norm_num)
  have hxpow_le : (r t) ^ (12 : ℕ) ≤ r t := by
    -- `0 ≤ r t ≤ 1` implies `x^12 ≤ x^1`.
    simpa using! (pow_le_pow_of_le_one hx0 hx1 (by decide : (1 : ℕ) ≤ 12))
  have heps0 : 0 ≤ eps := heps_pos.le
  have hmul : eps * (r t) ^ (12 : ℕ) ≤ eps * (r t) :=
    mul_le_mul_of_nonneg_left hxpow_le heps0
  have hsub_pos : 0 < r t - eps * (r t) ^ (12 : ℕ) := by
    have hsub_pos' : 0 < r t - eps * (r t) := by
      have : 0 < (1 - eps) * (r t) := by
        have : 0 < (1 - eps) := sub_pos.2 heps_lt_one
        exact mul_pos this hxpos
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, mul_add, add_mul] using! this
    -- Replace `eps * x^12` by the larger `eps * x`.
    have : r t - eps * (r t) ^ (12 : ℕ) ≥ r t - eps * (r t) :=
      sub_le_sub_left hmul (r t)
    exact lt_of_lt_of_le hsub_pos' this
  have : 0 < (ineq2_trunc_leOne.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ) := by
    have hlt : r t - eps * (r t) ^ (12 : ℕ) <
        (ineq2_trunc_leOne.eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ) :=
      sub_lt_sub_right hP_gt_r _
    exact lt_trans hsub_pos hlt
  simpa using! this

/-!
### Exact truncation certified bounds (Appendix A)

These two lemmas used to live in small single-importer files:

- `Ineq2LeOneTruncAux.ExactTruncPosRigorous.ineq2_exact_trunc_sub_eps_pos`
- `Ineq2LeOneTruncAux.NumTailBound.ineq2_exact_trunc_sub_eps_le_num_re`
-/

namespace Ineq2LeOneTruncAux.NumTailBound

/-- Cleared numerator real part ≥ exact truncation minus `eps * r^12`. -/
public theorem ineq2_exact_trunc_sub_eps_le_num_re (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    ExactTrunc.ineq2_exact_trunc t - eps * (r t) ^ 12 ≤ (ineq2_num t ht0).re := by
  intro ht0
  have htail : ‖ineq2_num_tail t ht0‖ ≤ AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
    simpa [ht0] using! (ineq2_num_tail_norm_le (t := t) ht)
  have hhead_eq : (ineq2_num_head t ht0).re = ExactTrunc.ineq2_exact_trunc t :=
    ineq2_num_head_re_eq_exact_trunc (t := t) (ht0 := ht0)
  have hsum_re : (ineq2_num t ht0).re = (ineq2_num_head t ht0).re + (ineq2_num_tail t ht0).re := by
    simpa [ht0] using! congrArg Complex.re (ineq2_num_eq_head_add_tail (t := t) (ht := ht))
  have htail_re : -(‖ineq2_num_tail t ht0‖) ≤ (ineq2_num_tail t ht0).re := by
    exact neg_le_of_abs_le (Complex.abs_re_le_norm (ineq2_num_tail t ht0))
  linarith

end Ineq2LeOneTruncAux.NumTailBound

namespace Ineq2LeOneTruncAux.ExactTruncPosRigorous

/-- For `t ≥ 1`, the explicit truncation `ExactTrunc.ineq2_exact_trunc t` dominates the tail
`eps * r(t)^12`, hence `ExactTrunc.ineq2_exact_trunc t - eps * r(t)^12` is strictly positive. -/
public theorem ineq2_exact_trunc_sub_eps_pos (t : ℝ) (ht : 1 ≤ t) :
    0 < ExactTrunc.ineq2_exact_trunc t - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
  rcases le_total t t0 with ht0 | ht0
  · exact exact_trunc_sub_eps_pos_of_le_t0 (t := t) ht ht0
  · exact exact_trunc_sub_eps_pos_of_t0_le (t := t) ht ht0

end Ineq2LeOneTruncAux.ExactTruncPosRigorous

/-- Tail bound for the `t ≤ 1` reduction in Lemma `ineq2`.
In the paper, one reduces `varphi(it) - (432/π^2) ψS(it) > 0` on `0 < t ≤ 1`
to the positivity of the negation of the transformed expression
`-t^2 varphi(it) + i t varphi₁(it) + varphi₂(it) - (432/π^2) ψI(it)`
on `t ≥ 1` (Appendix A, Lemma `ineq2`, second case). -/
public theorem ineq2_tail_bound_leOne (t : ℝ) (ht : 1 ≤ t) :
    Ineq2LeOneTruncAux.ExactTrunc.ineq2_exact_trunc t -
        AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) ≤
      (((t : ℂ) ^ (2 : ℕ)) * varphi (it t (lt_of_lt_of_le (by norm_num) ht))
          - Complex.I * (t : ℂ) * varphi₁ (it t (lt_of_lt_of_le (by norm_num) ht))
          - varphi₂ (it t (lt_of_lt_of_le (by norm_num) ht))
          + (432 / (Real.pi ^ 2) : ℂ) * ψI (it t (lt_of_lt_of_le (by norm_num) ht))).re := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  set L : ℝ :=
    Ineq2LeOneTruncAux.ExactTrunc.ineq2_exact_trunc t -
      AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ)
  have hL0 : 0 ≤ L := le_of_lt (by
    simpa [L] using!
      (Ineq2LeOneTruncAux.ExactTruncPosRigorous.ineq2_exact_trunc_sub_eps_pos (t := t) ht))
  have hnum : L ≤ (Ineq2LeOneTruncAux.ineq2_num t ht0).re := by
    -- `NumTailBound` gives the truncation-minus-`eps*r^12` lower bound for the cleared numerator.
    exact Ineq2LeOneTruncAux.NumTailBound.ineq2_exact_trunc_sub_eps_le_num_re t ht
  have h :=
    Ineq2LeOneTruncAux.ineq2_lowerBound_of_num (t := t) ht0 (L := L) hL0 hnum
  simpa [L, Ineq2LeOneTruncAux.ineq2_transformed_neg] using! h

end SpherePacking.Dim24
