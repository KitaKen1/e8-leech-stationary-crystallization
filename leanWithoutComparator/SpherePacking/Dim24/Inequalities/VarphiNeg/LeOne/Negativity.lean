-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Transform
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Trunc.ExactTruncTailBound
import Mathlib.Tactic.NormNum


/-!
# Negativity for `0 < t ≤ 1`

Conclusion for the `t ≤ 1` case of `varphi(it) < 0` (Appendix A, Lemma `phinonpos`).

## Main statements
* `varphi_imagAxis_neg_le_one`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

/-- Tail bound for the `t ≤ 1` reduction (second half of Lemma `phinonpos`). -/
public theorem varphi_tail_bound_leOne (t : ℝ) (ht : 1 ≤ t) :
    AppendixA.VarphiLeOne.exactTrunc t - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ)
      ≤ (-((t : ℂ) ^ (2 : ℕ)) * varphi (it t (lt_of_lt_of_le (by norm_num) ht))
            + Complex.I * (t : ℂ) * varphi₁ (it t (lt_of_lt_of_le (by norm_num) ht))
            + varphi₂ (it t (lt_of_lt_of_le (by norm_num) ht))).re := by
  simpa using! (VarphiNeg.LeOne.Trunc.exactTrunc_sub_eps_le_transformed_re (t := t) ht)

/-- Positivity of the exact truncation head with tail error term for all `t ≥ 1`. -/
public theorem varphi_trunc_leOne_pos (t : ℝ) (ht : 1 ≤ t) :
    0 < AppendixA.VarphiLeOne.exactTrunc t - AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
  simpa using! (VarphiNeg.LeOne.Trunc.varphi_exact_trunc_sub_eps_pos (t := t) ht)

/-- Negativity of `varphi(it)` for `0 < t ≤ 1` (Appendix A, Lemma `phinonpos`, second case). -/
public theorem varphi_imagAxis_neg_le_one (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1) :
    (varphi (it t ht0)).re < 0 := by
  /- Proof sketch:
  Set `T = 1/t ≥ 1`. Using `tPow10_varphi_iOverT` and the `S`-transform, reduce the goal to
  positivity of the transformed expression at `T`, then use the exact-truncation head positivity
  (`varphi_trunc_leOne_pos`) together with the analytic tail bound (`varphi_tail_bound_leOne`). -/
  set T : ℝ := 1 / t
  have hTone : 1 ≤ T := by
    dsimp [T]
    exact one_le_one_div ht0 ht
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTone
  let zT : ℍ := it T hTpos
  let transformed : ℂ :=
    -((T : ℂ) ^ (2 : ℕ)) * varphi zT + Complex.I * (T : ℂ) * varphi₁ zT + varphi₂ zT
  have hTransPos : 0 < transformed.re := by
    dsimp [transformed, zT]
    exact
      lt_of_lt_of_le
        (varphi_trunc_leOne_pos (t := T) hTone)
        (varphi_tail_bound_leOne (t := T) hTone)
  have hId : (T : ℂ) ^ (10 : ℕ) * varphi (iOverT T hTpos) = -transformed := by
    have h := tPow10_varphi_iOverT (t := T) hTpos
    grind only
  have hmulEq : (T ^ (10 : ℕ)) * (varphi (iOverT T hTpos)).re = (-transformed).re := by
    have h' := congrArg Complex.re hId
    have hT10 : ((T : ℂ) ^ (10 : ℕ)) = ((T ^ (10 : ℕ) : ℝ) : ℂ) := by
      simp [Complex.ofReal_pow]
    rw [hT10] at h'
    rw [Complex.re_ofReal_mul] at h'
    exact h'
  have hRHS : (-transformed).re < 0 := by
    simpa [Complex.neg_re] using! (neg_neg_of_pos hTransPos)
  have hT10pos : 0 < T ^ (10 : ℕ) := pow_pos hTpos _
  have hmulLt : (T ^ (10 : ℕ)) * (varphi (iOverT T hTpos)).re < 0 := by
    simpa [hmulEq] using! hRHS
  have hmulLt' : (T ^ (10 : ℕ)) * (varphi (iOverT T hTpos)).re < (T ^ (10 : ℕ)) * 0 := by
    simpa using! hmulLt
  have hvarphi : (varphi (iOverT T hTpos)).re < 0 :=
    lt_of_mul_lt_mul_left hmulLt' hT10pos.le
  have hiOver : iOverT T hTpos = it t ht0 := by
    ext1
    have hTinvtC : ((T : ℂ)⁻¹) = (t : ℂ) := by
      dsimp [T]
      simp [one_div]
    simp [iOverT, it, hTinvtC]
  simpa [hiOver] using! hvarphi

end SpherePacking.Dim24
