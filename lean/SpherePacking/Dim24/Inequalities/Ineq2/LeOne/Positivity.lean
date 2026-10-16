-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.Trunc
public import SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Transform
public import SpherePacking.ModularForms.ResToImagAxis
import SpherePacking.Tactic.NormNumI


/-!
# Positivity for `ineq2` on the imaginary axis (`t ≤ 1`)

This file proves the final positivity statement for the `t ≤ 1` case of Appendix A, Lemma `ineq2`.
Using the modular transformation to `T = 1 / t` and the certified truncation bounds from
`SpherePacking.Dim24.Inequalities.Ineq2.LeOne.Trunc`, we show that for `0 < t ≤ 1` the real part of
`varphi (it t) - (432 / Real.pi ^ 2) * ψS (it t)` is positive.

## Main statements
* `ineq2_imagAxis_le_one`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

/-- Positivity for `0 < t ≤ 1` (Appendix A, Lemma `ineq2`, second case). -/
public theorem ineq2_imagAxis_le_one (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1) :
    0 < (varphi (it t ht0) - (432 / (Real.pi ^ 2) : ℂ) * ψS (it t ht0)).re := by
  set T : ℝ := 1 / t
  have hT0 : 0 < T := by simpa [T] using! (one_div_pos.2 ht0)
  have hT1 : 1 ≤ T := by
    simpa [T] using! (one_le_one_div ht0 ht)
  have hT0' : 0 < T := lt_of_lt_of_le (by simp : (0 : ℝ) < 1) hT1
  set c : ℂ := (432 / (Real.pi ^ 2) : ℂ)
  have hpos_trans' :
      0 <
        (((T : ℂ) ^ (2 : ℕ)) * varphi (it T hT0')
            - Complex.I * (T : ℂ) * varphi₁ (it T hT0')
            - varphi₂ (it T hT0')
            + c * ψI (it T hT0')).re := by
    have htrunc :=
      Ineq2LeOneTruncAux.ExactTruncPosRigorous.ineq2_exact_trunc_sub_eps_pos (t := T) hT1
    have hle := (ineq2_tail_bound_leOne (t := T) hT1)
    exact lt_of_lt_of_le htrunc (by simpa [c] using! hle)
  have hitT :
      it T hT0' = it T hT0 := by
    ext1
    simp [it]
  have hpos_trans :
      0 <
        (((T : ℂ) ^ (2 : ℕ)) * varphi (it T hT0)
            - Complex.I * (T : ℂ) * varphi₁ (it T hT0)
            - varphi₂ (it T hT0)
            + c * ψI (it T hT0)).re := by
    simpa [hitT] using! hpos_trans'
  have hvarphi :
      (T : ℂ) ^ (10 : ℕ) * varphi (it t ht0) =
        (T : ℂ) ^ (2 : ℕ) * varphi (it T hT0)
          - Complex.I * (T : ℂ) * varphi₁ (it T hT0) - varphi₂ (it T hT0) := by
    simpa [T, iOverT, it] using! (tPow10_varphi_iOverT (t := T) hT0)
  have hpsiS :
      ψS (it t ht0) = -((t : ℂ) ^ (10 : ℕ)) * ψI (it T hT0) := by
    have h := ResToImagAxis.SlashActionS (F := ψI) (k := (-10 : ℤ)) (t := t) ht0
    have h' :
        ψS (it t ht0) =
          (Complex.I : ℂ) ^ (10 : ℤ) * (t : ℝ) ^ (10 : ℤ) * ψI (it T hT0) := by
      simpa [Function.resToImagAxis, ResToImagAxis, ψS, T, it, ht0, hT0] using! h
    have hI10 : (Complex.I : ℂ) ^ (10 : ℤ) = (-1 : ℂ) := by norm_num1
    have ht10 : ((t : ℝ) ^ (10 : ℤ) : ℂ) = (t : ℂ) ^ (10 : ℕ) := by
      simp [zpow_ofNat]
    simpa [hI10, ht10, mul_assoc, mul_left_comm, mul_comm] using! h'
  have hTtR : T * t = 1 := by
    simp [T, ht0.ne']
  have hTtC : (T : ℂ) * (t : ℂ) = 1 := by
    exact_mod_cast hTtR
  have hpow : (T : ℂ) ^ (10 : ℕ) * (t : ℂ) ^ (10 : ℕ) = 1 := by
    have := congrArg (fun z : ℂ => z ^ (10 : ℕ)) hTtC
    simpa [mul_pow] using! this
  have hpsi_mul :
      (T : ℂ) ^ (10 : ℕ) * ψS (it t ht0) = -ψI (it T hT0) := by
    grind only
  let z : ℂ := varphi (it t ht0) - c * ψS (it t ht0)
  let trans : ℂ :=
    (T : ℂ) ^ (2 : ℕ) * varphi (it T hT0)
      - Complex.I * (T : ℂ) * varphi₁ (it T hT0) - varphi₂ (it T hT0) + c * ψI (it T hT0)
  have hz_scale : (T : ℂ) ^ (10 : ℕ) * z = trans := by
    dsimp [z, trans]
    calc
      (T : ℂ) ^ (10 : ℕ) * (varphi (it t ht0) - c * ψS (it t ht0)) =
          (T : ℂ) ^ (10 : ℕ) * varphi (it t ht0) - c * ((T : ℂ) ^ (10 : ℕ) * ψS (it t ht0)) := by
        ring_nf
      _ =
          (T : ℂ) ^ (2 : ℕ) * varphi (it T hT0)
            - Complex.I * (T : ℂ) * varphi₁ (it T hT0)
            - varphi₂ (it T hT0)
            + c * ψI (it T hT0) := by
        simp [hvarphi, hpsi_mul, sub_eq_add_neg, add_assoc]
  have hz_scale_re : ((T : ℂ) ^ (10 : ℕ) * z).re = trans.re := by
    simpa using! congrArg Complex.re hz_scale
  have hmul_re :
      ((T : ℂ) ^ (10 : ℕ) * z).re = (T ^ (10 : ℕ)) * z.re := by
    have hT : ((T : ℂ) ^ (10 : ℕ)) = ((T ^ (10 : ℕ) : ℝ) : ℂ) :=
      (Complex.ofReal_pow T 10).symm
    have hT_im : ((T : ℂ) ^ (10 : ℕ)).im = 0 := by
      rw [hT]
      simp [-Complex.ofReal_pow]
    have hT_re : ((T : ℂ) ^ (10 : ℕ)).re = T ^ (10 : ℕ) := by
      rw [hT]
      simp [-Complex.ofReal_pow]
    simp [Complex.mul_re, hT_im, hT_re]
  have hTpow_pos : 0 < T ^ (10 : ℕ) := pow_pos hT0 _
  nlinarith

end SpherePacking.Dim24
