-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Aux01
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import SpherePacking.ForMathlib.IntegrablePowMulExp


/-!
# Strip cancellation: `∫ f0 + I₆' = 0`

For `u` with `expU u 1 = 1`, the strip finite difference of `f0` cancels the tail integral `I₆'`.
The proof is a Cauchy-Goursat argument on a rectangle in the upper half-plane, using decay bounds
for `varphi` on vertical lines.

## Main statement
* `SpecialValuesAux.f0_strip_cancel_I6`
-/


open scoped Manifold
open Complex Real

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

open MagicFunction.Parametrisations RealIntegrals intervalIntegral Complex MeasureTheory Set Filter
open UpperHalfPlane
open scoped Topology
open scoped UpperHalfPlane

/-- For `expU u 1 = 1` and `0 ≤ u`, the period integral of `f0 u` on `im = 1` cancels `I₆' u`. -/
public lemma f0_strip_cancel_I6 (u : ℝ) (hu : expU u 1 = 1) (hu0 : 0 ≤ u) :
    (∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) + I₆' u = 0 := by
  -- Truncate outside the vertical strip so the uniform `Im → ∞` decay hypothesis
  -- is trivial there.
  letI : DecidablePred (fun z : ℂ => z.re ∈ Set.uIcc (0 : ℝ) 1) := Classical.decPred _
  let fStrip : ℂ → ℂ := fun z : ℂ =>
    if hz : z.re ∈ Set.uIcc (0 : ℝ) 1 then f0 u z else 0
  have hfStrip_eq_of_mem {z : ℂ} (hz : z.re ∈ Set.uIcc (0 : ℝ) 1) : fStrip z = f0 u z := by
    dsimp [fStrip]
    exact dif_pos hz
  /- Continuity on the closed rectangle `[[0,1]] × Ici 1`. -/
  have hcont_varphi' :
      ContinuousOn (fun z : ℂ => varphi' z) (Set.uIcc (0 : ℝ) 1 ×ℂ (Set.Ici (1 : ℝ))) := by
    have hcont0 :
        ContinuousOn (fun z : ℂ => varphi (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
      differentiableOn_varphiOfComplex.continuousOn
    have hsubset :
        Set.uIcc (0 : ℝ) 1 ×ℂ (Set.Ici (1 : ℝ)) ⊆ {z : ℂ | 0 < z.im} := by
      intro z hz
      have hzIm1 : (1 : ℝ) ≤ z.im := by simpa [mem_reProdIm] using! (mem_reProdIm.1 hz).2
      exact lt_of_lt_of_le (by norm_num) hzIm1
    have hcontRect := hcont0.mono hsubset
    refine hcontRect.congr ?_
    intro z hz
    have hzpos : 0 < z.im := hsubset (a := z) hz
    simp [varphi', hzpos, UpperHalfPlane.ofComplex_apply_of_im_pos hzpos]
  have hcont_f0 :
      ContinuousOn (f0 u) (Set.uIcc (0 : ℝ) 1 ×ℂ (Set.Ici (1 : ℝ))) := by
    have hpoly : Continuous (fun z : ℂ => ((2 : ℂ) * z) - 1) := by fun_prop
    have hexp : Continuous (expU u) := by
      unfold expU
      fun_prop
    have hmul :
        ContinuousOn (fun z : ℂ => varphi' z * (((2 : ℂ) * z) - 1) * expU u z)
          (Set.uIcc (0 : ℝ) 1 ×ℂ (Set.Ici (1 : ℝ))) :=
      (hcont_varphi'.mul hpoly.continuousOn).mul hexp.continuousOn
    simpa [f0] using! hmul
  have hcont :
      ContinuousOn fStrip (Set.uIcc (0 : ℝ) 1 ×ℂ (Set.Ici (1 : ℝ))) := by
    refine hcont_f0.congr ?_
    intro z hz
    have hzRe : z.re ∈ Set.uIcc (0 : ℝ) 1 := (mem_reProdIm.1 hz).1
    simp [hfStrip_eq_of_mem hzRe]
  /- Differentiability on the open rectangle. -/
  have hdiff :
      ∀ z ∈
        ((Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) ×ℂ (Set.Ioi (1 : ℝ))) \ (∅ : Set ℂ),
        DifferentiableAt ℂ fStrip z := by
    intro z hz
    have hzIm1 : z.im ∈ Set.Ioi (1 : ℝ) := by
      simpa [mem_reProdIm] using! (mem_reProdIm.1 (by simpa using! hz.1)).2
    have hzIm : 0 < z.im := lt_of_lt_of_le (by norm_num) (le_of_lt hzIm1)
    have hzRe : z.re ∈ Set.Ioo (0 : ℝ) 1 := by
      have hzRe' : z.re ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1) :=
        (mem_reProdIm.1 (by simpa using! hz.1)).1
      simpa [min_eq_left (zero_le_one : (0 : ℝ) ≤ 1),
        max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] using! hzRe'
    have hAtVarphi :
        DifferentiableAt ℂ (fun w : ℂ => varphi (UpperHalfPlane.ofComplex w)) z :=
      (differentiableOn_varphiOfComplex z hzIm).differentiableAt
        (isOpen_upperHalfPlaneSet.mem_nhds hzIm)
    have hEqVarphi' :
        (fun w : ℂ => varphi (UpperHalfPlane.ofComplex w)) =ᶠ[𝓝 z]
          fun w : ℂ => varphi' w := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hzIm] with w hw
      simp [varphi', hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    have hAtVarphi' : DifferentiableAt ℂ (fun w : ℂ => varphi' w) z :=
      hAtVarphi.congr_of_eventuallyEq hEqVarphi'.symm
    have hpoly : DifferentiableAt ℂ (fun w : ℂ => ((2 : ℂ) * w) - 1) z := by fun_prop
    have hexp : DifferentiableAt ℂ (expU u) z := by
      unfold expU
      fun_prop
    have hAt_f0 : DifferentiableAt ℂ (f0 u) z := by
      simpa [f0] using! (hAtVarphi'.mul hpoly).mul hexp
    have hEqStrip : (fun w : ℂ => fStrip w) =ᶠ[𝓝 z] fun w : ℂ => f0 u w := by
      have hnhdsRe : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 z.re := isOpen_Ioo.mem_nhds hzRe
      have hnhds : {w : ℂ | w.re ∈ Set.Ioo (0 : ℝ) 1} ∈ 𝓝 z :=
        (Complex.continuous_re.continuousAt.preimage_mem_nhds hnhdsRe)
      filter_upwards [hnhds] with w hw
      have hw' : w.re ∈ Set.uIcc (0 : ℝ) 1 := by
        have hwIcc : w.re ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hw
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! hwIcc
      dsimp [fStrip]
      exact dif_pos hw'
    exact hAt_f0.congr_of_eventuallyEq hEqStrip
  /- Integrability on both vertical contours. -/
  -- A basic bound on the linear factor along the imaginary axis.
  have hlin_bound :
      ∀ t : ℝ, 0 ≤ t → ‖((2 : ℂ) * ((t : ℂ) * Complex.I) - 1)‖ ≤ 1 + 2 * t := by
    intro t ht0
    have h := norm_sub_le ((2 : ℂ) * ((t : ℂ) * Complex.I)) (1 : ℂ)
    -- `‖2*(tI)‖ = 2*|t| = 2t` for `t ≥ 0`.
    have ht : ‖(t : ℂ)‖ = t := by
      simp [Real.norm_eq_abs, abs_of_nonneg ht0]
    have h2 : ‖(2 : ℂ) * ((t : ℂ) * Complex.I)‖ = 2 * t := by
      simp [ht0]
    -- Combine.
    have : ‖(2 : ℂ) * ((t : ℂ) * Complex.I) - 1‖ ≤ 2 * t + 1 := by
      simpa [h2, norm_one, abs_of_nonneg ht0, add_comm, add_left_comm, add_assoc] using! h
    -- Rewrite.
    simpa [add_assoc, add_comm, add_left_comm] using! this
  -- Convert `varphi' (tI)` to `varphi.resToImagAxis t` for `t>0`.
  have hvarphi_axis :
      ∀ t : ℝ, 0 < t → varphi' ((t : ℂ) * Complex.I) = varphi.resToImagAxis t := by
    intro t ht
    have harg : ((t : ℂ) * Complex.I) = (Complex.I : ℂ) * ((t : ℝ) : ℂ) := by ring
    -- Match the `resToImagAxis` definition and use the positive-imaginary branch for `varphi'`.
    simp [Function.resToImagAxis, ResToImagAxis, varphi', harg, ht]
  -- Left boundary: integrability of `t ↦ fStrip (tI)` for `t>1`.
  have hint_left :
      MeasureTheory.IntegrableOn (fun t : ℝ => fStrip ((0 : ℂ) + t * Complex.I))
        (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
    -- On this boundary, `fStrip = f0`.
    have hEq : EqOn (fun t : ℝ => fStrip ((0 : ℂ) + t * Complex.I))
        (fun t : ℝ => f0 u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) := by
      intro t ht
      have htRe : (((0 : ℂ) + t * Complex.I) : ℂ).re ∈ Set.uIcc (0 : ℝ) 1 := by
        have : (((0 : ℂ) + t * Complex.I) : ℂ).re = (0 : ℝ) := by simp
        simp
      dsimp [fStrip]
      simp [add_comm, mul_comm]
    -- Prove integrability for `f0` via domination.
    rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ, hCφ⟩
    have hb : 0 < (2 * Real.pi) := by positivity [Real.pi_pos]
    have hI0 :
        IntegrableOn (fun t : ℝ => Real.exp (-(2 * Real.pi) * t))
        (Set.Ici (1 : ℝ)) volume := by
      simpa [pow_zero, one_mul] using!
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici
          (n := 0) (b := (2 * Real.pi)) hb)
    have hI1 :
        IntegrableOn (fun t : ℝ => t * Real.exp (-(2 * Real.pi) * t))
        (Set.Ici (1 : ℝ)) volume := by
      simpa [pow_one] using!
        (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici
          (n := 1) (b := (2 * Real.pi)) hb)
    have hdomIci :
        IntegrableOn (fun t : ℝ => (Cφ * (1 + 2 * t)) * Real.exp (-(2 * Real.pi) * t))
          (Set.Ici (1 : ℝ)) volume := by
      -- Split into `Cφ*exp(-2πt) + (2Cφ)*(t*exp(-2πt))`.
      have h1' :
          IntegrableOn (fun t : ℝ => (Cφ : ℝ) * Real.exp (-(2 * Real.pi) * t))
            (Set.Ici (1 : ℝ)) volume := by
        simpa [mul_assoc] using! hI0.const_mul (Cφ : ℝ)
      have h2' :
          IntegrableOn (fun t : ℝ => (2 * (Cφ : ℝ)) * (t * Real.exp (-(2 * Real.pi) * t)))
            (Set.Ici (1 : ℝ)) volume := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! hI1.const_mul (2 * (Cφ : ℝ))
      have hsum :
          IntegrableOn (fun t : ℝ =>
              (Cφ : ℝ) * Real.exp (-(2 * Real.pi) * t) +
                (2 * (Cφ : ℝ)) * (t * Real.exp (-(2 * Real.pi) * t)))
            (Set.Ici (1 : ℝ)) volume := h1'.add h2'
      refine hsum.congr_fun ?_ measurableSet_Ici
      intro t ht
      ring
    have hdom :
        IntegrableOn (fun t : ℝ => (Cφ * (1 + 2 * t)) * Real.exp (-(2 * Real.pi) * t))
          (Set.Ioi (1 : ℝ)) volume := hdomIci.mono_set (by
          intro t ht; exact le_of_lt (by simpa [Set.mem_Ioi] using! ht))
    -- Measurability via continuity on `Ioi 1`.
    have hcont_axis :
        ContinuousOn (fun t : ℝ => f0 u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) := by
      -- On `t>1`, rewrite through `varphi.resToImagAxis`.
      have hcontφ : ContinuousOn (fun t : ℝ => varphi.resToImagAxis t) (Set.Ioi (1 : ℝ)) :=
        (VarphiExpBounds.continuousOn_varphi_resToImagAxis_Ici_one.mono (by
          intro t ht
          exact le_of_lt (by simpa [Set.mem_Ioi] using! ht)))
      have hpoly : Continuous fun t : ℝ => ((2 : ℂ) * ((t : ℂ) * Complex.I) - 1) := by
        fun_prop
      have hexp : Continuous fun t : ℝ => expU u ((t : ℂ) * Complex.I) := by
        unfold expU
        fun_prop
      have hmul := (hcontφ.mul hpoly.continuousOn).mul hexp.continuousOn
      refine hmul.congr ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
      simp [f0, hvarphi_axis t ht0, mul_assoc]
    have hmeas :
        AEStronglyMeasurable (fun t : ℝ => f0 u ((t : ℂ) * Complex.I))
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
      hcont_axis.aestronglyMeasurable measurableSet_Ioi
    have hgintegrable :
        MeasureTheory.Integrable
          (fun t : ℝ => (Cφ * (1 + 2 * t)) * Real.exp (-(2 * Real.pi) * t))
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using! hdom
    have hinter :
        MeasureTheory.Integrable (fun t : ℝ => f0 u ((t : ℂ) * Complex.I))
          (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      refine MeasureTheory.Integrable.mono' hgintegrable hmeas ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht1 : 1 ≤ t := le_of_lt ht
      have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht1
      have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht1
      have hvarphi_norm :
          ‖varphi' ((t : ℂ) * Complex.I)‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) := by
        have hres := hCφ t ht1
        simpa [hvarphi_axis t htpos] using! hres
      have hexp_le : ‖expU u ((t : ℂ) * Complex.I)‖ ≤ 1 := by
        -- `‖expU‖ = exp(-π*u*t) ≤ 1` for `u,t ≥ 0`.
        have hn : ‖expU u ((t : ℂ) * Complex.I)‖ = Real.exp (-Real.pi * u * t) :=
          norm_expU_mul_I (u := u) (t := t)
        have hnonpos : -Real.pi * u * t ≤ 0 := by
          have : 0 ≤ Real.pi * u * t := by positivity [Real.pi_pos, hu0, ht0]
          linarith
        have : Real.exp (-Real.pi * u * t) ≤ 1 := by
          simpa using! (Real.exp_le_one_iff.2 hnonpos)
        simpa [hn] using! this
      have hlin := hlin_bound t ht0
      -- Bound `‖f0‖`.
      calc
        ‖f0 u ((t : ℂ) * Complex.I)‖ =
            ‖varphi' ((t : ℂ) * Complex.I)‖ *
              ‖(2 : ℂ) * ((t : ℂ) * Complex.I) - 1‖ *
                ‖expU u ((t : ℂ) * Complex.I)‖ := by
          simp [f0]
        _ ≤ (Cφ * Real.exp (-(2 * Real.pi) * t)) * (1 + 2 * t) * 1 := by
              have hCφ0 : 0 ≤ Cφ := by
                have h1 := hCφ 1 (by simp)
                have hexp1 : 0 < Real.exp (-(2 * Real.pi) * (1 : ℝ)) := by positivity
                have hprod : 0 ≤ Cφ * Real.exp (-(2 * Real.pi) * (1 : ℝ)) :=
                  le_trans (norm_nonneg _) h1
                exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using! hprod) hexp1
              have hCφexp0 : 0 ≤ Cφ * Real.exp (-(2 * Real.pi) * t) :=
                mul_nonneg hCφ0 (le_of_lt (Real.exp_pos _))
              have h12t0 : 0 ≤ (1 + 2 * t) := by nlinarith [ht0]
              have hac :
                  ‖varphi' ((t : ℂ) * Complex.I)‖ *
                      ‖(2 : ℂ) * ((t : ℂ) * Complex.I) - 1‖ ≤
                    (Cφ * Real.exp (-(2 * Real.pi) * t)) * (1 + 2 * t) :=
                mul_le_mul hvarphi_norm hlin (norm_nonneg _) hCφexp0
              have hace :
                  (‖varphi' ((t : ℂ) * Complex.I)‖ *
                      ‖(2 : ℂ) * ((t : ℂ) * Complex.I) - 1‖) *
                      ‖expU u ((t : ℂ) * Complex.I)‖ ≤
                    ((Cφ * Real.exp (-(2 * Real.pi) * t)) * (1 + 2 * t)) *
                      ‖expU u ((t : ℂ) * Complex.I)‖ :=
                mul_le_mul_of_nonneg_right hac (norm_nonneg _)
              have hbd0 :
                  0 ≤ (Cφ * Real.exp (-(2 * Real.pi) * t)) * (1 + 2 * t) :=
                mul_nonneg hCφexp0 h12t0
              exact le_mul_of_le_mul_of_nonneg_left hace hexp_le hbd0
        _ = (Cφ * (1 + 2 * t)) * Real.exp (-(2 * Real.pi) * t) := by ring
    have hinterOn :
        MeasureTheory.IntegrableOn (fun t : ℝ => f0 u ((t : ℂ) * Complex.I))
          (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
      simpa [MeasureTheory.IntegrableOn] using! hinter
    exact hinterOn.congr_fun hEq.symm measurableSet_Ioi
  -- Right boundary: use `f0_add_one_sub` plus integrability of the correction term.
  have hint_right :
        MeasureTheory.IntegrableOn (fun t : ℝ => fStrip ((1 : ℂ) + t * Complex.I))
          (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
    -- AE equality `f0(1+ti) = f0(ti) + 2*varphi'(ti)*expU(ti)` on `t>1`.
    have hEqAE :
        (fun t : ℝ => f0 u ((1 : ℂ) + (t : ℂ) * Complex.I)) =ᵐ[
          MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))]
          fun t : ℝ =>
            f0 u ((t : ℂ) * Complex.I) +
              (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
      have h := f0_add_one_sub (u := u) hu (t := t) ht0
      -- `a - b = c` implies `a = b + c`.
      have h' :
          f0 u ((1 : ℂ) + (t : ℂ) * Complex.I) =
            f0 u ((t : ℂ) * Complex.I) +
              (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) := by
        -- `eq_add_of_sub_eq` gives `a = c + b`.
        simpa [add_comm, add_left_comm, add_assoc] using! (eq_add_of_sub_eq h)
      simpa using! h'
    have hint_corr :
        MeasureTheory.IntegrableOn
          (fun t : ℝ =>
            (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)))
          (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
      -- Dominate by `‖2‖*Cφ*exp(-2π t)`.
      rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ, hCφ⟩
      have hb : 0 < (2 * Real.pi) := by positivity [Real.pi_pos]
      have hI0 :
          IntegrableOn (fun t : ℝ => Real.exp (-(2 * Real.pi) * t))
            (Set.Ici (1 : ℝ)) volume := by
        simpa [pow_zero, one_mul] using!
          (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici
            (n := 0) (b := (2 * Real.pi)) hb)
      have hdomIci :
          IntegrableOn (fun t : ℝ => (‖(2 : ℂ)‖ * Cφ) * Real.exp (-(2 * Real.pi) * t))
            (Set.Ici (1 : ℝ)) volume := by
        simpa [mul_assoc] using! hI0.const_mul (‖(2 : ℂ)‖ * Cφ)
      have hdom :
          IntegrableOn (fun t : ℝ => (‖(2 : ℂ)‖ * Cφ) * Real.exp (-(2 * Real.pi) * t))
            (Set.Ioi (1 : ℝ)) volume := hdomIci.mono_set (by
              intro t ht
              exact le_of_lt (by simpa [Set.mem_Ioi] using! ht))
      have hmeas :
          AEStronglyMeasurable
            (fun t : ℝ =>
              (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)))
            (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
        have hcontφ : ContinuousOn (fun t : ℝ => varphi.resToImagAxis t) (Set.Ioi (1 : ℝ)) :=
          (VarphiExpBounds.continuousOn_varphi_resToImagAxis_Ici_one.mono (by
            intro t ht
            exact le_of_lt (by simpa [Set.mem_Ioi] using! ht)))
        have hexp : Continuous fun t : ℝ => expU u ((t : ℂ) * Complex.I) := by
          unfold expU
          fun_prop
        have hcontVarphi' :
            ContinuousOn (fun t : ℝ => varphi' ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) := by
          refine hcontφ.congr ?_
          intro t ht
          have ht0 : 0 < t := lt_trans (show (0 : ℝ) < 1 from zero_lt_one) (by
            simpa [Set.mem_Ioi] using! ht)
          simp [hvarphi_axis t ht0]
        have hcontMul :
            ContinuousOn
              (fun t : ℝ => varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I))
              (Set.Ioi (1 : ℝ)) := hcontVarphi'.mul hexp.continuousOn
        have hcont :
            ContinuousOn
              (fun t : ℝ =>
                (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)))
              (Set.Ioi (1 : ℝ)) :=
          (continuous_const.continuousOn.mul hcontMul)
        exact hcont.aestronglyMeasurable measurableSet_Ioi
      have hgintegrable :
          MeasureTheory.Integrable
            (fun t : ℝ => (‖(2 : ℂ)‖ * Cφ) * Real.exp (-(2 * Real.pi) * t))
            (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
        simpa [MeasureTheory.IntegrableOn] using! hdom
      have hinter :
          MeasureTheory.Integrable
            (fun t : ℝ =>
              (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)))
            (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
        refine MeasureTheory.Integrable.mono' hgintegrable hmeas ?_
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        have ht1 : 1 ≤ t := le_of_lt (by simpa [Set.mem_Ioi] using! ht)
        have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht1
        have hvarphi_norm :
            ‖varphi' ((t : ℂ) * Complex.I)‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) := by
          simpa [hvarphi_axis t htpos] using! hCφ t ht1
        have hexp_le : ‖expU u ((t : ℂ) * Complex.I)‖ ≤ 1 := by
          have hn : ‖expU u ((t : ℂ) * Complex.I)‖ = Real.exp (-Real.pi * u * t) :=
            norm_expU_mul_I (u := u) (t := t)
          have hnonpos : -Real.pi * u * t ≤ 0 := by
            have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht1
            have : 0 ≤ Real.pi * u * t := by positivity [Real.pi_pos, hu0, ht0]
            linarith
          have : Real.exp (-Real.pi * u * t) ≤ 1 := by
            simpa using! (Real.exp_le_one_iff.2 hnonpos)
          simpa [hn] using! this
        have hCφ0 : 0 ≤ Cφ := by
          have h1 := hCφ 1 (by simp)
          have hexp1 : 0 < Real.exp (-(2 * Real.pi) * (1 : ℝ)) := by positivity
          have hprod : 0 ≤ Cφ * Real.exp (-(2 * Real.pi) * (1 : ℝ)) :=
            le_trans (norm_nonneg _) h1
          exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using! hprod) hexp1
        have hCφexp0 : 0 ≤ Cφ * Real.exp (-(2 * Real.pi) * t) :=
          mul_nonneg hCφ0 (le_of_lt (Real.exp_pos _))
        have hnorm2 : 0 ≤ ‖(2 : ℂ)‖ := norm_nonneg _
        have hvar0 : 0 ≤ ‖varphi' ((t : ℂ) * Complex.I)‖ := norm_nonneg _
        have hexp0 : 0 ≤ ‖expU u ((t : ℂ) * Complex.I)‖ := norm_nonneg _
        calc
          ‖(2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I))‖
              =
                ‖(2 : ℂ)‖ *
                  (‖varphi' ((t : ℂ) * Complex.I)‖ *
                    ‖expU u ((t : ℂ) * Complex.I)‖) := by
            simp
          _ ≤ (‖(2 : ℂ)‖ * Cφ) * Real.exp (-(2 * Real.pi) * t) := by
                have hmul1 :
                    ‖varphi' ((t : ℂ) * Complex.I)‖ * ‖expU u ((t : ℂ) * Complex.I)‖ ≤
                      (Cφ * Real.exp (-(2 * Real.pi) * t)) *
                        ‖expU u ((t : ℂ) * Complex.I)‖ :=
                  mul_le_mul_of_nonneg_right hvarphi_norm hexp0
                have hmul2 :
                    (Cφ * Real.exp (-(2 * Real.pi) * t)) * ‖expU u ((t : ℂ) * Complex.I)‖ ≤
                      (Cφ * Real.exp (-(2 * Real.pi) * t)) * 1 :=
                  mul_le_mul_of_nonneg_left hexp_le hCφexp0
                have hmul :
                    ‖varphi' ((t : ℂ) * Complex.I)‖ * ‖expU u ((t : ℂ) * Complex.I)‖ ≤
                      (Cφ * Real.exp (-(2 * Real.pi) * t)) * 1 :=
                  le_trans hmul1 hmul2
                have hmul3 :
                    ‖(2 : ℂ)‖ *
                        (‖varphi' ((t : ℂ) * Complex.I)‖ *
                          ‖expU u ((t : ℂ) * Complex.I)‖) ≤
                      ‖(2 : ℂ)‖ * ((Cφ * Real.exp (-(2 * Real.pi) * t)) * 1) :=
                  mul_le_mul_of_nonneg_left hmul hnorm2
                simpa [mul_assoc, mul_left_comm, mul_comm] using! hmul3
      simpa [MeasureTheory.IntegrableOn] using! hinter
    have hint_f0_left :
        MeasureTheory.IntegrableOn (fun t : ℝ => f0 u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
          MeasureTheory.volume := by
      have hEq : EqOn (fun t : ℝ => fStrip ((0 : ℂ) + t * Complex.I))
          (fun t : ℝ => f0 u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) := by
        intro t ht
        have htRe : (((0 : ℂ) + t * Complex.I) : ℂ).re ∈ Set.uIcc (0 : ℝ) 1 := by
          simp
        dsimp [fStrip]
        simp
      exact hint_left.congr_fun hEq measurableSet_Ioi
    have hint_sum :
        MeasureTheory.IntegrableOn
          (fun t : ℝ =>
            f0 u ((t : ℂ) * Complex.I) +
              (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)))
          (Set.Ioi (1 : ℝ)) MeasureTheory.volume := hint_f0_left.add hint_corr
    have hint_f0_right :
        MeasureTheory.IntegrableOn (fun t : ℝ => f0 u ((1 : ℂ) + (t : ℂ) * Complex.I))
          (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
      hint_sum.congr_fun_ae hEqAE.symm
    -- Finally transport to `fStrip`.
    have hEq : EqOn (fun t : ℝ => f0 u ((1 : ℂ) + (t : ℂ) * Complex.I))
        (fun t : ℝ => fStrip ((1 : ℂ) + t * Complex.I)) (Set.Ioi (1 : ℝ)) := by
      intro t ht
      have htRe : (((1 : ℂ) + t * Complex.I) : ℂ).re ∈ Set.uIcc (0 : ℝ) 1 := by
        have : (((1 : ℂ) + t * Complex.I) : ℂ).re = (1 : ℝ) := by simp
        simp
      dsimp [fStrip]
      simp
    exact hint_f0_right.congr_fun hEq measurableSet_Ioi
  /- Uniform decay as `Im → ∞` (needed for `OpenRectangular`). -/
  have htendsto :
      ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖fStrip z‖ < ε := by
    intro ε hε
    -- Use the Big-O bound for `varphi` at `Im → ∞`.
    rcases (VarphiBounds.varphi_isBigO_exp_neg_two_pi :
        (varphi : ℍ → ℂ) =O[UpperHalfPlane.atImInfty] fun z : ℍ =>
          Real.exp (-(2 * Real.pi) * z.im)).exists_pos with ⟨Cφ, hCφpos, hCφ⟩
    have hCφ' :
        ∀ᶠ z : ℍ in UpperHalfPlane.atImInfty,
          ‖varphi z‖ ≤ Cφ * ‖Real.exp (-(2 * Real.pi) * z.im)‖ := hCφ.bound
    rcases (Filter.eventually_atImInfty).1 hCφ' with ⟨A0, hA0⟩
    let A : ℝ := max A0 1
    have hb : 0 < (2 * Real.pi) := by positivity [Real.pi_pos]
    have hlim :
        Tendsto (fun y : ℝ => y * Real.exp (-(2 * Real.pi) * y)) atTop (𝓝 (0 : ℝ)) := by
      simpa [Real.rpow_one] using!
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (1 : ℝ)) (b := (2 * Real.pi)) hb)
    have hε' : 0 < ε / (5 * Cφ) := by
      have hden : 0 < (5 * Cφ) := mul_pos (by norm_num) hCφpos
      exact div_pos hε hden
    have hEv :
        ∀ᶠ y : ℝ in atTop, |y * Real.exp (-(2 * Real.pi) * y)| < ε / (5 * Cφ) := by
      have habs :
          Tendsto (fun y : ℝ => |y * Real.exp (-(2 * Real.pi) * y)|) atTop (𝓝 (0 : ℝ)) := by
        simpa using! hlim.abs
      exact (tendsto_order.1 habs).2 _ hε'
    rcases (eventually_atTop.1 hEv) with ⟨M0, hM0⟩
    let M : ℝ := max A M0
    refine ⟨M, ?_⟩
    intro z hzIm
    by_cases hzRe : z.re ∈ Set.uIcc (0 : ℝ) 1
    · -- On the strip, use a crude bound `‖2z-1‖ ≤ 5*z.im` for `Im(z) ≥ 1`.
      have hzIm1 : (1 : ℝ) ≤ z.im := by
        have h1A : (1 : ℝ) ≤ A := by
          dsimp [A]
          exact le_max_right A0 1
        have hAM : A ≤ M := by
          dsimp [M]
          exact le_max_left A M0
        have h1M : (1 : ℝ) ≤ M := le_trans h1A hAM
        exact le_trans h1M hzIm
      have hzIm_pos : 0 < z.im := lt_of_lt_of_le (by norm_num) hzIm1
      have hzImA : A0 ≤ z.im := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hzIm)
      have hvarphi_norm :
          ‖varphi' z‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * z.im) := by
        have h0 := hA0 ⟨z, hzIm_pos⟩ hzImA
        have hEq' : varphi' z = varphi ⟨z, hzIm_pos⟩ := by
          simp [varphi', hzIm_pos]
        have hEq : varphi ⟨z, hzIm_pos⟩ = varphi' z := hEq'.symm
        have hnorm : ‖Real.exp (-(2 * Real.pi) * (UpperHalfPlane.mk z hzIm_pos).im)‖ =
            Real.exp (-(2 * Real.pi) * z.im) := by
          simp [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        have h0' : ‖varphi' z‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * z.im) := by
          simpa [hEq, hnorm] using! h0
        exact h0'
      have hlin :
          ‖((2 : ℂ) * z - 1)‖ ≤ 5 * z.im := by
        -- A short estimate for `‖(2 : ℂ) * z - 1‖` in terms of `z.im`.
        have h2z :
            ‖(2 : ℂ) * z - 1‖ ≤ 2 * ‖z‖ + 1 := by
          simpa [sub_eq_add_neg, norm_mul, add_assoc, add_left_comm, add_comm] using!
            (norm_add_le ((2 : ℂ) * z) (-(1 : ℂ)))
        have hre_abs : |z.re| ≤ 1 := by
          have hzRe' : z.re ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! hzRe
          have hzRe0 : 0 ≤ z.re := hzRe'.1
          have hzRe1 : z.re ≤ 1 := hzRe'.2
          have hzRe1' : |z.re| ≤ 1 := by
            calc
              |z.re| = z.re := abs_of_nonneg hzRe0
              _ ≤ 1 := hzRe1
          exact hzRe1'
        have hznorm : ‖z‖ ≤ 1 + z.im := by
          have hznorm' :
              ‖z‖ ≤ |z.re| + |z.im| :=
            norm_le_abs_re_add_abs_im z
          have him_abs : |z.im| = z.im := by
            have : 0 ≤ z.im := le_of_lt hzIm_pos
            simp [abs_of_nonneg this]
          calc
            ‖z‖ ≤ |z.re| + |z.im| := hznorm'
            _ ≤ 1 + z.im := by
                  refine add_le_add hre_abs ?_
                  -- `|z.im| = z.im` since `0 ≤ z.im`.
                  exact ge_of_eq (id (Eq.symm him_abs))
        linarith
      have hexp_le : ‖expU u z‖ ≤ 1 := by
        -- `‖expU‖ = exp(-π*u*Im(z)) ≤ 1`.
        unfold expU
        have hre :
            ((Real.pi : ℂ) * Complex.I * (u : ℂ) * z).re = -Real.pi * u * z.im := by
          simp [mul_assoc]
        have hn : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (u : ℂ) * z)‖ =
            Real.exp (-Real.pi * u * z.im) := by
          simp [Complex.norm_exp, hre]
        have hnonpos : -Real.pi * u * z.im ≤ 0 := by
          have : 0 ≤ Real.pi * u * z.im := by
            have hzIm0 : 0 ≤ z.im := le_of_lt hzIm_pos
            have hpi : 0 ≤ (Real.pi : ℝ) := le_of_lt Real.pi_pos
            exact mul_nonneg (mul_nonneg hpi hu0) hzIm0
          linarith
        have : Real.exp (-Real.pi * u * z.im) ≤ 1 := Real.exp_le_one_iff.2 hnonpos
        simpa [hn] using! this
      have hmain :
          ‖fStrip z‖ ≤ (5 * Cφ) * (z.im * Real.exp (-(2 * Real.pi) * z.im)) := by
        have : fStrip z = f0 u z := by
          dsimp [fStrip]
          exact dif_pos hzRe
        have hgoal :
            (‖varphi' z‖ * ‖(2 : ℂ) * z - 1‖) * ‖expU u z‖ ≤
              (5 * Cφ) * (z.im * Real.exp (-(2 * Real.pi) * z.im)) := by
          have hzIm0 : 0 ≤ z.im := le_of_lt hzIm_pos
          have hCφ0 : 0 ≤ Cφ := le_of_lt hCφpos
          have hCφexp0 : 0 ≤ Cφ * Real.exp (-(2 * Real.pi) * z.im) :=
            mul_nonneg hCφ0 (le_of_lt (Real.exp_pos _))
          have h5z0 : 0 ≤ 5 * z.im := by nlinarith [hzIm0]
          have hprod0 : 0 ≤ (Cφ * Real.exp (-(2 * Real.pi) * z.im)) * (5 * z.im) :=
            mul_nonneg hCφexp0 h5z0
          have hac :
              ‖varphi' z‖ * ‖(2 : ℂ) * z - 1‖ ≤
                (Cφ * Real.exp (-(2 * Real.pi) * z.im)) * (5 * z.im) :=
            mul_le_mul hvarphi_norm hlin (norm_nonneg _) hCφexp0
          have hace :
              (‖varphi' z‖ * ‖(2 : ℂ) * z - 1‖) * ‖expU u z‖ ≤
                ((Cφ * Real.exp (-(2 * Real.pi) * z.im)) * (5 * z.im)) * ‖expU u z‖ :=
            mul_le_mul_of_nonneg_right hac (norm_nonneg _)
          have hce :
              ((Cφ * Real.exp (-(2 * Real.pi) * z.im)) * (5 * z.im)) * ‖expU u z‖ ≤
                ((Cφ * Real.exp (-(2 * Real.pi) * z.im)) * (5 * z.im)) * 1 :=
            mul_le_mul_of_nonneg_left hexp_le hprod0
          linarith
        simpa [this, f0, mul_assoc] using! hgoal
      have hzImM0 : M0 ≤ z.im := le_trans (le_max_right _ _) hzIm
      have hsmall : (5 * Cφ) * (z.im * Real.exp (-(2 * Real.pi) * z.im)) < ε := by
        have htmpAbs :
            |z.im| * Real.exp (-(2 * Real.pi) * z.im) < ε / (5 * Cφ) := by
          have htmpAbs' : |z.im * Real.exp (-(2 * Real.pi) * z.im)| < ε / (5 * Cφ) :=
            hM0 (z.im) hzImM0
          -- `|a*b| = |a|*|b|`, and `|exp(...)| = exp(...)`.
          simpa [abs_mul, abs_of_nonneg (Real.exp_pos _).le] using! htmpAbs'
        have hzIm0 : 0 ≤ z.im := le_of_lt hzIm_pos
        have htmp :
            z.im * Real.exp (-(2 * Real.pi) * z.im) < ε / (5 * Cφ) := by
          have htmp' := htmpAbs
          simp only [abs_of_nonneg hzIm0, neg_mul] at htmp'
          have hmul : -(2 * Real.pi * z.im) = -(2 * Real.pi) * z.im := by ring
          rw [hmul] at htmp'
          exact htmp'
        have hden : 0 < (5 * Cφ) := mul_pos (by norm_num) hCφpos
        exact (lt_div_iff₀' hden).mp htmp
      exact lt_of_le_of_lt hmain hsmall
    · -- Outside the strip, `fStrip = 0`.
      have : fStrip z = 0 := by
        dsimp [fStrip]
        exact dif_neg hzRe
      simp [this, hε]
  /- Apply open-rectangle deformation and simplify. -/
  have hrect :
      (∫ (x : ℝ) in (0 : ℝ)..1, fStrip (x + (1 : ℝ) * Complex.I)) +
          (Complex.I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ),
            fStrip ((1 : ℂ) + t * Complex.I)) -
          (Complex.I • ∫ (t : ℝ) in Set.Ioi (1 : ℝ),
            fStrip ((0 : ℂ) + t * Complex.I)) = 0 := by
    have hrect' :=
      integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ)) (f := fStrip) (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ)) hcont
        (s := (∅ : Set ℂ)) (by simp) hdiff hint_left hint_right htendsto
    simpa [min_eq_left (zero_le_one : (0 : ℝ) ≤ 1),
      max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] using! hrect'
  -- Replace the horizontal integral and vertical integrals by `f0` (on the strip).
  have hhor :
      (∫ (x : ℝ) in (0 : ℝ)..1, fStrip (x + (1 : ℝ) * Complex.I)) =
        ∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hxRe : (x + (1 : ℝ) * Complex.I).re ∈ Set.uIcc (0 : ℝ) 1 := by
      simpa using! hx
    have hxEq : fStrip (x + (1 : ℝ) * Complex.I) = f0 u (x + (1 : ℝ) * Complex.I) := by
      dsimp [fStrip]
      exact dif_pos hxRe
    simpa [zI, one_mul] using! hxEq
  have hleft :
      (∫ (t : ℝ) in Set.Ioi (1 : ℝ), fStrip ((0 : ℂ) + t * Complex.I)) =
        ∫ t in Set.Ioi (1 : ℝ), f0 u ((t : ℂ) * Complex.I) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    simp [fStrip]
  have hright :
      (∫ (t : ℝ) in Set.Ioi (1 : ℝ), fStrip ((1 : ℂ) + t * Complex.I)) =
        ∫ t in Set.Ioi (1 : ℝ), f0 u ((1 : ℂ) + (t : ℂ) * Complex.I) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    simp [fStrip]
  -- Use `f0_add_one_sub` to rewrite the vertical difference.
  have hvert :
      (∫ t in Set.Ioi (1 : ℝ), f0 u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
          ∫ t in Set.Ioi (1 : ℝ), f0 u ((t : ℂ) * Complex.I) =
        ∫ t in Set.Ioi (1 : ℝ),
          (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) := by
    let f : ℝ → ℂ := fun t => f0 u ((1 : ℂ) + (t : ℂ) * Complex.I)
    let g : ℝ → ℂ := fun t => f0 u ((t : ℂ) * Complex.I)
    let corr : ℝ → ℂ :=
      fun t => (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I))
    let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))
    have hint_g : MeasureTheory.IntegrableOn g (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
      refine hint_left.congr_fun ?_ measurableSet_Ioi
      intro t ht
      simp [fStrip, g]
    have hint_f : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
      refine hint_right.congr_fun ?_ measurableSet_Ioi
      intro t ht
      simp [fStrip, f]
    have hf : MeasureTheory.Integrable f μ := by
      simpa [μ, MeasureTheory.IntegrableOn] using! hint_f
    have hg : MeasureTheory.Integrable g μ := by
      simpa [μ, MeasureTheory.IntegrableOn] using! hint_g
    have hEqμ : (fun t : ℝ => f t - g t) =ᵐ[μ] corr := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
      simpa [f, g, corr] using! (f0_add_one_sub (u := u) hu (t := t) ht0)
    have hIntEqμ : (∫ t, (f t - g t) ∂μ) = ∫ t, corr t ∂μ := by
      simpa using! (MeasureTheory.integral_congr_ae hEqμ)
    calc
      (∫ t, f t ∂μ) - ∫ t, g t ∂μ = ∫ t, (f t - g t) ∂μ := by
        simpa using! (MeasureTheory.integral_sub hf hg).symm
      _ = ∫ t, corr t ∂μ := hIntEqμ
  -- Identify `I₆' u` with the same vertical integral (up to the contour factor `I`).
  have hI6 :
      I₆' u =
        Complex.I • ∫ t in Set.Ioi (1 : ℝ),
          (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) := by
    rw [RealIntegrals.I₆']
    have hIci :
        (∫ t in Set.Ici (1 : ℝ), RealIntegrands.Φ₆ u t) =
          ∫ t in Set.Ioi (1 : ℝ), RealIntegrands.Φ₆ u t := by
      exact integral_Ici_eq_integral_Ioi
    have hparam :
        (∫ t in Set.Ioi (1 : ℝ), RealIntegrands.Φ₆ u t) =
          ∫ t in Set.Ioi (1 : ℝ),
            (Complex.I : ℂ) *
              (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht' : t ∈ Set.Ici (1 : ℝ) := le_of_lt (by simpa [Set.mem_Ioi] using! ht)
      simp [RealIntegrands.Φ₆, ComplexIntegrands.Φ₆', expU,
        MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t) ht', mul_left_comm, mul_comm]
    simp [hIci, hparam, MeasureTheory.integral_const_mul, smul_eq_mul, mul_left_comm, mul_comm]
  -- Combine `hrect` with `hvert` and rewrite `I₆'`.
  have hrect0 := hrect
  rw [hhor, hright, hleft] at hrect0
  -- Substitute the vertical difference and cancel.
  have hrect1 :
      (∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) +
        Complex.I • ∫ t in Set.Ioi (1 : ℝ),
          (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) = 0 := by
    -- From `hrect0`: `H + I•R - I•L = 0`, and `R - L = corr`.
    let R : ℂ := ∫ t in Set.Ioi (1 : ℝ), f0 u ((1 : ℂ) + (t : ℂ) * Complex.I)
    let L : ℂ := ∫ t in Set.Ioi (1 : ℝ), f0 u ((t : ℂ) * Complex.I)
    have hrect0' :
        (∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) +
            ((Complex.I : ℂ) * R - (Complex.I : ℂ) * L) = 0 := by
      simpa [R, L, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_eq_mul] using! hrect0
    have hmul : (Complex.I : ℂ) * R - (Complex.I : ℂ) * L = (Complex.I : ℂ) * (R - L) := by
      simp [mul_sub]
    have hrect0'' :
        (∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) + (Complex.I : ℂ) * (R - L) = 0 := by
      simpa [hmul] using! hrect0'
    have hRL :
        R - L =
          ∫ t in Set.Ioi (1 : ℝ),
            (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) := by
      simpa [R, L] using! hvert
    have hrect0''' :
        (∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) +
            (Complex.I : ℂ) *
              (∫ t in Set.Ioi (1 : ℝ),
                (2 : ℂ) *
                  (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I))) = 0 := by
      simpa [hRL] using! hrect0''
    simpa [smul_eq_mul] using! hrect0'''
-- Final step.
  lia


end SpecialValuesAux

end

end SpherePacking.Dim24
