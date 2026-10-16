-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingContinuation.TailIntegrand


/-!
# Analyticity of the subleading continuation

This file shows that `rhsBSubLeading` is analytic on the domain `Re u > 0` with `u ≠ 2`, and
relates the explicit tail integral of the leading term to the closed-form correction
`BleadingCorrectionC` on the real range `u > 2`.

## Main statements
* `analyticOnNhd_rhsBSubLeading`
* `integral_Ioi_one_BleadingTermC_mul_exp_neg_pi_complex`

-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceBSubLeadingCont.Private

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Topology

open Complex Filter MeasureTheory Real Set SchwartzMap
open UpperHalfPlane

open LaplaceFourierCont
open LaplaceFourierCont.PrivateDefs

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

lemma hasDerivAt_tailIntegral (u0 : ℂ) (hu0 : 0 < u0.re) :
    HasDerivAt (fun u : ℂ => ∫ t in Set.Ioi (1 : ℝ), tailIntegrand u t)
      (∫ t in Set.Ioi (1 : ℝ), tailIntegrandDeriv u0 t) u0 := by
  let μ1 : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  -- Choose a ball around `u0` staying in the right half-plane.
  let r : ℝ := u0.re / 2
  have hrpos : 0 < r := half_pos hu0
  have hreBall : ∀ {u : ℂ}, u ∈ Metric.ball u0 r → (r : ℝ) ≤ u.re := by
    intro u hu
    have hge : u0.re - r ≤ u.re :=
      LaplaceBKernelAnalytic.re_ge_of_mem_ball (u := u) (u0 := u0) (r := r) hu
    have : u0.re - r = r := by
      dsimp [r]
      ring_nf
    simpa [this] using! hge
  have hF_meas :
      ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (tailIntegrand u) μ1 := by
    refine Filter.Eventually.of_forall ?_
    intro u
    simpa [μ1] using! aestronglyMeasurable_tailIntegrand_Ioi_one (u := u)
  have hF_int : Integrable (tailIntegrand u0) μ1 := by
    -- Use `Integrable.mono'` with the polynomial majorant.
    have hmeas : AEStronglyMeasurable (tailIntegrand u0) μ1 := by
      simpa [μ1] using! aestronglyMeasurable_tailIntegrand_Ioi_one (u := u0)
    have hbound :
        ∀ᵐ t : ℝ ∂μ1, ‖tailIntegrand u0 t‖ ≤ (polyBound t) * Real.exp (-Real.pi * u0.re * t) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
      have ht0 : 0 < t := lt_trans (by norm_num) ht
      have hpoly :
          ‖BKernel0 t - (BleadingTermR t : ℂ)‖ ≤ polyBound t := by
        simpa [polyBound] using! (norm_BKernel0_sub_leading_le_poly (t := t) ht1)
      have hexp :
          ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ = Real.exp (-Real.pi * u0.re * t) := by
        simpa [mul_assoc] using! LaplaceBKernelAnalytic.norm_kernelExp (u := u0) (t := t)
      calc
        ‖tailIntegrand u0 t‖
            = ‖BKernel0 t - (BleadingTermR t : ℂ)‖ * ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ := by
                simp [tailIntegrand, mul_assoc]
        _ ≤ (polyBound t) * Real.exp (-Real.pi * u0.re * t) := by
              have hmul :
                  ‖BKernel0 t - (BleadingTermR t : ℂ)‖ *
                      ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ ≤
                    (polyBound t) * ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ :=
                mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
              exact le_of_le_of_eq hmul (congrArg (HMul.hMul (polyBound t)) hexp)
    have hintg : Integrable (fun t : ℝ => (polyBound t) * Real.exp (-Real.pi * u0.re * t)) μ1 := by
      have :
          IntegrableOn (fun t : ℝ => (polyBound t) * Real.exp (-Real.pi * u0.re * t))
            (Set.Ioi (1 : ℝ)) volume :=
        integrable_polyBound_mul_exp_Ioi_one (uMin := u0.re) hu0
      simpa [μ1, MeasureTheory.IntegrableOn] using! this
    exact Integrable.mono' hintg hmeas hbound
  have hF'_meas : AEStronglyMeasurable (tailIntegrandDeriv u0) μ1 := by
    simpa [μ1] using! aestronglyMeasurable_tailIntegrandDeriv_Ioi_one (u := u0)
  -- Uniform bound on the derivative inside the ball.
  let bound : ℝ → ℝ := fun t => (Real.pi * t) * (polyBound t) * Real.exp (-Real.pi * r * t)
  have h_bound :
      ∀ᵐ t : ℝ ∂μ1, ∀ u ∈ Metric.ball u0 r, ‖tailIntegrandDeriv u t‖ ≤ bound t := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht u hu
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    have hpoly :
        ‖BKernel0 t - (BleadingTermR t : ℂ)‖ ≤ polyBound t := by
      simpa [polyBound] using! (norm_BKernel0_sub_leading_le_poly (t := t) ht1)
    have hure : r ≤ u.re := hreBall hu
    have hexp :
        ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ = Real.exp (-Real.pi * u.re * t) := by
      simpa [mul_assoc] using! LaplaceBKernelAnalytic.norm_kernelExp (u := u) (t := t)
    have hexp_le :
        Real.exp (-Real.pi * u.re * t) ≤ Real.exp (-Real.pi * r * t) := by
      have ht0' : 0 ≤ t := le_of_lt ht0
      have hmul1 : Real.pi * r ≤ Real.pi * u.re :=
        mul_le_mul_of_nonneg_left hure Real.pi_pos.le
      simp_all
    have hct : ‖-(π : ℂ) * (t : ℂ)‖ = Real.pi * t := by
      have ht0' : 0 ≤ t := le_of_lt ht0
      calc
        ‖-(π : ℂ) * (t : ℂ)‖ = ‖-(π : ℂ)‖ * ‖(t : ℂ)‖ := by simp []
        _ = Real.pi * t := by
          simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0', Real.pi_pos.le]
    calc
      ‖tailIntegrandDeriv u t‖
          = ‖BKernel0 t - (BleadingTermR t : ℂ)‖ * ‖-(π : ℂ) * (t : ℂ)‖ *
              ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by
                simp [tailIntegrandDeriv, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (polyBound t) * (Real.pi * t) * Real.exp (-Real.pi * r * t) := by
            have hpoly0 : 0 ≤ polyBound t := le_trans (norm_nonneg _) hpoly
            have hb : ‖-(π : ℂ) * (t : ℂ)‖ ≤ Real.pi * t := by
              simpa using! (le_of_eq hct)
            have hpi0 : 0 ≤ Real.pi * t := by positivity [Real.pi_pos, le_of_lt ht0]
            have hc : ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ Real.exp (-Real.pi * r * t) := by
              exact le_of_eq_of_le hexp hexp_le
            have h1 :
                ‖BKernel0 t - (BleadingTermR t : ℂ)‖ * ‖-(π : ℂ) * (t : ℂ)‖ ≤
                  (polyBound t) * (Real.pi * t) := by
              exact mul_le_mul hpoly hb (norm_nonneg _) hpoly0
            have h10 : 0 ≤ (polyBound t) * (Real.pi * t) := mul_nonneg hpoly0 hpi0
            -- multiply by the third factor
            have h2 :
                (‖BKernel0 t - (BleadingTermR t : ℂ)‖ * ‖-(π : ℂ) * (t : ℂ)‖) *
                    ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤
                  ((polyBound t) * (Real.pi * t)) * Real.exp (-Real.pi * r * t) := by
              exact mul_le_mul h1 hc (norm_nonneg _) h10
            simpa [mul_assoc] using! h2
      _ = bound t := by
            simp [bound, mul_assoc, mul_left_comm, mul_comm]
  have hbound_int : Integrable bound μ1 := by
    have : IntegrableOn bound (Set.Ioi (1 : ℝ)) volume := by
      simpa [bound] using! (integrable_polyBoundDeriv_mul_exp_Ioi_one (uMin := r) hrpos)
    simpa [μ1, MeasureTheory.IntegrableOn] using! this
  have h :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun u : ℂ => tailIntegrand u)
        (μ := μ1) (x₀ := u0) (s := Metric.ball u0 r) (bound := bound)
        (Metric.ball_mem_nhds u0 hrpos)
        hF_meas hF_int hF'_meas h_bound hbound_int
        (by
          refine Filter.Eventually.of_forall ?_
          intro t u hu
          simpa using! hasDerivAt_tailIntegrand (u := u) (t := t)))
  exact h.2

lemma analyticAt_BleadingCorrectionC (u0 : ℂ) (hu0 : u0 ≠ (2 : ℂ)) :
    AnalyticAt ℂ BleadingCorrectionC u0 := by
  -- Rational combination of analytic functions; the only singularity is at `u = 2`.
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hden : (u0 - (2 : ℂ)) ^ (2 : ℕ) ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.2 hu0)
  -- Build the expression with `simp` and `fun_prop`.
  have hpoly :
      AnalyticAt ℂ
          (fun u : ℂ =>
            ((((10 : ℂ) - 3 * (Real.pi : ℂ)) * ((2 : ℂ) - u) + (3 : ℂ)) /
                  ((117 : ℂ) * ((Real.pi : ℂ) ^ (2 : ℕ)) * (u - (2 : ℂ)) ^ (2 : ℕ))))
          u0 := by
    -- numerator and denominator are analytic; denominator nonzero at `u0`.
    have hnum :
        AnalyticAt ℂ (fun u : ℂ => ((10 : ℂ) - 3 * (Real.pi : ℂ)) * ((2 : ℂ) - u) + (3 : ℂ)) u0
          := by
      fun_prop
    have hdenom :
        AnalyticAt ℂ (fun u : ℂ => (117 : ℂ) * ((Real.pi : ℂ) ^ (2 : ℕ)) * (u - (2 : ℂ)) ^ (2 :
        ℕ)) u0
          := by
      fun_prop
    have hdenom_ne :
        (fun u : ℂ => (117 : ℂ) * ((Real.pi : ℂ) ^ (2 : ℕ)) * (u - (2 : ℂ)) ^ (2 : ℕ)) u0 ≠ 0 := by
      have h117 : (117 : ℂ) ≠ 0 := by norm_num
      have hpi2 : ((Real.pi : ℂ) ^ (2 : ℕ)) ≠ 0 :=
        pow_ne_zero 2 hpi
      have hsub : (u0 - (2 : ℂ)) ^ (2 : ℕ) ≠ 0 := hden
      simp [h117, hpi2, hsub]
    exact hnum.div hdenom hdenom_ne
  have hexp : AnalyticAt ℂ (fun u : ℂ => Complex.exp (-(Real.pi : ℂ) * (u - (2 : ℂ)))) u0 := by
    fun_prop
  -- Multiply.
  unfold BleadingCorrectionC
  simpa [mul_assoc] using! hpoly.mul hexp

lemma differentiableAt_laplaceBKernelSubLeading (u0 : ℂ)
    (hu0 : u0 ∈ LaplaceDomains.domainPosNeTwo) :
    DifferentiableAt ℂ laplaceBKernelSubLeading u0 := by
  have hu0re : 0 < u0.re := by
    simpa [LaplaceDomains.domainPosNeTwo] using! hu0.1
  have hu0ne : u0 ≠ (2 : ℂ) := by
    have : u0 ∉ ({2} : Set ℂ) := hu0.2
    simpa [Set.mem_singleton_iff] using! this
  -- `Ioc (0,1]` part is handled as in the `Re u > 2` case.
  let μ0 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let r : ℝ := u0.re / 2
  have hrpos : 0 < r := half_pos hu0re
  have hureBall : ∀ {u : ℂ}, u ∈ Metric.ball u0 r → 0 ≤ u.re := by
    intro u hu
    have hge : u0.re - r ≤ u.re :=
      LaplaceBKernelAnalytic.re_ge_of_mem_ball (u := u) (u0 := u0) (r := r) hu
    have hmid : 0 ≤ u0.re - r := by
      dsimp [r]
      linarith [le_of_lt hu0re]
    exact le_trans hmid hge
  have hDeriv0 :
      HasDerivAt (fun u : ℂ => ∫ t in Set.Ioc (0 : ℝ) 1, LaplaceBKernelAnalytic.kernelIntegrand u t)
        (∫ t in Set.Ioc (0 : ℝ) 1, LaplaceBKernelAnalytic.kernelIntegrandDeriv u0 t) u0 := by
    -- Same argument as `LaplaceBKernelAnalytic.hasDerivAt_laplaceSplit`, but with the
    -- right-half-plane ball.
    have hF_meas :
        ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (LaplaceBKernelAnalytic.kernelIntegrand u) μ0 := by
      have hball : ∀ᶠ u in 𝓝 u0, u ∈ Metric.ball u0 r := Metric.ball_mem_nhds u0 hrpos
      refine hball.mono ?_
      intro u hu
      have hure0 : 0 ≤ u.re := hureBall hu
      have hInt :
          IntegrableOn (LaplaceBKernelAnalytic.kernelIntegrand u) (Set.Ioc (0 : ℝ) 1) volume :=
        LaplaceBKernelAnalytic.integrableOn_kernelIntegrand_Ioc (u := u) hure0
      have : Integrable (LaplaceBKernelAnalytic.kernelIntegrand u) μ0 := by
        simpa [μ0, MeasureTheory.IntegrableOn] using! hInt
      exact this.aestronglyMeasurable
    have hF_int : Integrable (LaplaceBKernelAnalytic.kernelIntegrand u0) μ0 := by
      have hInt :
          IntegrableOn (LaplaceBKernelAnalytic.kernelIntegrand u0) (Set.Ioc (0 : ℝ) 1) volume :=
        LaplaceBKernelAnalytic.integrableOn_kernelIntegrand_Ioc (u := u0) (le_of_lt hu0re)
      simpa [μ0, MeasureTheory.IntegrableOn] using! hInt
    have hF'_meas : AEStronglyMeasurable (LaplaceBKernelAnalytic.kernelIntegrandDeriv u0) μ0 := by
      -- `kernelIntegrandDeriv u0 = kernelIntegrand u0 * (-(π)*t)` up to commutativity.
      have hK : AEStronglyMeasurable (LaplaceBKernelAnalytic.kernelIntegrand u0) μ0 :=
        hF_int.aestronglyMeasurable
      have h1 : AEStronglyMeasurable (fun t : ℝ => (-(π : ℂ) * (t : ℂ))) μ0 := by
        exact (measurable_const.mul measurable_ofReal).aestronglyMeasurable
      have hKm :
          AEStronglyMeasurable
              (fun t : ℝ => LaplaceBKernelAnalytic.kernelIntegrand u0 t * (-(π : ℂ) * (t :
              ℂ))) μ0 :=
        hK.mul h1
      have hEq :
          (fun t : ℝ => LaplaceBKernelAnalytic.kernelIntegrand u0 t * (-(π : ℂ) * (t : ℂ))) =ᵐ[μ0]
            fun t : ℝ => LaplaceBKernelAnalytic.kernelIntegrandDeriv u0 t := by
        refine Filter.Eventually.of_forall ?_
        intro t
        simp [LaplaceBKernelAnalytic.kernelIntegrandDeriv, LaplaceBKernelAnalytic.kernelIntegrand,
          mul_assoc, mul_left_comm, mul_comm]
      exact hKm.congr hEq
    let bound0 : ℝ → ℝ := fun t => Real.pi * ‖BKernel0 t‖
    have h_bound :
        ∀ᵐ t ∂μ0, ∀ u ∈ Metric.ball u0 r,
          ‖LaplaceBKernelAnalytic.kernelIntegrandDeriv u t‖ ≤ bound0 t := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc ?_
      intro t ht u hu
      have ht0 : 0 ≤ t := ht.1.le
      have ht1 : t ≤ (1 : ℝ) := ht.2
      have hure : 0 ≤ u.re := hureBall hu
      have hexp :
          ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ 1 :=
        LaplaceBKernelAnalytic.norm_exp_neg_pi_mul_le_one (u := u) (t := t) ht.1 hure
      have hct : ‖-(π : ℂ) * (t : ℂ)‖ ≤ Real.pi := by
        have : ‖(t : ℂ)‖ ≤ (1 : ℝ) := by
          simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] using! ht1
        calc
          ‖-(π : ℂ) * (t : ℂ)‖ = ‖-(π : ℂ)‖ * ‖(t : ℂ)‖ := by simp []
          _ ≤ ‖-(π : ℂ)‖ * (1 : ℝ) := by gcongr
          _ = Real.pi := by simp [Real.pi_pos.le]
      calc
        ‖LaplaceBKernelAnalytic.kernelIntegrandDeriv u t‖
            = ‖BKernel0 t‖ * ‖-(π : ℂ) * (t : ℂ)‖ * ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by
                simp [
                  LaplaceBKernelAnalytic.kernelIntegrandDeriv,
                  mul_assoc,
                  mul_left_comm,
                  mul_comm
                ]
        _ ≤ ‖BKernel0 t‖ * Real.pi * 1 := by gcongr
        _ = bound0 t := by simp [bound0, mul_left_comm, mul_comm]
    have hbound_int : Integrable bound0 μ0 := by
      have : Integrable (fun t : ℝ => ‖BKernel0 t‖) μ0 := by
        have hInt0 : IntegrableOn (fun t : ℝ => BKernel0 t) (Set.Ioc (0 : ℝ) 1) volume :=
          LaplaceBKernelAnalytic.integrableOn_BKernel0_Ioc_zero_one
        have : Integrable (fun t : ℝ => BKernel0 t) μ0 := by
          simpa [μ0, MeasureTheory.IntegrableOn] using! hInt0
        simpa using! this.norm
      simpa [bound0] using! this.const_mul Real.pi
    have h :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le
          (F := fun u : ℂ => LaplaceBKernelAnalytic.kernelIntegrand u)
          (μ := μ0) (x₀ := u0) (s := Metric.ball u0 r) (bound := bound0)
          (Metric.ball_mem_nhds u0 hrpos)
          hF_meas hF_int hF'_meas h_bound hbound_int
          (by
            refine Filter.Eventually.of_forall ?_
            intro t u hu
            simpa using! LaplaceBKernelAnalytic.hasDerivAt_kernelIntegrand (u := u) (t := t)))
    exact h.2
  have hDeriv1 :
      HasDerivAt (fun u : ℂ => ∫ t in Set.Ioi (1 : ℝ), tailIntegrand u t)
        (∫ t in Set.Ioi (1 : ℝ), tailIntegrandDeriv u0 t) u0 :=
    hasDerivAt_tailIntegral (u0 := u0) hu0re
  have hCorr : DifferentiableAt ℂ BleadingCorrectionC u0 :=
    (analyticAt_BleadingCorrectionC (u0 := u0) hu0ne).differentiableAt
  -- Combine.
  have h0 :
      DifferentiableAt ℂ
        (fun u : ℂ =>
          ∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Complex.exp (-(π : ℂ) * u * (t : ℂ))) u0 := by
    -- `kernelIntegrand` unfolds to the integrand in `laplaceBKernelSubLeading`.
    have hEq :
        (fun u : ℂ => ∫ t in Set.Ioc (0 : ℝ) 1, LaplaceBKernelAnalytic.kernelIntegrand u t) =
          fun u : ℂ => ∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Complex.exp (-(π : ℂ) * u * (t : ℂ))
            := by
      funext u
      rfl
    simpa [hEq] using! hDeriv0.differentiableAt
  have h1 :
      DifferentiableAt ℂ (fun u : ℂ => ∫ t in Set.Ioi (1 : ℝ), (BKernel0 t - (BleadingTermR t : ℂ))
      *
        Complex.exp (-(π : ℂ) * u * (t : ℂ))) u0 :=
    hDeriv1.differentiableAt
  -- Unfold and use closure under addition.
  have h01 :
      DifferentiableAt ℂ
        (fun u : ℂ =>
          (∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Complex.exp (-(π : ℂ) * u * (t : ℂ))) +
            ∫ t in Set.Ioi (1 : ℝ),
              (BKernel0 t - (BleadingTermR t : ℂ)) * Complex.exp (-(π : ℂ) * u * (t : ℂ))) u0 :=
    h0.add h1
  have h012 :
      DifferentiableAt ℂ
        (fun u : ℂ =>
          ((∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Complex.exp (-(π : ℂ) * u * (t : ℂ))) +
              ∫ t in Set.Ioi (1 : ℝ),
                (BKernel0 t - (BleadingTermR t : ℂ)) * Complex.exp (-(π : ℂ) * u * (t : ℂ))) +
            BleadingCorrectionC u) u0 :=
    h01.add hCorr
  assumption

lemma analyticOnNhd_laplaceBKernelSubLeading :
    AnalyticOnNhd ℂ laplaceBKernelSubLeading LaplaceDomains.domainPosNeTwo := by
  have hopen : IsOpen LaplaceDomains.domainPosNeTwo := by
    have h0 : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
    simpa [
      LaplaceDomains.domainPosNeTwo,
      Set.diff_eq
    ] using! h0.inter isClosed_singleton.isOpen_compl
  have hd : DifferentiableOn ℂ laplaceBKernelSubLeading LaplaceDomains.domainPosNeTwo := by
    intro u hu
    exact (differentiableAt_laplaceBKernelSubLeading (u0 := u) hu).differentiableWithinAt
  exact (analyticOnNhd_iff_differentiableOn hopen).2 hd

lemma analyticOnNhd_sinSqC_domainPosNeTwo :
    AnalyticOnNhd ℂ sinSqC LaplaceDomains.domainPosNeTwo := by
  intro z hz
  -- `sinSqC` is entire.
  have hlin : AnalyticAt ℂ (fun u : ℂ => ((π : ℂ) / 2) * u) z :=
    analyticAt_const.mul analyticAt_id
  have hsin_outer : AnalyticAt ℂ (sin : ℂ → ℂ) (((π : ℂ) / 2) * z) := by
    simpa using! (analyticAt_sin (x := ((π : ℂ) / 2) * z))
  have hsin : AnalyticAt ℂ (fun u : ℂ => (sin : ℂ → ℂ) (((π : ℂ) / 2) * u)) z :=
    hsin_outer.comp hlin
  have hpow : AnalyticAt ℂ (fun u : ℂ => ((sin : ℂ → ℂ) (((π : ℂ) / 2) * u)) ^ (2 : ℕ)) z :=
    hsin.pow 2
  have hEq : (fun u : ℂ => ((sin : ℂ → ℂ) (((π : ℂ) / 2) * u)) ^ (2 : ℕ)) = sinSqC := by
    funext u
    simp [sinSqC, div_eq_mul_inv, mul_assoc, mul_comm]
  simpa [hEq] using! hpow

/-- Analyticity of `rhsBSubLeading` on the common domain `Re u > 0` with `u ≠ 2`. -/
public lemma analyticOnNhd_rhsBSubLeading :
    AnalyticOnNhd ℂ rhsBSubLeading LaplaceDomains.domainPosNeTwo := by
  have hs : AnalyticOnNhd ℂ sinSqC LaplaceDomains.domainPosNeTwo :=
    analyticOnNhd_sinSqC_domainPosNeTwo
  have hl : AnalyticOnNhd ℂ laplaceBKernelSubLeading LaplaceDomains.domainPosNeTwo :=
    analyticOnNhd_laplaceBKernelSubLeading
  simpa [rhsBSubLeading] using! hs.mul hl


/-- Closed form for the tail integral of the explicit leading term, viewed as a complex integral. -/
public lemma integral_Ioi_one_BleadingTermC_mul_exp_neg_pi_complex (u : ℝ) (hu : 2 < u) :
    (∫ t in Set.Ioi (1 : ℝ),
        (BleadingTermR t : ℂ) * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))) =
      BleadingCorrectionC (u : ℂ) := by
  have hreal := integral_Ioi_one_BleadingTermC_mul_exp_neg_pi (u := u) hu
  -- Rewrite the exponential into `Real.exp` and use the computed closed form.
  simpa [
    LaplaceFourierCont.laplaceBKernelC_ofReal,
    BleadingCorrectionC_ofReal,
    mul_assoc
  ] using! hreal

/-- Parentheses normalization for the exponential factor `exp (-(π * u * t))`. -/
public lemma exp_neg_pi_mul_outer (u : ℂ) (t : ℝ) :
    Complex.exp (-(π : ℂ) * u * (t : ℂ)) = Complex.exp (-((π : ℂ) * u * (t : ℂ))) := by
  congr 1
  ring_nf

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceBSubLeadingCont.Private
