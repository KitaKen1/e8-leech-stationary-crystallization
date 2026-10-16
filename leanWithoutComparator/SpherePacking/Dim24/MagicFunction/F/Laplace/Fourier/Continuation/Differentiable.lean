-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Continuation.LaplaceSplit


/-!
# Differentiability of `laplaceBKernelC` on `Re u > 2`

This file differentiates the split integral formula `laplaceSplit` under the integral sign and
deduces differentiability of `laplaceBKernelC` on `LaplaceDomains.domainTwo`.

## Main statements
* `hasDerivAt_laplaceSplit`
* `differentiableOn_laplaceBKernelC_domainTwo`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Topology

open Complex Filter MeasureTheory Real Set SchwartzMap
open UpperHalfPlane
open PrivateDefs

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Differentiate `laplaceSplit` under the integral sign at a point with `2 < Re u`. -/
public lemma hasDerivAt_laplaceSplit (u0 : ℂ) (hu0 : 2 < u0.re) :
    HasDerivAt laplaceSplit
      ((∫ t in Set.Ioc (0 : ℝ) 1, kernelIntegrandDeriv u0 t) +
        ∫ t in Set.Ioi (1 : ℝ), kernelIntegrandDeriv u0 t) u0 := by
  -- Use dominated differentiation under the integral on each piece.
  let r : ℝ := (u0.re - 2) / 2
  have hrpos : 0 < r := by
    have : 0 < u0.re - 2 := sub_pos.2 hu0
    exact half_pos this
  have hreBall : ∀ {u : ℂ}, u ∈ Metric.ball u0 r → (2 : ℝ) < u.re := by
    intro u hu
    have hge : u0.re - r ≤ u.re :=
      LaplaceBKernelAnalytic.re_ge_of_mem_ball (u := u) (u0 := u0) (r := r) hu
    have hmid : (2 : ℝ) < u0.re - r := by
      dsimp [r]
      nlinarith [hu0]
    exact lt_of_lt_of_le hmid hge
  have hEqBall : (fun u : ℂ => laplaceBKernelC u) =ᶠ[𝓝 u0] fun u : ℂ => laplaceSplit u := by
    have hball : ∀ᶠ u in 𝓝 u0, u ∈ Metric.ball u0 r := Metric.ball_mem_nhds u0 hrpos
    refine hball.mono ?_
    intro u hu
    exact laplaceBKernelC_eq_laplaceSplit (u := u) (hu := hreBall hu)
  -- `Ioc (0,1]` part
  let μ0 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let μ1 : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  have hDeriv0 :
      HasDerivAt (fun u : ℂ => ∫ t in Set.Ioc (0 : ℝ) 1, kernelIntegrand u t)
        (∫ t in Set.Ioc (0 : ℝ) 1, kernelIntegrandDeriv u0 t) u0 := by
    -- Apply the general derivative-under-the-integral lemma on a finite interval.
    have hF_meas :
        ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (kernelIntegrand u) μ0 := by
      have hball : ∀ᶠ u in 𝓝 u0, u ∈ Metric.ball u0 r := Metric.ball_mem_nhds u0 hrpos
      refine hball.mono ?_
      intro u hu
      have hure0 : 0 ≤ u.re := le_trans (by nlinarith) (le_of_lt (hreBall hu))
      have hInt : IntegrableOn (kernelIntegrand u) (Set.Ioc (0 : ℝ) 1) volume :=
        integrableOn_kernelIntegrand_Ioc (u := u) hure0
      have : Integrable (kernelIntegrand u) μ0
        := by simpa [μ0, MeasureTheory.IntegrableOn] using! hInt
      exact this.aestronglyMeasurable
    have hF_int : Integrable (kernelIntegrand u0) μ0 := by
      have hu0' : 0 ≤ u0.re := le_trans (by linarith) (le_of_lt hu0)
      have hInt : IntegrableOn (kernelIntegrand u0) (Set.Ioc (0 : ℝ) 1) volume :=
        integrableOn_kernelIntegrand_Ioc (u := u0) hu0'
      simpa [μ0, MeasureTheory.IntegrableOn] using! hInt
    -- Measurability of the derivative integrand follows from measurability of `BKernel0` on
    -- `(0,1]`.
    have hB0_meas : AEStronglyMeasurable (fun t : ℝ => BKernel0 t) μ0 := by
      have hInt0 : IntegrableOn (fun t : ℝ => BKernel0 t) (Set.Ioc (0 : ℝ) 1) volume :=
        integrableOn_BKernel0_Ioc_zero_one
      have : Integrable (fun t : ℝ => BKernel0 t) μ0 := by
        simpa [μ0, MeasureTheory.IntegrableOn] using! hInt0
      exact this.aestronglyMeasurable
    have hF'_meas : AEStronglyMeasurable (kernelIntegrandDeriv u0) μ0 := by
      -- Product of measurable functions.
      have h1 : AEStronglyMeasurable (fun t : ℝ => (-(π : ℂ) * (t : ℂ))) μ0 := by
        exact (measurable_const.mul measurable_ofReal).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(π : ℂ) * u0 * (t : ℂ))) μ0 := by
        have hcont : Continuous fun t : ℝ => (-(π : ℂ) * u0) * (t : ℂ) :=
          continuous_const.mul Complex.continuous_ofReal
        have hcont' : Continuous fun t : ℝ => (-(π : ℂ) * u0 * (t : ℂ)) := by
          simpa [mul_assoc] using! hcont
        exact hcont'.cexp.aestronglyMeasurable
      have h12 :
          AEStronglyMeasurable
            (fun t : ℝ => (-(π : ℂ) * (t : ℂ)) * Complex.exp (-(π : ℂ) * u0 * (t : ℂ))) μ0 :=
        h1.mul h2
      have h :
          AEStronglyMeasurable
            (fun t : ℝ =>
              BKernel0 t * ((-(π : ℂ) * (t : ℂ)) * Complex.exp (-(π : ℂ) * u0 * (t : ℂ)))) μ0 :=
        hB0_meas.mul h12
      have hEq :
          (fun t : ℝ =>
              BKernel0 t * ((-(π : ℂ) * (t : ℂ)) * Complex.exp (-(π : ℂ) * u0 * (t : ℂ)))) =ᵐ[μ0]
            fun t : ℝ => kernelIntegrandDeriv u0 t := by
        refine Filter.Eventually.of_forall ?_
        intro t
        simp [kernelIntegrandDeriv, mul_assoc, mul_left_comm, mul_comm]
      exact h.congr hEq
    -- Uniform bound on the derivative for `u` in a ball.
    let bound0 : ℝ → ℝ := fun t => Real.pi * ‖BKernel0 t‖
    have h_bound :
        ∀ᵐ t ∂μ0, ∀ u ∈ Metric.ball u0 r, ‖kernelIntegrandDeriv u t‖ ≤ bound0 t := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc ?_
      intro t ht u hu
      have ht0 : 0 ≤ t := ht.1.le
      have ht1 : t ≤ (1 : ℝ) := ht.2
      have hure : 0 ≤ u.re := le_trans (by nlinarith) (le_of_lt (hreBall hu))
      have hexp :
          ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ 1 := by
        have hmul : 0 ≤ Real.pi * u.re * t := by
          have hpi : 0 ≤ Real.pi := Real.pi_pos.le
          exact mul_nonneg (mul_nonneg hpi hure) ht0
        have hx : -Real.pi * u.re * t ≤ 0 := by
          have hx0 : -(Real.pi * u.re * t) ≤ 0 := neg_nonpos.2 hmul
          have hx' : -Real.pi * u.re * t = -(Real.pi * u.re * t) := by ring
          rw [hx']
          exact hx0
        -- `‖exp‖ = exp(re)` and `re ≤ 0`.
        have hn : ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ = Real.exp (-Real.pi * u.re * t) := by
          simpa using! LaplaceBKernelAnalytic.norm_kernelExp (u := u) (t := t)
        -- `Real.exp x ≤ 1` for `x ≤ 0`.
        have hExp : Real.exp (-Real.pi * u.re * t) ≤ 1 := (Real.exp_le_one_iff.2 hx)
        rw [hn]
        exact hExp
      have hct : ‖-(π : ℂ) * (t : ℂ)‖ ≤ Real.pi := by
        -- `t ∈ [0,1]` gives `‖t‖ ≤ 1`.
        have : ‖(t : ℂ)‖ ≤ (1 : ℝ) := by
          simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] using! ht1
        calc
          ‖-(π : ℂ) * (t : ℂ)‖ = ‖-(π : ℂ)‖ * ‖(t : ℂ)‖ := by simp []
          _ ≤ ‖-(π : ℂ)‖ * (1 : ℝ) := by
                gcongr
          _ = Real.pi := by
                simp [Real.pi_pos.le]
      -- Combine.
      calc
        ‖kernelIntegrandDeriv u t‖
            = ‖BKernel0 t‖ * ‖-(π : ℂ) * (t : ℂ)‖ * ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by
                simp [kernelIntegrandDeriv, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ ‖BKernel0 t‖ * Real.pi * 1 := by
              gcongr
        _ = bound0 t := by simp [bound0, mul_left_comm, mul_comm]
    have hbound_int : Integrable bound0 μ0 := by
      -- `BKernel0` is integrable on `Ioc (0,1]`.
      have : Integrable (fun t : ℝ => ‖BKernel0 t‖) μ0 := by
        have hInt0 : Integrable (fun t : ℝ => BKernel0 t) μ0 := by
          have hInt0' : IntegrableOn (fun t : ℝ => BKernel0 t) (Set.Ioc (0 : ℝ) 1) volume :=
            integrableOn_BKernel0_Ioc_zero_one
          simpa [μ0, MeasureTheory.IntegrableOn] using! hInt0'
        simpa using! hInt0.norm
      simpa [bound0] using! this.const_mul Real.pi
    -- Apply the parametric integral lemma.
    have h :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun u : ℂ => kernelIntegrand u)
          (μ := μ0) (x₀ := u0) (s := Metric.ball u0 r) (bound :=
          bound0) (Metric.ball_mem_nhds u0 hrpos) hF_meas hF_int hF'_meas h_bound hbound_int
          (by
            refine Filter.Eventually.of_forall ?_
            intro t u hu
            simpa using! (kernelIntegrand_hasDerivAt (u := u) (t := t))))
    exact h.2
  -- Tail `Ioi 1` part
  have hDeriv1 :
      HasDerivAt (fun u : ℂ => ∫ t in Set.Ioi (1 : ℝ), kernelIntegrand u t)
        (∫ t in Set.Ioi (1 : ℝ), kernelIntegrandDeriv u0 t) u0 := by
    -- Apply dominated differentiation using the explicit exponential bounds from
    -- `norm_BKernel0_le`.
    have hF_meas :
        ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (kernelIntegrand u) μ1 := by
      have hball : ∀ᶠ u in 𝓝 u0, u ∈ Metric.ball u0 r := Metric.ball_mem_nhds u0 hrpos
      refine hball.mono ?_
      intro u hu
      have hu' : 2 < u.re := hreBall hu
      have hInt : IntegrableOn (kernelIntegrand u) (Set.Ioi (1 : ℝ)) volume :=
        integrableOn_kernelIntegrand_Ioi_one (u := u) hu'
      have : Integrable (kernelIntegrand u) μ1
        := by simpa [μ1, MeasureTheory.IntegrableOn] using! hInt
      exact this.aestronglyMeasurable
    have hF_int : Integrable (kernelIntegrand u0) μ1 := by
      have hInt : IntegrableOn (kernelIntegrand u0) (Set.Ioi (1 : ℝ)) volume :=
        integrableOn_kernelIntegrand_Ioi_one (u := u0) hu0
      simpa [μ1, MeasureTheory.IntegrableOn] using! hInt
    have hF'_meas : AEStronglyMeasurable (kernelIntegrandDeriv u0) μ1 := by
      -- `kernelIntegrandDeriv u0 = kernelIntegrand u0 * (-(π)*t)` up to commutativity.
      have hK : AEStronglyMeasurable (kernelIntegrand u0) μ1 := hF_int.aestronglyMeasurable
      have h1 : AEStronglyMeasurable (fun t : ℝ => (-(π : ℂ) * (t : ℂ))) μ1 := by
        exact (measurable_const.mul measurable_ofReal).aestronglyMeasurable
      have hKm :
          AEStronglyMeasurable (fun t : ℝ => kernelIntegrand u0 t * (-(π : ℂ) * (t : ℂ))) μ1 :=
        hK.mul h1
      have hEq :
          (fun t : ℝ => kernelIntegrand u0 t * (-(π : ℂ) * (t : ℂ))) =ᵐ[μ1]
            fun t : ℝ => kernelIntegrandDeriv u0 t := by
        refine Filter.Eventually.of_forall ?_
        intro t
        simp [kernelIntegrandDeriv, kernelIntegrand, mul_assoc, mul_left_comm, mul_comm]
      exact hKm.congr hEq
    -- Uniform bound on the derivative in a neighborhood: use the minimal real part in the ball.
    let uMin : ℝ := u0.re - r
    have huMin : 2 < uMin := by
      dsimp [uMin, r]
      nlinarith [hu0]
    let K : ℝ := ‖((π : ℂ) / (28304640 : ℂ))‖
    let bPos : ℝ := Real.pi * (uMin - 2)
    let bNeg : ℝ := Real.pi * (uMin + 2)
    let bound1 : ℝ → ℝ :=
      fun t : ℝ =>
        (Real.pi * K * Cφ) * (t ^ (3 : ℕ) * Real.exp (-bNeg * t)) +
          (Real.pi * K * Cφ1q) * (t ^ (2 : ℕ) * Real.exp (-bPos * t)) +
            (Real.pi * CDq) * (t * Real.exp (-bPos * t))
    have hbPos : 0 < bPos := by
      have : 0 < uMin - 2 := sub_pos.2 huMin
      exact mul_pos Real.pi_pos this
    have hbNeg : 0 < bNeg := by
      have : 0 < uMin + 2 := by nlinarith
      exact mul_pos Real.pi_pos this
    have hbound_int : Integrable bound1 μ1 := by
      have h3 :
          Integrable (fun t : ℝ => t ^ (3 : ℕ) * Real.exp (-bNeg * t)) μ1 := by
        simpa [μ1, MeasureTheory.IntegrableOn] using!
          (integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 3) (b := bNeg) hbNeg)
      have h2 :
          Integrable (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-bPos * t)) μ1 := by
        simpa [μ1, MeasureTheory.IntegrableOn] using!
          (integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 2) (b := bPos) hbPos)
      have h1 :
          Integrable (fun t : ℝ => t * Real.exp (-bPos * t)) μ1 := by
        simpa [μ1, MeasureTheory.IntegrableOn, pow_one] using!
          (integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 1) (b := bPos) hbPos)
      have h3' :
          Integrable (fun t : ℝ => (Real.pi * K * Cφ) * (t ^ (3 : ℕ) * Real.exp (-bNeg * t))) μ1 :=
        h3.const_mul (Real.pi * K * Cφ)
      have h2' :
          Integrable
            (fun t : ℝ => (Real.pi * K * Cφ1q) * (t ^ (2 : ℕ) * Real.exp (-bPos * t))) μ1 :=
        h2.const_mul (Real.pi * K * Cφ1q)
      have h1' : Integrable (fun t : ℝ => (Real.pi * CDq) * (t * Real.exp (-bPos * t))) μ1 :=
        h1.const_mul (Real.pi * CDq)
      simpa [bound1, add_assoc] using! (h3'.add (h2'.add h1'))
    have h_bound :
        ∀ᵐ t ∂μ1, ∀ u ∈ Metric.ball u0 r, ‖kernelIntegrandDeriv u t‖ ≤ bound1 t := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht u hu
      have ht1 : 1 ≤ t := le_of_lt ht
      have hB : ‖BKernel0 t‖ ≤
          K *
              ((t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
                t * (Cφ1q * Real.exp (2 * Real.pi * t))) +
            CDq * Real.exp (2 * Real.pi * t) := by
        simpa [K] using! (norm_BKernel0_le (t := t) ht1)
      have hure : uMin ≤ u.re := by
        -- `u.re` is bounded below on the ball.
        exact re_ge_of_mem_ball hu
      have hexp :
          ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ Real.exp (-Real.pi * uMin * t) := by
        have hn : ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ = Real.exp (-Real.pi * u.re * t) := by
          simpa using! LaplaceBKernelAnalytic.norm_kernelExp (u := u) (t := t)
        have hmono : Real.exp (-Real.pi * u.re * t) ≤ Real.exp (-Real.pi * uMin * t) := by
          have ht0 : 0 ≤ t := le_trans (by norm_num) ht1
          have hmul : uMin * t ≤ u.re * t := mul_le_mul_of_nonneg_right hure ht0
          have hpi : Real.pi * (uMin * t) ≤ Real.pi * (u.re * t) :=
            mul_le_mul_of_nonneg_left hmul Real.pi_pos.le
          have : -(Real.pi * (u.re * t)) ≤ -(Real.pi * (uMin * t)) := neg_le_neg hpi
          have : -Real.pi * u.re * t ≤ -Real.pi * uMin * t := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using! this
          exact Real.exp_le_exp.2 this
        rw [hn]
        exact hmono
      -- Now bound the norm of the derivative integrand.
      have hnorm :
          ‖kernelIntegrandDeriv u t‖ =
            ‖BKernel0 t‖ * ‖-(π : ℂ) * (t : ℂ)‖ * ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by
        simp [kernelIntegrandDeriv, mul_assoc, mul_left_comm, mul_comm]
      have hπt : ‖-(π : ℂ) * (t : ℂ)‖ = Real.pi * t := by
        have ht0 : 0 ≤ t := le_trans (by norm_num) ht1
        calc
          ‖-(π : ℂ) * (t : ℂ)‖ = ‖-(π : ℂ)‖ * ‖(t : ℂ)‖ := by simp []
          _ = (Real.pi : ℝ) * |t| := by
                simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
          _ = Real.pi * t := by simp [abs_of_nonneg ht0]
      have hle :
          ‖kernelIntegrandDeriv u t‖ ≤
            ‖BKernel0 t‖ * (Real.pi * t) * Real.exp (-Real.pi * uMin * t) := by
        -- use `hnorm` and bounds for each factor
        rw [hnorm, hπt]
        have hfac0 : 0 ≤ ‖BKernel0 t‖ * (Real.pi * t) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hexp hfac0
        simpa [mul_assoc] using! hmul
      -- Rewrite the RHS using `hB` and simplify exponentials.
      have ht0 : 0 ≤ t := le_trans (by norm_num) ht1
      have hmul :
          ‖BKernel0 t‖ * (Real.pi * t) * Real.exp (-Real.pi * uMin * t) ≤
            (K *
                ((t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
                  t * (Cφ1q * Real.exp (2 * Real.pi * t))) +
              CDq * Real.exp (2 * Real.pi * t)) * (Real.pi * t) * Real.exp (-Real.pi * uMin * t)
                := by
        have :=
          mul_le_mul_of_nonneg_right hB
            (by
              positivity : 0 ≤ (Real.pi * t) * Real.exp (-Real.pi * uMin * t))
        simpa [mul_assoc] using! this
      have hrewrite :
          (K *
                ((t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
                  t * (Cφ1q * Real.exp (2 * Real.pi * t))) +
              CDq * Real.exp (2 * Real.pi * t)) *
              (Real.pi * t) * Real.exp (-Real.pi * uMin * t) =
            bound1 t := by
        -- expand and combine exponentials into `bPos`/`bNeg`.
        have hpos :
            Real.exp (t * (Real.pi * 2)) * Real.exp (-(t * (Real.pi * uMin))) =
              Real.exp (-(t * bPos)) := by
          calc
            Real.exp (t * (Real.pi * 2)) * Real.exp (-(t * (Real.pi * uMin))) =
                Real.exp (t * (Real.pi * 2) + (-(t * (Real.pi * uMin)))) := by
                  exact
                    (Real.exp_add (t * (Real.pi * 2)) (-(t * (Real.pi * uMin)))).symm
            _ = Real.exp (-(t * bPos)) := by
                  congr 1
                  dsimp [bPos]
                  ring_nf
        have hneg :
            Real.exp (-(t * (Real.pi * 2))) * Real.exp (-(t * (Real.pi * uMin))) =
              Real.exp (-(t * bNeg)) := by
          calc
            Real.exp (-(t * (Real.pi * 2))) * Real.exp (-(t * (Real.pi * uMin))) =
                Real.exp (-(t * (Real.pi * 2)) + (-(t * (Real.pi * uMin)))) := by
                  exact
                    (Real.exp_add (-(t * (Real.pi * 2))) (-(t * (Real.pi * uMin)))).symm
            _ = Real.exp (-(t * bNeg)) := by
                  congr 1
                  dsimp [bNeg]
                  ring_nf
        grind only
      exact (le_trans (le_trans hle hmul) (le_of_eq hrewrite))
    -- Apply the parametric integral lemma.
    have h :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun u : ℂ => kernelIntegrand u)
          (μ := μ1) (x₀ := u0) (s := Metric.ball u0 r) (bound :=
          bound1) (Metric.ball_mem_nhds u0 hrpos) hF_meas hF_int hF'_meas h_bound hbound_int
          (by
            refine Filter.Eventually.of_forall ?_
            intro t u hu
            simpa using! (kernelIntegrand_hasDerivAt (u := u) (t := t))))
    exact h.2
  -- Combine the two pieces.
  simpa [laplaceSplit] using! hDeriv0.add hDeriv1

lemma differentiableAt_laplaceBKernelC (u0 : ℂ) (hu0 : 2 < u0.re) :
    DifferentiableAt ℂ laplaceBKernelC u0 := by
  -- Use `HasDerivAt` for `laplaceSplit` together with eventual equality on a neighborhood.
  have hderiv : HasDerivAt laplaceSplit
      ((∫ t in Set.Ioc (0 : ℝ) 1, kernelIntegrandDeriv u0 t) +
        ∫ t in Set.Ioi (1 : ℝ), kernelIntegrandDeriv u0 t) u0 :=
    hasDerivAt_laplaceSplit (u0 := u0) hu0
  -- `laplaceBKernelC = laplaceSplit` near `u0`.
  let r : ℝ := (u0.re - 2) / 2
  have hrpos : 0 < r := by
    have : 0 < u0.re - 2 := sub_pos.2 hu0
    exact half_pos this
  have hreBall : ∀ {u : ℂ}, u ∈ Metric.ball u0 r → (2 : ℝ) < u.re := by
    intro u hu
    have hge : u0.re - r ≤ u.re :=
      LaplaceBKernelAnalytic.re_ge_of_mem_ball (u := u) (u0 := u0) (r := r) hu
    have hmid : (2 : ℝ) < u0.re - r := by
      dsimp [r]
      nlinarith [hu0]
    exact lt_of_lt_of_le hmid hge
  have hEq : (fun u : ℂ => laplaceBKernelC u) =ᶠ[𝓝 u0] fun u : ℂ => laplaceSplit u := by
    have hball : ∀ᶠ u in 𝓝 u0, u ∈ Metric.ball u0 r := Metric.ball_mem_nhds u0 hrpos
    refine hball.mono ?_
    intro u hu
    exact laplaceBKernelC_eq_laplaceSplit (u := u) (hu := hreBall hu)
  have hderiv' : HasDerivAt laplaceBKernelC
      ((∫ t in Set.Ioc (0 : ℝ) 1, kernelIntegrandDeriv u0 t) +
        ∫ t in Set.Ioi (1 : ℝ), kernelIntegrandDeriv u0 t) u0 :=
    hderiv.congr_of_eventuallyEq hEq
  exact hderiv'.differentiableAt

/-- `laplaceBKernelC` is complex-differentiable on the half-plane `LaplaceDomains.domainTwo`. -/
public lemma differentiableOn_laplaceBKernelC_domainTwo :
    DifferentiableOn ℂ laplaceBKernelC LaplaceDomains.domainTwo := by
  intro u hu
  have : DifferentiableAt ℂ laplaceBKernelC u := differentiableAt_laplaceBKernelC (u0 := u) hu
  exact this.differentiableWithinAt


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic
