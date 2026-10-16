-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Continuation.BKernelBounds
import SpherePacking.Dim24.ModularForms.Psi.Relations


/-!
# Splitting the Laplace integral at `t = 1`

This file proves integrability of `kernelIntegrand u` on the tail `t > 1` when `2 < Re u`, and
splits the defining Laplace integral into an integral over `(0,1]` and one over `(1,∞)`.

The resulting split expression `laplaceSplit` is used later to differentiate under the integral
sign.

## Main definition
* `laplaceSplit`

## Main statements
* `integrableOn_kernelIntegrand_Ioi_one`
* `laplaceBKernelC_eq_laplaceSplit`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic

noncomputable section

open scoped FourierTransform SchwartzMap

open Complex Filter MeasureTheory Real Set SchwartzMap
open UpperHalfPlane
open PrivateDefs

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Integrability of `kernelIntegrand u` on the tail `t > 1` when `2 < Re u`. -/
public lemma integrableOn_kernelIntegrand_Ioi_one {u : ℂ} (hu : 2 < u.re) :
    IntegrableOn (kernelIntegrand u) (Set.Ioi (1 : ℝ)) volume := by
  have hu0 : 0 ≤ u.re := le_trans (by linarith) (le_of_lt hu)
  -- measurability
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  have hmeas : AEStronglyMeasurable (kernelIntegrand u) μ := by
    -- `kernelIntegrand` is continuous on `t > 1`, hence a.e. strongly measurable on the restricted
    -- measure.
    have hcontOn : ContinuousOn (kernelIntegrand u) (Set.Ioi (1 : ℝ)) := by
      let s : Set ℝ := Set.Ioi (1 : ℝ)
      have hcont_restrict : Continuous fun p : s => kernelIntegrand u (p : ℝ) := by
        have hp0 : ∀ p : s, 0 < (p : ℝ) := fun p => lt_trans (by norm_num) p.property
        -- Continuity of `t ↦ it t` on the positive reals (restricted to `s`).
        have h_it : Continuous fun p : s => (it (p : ℝ) (hp0 p) : ℍ) := by
          have hval : Continuous fun p : s => ((p : ℝ) : ℂ) :=
            (Complex.continuous_ofReal.comp continuous_subtype_val)
          have hbase : Continuous fun p : s => (Complex.I : ℂ) * ((p : ℝ) : ℂ) := by
            simpa using! (continuous_const.mul hval)
          simpa [Dim24.it] using!
            Continuous.upperHalfPlaneMk hbase (fun p => by
              have : 0 < (p : ℝ) := hp0 p
              simpa [Complex.mul_im] using! this)
        -- Continuity of `t ↦ iOverT t` on the positive reals (restricted to `s`).
        have h_iOverT : Continuous fun p : s => (iOverT (p : ℝ) (hp0 p) : ℍ) := by
          -- `iOverT t = it (1/t)`.
          have hinv : Continuous fun p : s => (1 / (p : ℝ) : ℝ) := by
            have hval : Continuous fun p : s => (p : ℝ) := continuous_subtype_val
            have hne : ∀ p : s, (p : ℝ) ≠ 0 := fun p => ne_of_gt (hp0 p)
            simpa [one_div] using! (hval.inv₀ hne)
          have hbase : Continuous fun p : s => (Complex.I : ℂ) * (((1 / (p : ℝ) : ℝ) : ℂ)) := by
            have hcast : Continuous fun p : s => ((1 / (p : ℝ) : ℝ) : ℂ) :=
              Complex.continuous_ofReal.comp hinv
            simpa using! (continuous_const.mul hcast)
          simpa [Dim24.iOverT, Dim24.it] using!
            Continuous.upperHalfPlaneMk hbase (fun p => by
              have : 0 < (1 / (p : ℝ) : ℝ) := one_div_pos.2 (hp0 p)
              simpa [Complex.mul_im] using! this)
        have hvarphi : Continuous (varphi : ℍ → ℂ) := varphi_holo'.continuous
        have hψ : Continuous (ψI : ℍ → ℂ) := SpherePacking.Dim24.continuous_ψI
        have hBK : Continuous fun p : s => BKernel (p : ℝ) (hp0 p) := by
          -- Unfold `BKernel` and use closure of continuity under arithmetic.
          have ht10 : Continuous fun p : s => ((p : ℝ) : ℂ) ^ (10 : ℕ) := by fun_prop
          have hterm1 : Continuous fun p : s =>
              ((π : ℂ) / (28304640 : ℂ)) * ((p : ℝ) : ℂ) ^ (10 : ℕ) * varphi (iOverT (p : ℝ) (hp0
              p))
                := by
            simpa [BKernel, mul_assoc] using!
              (continuous_const.mul (ht10.mul (hvarphi.comp h_iOverT)))
          have hterm2 : Continuous fun p : s =>
              (1 / ((65520 : ℂ) * π)) * ψI (it (p : ℝ) (hp0 p)) := by
            have hc2 : Continuous fun _ : s => (1 / ((65520 : ℂ) * π) : ℂ) := continuous_const
            exact hc2.mul (hψ.comp h_it)
          simpa [BKernel, add_assoc, mul_assoc] using! hterm1.add hterm2
        have hExp : Continuous fun p : s =>
            Complex.exp (-(π : ℂ) * u * ((p : ℝ) : ℂ)) := by
          fun_prop
        have hEq :
            (fun p : s => kernelIntegrand u (p : ℝ)) =
              fun p : s => BKernel (p : ℝ) (hp0 p) * Complex.exp (-(π : ℂ) * u * ((p : ℝ) : ℂ))
                := by
          funext p
          have hp0' : 0 < (p : ℝ) := hp0 p
          simp [kernelIntegrand, BKernel0, hp0', mul_assoc]
        simpa [hEq] using! (hBK.mul hExp)
      -- transport back to a `ContinuousOn` statement on `ℝ`.
      simpa [s] using! (continuousOn_iff_continuous_restrict.2 hcont_restrict)
    simpa [μ] using! (hcontOn.aestronglyMeasurable (μ := volume) measurableSet_Ioi)
  -- a convenient product majorant coming directly from `norm_BKernel0_le`
  let K : ℝ := ‖((π : ℂ) / (28304640 : ℂ))‖
  let boundProd : ℝ → ℝ :=
    fun t : ℝ =>
      (K *
            ((t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
              t * (Cφ1q * Real.exp (2 * Real.pi * t))) +
          CDq * Real.exp (2 * Real.pi * t)) *
        Real.exp (-Real.pi * u.re * t)
  -- establish integrability of the majorant by rewriting it into `t^n * exp(-b*t)` terms
  let bPos : ℝ := Real.pi * (u.re - 2)
  let bNeg : ℝ := Real.pi * (u.re + 2)
  let boundSum : ℝ → ℝ :=
    fun t : ℝ =>
      (K * Cφ) * (t ^ (2 : ℕ) * Real.exp (-bNeg * t)) +
        (K * Cφ1q) * (t * Real.exp (-bPos * t)) +
          CDq * Real.exp (-bPos * t)
  have hboundSum_int : Integrable boundSum μ := by
    have hbPos : 0 < bPos := by
      have : 0 < u.re - 2 := sub_pos.2 hu
      exact mul_pos Real.pi_pos this
    have hbNeg : 0 < bNeg := by
      have : 0 < u.re + 2 := by nlinarith [hu0]
      exact mul_pos Real.pi_pos this
    have h2 :
        Integrable (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-bNeg * t)) μ := by
      simpa [μ, MeasureTheory.IntegrableOn] using!
        (integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 2) (b := bNeg) hbNeg)
    have h1 :
        Integrable (fun t : ℝ => t * Real.exp (-bPos * t)) μ := by
      simpa [μ, MeasureTheory.IntegrableOn, pow_one] using!
        (integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 1) (b := bPos) hbPos)
    have h0 :
        Integrable (fun t : ℝ => Real.exp (-bPos * t)) μ := by
      simpa [μ, MeasureTheory.IntegrableOn, pow_zero] using!
        (integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 0) (b := bPos) hbPos)
    have h2' : Integrable (fun t : ℝ => (K * Cφ) * (t ^ (2 : ℕ) * Real.exp (-bNeg * t))) μ :=
      h2.const_mul (K * Cφ)
    have h1' : Integrable (fun t : ℝ => (K * Cφ1q) * (t * Real.exp (-bPos * t))) μ :=
      h1.const_mul (K * Cφ1q)
    have h0' : Integrable (fun t : ℝ => CDq * Real.exp (-bPos * t)) μ :=
      h0.const_mul CDq
    simpa [boundSum, add_assoc] using! (h2'.add (h1'.add h0'))
  have hboundProd_int : Integrable boundProd μ := by
    have hEq : boundProd =ᵐ[μ] boundSum := by
      refine Filter.Eventually.of_forall ?_
      intro t
      -- combine the exponential factors
      have hneg :
          Real.exp (-(2 * Real.pi * t)) * Real.exp (-(Real.pi * u.re * t)) =
            Real.exp (-bNeg * t) := by
        calc
          Real.exp (-(2 * Real.pi * t)) * Real.exp (-(Real.pi * u.re * t)) =
              Real.exp (-(2 * Real.pi * t) + (-(Real.pi * u.re * t))) := by
                exact
                  (Real.exp_add (-(2 * Real.pi * t)) (-(Real.pi * u.re * t))).symm
          _ = Real.exp (-bNeg * t) := by
                congr 1
                dsimp [bNeg]
                ring_nf
      have hpos :
          Real.exp (2 * Real.pi * t) * Real.exp (-(Real.pi * u.re * t)) =
            Real.exp (-bPos * t) := by
        calc
          Real.exp (2 * Real.pi * t) * Real.exp (-(Real.pi * u.re * t)) =
              Real.exp ((2 * Real.pi * t) + (-(Real.pi * u.re * t))) := by
                exact (Real.exp_add (2 * Real.pi * t) (-(Real.pi * u.re * t))).symm
          _ = Real.exp (-bPos * t) := by
                congr 1
                dsimp [bPos]
                ring_nf
      -- rewrite `boundProd` into `boundSum` by expanding and applying `hneg`/`hpos`
      grind only
    exact hboundSum_int.congr hEq.symm
  have hle :
      ∀ᵐ t ∂μ, ‖kernelIntegrand u t‖ ≤ boundProd t := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht1 : 1 ≤ t := le_of_lt ht
    have hB : ‖BKernel0 t‖ ≤
        K *
            ((t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
              t * (Cφ1q * Real.exp (2 * Real.pi * t))) +
          CDq * Real.exp (2 * Real.pi * t) := by
      simpa [K] using! (norm_BKernel0_le (t := t) ht1)
    have hexp :
        ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ = Real.exp (-Real.pi * u.re * t) := by
      simpa using! LaplaceBKernelAnalytic.norm_kernelExp (u := u) (t := t)
    have hnorm :
        ‖kernelIntegrand u t‖ = ‖BKernel0 t‖ * Real.exp (-Real.pi * u.re * t) := by
      calc
        ‖kernelIntegrand u t‖ =
            ‖BKernel0 t‖ * ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by
              simp [kernelIntegrand]
        _ = ‖BKernel0 t‖ * Real.exp (-Real.pi * u.re * t) := by
              simpa using! congrArg (fun r : ℝ => ‖BKernel0 t‖ * r) hexp
    have hmul :
        ‖BKernel0 t‖ * Real.exp (-Real.pi * u.re * t) ≤
          (K *
              ((t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) +
                t * (Cφ1q * Real.exp (2 * Real.pi * t))) +
            CDq * Real.exp (2 * Real.pi * t)) *
            Real.exp (-Real.pi * u.re * t) := by
      exact mul_le_mul_of_nonneg_right hB (by positivity)
    exact le_of_eq_of_le hnorm hmul
  have hint : Integrable (kernelIntegrand u) μ :=
    Integrable.mono' (μ := μ) hboundProd_int hmeas hle
  simpa [μ, MeasureTheory.IntegrableOn] using! hint


/-- Derivative of `u ↦ kernelIntegrand u t` with respect to `u`. -/
public lemma kernelIntegrand_hasDerivAt (u : ℂ) (t : ℝ) :
    HasDerivAt (fun w : ℂ => kernelIntegrand w t) (kernelIntegrandDeriv u t) u := by
  simpa using! (hasDerivAt_kernelIntegrand (u := u) (t := t))

/-- Split the `kernelIntegrand` integral over `t > 0` into `(0,1]` and `(1,∞)`. -/
public lemma laplaceBKernelC_eq_Ioc_add_Ioi_one (u : ℂ) (hu : 2 < u.re) :
    (∫ t in Set.Ioi (0 : ℝ), kernelIntegrand u t) =
      (∫ t in Set.Ioc (0 : ℝ) 1, kernelIntegrand u t) + ∫ t in Set.Ioi (1 : ℝ), kernelIntegrand u t
        := by
  have hu0 : 0 ≤ u.re := le_trans (by linarith) (le_of_lt hu)
  have hIntIoc : IntegrableOn (kernelIntegrand u) (Set.Ioc (0 : ℝ) 1) volume :=
    integrableOn_kernelIntegrand_Ioc (u := u) hu0
  have hIntIoi : IntegrableOn (kernelIntegrand u) (Set.Ioi (1 : ℝ)) volume :=
    integrableOn_kernelIntegrand_Ioi_one (u := u) hu
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
    Ioc_disjoint_Ioi_same
  have hUnionEq : (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)) = Set.Ioi (0 : ℝ) :=
    Eq.symm LaplaceEqA.Ioi_eq_Ioc_union_Ioi_one
  have hIntegralUnion :
      (∫ t in (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)), kernelIntegrand u t) =
        (∫ t in Set.Ioc (0 : ℝ) 1, kernelIntegrand u t) + ∫ t in Set.Ioi (1 :
        ℝ), kernelIntegrand u t :=
    (MeasureTheory.setIntegral_union (μ := volume) (f := kernelIntegrand u) hdisj measurableSet_Ioi
      hIntIoc hIntIoi)
  -- Rewrite the union as `Ioi 0` without triggering simp recursion.
  simpa [hUnionEq] using! hIntegralUnion

/-- Split integral expression for `laplaceBKernelC`, integrating over `(0,1]` and `(1,∞)`. -/
@[expose] public def laplaceSplit (u : ℂ) : ℂ :=
  (∫ t in Set.Ioc (0 : ℝ) 1, kernelIntegrand u t) + ∫ t in Set.Ioi (1 : ℝ), kernelIntegrand u t

/-- For `2 < Re u`, the split expression `laplaceSplit u` equals `laplaceBKernelC u`. -/
public lemma laplaceBKernelC_eq_laplaceSplit (u : ℂ) (hu : 2 < u.re) :
    laplaceBKernelC u = laplaceSplit u := by
  -- Unfold the complexified Laplace integral and split at `t = 1`.
  have hsplit := laplaceBKernelC_eq_Ioc_add_Ioi_one (u := u) hu
  simpa [PrivateDefs.laplaceBKernelC, laplaceSplit, kernelIntegrand] using! hsplit


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic
