-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingContinuation.Analyticity


/-!
# Agreement of the continuations

This file shows that the original continuation `fhatProfileC` and the subtract-leading
continuation `rhsBSubLeading` agree on the connected domain `Re u > 0` with `u ≠ 2`, via an
identity-theorem argument using agreement on the real range `u > 4`.

## Main statement
* `eqOn_domainPosNeTwo_fhatProfileC_rhsBSubLeading`

-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceBSubLeadingCont.Private

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Topology

open Complex Filter MeasureTheory Real Set SchwartzMap
open UpperHalfPlane

open LaplaceFourierCont

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open LaplaceFourierCont.PrivateDefs

lemma laplaceBKernelC_eq_laplaceBKernelSubLeading_ofReal (u : ℝ) (hu : 4 < u) :
    LaplaceFourierCont.PrivateDefs.laplaceBKernelC (u : ℂ) = laplaceBKernelSubLeading (u : ℂ) := by
  have hu2 : (2 : ℝ) < u := lt_trans (by norm_num) hu
  have hsplit :=
    LaplaceBKernelAnalytic.laplaceBKernelC_eq_Ioc_add_Ioi_one (u := (u : ℂ)) (by simpa using! hu2)
  -- Split the tail integral into the subtracted part plus the explicit leading term.
  have htail :
      (∫ t in Set.Ioi (1 : ℝ), BKernel0 t * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))) =
        (∫ t in Set.Ioi (1 : ℝ),
            (BKernel0 t - (BleadingTermR t : ℂ)) * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))) +
          ∫ t in Set.Ioi (1 : ℝ),
            (BleadingTermR t : ℂ) * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ)) := by
    -- Use linearity of the integral (providing the needed integrability witnesses).
    let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
    let f : ℝ → ℂ := fun t : ℝ => tailIntegrand (u : ℂ) t
    let g : ℝ → ℂ :=
      fun t : ℝ =>
        (BleadingTermR t : ℂ) * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))
    have hf : Integrable f μ := by
      -- `f` is the `tailIntegrand` at the real parameter `u`.
      have hmeas : AEStronglyMeasurable f μ := by
        simpa [f, μ] using! aestronglyMeasurable_tailIntegrand_Ioi_one (u := (u : ℂ))
      have hbound :
          ∀ᵐ t : ℝ ∂μ, ‖f t‖ ≤ (polyBound t) * Real.exp (-Real.pi * u * t) := by
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
        have hpoly : ‖BKernel0 t - (BleadingTermR t : ℂ)‖ ≤ polyBound t := by
          simpa [polyBound] using! (norm_BKernel0_sub_leading_le_poly (t := t) ht1)
        have hexp : ‖Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))‖ = Real.exp (-Real.pi * u * t) := by
          simpa using! LaplaceBKernelAnalytic.norm_kernelExp (u := (u : ℂ)) (t := t)
        calc
          ‖f t‖
              = ‖BKernel0 t - (BleadingTermR t : ℂ)‖ *
                  ‖Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))‖ := by
                    simp [f, tailIntegrand, mul_assoc]
          _ ≤ (polyBound t) * Real.exp (-Real.pi * u * t) := by
                have hpoly0 : 0 ≤ polyBound t := le_trans (norm_nonneg _) hpoly
                -- rewrite the exponential norm and apply `mul_le_mul`.
                rw [hexp]
                exact mul_le_mul hpoly le_rfl (by positivity) hpoly0
      have hintg : Integrable (fun t : ℝ => (polyBound t) * Real.exp (-Real.pi * u * t)) μ := by
        have :
            IntegrableOn (fun t : ℝ => (polyBound t) * Real.exp (-Real.pi * u * t))
              (Set.Ioi (1 : ℝ)) volume :=
          integrable_polyBound_mul_exp_Ioi_one (uMin := u) (by nlinarith [hu2])
        simpa [μ, MeasureTheory.IntegrableOn] using! this
      exact Integrable.mono' hintg hmeas hbound
    have hg : Integrable g μ := by
      -- The explicit leading term is integrable for `u > 2`.
      have hcont : Continuous g := by
        -- unfold the explicit formula for `BleadingTermR` to make `fun_prop` succeed
        dsimp [g, BleadingTermR]
        fun_prop
      have hmeas : AEStronglyMeasurable g μ := by
        exact hcont.aestronglyMeasurable
      let b : ℝ := Real.pi * (u - 2)
      have hb : 0 < b := by
        have : 0 < u - 2 := sub_pos.2 hu2
        exact mul_pos Real.pi_pos this
      have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume := by
        simpa [
          pow_one
        ] using! (LaplaceBKernelAnalytic.integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 1) (b := b)
        hb)
      have h0 : IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume := by
        exact exp_neg_integrableOn_Ioi 1 hb
      have hbound :
          ∀ᵐ t : ℝ ∂μ, ‖g t‖ ≤
            ((1 / 39 : ℝ) * t + (10 / (117 * Real.pi) : ℝ)) * Real.exp (-b * t) := by
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        have ht0 : 0 ≤ t := le_of_lt (lt_trans (by norm_num) ht)
        have hexp : ‖Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))‖ = Real.exp (-Real.pi * u * t) := by
          simpa using! LaplaceBKernelAnalytic.norm_kernelExp (u := (u : ℂ)) (t := t)
        have habs :
            ‖(BleadingTermR t : ℂ)‖ ≤
              ((1 / 39 : ℝ) * t + (10 / (117 * Real.pi) : ℝ)) * Real.exp (2 * Real.pi * t) := by
          -- Start from the explicit formula and use the triangle inequality:
          -- `|a*e - b*e| ≤ |a*e| + |b*e| = (|a|+|b|) * e`.
          have hnorm : ‖(BleadingTermR t : ℂ)‖ = |BleadingTermR t| := by
            simp [Complex.norm_real, Real.norm_eq_abs]
          rw [hnorm]
          let a : ℝ := (1 / 39 : ℝ)
          let c : ℝ := (10 / (117 * Real.pi) : ℝ)
          have hc0 : 0 ≤ c := by
            dsimp [c]
            positivity [Real.pi_pos]
          have ha0 : 0 ≤ a := by dsimp [a]; positivity
          have hexp0 : 0 ≤ Real.exp (2 * Real.pi * t) := (Real.exp_pos _).le
          have htri :
              |a * t * Real.exp (2 * Real.pi * t) - c * Real.exp (2 * Real.pi * t)| ≤
                |a * t * Real.exp (2 * Real.pi * t)| + |c * Real.exp (2 * Real.pi * t)| := by
            -- `|x - y| ≤ |x| + |y|` via the metric triangle inequality specialized at `0`.
            simpa [sub_eq_add_neg, abs_neg] using!
              (abs_sub_le (a * t * Real.exp (2 * Real.pi * t)) 0 (c * Real.exp (2 * Real.pi * t)))
          have habsA : |a * t * Real.exp (2 * Real.pi * t)| = a * t * Real.exp (2 * Real.pi * t)
            := by
            have : 0 ≤ a * t * Real.exp (2 * Real.pi * t) := by
              positivity [ha0, ht0, Real.exp_pos (2 * Real.pi * t)]
            exact abs_of_nonneg this
          have habsC : |c * Real.exp (2 * Real.pi * t)| = c * Real.exp (2 * Real.pi * t) := by
            have : 0 ≤ c * Real.exp (2 * Real.pi * t) := by
              positivity [hc0, Real.exp_pos (2 * Real.pi * t)]
            exact abs_of_nonneg this
          -- Now combine and rewrite.
          have : |BleadingTermR t| ≤ (a * t + c) * Real.exp (2 * Real.pi * t) := by
            -- Expand `BleadingTermR` and apply the bound.
            have hBlead :
                BleadingTermR t =
                  a * t * Real.exp (2 * Real.pi * t) -
                    c * Real.exp (2 * Real.pi * t) := by
              dsimp [BleadingTermR, a, c]
            -- Apply the triangle inequality.
            rw [hBlead]
            have hxy :
                |a * t * Real.exp (2 * Real.pi * t)| + |c * Real.exp (2 * Real.pi * t)| =
                  (a * t + c) * Real.exp (2 * Real.pi * t) := by
              rw [habsA, habsC]
              ring_nf
            exact (le_trans htri (le_of_eq hxy))
          -- Finish by rewriting `a,c`.
          simpa [a, c, mul_assoc, add_assoc] using! this
        have hexp_prod :
            Real.exp (2 * Real.pi * t) * Real.exp (-Real.pi * u * t) = Real.exp (-b * t) := by
          -- Combine the exponential factors.
          have : 2 * Real.pi * t + (-Real.pi * u * t) = -b * t := by
            dsimp [b]
            ring
          calc
            Real.exp (2 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
                Real.exp (2 * Real.pi * t + (-Real.pi * u * t)) := by
                  exact (Real.exp_add (2 * Real.pi * t) (-Real.pi * u * t)).symm
            _ = Real.exp (-b * t) := by simpa [this]
        calc
          ‖g t‖ = ‖(BleadingTermR t : ℂ)‖ * ‖Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))‖ := by
            simp [g, mul_assoc]
          _ ≤ (((1 / 39 : ℝ) * t + (10 / (117 * Real.pi) : ℝ)) * Real.exp (2 * Real.pi * t)) *
                Real.exp (-Real.pi * u * t) := by
              -- Rewrite the exponential norm and apply the coefficient bound.
              rw [hexp]
              exact mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
          _ = ((1 / 39 : ℝ) * t + (10 / (117 * Real.pi) : ℝ)) *
                (Real.exp (2 * Real.pi * t) * Real.exp (-Real.pi * u * t)) := by
              simp [mul_assoc]
          _ = ((1 / 39 : ℝ) * t + (10 / (117 * Real.pi) : ℝ)) * Real.exp (-b * t) := by
              -- Avoid cancellation simp lemmas; just rewrite using `hexp_prod`.
              lia
      have hint :
          Integrable (fun t : ℝ => ((1 / 39 : ℝ) * t + (10 / (117 * Real.pi) : ℝ)) * Real.exp (-b *
          t)) μ
            := by
        have h1' : Integrable (fun t : ℝ => (1 / 39 : ℝ) * (t * Real.exp (-b * t))) μ := by
          have : IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume := h1
          have : Integrable (fun t : ℝ => t * Real.exp (-b * t)) μ := by
            simpa [μ, MeasureTheory.IntegrableOn] using! this
          simpa [mul_assoc, mul_left_comm, mul_comm] using! this.const_mul (1 / 39 : ℝ)
        have h0' : Integrable (fun t : ℝ => (10 / (117 * Real.pi) : ℝ) * Real.exp (-b * t)) μ := by
          have : IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume := h0
          have : Integrable (fun t : ℝ => Real.exp (-b * t)) μ := by
            simpa [μ, MeasureTheory.IntegrableOn] using! this
          simpa [mul_assoc] using! this.const_mul (10 / (117 * Real.pi) : ℝ)
        -- Add and rewrite.
        have hsum :
            Integrable
                (fun t : ℝ =>
                  (1 / 39 : ℝ) * (t * Real.exp (-b * t)) +
                    (10 / (117 * Real.pi) : ℝ) * Real.exp (-b * t)) μ :=
          h1'.add h0'
        have hEq :
            (fun t : ℝ => ((1 / 39 : ℝ) * t + (10 / (117 * Real.pi) : ℝ)) * Real.exp (-b * t)) =ᵐ[μ]
              fun t : ℝ =>
                (1 / 39 : ℝ) * (t * Real.exp (-b * t)) +
                  (10 / (117 * Real.pi) : ℝ) * Real.exp (-b * t) := by
          refine Filter.Eventually.of_forall ?_
          intro t
          ring_nf
        exact hsum.congr hEq.symm
      exact Integrable.mono' hint hmeas hbound
    have hadd :
        (∫ t : ℝ, f t + g t ∂μ) = (∫ t : ℝ, f t ∂μ) + ∫ t : ℝ, g t ∂μ :=
      MeasureTheory.integral_add (μ := μ) hf hg
    -- Rewrite the integrand.
    have hdecomp : (fun t : ℝ => BKernel0 t * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))) =
        fun t : ℝ => f t + g t := by
      funext t
      dsimp [f, g, tailIntegrand]
      ring_nf
    have haddSet :
        (∫ t : ℝ, f t + g t ∂μ) = (∫ t : ℝ, f t ∂μ) + ∫ t : ℝ, g t ∂μ := hadd
    -- Convert back to set integral notation, and rewrite the integrand using `hdecomp`.
    have haddSet' :
        (∫ t in Set.Ioi (1 : ℝ), f t + g t) =
          (∫ t in Set.Ioi (1 : ℝ), f t) + ∫ t in Set.Ioi (1 : ℝ), g t := by
      simpa [μ] using! haddSet
    calc
        (∫ t in Set.Ioi (1 : ℝ), BKernel0 t * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ)))
            = ∫ t in Set.Ioi (1 : ℝ), f t + g t := by
                exact
                  Complex.ext
                    (congrArg Complex.re
                      (congrArg (integral (volume.restrict (Ioi 1))) hdecomp))
                    (congrArg Complex.im
                      (congrArg (integral (volume.restrict (Ioi 1))) hdecomp))
      _ = (∫ t in Set.Ioi (1 : ℝ), f t) + ∫ t in Set.Ioi (1 : ℝ), g t := haddSet'
      _ = (∫ t in Set.Ioi (1 : ℝ),
              (BKernel0 t - (BleadingTermR t : ℂ)) * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))) +
            ∫ t in Set.Ioi (1 : ℝ),
              (BleadingTermR t : ℂ) * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ)) := by
          rfl
  have htail_outer :
        (∫ t in Set.Ioi (1 : ℝ), BKernel0 t * Complex.exp (-((π : ℂ) * (u : ℂ) * (t : ℂ)))) =
          (∫ t in Set.Ioi (1 : ℝ),
              (BKernel0 t - (BleadingTermR t : ℂ)) * Complex.exp (-((π : ℂ) * (u : ℂ) * (t : ℂ)))) +
            ∫ t in Set.Ioi (1 : ℝ),
              (BleadingTermR t : ℂ) * Complex.exp (-((π : ℂ) * (u : ℂ) * (t : ℂ))) := by
      simpa [exp_neg_pi_mul_outer] using! htail
  -- Put everything together.
  have hlead :
        (∫ t in Set.Ioi (1 : ℝ),
            (BleadingTermR t : ℂ) * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))) =
          BleadingCorrectionC (u : ℂ) :=
      integral_Ioi_one_BleadingTermC_mul_exp_neg_pi_complex (u := u) hu2
  have hlead_outer :
        (∫ t in Set.Ioi (1 : ℝ),
            (BleadingTermR t : ℂ) * Complex.exp (-((π : ℂ) * (u : ℂ) * (t : ℂ)))) =
          BleadingCorrectionC (u : ℂ) := by
      simpa [exp_neg_pi_mul_outer] using! hlead
  -- Unfold `laplaceBKernelC` and compare with the definition of `laplaceBKernelSubLeading`.
  -- `hsplit` is stated for `kernelIntegrand`; unfold it into the `BKernel0 * exp` form.
  have hsplit' :
        LaplaceFourierCont.PrivateDefs.laplaceBKernelC (u : ℂ) =
          (∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))) +
            ∫ t in Set.Ioi (1 : ℝ), BKernel0 t * Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ)) := by
      assumption
  have hsplit_outer :
        LaplaceFourierCont.PrivateDefs.laplaceBKernelC (u : ℂ) =
          (∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Complex.exp (-((π : ℂ) * (u : ℂ) * (t : ℂ)))) +
            ∫ t in Set.Ioi (1 : ℝ), BKernel0 t * Complex.exp (-((π : ℂ) * (u : ℂ) * (t : ℂ))) := by
      simpa [exp_neg_pi_mul_outer] using! hsplit'
  -- Substitute the tail decomposition and the closed form.
  calc
      LaplaceFourierCont.PrivateDefs.laplaceBKernelC (u : ℂ)
          = (∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Complex.exp (-((π : ℂ) * (u : ℂ) * (t : ℂ)))) +
              ∫ t in Set.Ioi (1 : ℝ), BKernel0 t * Complex.exp (-((π : ℂ) * (u : ℂ) * (t :
              ℂ))) := hsplit_outer
      _ = (∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Complex.exp (-((π : ℂ) * (u : ℂ) * (t : ℂ)))) +
            ((∫ t in Set.Ioi (1 : ℝ),
                (BKernel0 t - (BleadingTermR t : ℂ)) *
                  Complex.exp (-((π : ℂ) * (u : ℂ) * (t : ℂ)))) +
              ∫ t in Set.Ioi (1 : ℝ),
                (BleadingTermR t : ℂ) * Complex.exp (-((π : ℂ) * (u : ℂ) * (t : ℂ)))) := by
              simp [htail_outer]
        _ = laplaceBKernelSubLeading (u : ℂ) := by
              simp [
                laplaceBKernelSubLeading,
                hlead_outer,
                add_left_comm,
                add_comm
              ]

lemma rhsB_eq_rhsBSubLeading_ofReal (u : ℝ) (hu : 4 < u) :
    LaplaceFourierCont.PrivateDefs.rhsB (u : ℂ) = rhsBSubLeading (u : ℂ) := by
  simp [LaplaceFourierCont.PrivateDefs.rhsB, rhsBSubLeading,
    laplaceBKernelC_eq_laplaceBKernelSubLeading_ofReal (u := u) hu]

lemma rhsBSubLeading_agrees_of_four (u : ℝ) (hu : 4 < u) :
    LaplaceFourierCont.PrivateDefs.fhatProfileC (u : ℂ) = rhsBSubLeading (u : ℂ) := by
  have h0 := LaplaceFourierCont.rhsB_agrees_of_four (u := u) hu
  have h1 := rhsB_eq_rhsBSubLeading_ofReal (u := u) hu
  exact h0.trans h1


lemma analyticOnNhd_fhatProfileC_domainPosNeTwo :
    AnalyticOnNhd ℂ LaplaceFourierCont.PrivateDefs.fhatProfileC LaplaceDomains.domainPosNeTwo := by
  intro z hz
  have hzRe : z ∈ SpherePacking.rightHalfPlane := hz.1
  exact LaplaceFourierCont.analyticOnNhd_fhatProfileC z hzRe

/-- `fhatProfileC` agrees with `rhsBSubLeading` on `Re u > 0` with `u ≠ 2`. -/
public lemma eqOn_domainPosNeTwo_fhatProfileC_rhsBSubLeading :
    Set.EqOn LaplaceFourierCont.PrivateDefs.fhatProfileC rhsBSubLeading
      LaplaceDomains.domainPosNeTwo := by
  have hana_fhat :
      AnalyticOnNhd ℂ LaplaceFourierCont.PrivateDefs.fhatProfileC LaplaceDomains.domainPosNeTwo :=
    analyticOnNhd_fhatProfileC_domainPosNeTwo
  have hana_rhs : AnalyticOnNhd ℂ rhsBSubLeading LaplaceDomains.domainPosNeTwo :=
    analyticOnNhd_rhsBSubLeading
  have hfreq :
      (∃ᶠ z in 𝓝[≠] (5 : ℂ),
        LaplaceFourierCont.PrivateDefs.fhatProfileC z = rhsBSubLeading z) :=
    LaplaceDomains.frequently_eq_near_five
      (f := LaplaceFourierCont.PrivateDefs.fhatProfileC)
      (g := rhsBSubLeading)
      (fun u hu => rhsBSubLeading_agrees_of_four (u := u) hu)
  have h5 : (5 : ℂ) ∈ LaplaceDomains.domainPosNeTwo := by
    refine ⟨?_, ?_⟩
    · -- `0 < (5 : ℂ).re`.
      simp [SpherePacking.rightHalfPlane]
    · simp
  simpa using!
    (AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (𝕜 := ℂ)
      (f := LaplaceFourierCont.PrivateDefs.fhatProfileC) (g := rhsBSubLeading)
      hana_fhat hana_rhs LaplaceDomains.domainPosNeTwo_isPreconnected h5 hfreq)


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceBSubLeadingCont.Private
