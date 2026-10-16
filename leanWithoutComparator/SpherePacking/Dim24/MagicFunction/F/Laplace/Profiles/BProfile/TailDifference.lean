-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Profiles.BProfile.Bounds
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular


/-!
# Tail difference in the `ψT'` rectangle identity

This file rewrites the horizontal rectangle integral of the `ψT'` integrand against the weight
`expU u` as a difference of two tail integrals on the vertical lines `Re z = 0` and `Re z = 1`.
The assumption `u > 4` ensures integrability on the top edge.

## Main statement
* `ψT_rect_integral_eq_I_mul_tail_diff`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped UpperHalfPlane Interval Topology

open Complex Filter MeasureTheory Real SchwartzMap Set
open UpperHalfPlane
open MagicFunction.Parametrisations RealIntegrals SpecialValuesAux

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


/-- Rectangle identity for the `ψT'` horizontal integral, expressed as a difference of two tail
integrals on `t ≥ 1`. -/
public lemma ψT_rect_integral_eq_I_mul_tail_diff (u : ℝ) (hu : 4 < u) :
    (∫ x in (0 : ℝ)..1, ψT' ((x : ℂ) + Complex.I) * expU u ((x : ℂ) + Complex.I)) =
      (Complex.I • ∫ t in Set.Ioi (1 : ℝ), ψT' ((0 : ℂ) + (t : ℂ) * Complex.I) * expU u ((0 : ℂ) +
      (t : ℂ) * Complex.I)) -
        (Complex.I • ∫ t in Set.Ioi (1 : ℝ), ψT' ((1 : ℂ) + (t : ℂ) * Complex.I) * expU u ((1 : ℂ) +
        (t : ℂ) * Complex.I))
          := by
  have hu0 : 0 ≤ u := le_trans (by linarith) (le_of_lt hu)
  let fU : ℂ → ℂ := fun z : ℂ => ψT' z * expU u z
  have hsubset :
      (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) ⊆ UpperHalfPlane.upperHalfPlaneSet := by
    intro z hz
    have hzIm : (1 : ℝ) ≤ z.im := by
      simpa using! (mem_reProdIm.1 hz).2
    exact lt_of_lt_of_le (by norm_num) hzIm
  have hcont : ContinuousOn fU (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
    have hψ : ContinuousOn ψT' (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
      have hcont' := (SpherePacking.Dim24.differentiableOn_ψT'_upper.continuousOn).mono hsubset
      simpa using! hcont'
    have hE : ContinuousOn (fun z : ℂ => expU u z) (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
      have : Continuous fun z : ℂ => expU u z := by
        simpa using! (continuous_expU (u := u))
      exact this.continuousOn
    exact hψ.mul hE
  have hdiff :
      ∀ z ∈ (Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1) ×ℂ Set.Ioi (1 : ℝ)),
        DifferentiableAt ℂ fU z := by
    intro z hz
    have hzIm : z ∈ UpperHalfPlane.upperHalfPlaneSet := by
      have hzIm1 : (1 : ℝ) < z.im := by
        simpa using! (mem_reProdIm.1 (by simpa using! hz)).2
      exact lt_of_lt_of_le (by norm_num) (le_of_lt hzIm1)
    have hψ : DifferentiableAt ℂ ψT' z :=
      (SpherePacking.Dim24.differentiableOn_ψT'_upper z
      hzIm).differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzIm)
    have hE : DifferentiableAt ℂ (fun w : ℂ => expU u w) z := by
      simpa using! (differentiableAt_expU (u := u) (z := z))
    simpa [fU] using! hψ.mul hE
  -- Vertical integrability: on each vertical line (`Re z = 0` and `Re z = 1`), the growth bound
  -- `‖ψT z‖ ≤ C * exp(4π Im z)` and the identity `‖expU u (a + tI)‖ = exp(-π u t)` give the
  -- dominating integrable bound `C * exp(-π (u-4) t)` since `u > 4`.
  rcases exists_ψT_bound_exp with ⟨Cψ, Aψ, hCψ, hψT⟩
  have hint (a : ℝ) (ha : a ∈ Set.uIcc (0 : ℝ) 1) :
      IntegrableOn (fun t : ℝ => fU ((a : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
    let A : ℝ := max Aψ 1
    have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
    -- Continuity along the vertical line gives integrability on `(1, A]`.
    let γ : ℝ → ℂ := fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I
    have hγcont : Continuous γ := by
      have : Continuous fun t : ℝ => (t : ℂ) := Complex.continuous_ofReal
      simpa [γ] using! (continuous_const.add (this.mul continuous_const))
    have hmapIcc : Set.MapsTo γ (Set.Icc (1 : ℝ) A) (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1
      have htIci : t ∈ Set.Ici (1 : ℝ) := ht1
      have hre : (γ t).re ∈ Set.uIcc (0 : ℝ) 1 := by simpa [γ, Complex.add_re] using! ha
      have him : (γ t).im ∈ Set.Ici (1 : ℝ) := by simpa [γ, Complex.add_im] using! htIci
      exact (mem_reProdIm.2 ⟨hre, him⟩)
    have hcontIcc : ContinuousOn (fun t : ℝ => fU (γ t)) (Set.Icc (1 : ℝ) A) :=
      hcont.comp hγcont.continuousOn hmapIcc
    have hInt_finite : IntegrableOn (fun t : ℝ => fU (γ t)) (Set.Ioc (1 : ℝ) A) volume := by
      have hIcc : IntegrableOn (fun t : ℝ => fU (γ t)) (Set.Icc (1 : ℝ) A) volume :=
        hcontIcc.integrableOn_Icc (μ := volume)
      refine hIcc.mono_set ?_
      intro t ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    -- On the tail `t > A`, use the exponential bound from `exists_ψT_bound_exp`.
    let b : ℝ := Real.pi * (u - 4)
    have hb : 0 < b := by nlinarith [Real.pi_pos, sub_pos.2 hu]
    let g : ℝ → ℝ := fun t : ℝ => (Cψ : ℝ) * Real.exp (-b * t)
    have hg : IntegrableOn (fun t : ℝ => g t) (Set.Ioi A) volume := by
      have hexp : IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Set.Ioi A) volume :=
        exp_neg_integrableOn_Ioi A hb
      simpa [g, mul_assoc] using! (hexp.const_mul Cψ)
    have hf_meas : AEStronglyMeasurable (fun t : ℝ => fU (γ t)) (volume.restrict (Set.Ioi A)) := by
      have hmapIoi : Set.MapsTo γ (Set.Ioi A) (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := le_trans hA1 (le_of_lt ht)
        have htIci : t ∈ Set.Ici (1 : ℝ) := ht1
        have hre : (γ t).re ∈ Set.uIcc (0 : ℝ) 1 := by simpa [γ, Complex.add_re] using! ha
        have him : (γ t).im ∈ Set.Ici (1 : ℝ) := by simpa [γ, Complex.add_im] using! htIci
        exact (mem_reProdIm.2 ⟨hre, him⟩)
      have hcontIoi : ContinuousOn (fun t : ℝ => fU (γ t)) (Set.Ioi A) :=
        hcont.comp hγcont.continuousOn hmapIoi
      simpa using! (hcontIoi.aestronglyMeasurable (μ := volume) measurableSet_Ioi)
    have hf_bound :
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi A)), ‖fU (γ t)‖ ≤ g t := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have htA : Aψ ≤ t := le_trans (le_max_left _ _) (le_of_lt ht)
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_trans hA1 (le_of_lt ht))
      have him : (γ t).im = t := by simp [γ, Complex.add_im]
      have hz : 0 < (γ t).im := by simpa [γ, Complex.add_im] using! ht0
      have hψ : ‖ψT' (γ t)‖ ≤ Cψ * Real.exp (4 * Real.pi * t) := by
        have htA' : Aψ ≤ (γ t).im := by simpa [him] using! htA
        have h := hψT (UpperHalfPlane.mk (γ t) hz) (by simpa using! htA')
        have himH : (UpperHalfPlane.mk (γ t) hz).im = t := by simp [UpperHalfPlane.im, him]
        have hψT' : ψT' (γ t) = ψT (UpperHalfPlane.mk (γ t) hz) := ψT'_eq (z := γ t) hz
        simpa [hψT', himH] using! h
      have hexp : ‖expU u (γ t)‖ = Real.exp (-Real.pi * u * t) :=
        norm_expU_real (u := u) (a := a) (t := t)
      have hmul :
          ‖fU (γ t)‖ ≤ (Cψ * Real.exp (4 * Real.pi * t)) * Real.exp (-Real.pi * u * t) := by
        simpa [fU, norm_mul, hexp] using! mul_le_mul_of_nonneg_right hψ (by positivity)
      have hE :
          (Real.exp (4 * Real.pi * t)) * Real.exp (-Real.pi * u * t) = Real.exp (-b * t) := by
        have hsum : (4 * Real.pi * t) + (-Real.pi * u * t) = -b * t := by dsimp [b]; ring
        calc
          Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
              Real.exp ((4 * Real.pi * t) + (-Real.pi * u * t)) := by
                simpa using! (Real.exp_add (4 * Real.pi * t) (-Real.pi * u * t)).symm
          _ = Real.exp (-b * t) := by simpa using! congrArg Real.exp hsum
      dsimp [g] at *
      nlinarith [hmul, hE]
    have hInt_tail : IntegrableOn (fun t : ℝ => fU (γ t)) (Set.Ioi A) volume := by
      have hg' : Integrable (fun t : ℝ => g t) (volume.restrict (Set.Ioi A)) := by
        simpa [IntegrableOn] using! hg
      have hF : Integrable (fun t : ℝ => fU (γ t)) (volume.restrict (Set.Ioi A)) :=
        Integrable.mono' hg' hf_meas hf_bound
      simpa [IntegrableOn] using! hF
    -- Combine `(1, A]` and `(A, ∞)`.
    have hUnion : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A := by
      simpa using! (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) hA1).symm
    simpa [hUnion] using! hInt_finite.union hInt_tail
  have hint₁ :
      IntegrableOn (fun t : ℝ => fU ((0 : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume :=
    by
      simpa using! (hint 0 (by simp))
  have hint₂ :
      IntegrableOn (fun t : ℝ => fU ((1 : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume :=
    by
      simpa using! (hint 1 (by simp))
  -- Top edge tends to `0` by the same exponential estimate (uniform in `x∈[0,1]`).
  have htop :
      Tendsto (fun m : ℝ => ∫ x in (0 : ℝ)..1, fU ((x : ℂ) + (m : ℂ) * Complex.I)) atTop (𝓝 0) := by
    -- It suffices to show the norms tend to `0`.
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : 0 < Real.pi * (u - 4) := by
      have : 0 < u - 4 := sub_pos.2 hu
      nlinarith [Real.pi_pos, this]
    -- Use the norm bound `‖top m‖ ≤ Cψ * exp(-π(u-4) m)`.
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (f := fun m : ℝ => ‖∫ x in (0 : ℝ)..1, fU ((x : ℂ) + (m : ℂ) * Complex.I)‖)
        (g := fun _ : ℝ => (0 : ℝ))
        (h := fun m : ℝ => (Cψ : ℝ) * Real.exp (-(Real.pi * (u - 4)) * m)) ?_ ?_ ?_ ?_
    · exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
    · have : Tendsto (fun m : ℝ => (Cψ : ℝ) * Real.exp (-(Real.pi * (u - 4)) * m)) atTop (𝓝 0) := by
        have hlin : Tendsto (fun m : ℝ => -(Real.pi * (u - 4)) * m) atTop atBot :=
          tendsto_id.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos, sub_pos.2 hu])
        have hexp := (Real.tendsto_exp_atBot.comp hlin)
        simpa [mul_assoc] using! (tendsto_const_nhds.mul hexp)
      exact this
    · exact Filter.Eventually.of_forall (fun _m : ℝ => by positivity)
    · filter_upwards [eventually_ge_atTop (max Aψ 1)] with m hm
      -- bound the integrand uniformly in `x∈[0,1]`
      have hnorm :
          ‖∫ x in (0 : ℝ)..1, fU ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
            (Cψ : ℝ) * Real.exp (-(Real.pi * (u - 4)) * m) := by
        have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_right _ _) hm
        have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm1
        have hboundx :
            ∀ x : ℝ, ‖fU ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤ (Cψ : ℝ) * Real.exp (-(Real.pi * (u -
            4)) * m)
              := by
          intro x
          have hψ : ‖ψT' ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤ Cψ * Real.exp (4 * Real.pi * m) := by
            -- apply the upper-half-plane bound to `z = x + mI`
            have hmA :
                Aψ ≤ (UpperHalfPlane.mk ((x : ℂ) + (m : ℂ) * Complex.I) (by simpa)).im := by
              simpa [UpperHalfPlane.im] using! (le_trans (le_max_left Aψ 1) hm)
            have h :=
              hψT (UpperHalfPlane.mk ((x : ℂ) + (m : ℂ) * Complex.I) (by simpa)) hmA
            simpa [ψT', hmpos] using! h
          have hexp : ‖expU u ((x : ℂ) + (m : ℂ) * Complex.I)‖ = Real.exp (-Real.pi * u * m) :=
            norm_expU_real (u := u) (a := x) (t := m)
          have hmul :
              ‖fU ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤ (Cψ * Real.exp (4 * Real.pi *
              m)) * Real.exp (-Real.pi * u * m)
                := by
            simpa [fU, norm_mul, hexp] using! mul_le_mul_of_nonneg_right hψ (by positivity)
          have hE :
              (Real.exp (4 * Real.pi * m)) * Real.exp (-Real.pi * u * m) =
                Real.exp (-(Real.pi * (u - 4)) * m) := by
            have hsum : (4 * Real.pi * m) + (-Real.pi * u * m) = -(Real.pi * (u - 4)) * m := by
              ring
            calc
              Real.exp (4 * Real.pi * m) * Real.exp (-Real.pi * u * m) =
                  Real.exp ((4 * Real.pi * m) + (-Real.pi * u * m)) := by
                    simpa using! (Real.exp_add (4 * Real.pi * m) (-Real.pi * u * m)).symm
              _ = Real.exp (-(Real.pi * (u - 4)) * m) := by
                    simpa using! congrArg Real.exp hsum
          nlinarith [hmul, hE]
        have h01 : (0 : ℝ) ≤ 1 := by norm_num
        have hnorm' :
            ‖∫ x in (0 : ℝ)..1, fU ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
              ∫ x in (0 : ℝ)..1, ‖fU ((x : ℂ) + (m : ℂ) * Complex.I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm h01
        have hlen : (∫ x in (0 : ℝ)..1, (Cψ : ℝ) * Real.exp (-(Real.pi * (u - 4)) * m)) =
            (Cψ : ℝ) * Real.exp (-(Real.pi * (u - 4)) * m) := by simp
        -- compare integrals pointwise
        have hle :
            (∫ x in (0 : ℝ)..1, ‖fU ((x : ℂ) + (m : ℂ) * Complex.I)‖) ≤
              ∫ x in (0 : ℝ)..1, (Cψ : ℝ) * Real.exp (-(Real.pi * (u - 4)) * m) := by
          have hγcont : Continuous (fun x : ℝ => (x : ℂ) + (m : ℂ) * Complex.I) := by
            fun_prop
          have hmap :
              Set.MapsTo (fun x : ℝ => (x : ℂ) + (m : ℂ) * Complex.I) (Set.uIcc (0 : ℝ) 1)
                (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
            intro x hx
            have hre : ((x : ℂ) + (m : ℂ) * Complex.I).re ∈ Set.uIcc (0 : ℝ) 1 := by
              simpa [Complex.add_re] using! hx
            have him : ((x : ℂ) + (m : ℂ) * Complex.I).im ∈ Set.Ici (1 : ℝ) := by
              simpa [Complex.add_im] using! hm1
            exact mem_reProdIm.2 ⟨hre, him⟩
          have hcontTop :
              ContinuousOn (fun x : ℝ => fU ((x : ℂ) + (m : ℂ) * Complex.I)) (Set.uIcc (0 : ℝ) 1) :=
            hcont.comp hγcont.continuousOn hmap
          have hfI :
              IntervalIntegrable (fun x : ℝ => ‖fU ((x : ℂ) + (m : ℂ) * Complex.I)‖) volume 0 1
                :=
            (ContinuousOn.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
                hcontTop.norm)
          have hgI :
              IntervalIntegrable (fun _x : ℝ => (Cψ : ℝ) * Real.exp (-(Real.pi * (u - 4)) *
              m)) volume 0
                1 :=
            IntervalIntegrable.symm intervalIntegrable_const
          exact intervalIntegral.integral_mono_on h01 hfI hgI fun x a => hboundx x
        have : ‖∫ x in (0 : ℝ)..1, fU ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
            ∫ x in (0 : ℝ)..1, (Cψ : ℝ) * Real.exp (-(Real.pi * (u - 4)) * m) :=
          le_trans hnorm' hle
        simpa [hlen] using! this
      exact hnorm
  -- Apply the rectangle lemma at height `y=1`.
  have hrect :=
    Complex.rect_deform_of_tendsto_top (f := fU) (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ)) (y := (1 : ℝ))
      hcont hdiff hint₁ hint₂ htop
  -- Rearrange `top + I•right - I•left = 0` into `top = I•left - I•right`.
  have hAdd :
      (∫ x in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) +
          (Complex.I : ℂ) • ∫ t in Set.Ioi (1 : ℝ), fU ((1 : ℂ) + (t : ℂ) * Complex.I) =
        (Complex.I : ℂ) • ∫ t in Set.Ioi (1 : ℝ), fU ((0 : ℂ) + (t : ℂ) * Complex.I) := by
    have h :=
      congrArg
        (fun z : ℂ =>
          z + (Complex.I : ℂ) • ∫ t in Set.Ioi (1 : ℝ), fU ((0 : ℂ) + (t : ℂ) * Complex.I)) hrect
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! h
  have hEq :
      (∫ x in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) =
        ((Complex.I : ℂ) • ∫ t in Set.Ioi (1 : ℝ), fU ((0 : ℂ) + (t : ℂ) * Complex.I)) -
          ((Complex.I : ℂ) • ∫ t in Set.Ioi (1 : ℝ), fU ((1 : ℂ) + (t : ℂ) * Complex.I)) :=
    eq_sub_of_add_eq hAdd
  simpa [fU, zero_add, add_assoc] using! hEq


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile
