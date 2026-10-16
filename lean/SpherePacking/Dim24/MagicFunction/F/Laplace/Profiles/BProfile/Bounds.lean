-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Profiles.BProfile.RectangleIdentity
import SpherePacking.Dim24.ModularForms.Psi.Relations


/-!
# Exponential bounds for `ψI` and `ψT`

This file proves exponential growth bounds for `ψI` and `ψT` on the imaginary axis and uses
them to deduce integrability of the tail integrands appearing in the Laplace formula for
`bProfile` when `u > 4`.

## Main statements
* `exists_ψI_bound_exp`
* `exists_ψT_bound_exp`
* `integrableOn_ψT'_vertical_left_mul_expU`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped UpperHalfPlane Interval Topology

open Complex Filter MeasureTheory Real SchwartzMap Set
open UpperHalfPlane
open MagicFunction.Parametrisations RealIntegrals SpecialValuesAux

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The norm of `expU u (a + t * I)` depends only on the imaginary part `t`. -/
public lemma norm_expU_real (u a t : ℝ) :
    ‖expU u ((a : ℂ) + (t : ℂ) * Complex.I)‖ = Real.exp (-Real.pi * u * t) := by
  have hre : ((Real.pi : ℂ) * Complex.I * (u : ℂ) * ((a : ℂ) + (t : ℂ) * Complex.I)).re =
      -(Real.pi * u * t) := by
    ring_nf
    simp
  simp [expU, Complex.norm_exp, hre]

/-- Exponential bound for `ψI` on the imaginary axis for large imaginary part. -/
public lemma exists_ψI_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖ψI z‖ ≤ C * Real.exp (4 * Real.pi * z.im) := by
  let num : ℍ → ℂ :=
    fun z : ℍ =>
      7 * (H₄ z) ^ (5 : ℕ) * (H₂ z) ^ (2 : ℕ) + 7 * (H₄ z) ^ (6 : ℕ) * (H₂ z) + 2 * (H₄ z) ^ (7 : ℕ)
  have hH2 : Tendsto H₂ atImInfty (𝓝 (0 : ℂ)) := H₂_tendsto_atImInfty
  have hH4 : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
  have hnum : Tendsto num atImInfty (𝓝 (2 : ℂ)) := by
    have hH4_5 := hH4.pow 5
    have hH4_6 := hH4.pow 6
    have hH4_7 := hH4.pow 7
    have hH2_2 := hH2.pow 2
    have h7 : Tendsto (fun _ : ℍ => (7 : ℂ)) atImInfty (𝓝 (7 : ℂ)) := tendsto_const_nhds
    have h2c : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 (2 : ℂ)) := tendsto_const_nhds
    have hterm1 := (h7.mul hH4_5).mul hH2_2
    have hterm2 := (h7.mul hH4_6).mul hH2
    have hterm3 := (h2c.mul hH4_7)
    have hlim :
        (7 : ℂ) * (1 : ℂ) ^ 5 * (0 : ℂ) ^ 2 +
            (7 : ℂ) * (1 : ℂ) ^ 6 * (0 : ℂ) +
          (2 : ℂ) * (1 : ℂ) ^ 7 =
          (2 : ℂ) := by
      norm_num
    simpa [num, mul_assoc, add_assoc, add_left_comm, add_comm, hlim] using!
      (hterm1.add (hterm2.add hterm3))
  have hEvNum : ∀ᶠ z in atImInfty, ‖num z‖ ≤ (3 : ℝ) := by
    have hball : Metric.ball (2 : ℂ) 1 ∈ (𝓝 (2 : ℂ)) := Metric.ball_mem_nhds _ (by norm_num)
    have hmem : ∀ᶠ z in atImInfty, num z ∈ Metric.ball (2 : ℂ) 1 := hnum.eventually hball
    filter_upwards [hmem] with z hz
    have hdist : dist (num z) (2 : ℂ) < 1 := by
      simpa [Metric.mem_ball] using! hz
    have htriangle : ‖num z‖ ≤ ‖num z - (2 : ℂ)‖ + ‖(2 : ℂ)‖ := by
      simpa [sub_add_cancel] using! (norm_add_le (num z - (2 : ℂ)) (2 : ℂ))
    have hdist' : ‖num z - (2 : ℂ)‖ < 1 := by
      simpa [dist_eq_norm] using! hdist
    have : ‖num z‖ < (3 : ℝ) := by
      have : ‖num z‖ < 1 + 2 :=
        lt_of_le_of_lt htriangle (add_lt_add_of_lt_of_le hdist' (by simp))
      nlinarith
    exact le_of_lt this
  rcases (UpperHalfPlane.atImInfty_mem _).1 hEvNum with ⟨A0, hA0⟩
  rcases LaplaceZerosTail.TailBounds.exists_bound_norm_Δ_inv_mul_exp_two_pi with ⟨CΔ, AΔ, hCΔ, hΔ⟩
  refine ⟨3 * (CΔ ^ 2), max A0 AΔ, by positivity [hCΔ], ?_⟩
  intro z hz
  have hz0 : A0 ≤ z.im := le_trans (le_max_left _ _) hz
  have hzΔ : AΔ ≤ z.im := le_trans (le_max_right _ _) hz
  have hnum_le : ‖num z‖ ≤ (3 : ℝ) := hA0 z hz0
  have hΔinv : ‖(Δ z)⁻¹‖ ≤ CΔ * Real.exp (2 * Real.pi * z.im) := hΔ z hzΔ
  have hΔinv2 :
      ‖((Δ z) ^ (2 : ℕ))⁻¹‖ ≤ (CΔ ^ 2) * Real.exp (4 * Real.pi * z.im) := by
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hΔinv 2
    have hrew :
        ‖(Δ z)⁻¹‖ ^ 2 = ‖((Δ z) ^ (2 : ℕ))⁻¹‖ := by
      simp [pow_two]
    have hexp : (Real.exp (2 * Real.pi * z.im)) ^ 2 = Real.exp (4 * Real.pi * z.im) := by
      calc
        (Real.exp (2 * Real.pi * z.im)) ^ 2 = Real.exp (2 * (2 * Real.pi * z.im)) := by
              simpa using! (Real.exp_nat_mul (2 * Real.pi * z.im) 2).symm
        _ = Real.exp (4 * Real.pi * z.im) := by ring_nf
    -- `pow_le_pow_left₀` produced a bound on squares; rewrite it into the desired shape.
    simpa [hrew, mul_pow, hexp] using! hpow
  have hψ : ψI z = num z / (Δ z) ^ (2 : ℕ) := by
    -- `ψI_eq_H` provides exactly this denominator.
    simp [num, SpherePacking.Dim24.ψI_eq_H, div_eq_mul_inv, mul_left_comm, mul_comm]
  calc
    ‖ψI z‖ = ‖num z / (Δ z) ^ (2 : ℕ)‖ := by simp [hψ]
    _ = ‖num z‖ * ‖((Δ z) ^ (2 : ℕ))⁻¹‖ := by
          simp [div_eq_mul_inv]
    _ ≤ (3 : ℝ) * ((CΔ ^ 2) * Real.exp (4 * Real.pi * z.im)) :=
          mul_le_mul hnum_le hΔinv2 (by positivity) (by positivity)
    _ = (3 * (CΔ ^ 2)) * Real.exp (4 * Real.pi * z.im) := by ring

/-- Exponential bound for `ψT` on the imaginary axis for large imaginary part. -/
public lemma exists_ψT_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖ψT z‖ ≤ C * Real.exp (4 * Real.pi * z.im) := by
  rcases exists_ψI_bound_exp with ⟨C, A, hC, hψI⟩
  refine ⟨C, A, hC, ?_⟩
  intro z hz
  have hz' : A ≤ (((1 : ℝ) +ᵥ z : ℍ)).im := by simpa using! hz
  -- `ψT(z) = ψI(z+1)` and `Im(z+1) = Im z`.
  have hrel : ψT z = ψI ((1 : ℝ) +ᵥ z) := by simp [ψT, modular_slash_T_apply]
  have hIm : (((1 : ℝ) +ᵥ z : ℍ)).im = z.im := by simp
  simpa [hrel, hIm] using! hψI ((1 : ℝ) +ᵥ z) hz'

/-- Integrability of the `ψT'` tail integrand against the weight `expU u` for `u > 4`. -/
public lemma integrableOn_ψT'_vertical_left_mul_expU (u : ℝ) (hu : 4 < u) :
    IntegrableOn (fun t : ℝ => ψT' (t * Complex.I) * expU u (t * Complex.I)) (Set.Ioi (1 :
    ℝ)) volume
      := by
  rcases exists_ψT_bound_exp with ⟨Cψ, Aψ, hCψ, hψT⟩
  let A : ℝ := max Aψ 1
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hsubset :
      (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) ⊆ UpperHalfPlane.upperHalfPlaneSet := by
    intro z hz
    have hzIm : (1 : ℝ) ≤ z.im := by
      simpa using! (mem_reProdIm.1 hz).2
    exact lt_of_lt_of_le (by norm_num) hzIm
  -- Finite part `(1, A]` by continuity on `[1, A]`.
  let γ : ℝ → ℂ := fun t : ℝ => (t : ℂ) * Complex.I
  have hγcont : Continuous γ := by
    simpa [γ] using! (Complex.continuous_ofReal.mul continuous_const)
  have hmapIcc : Set.MapsTo γ (Set.Icc (1 : ℝ) A) (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1
    have hre : (γ t).re ∈ Set.uIcc (0 : ℝ) 1 := by
      -- `Re(tI)=0`.
      simp [γ]
    have him : (γ t).im ∈ Set.Ici (1 : ℝ) := by
      -- `Im(tI)=t`.
      simpa [γ] using! ht1
    exact mem_reProdIm.2 ⟨hre, him⟩
  have hψcont : ContinuousOn (fun z : ℂ => ψT' z) (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
    have hcont' := (SpherePacking.Dim24.differentiableOn_ψT'_upper.continuousOn).mono hsubset
    simpa using! hcont'
  have hEcont : ContinuousOn (fun z : ℂ => expU u z) (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
    have : Continuous fun z : ℂ => expU u z := by
      simpa using! (continuous_expU (u := u))
    exact this.continuousOn
  have hcontIcc :
      ContinuousOn (fun t : ℝ => ψT' (γ t) * expU u (γ t)) (Set.Icc (1 : ℝ) A) :=
    (hψcont.comp hγcont.continuousOn hmapIcc).mul (hEcont.comp hγcont.continuousOn hmapIcc)
  have hInt_finite :
      IntegrableOn (fun t : ℝ => ψT' (γ t) * expU u (γ t)) (Set.Ioc (1 : ℝ) A) volume := by
    have hIcc :
        IntegrableOn (fun t : ℝ => ψT' (γ t) * expU u (γ t)) (Set.Icc (1 : ℝ) A) volume :=
      hcontIcc.integrableOn_Icc (μ := volume)
    refine hIcc.mono_set ?_
    intro t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  -- Tail `(A, ∞)` by an exponential bound.
  let b : ℝ := Real.pi * (u - 4)
  have hb : 0 < b := by nlinarith [Real.pi_pos, sub_pos.2 hu]
  let g : ℝ → ℝ := fun t : ℝ => (Cψ : ℝ) * Real.exp (-b * t)
  have hg : IntegrableOn (fun t : ℝ => g t) (Set.Ioi A) volume := by
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Set.Ioi A) volume :=
      exp_neg_integrableOn_Ioi A hb
    simpa [g, mul_assoc] using! (hexp.const_mul Cψ)
  have hf_meas :
      AEStronglyMeasurable
        (fun t : ℝ => ψT' (γ t) * expU u (γ t))
        (volume.restrict (Set.Ioi A)) := by
    have hmapIoi : Set.MapsTo γ (Set.Ioi A) (Set.uIcc (0 : ℝ) 1 ×ℂ Set.Ici (1 : ℝ)) := by
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := le_trans hA1 (le_of_lt ht)
      have hre : (γ t).re ∈ Set.uIcc (0 : ℝ) 1 := by simp [γ]
      have him : (γ t).im ∈ Set.Ici (1 : ℝ) := by simpa [γ] using! ht1
      exact mem_reProdIm.2 ⟨hre, him⟩
    have hcontIoi :
        ContinuousOn (fun t : ℝ => ψT' (γ t) * expU u (γ t)) (Set.Ioi A) :=
      (hψcont.comp hγcont.continuousOn hmapIoi).mul (hEcont.comp hγcont.continuousOn hmapIoi)
    simpa using! (hcontIoi.aestronglyMeasurable (μ := volume) measurableSet_Ioi)
  have hf_bound :
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi A)), ‖ψT' (γ t) * expU u (γ t)‖ ≤ g t := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have htA : Aψ ≤ t := le_trans (le_max_left _ _) (le_of_lt ht)
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_trans hA1 (le_of_lt ht))
    have hz : 0 < (γ t).im := by simpa [γ] using! ht0
    have hψ :
        ‖ψT' (γ t)‖ ≤ Cψ * Real.exp (4 * Real.pi * t) := by
      have htA' : Aψ ≤ (γ t).im := by simpa [γ] using! htA
      have h := hψT (UpperHalfPlane.mk (γ t) hz) (by simpa using! htA')
      have hψT' : ψT' (γ t) = ψT (UpperHalfPlane.mk (γ t) hz) := ψT'_eq (z := γ t) hz
      have him : (UpperHalfPlane.mk (γ t) hz).im = t := by simp [γ, UpperHalfPlane.im]
      -- rewrite using `Im(tI)=t`
      simpa [hψT', him] using! h
    have hexp : ‖expU u (γ t)‖ = Real.exp (-Real.pi * u * t) := by
      simpa [γ] using! (norm_expU_real (u := u) (a := (0 : ℝ)) (t := t))
    have hmul :
        ‖ψT' (γ t) * expU u (γ t)‖ ≤ (Cψ * Real.exp (4 * Real.pi * t)) * Real.exp (-Real.pi * u * t)
          := by
      simpa [norm_mul, hexp] using! mul_le_mul_of_nonneg_right hψ (by positivity)
    have hE :
        (Real.exp (4 * Real.pi * t)) * Real.exp (-Real.pi * u * t) = Real.exp (-b * t) := by
      calc
        Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
            Real.exp ((4 * Real.pi * t) + (-Real.pi * u * t)) := by
              simpa using! (Real.exp_add (4 * Real.pi * t) (-Real.pi * u * t)).symm
        _ = Real.exp (-b * t) := by
              have hexp : (4 * Real.pi * t) + (-Real.pi * u * t) = -b * t := by
                dsimp [b]
                ring
              exact congrArg Real.exp hexp
    dsimp [g] at *
    nlinarith [hmul, hE]
  have hInt_tail : IntegrableOn (fun t : ℝ => ψT' (γ t) * expU u (γ t)) (Set.Ioi A) volume := by
    have hg' : Integrable (fun t : ℝ => g t) (volume.restrict (Set.Ioi A)) := by
      simpa [IntegrableOn] using! hg
    have hF :
        Integrable (fun t : ℝ => ψT' (γ t) * expU u (γ t)) (volume.restrict (Set.Ioi A)) :=
      Integrable.mono' hg' hf_meas hf_bound
    simpa [IntegrableOn] using! hF
  -- Combine `(1, A]` and `(A, ∞)`.
  have hUnion : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A := by
    simpa using! (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) hA1).symm
  simpa [hUnion] using! hInt_finite.union hInt_tail


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile
