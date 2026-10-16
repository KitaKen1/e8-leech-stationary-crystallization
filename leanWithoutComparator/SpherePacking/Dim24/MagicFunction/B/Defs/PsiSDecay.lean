-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
import SpherePacking.ForMathlib.BoundsOnIcc
import SpherePacking.ForMathlib.DerivHelpers


/-!
# Exponential decay of `ψS` on the imaginary axis

This is the key analytic input needed for the `J₆'` tail integral (and hence Schwartz decay).

## Main statements
* `PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one`
* `PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one`
-/

noncomputable section


namespace SpherePacking.Dim24.PsiExpBounds

open scoped UpperHalfPlane Topology Manifold
open UpperHalfPlane
open Filter

lemma continuousOn_resToImagAxis (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) : ContinuousOn F.resToImagAxis (Set.Ioi (0 : ℝ)) := by
  intro t ht
  exact (ResToImagAxis.Differentiable (F := F) hF t ht).continuousAt.continuousWithinAt

lemma exists_bounds_norm_resToImagAxis_Ici_one (F : ℍ → ℂ)
    (hF0 : ∀ z : ℍ, F z ≠ 0)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hF1 : Tendsto F atImInfty (𝓝 (1 : ℂ))) :
    ∃ C c : ℝ, 0 < c ∧ (∀ t : ℝ, 1 ≤ t → ‖F.resToImagAxis t‖ ≤ C) ∧
      (∀ t : ℝ, 1 ≤ t → c ≤ ‖F.resToImagAxis t‖) := by
  -- Tail: closeness to 1.
  have htend :
      Tendsto (fun t : ℝ => F.resToImagAxis t) atTop (𝓝 (1 : ℂ)) := by
    simpa using! (Function.tendsto_resToImagAxis_atImInfty (F := F) (l := (1 : ℂ)) hF1)
  have hEv : ∀ᶠ t in atTop, ‖F.resToImagAxis t - (1 : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    have hsub :
        Tendsto (fun t : ℝ => F.resToImagAxis t - (1 : ℂ)) atTop (𝓝 (0 : ℂ)) :=
      tendsto_sub_nhds_zero_iff.mpr htend
    exact hsub.norm.eventually (Iic_mem_nhds (by norm_num))
  rcases (eventually_atTop.1 hEv) with ⟨T0, hT0⟩
  let T : ℝ := max T0 1
  have hT1 : 1 ≤ T := le_max_right _ _
  -- Upper bound on the tail (use `2` to avoid fraction gymnastics).
  have htail_upper : ∀ t : ℝ, T ≤ t → ‖F.resToImagAxis t‖ ≤ (2 : ℝ) := by
    intro t htT
    have hclose : ‖F.resToImagAxis t - (1 : ℂ)‖ ≤ (1 / 2 : ℝ) :=
      hT0 t (le_trans (le_max_left _ _) htT)
    have htri : ‖F.resToImagAxis t‖ ≤ 1 + ‖F.resToImagAxis t - (1 : ℂ)‖ := by
      -- `F = 1 + (F - 1)`.
      simpa [sub_eq_add_neg, add_assoc] using!
        (norm_add_le (1 : ℂ) (F.resToImagAxis t - (1 : ℂ)))
    linarith
  -- Lower bound on the tail: `‖z‖ ≥ 1 - ‖z-1‖ ≥ 1/2`.
  have htail_lower : ∀ t : ℝ, T ≤ t → (1 / 2 : ℝ) ≤ ‖F.resToImagAxis t‖ := by
    intro t htT
    have hclose : ‖F.resToImagAxis t - (1 : ℂ)‖ ≤ (1 / 2 : ℝ) :=
      hT0 t (le_trans (le_max_left _ _) htT)
    have htri :
        (1 : ℝ) ≤ ‖F.resToImagAxis t‖ + ‖F.resToImagAxis t - (1 : ℂ)‖ := by
      have htri' :
          ‖(1 : ℂ)‖ ≤ ‖F.resToImagAxis t‖ + ‖(1 : ℂ) - F.resToImagAxis t‖ := by
        -- `1 = F + (1 - F)`.
        simpa [sub_eq_add_neg, add_assoc] using!
          (norm_add_le (F.resToImagAxis t) ((1 : ℂ) - F.resToImagAxis t))
      simpa [norm_sub_rev] using! htri'
    linarith
  -- Compact bounds on `[1,T]`.
  have hcont : ContinuousOn (fun t : ℝ => ‖F.resToImagAxis t‖) (Set.Icc 1 T) := by
    have hcont' : ContinuousOn (fun t : ℝ => F.resToImagAxis t) (Set.Ioi (0 : ℝ)) :=
      continuousOn_resToImagAxis (F := F) hF
    have hIcc : Set.Icc 1 T ⊆ Set.Ioi (0 : ℝ) := by
      intro t ht
      have : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
      exact this
    exact (hcont'.mono hIcc).norm
  rcases SpherePacking.ForMathlib.exists_upper_bound_on_Icc
      (g := fun t : ℝ => ‖F.resToImagAxis t‖) (hab := hT1) hcont with
    ⟨C_Icc, hC_Icc⟩
  have hpos : ∀ t ∈ Set.Icc 1 T, 0 < ‖F.resToImagAxis t‖ := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
    have hne : F.resToImagAxis t ≠ 0 := Function.resToImagAxis_ne_zero_of_pos (F := F) hF0 ht0
    exact norm_pos_iff.2 hne
  rcases
      SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc
        (g := fun t : ℝ => ‖F.resToImagAxis t‖) hcont hpos with
    ⟨c_Icc, hc_Icc_pos, hc_Icc⟩
  let C : ℝ := max C_Icc 2
  let c : ℝ := min c_Icc (1 / 2)
  have hc : 0 < c := lt_min hc_Icc_pos (by norm_num)
  refine ⟨C, c, hc, ?_, ?_⟩
  · intro t ht
    by_cases hle : t ≤ T
    · have htIcc : t ∈ Set.Icc 1 T := ⟨ht, hle⟩
      exact (hC_Icc t htIcc).trans (le_max_left _ _)
    · have htT : T ≤ t := le_of_not_ge hle
      exact (htail_upper t htT).trans (le_max_right _ _)
  · intro t ht
    by_cases hle : t ≤ T
    · have htIcc : t ∈ Set.Icc 1 T := ⟨ht, hle⟩
      exact (min_le_left _ _).trans (hc_Icc t htIcc)
    · have htT : T ≤ t := le_of_not_ge hle
      exact (min_le_right _ _).trans (htail_lower t htT)

private lemma psiS_numerator_bound (z : ℍ) (B2 CH4 : ℝ)
    (hH2u : ‖H₂ z‖ ≤ B2) (hH4u : ‖H₄ z‖ ≤ CH4) :
    ‖7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3‖ ≤
      (7 * CH4 ^ 2 + 7 * B2 * CH4 + 2 * B2 ^ 2) * ‖H₂ z‖ := by
  set a : ℂ := 7 * (H₂ z) * (H₄ z) ^ 2
  set b : ℂ := 7 * (H₂ z) ^ 2 * (H₄ z)
  set c : ℂ := 2 * (H₂ z) ^ 3
  have hsum : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    norm_add₃_le
  have hH2sq : ‖H₂ z‖ ^ 2 ≤ B2 * ‖H₂ z‖ := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using!
      mul_le_mul_of_nonneg_right hH2u (norm_nonneg (H₂ z))
  have hB2 : 0 ≤ B2 := (norm_nonneg (H₂ z)).trans hH2u
  have hH2cu : ‖H₂ z‖ ^ 3 ≤ B2 ^ 2 * ‖H₂ z‖ := by
    have hsq : ‖H₂ z‖ ^ 2 ≤ B2 ^ 2 := by
      simpa using! pow_le_pow_left₀ (norm_nonneg (H₂ z)) hH2u 2
    have hmul := mul_le_mul_of_nonneg_right hsq (norm_nonneg (H₂ z))
    simpa [pow_succ, pow_two, mul_assoc] using! hmul
  have hH4sq : ‖H₄ z‖ ^ 2 ≤ CH4 ^ 2 := by
    simpa using! pow_le_pow_left₀ (norm_nonneg (H₄ z)) hH4u 2
  have hterm1 : ‖a‖ ≤ (7 * CH4 ^ 2) * ‖H₂ z‖ := by
    calc
      ‖a‖ = 7 * ‖H₂ z‖ * ‖H₄ z‖ ^ 2 := by simp [a, mul_assoc, norm_pow]
      _ ≤ 7 * ‖H₂ z‖ * (CH4 ^ 2) :=
        mul_le_mul_of_nonneg_left hH4sq (by positivity)
      _ = (7 * CH4 ^ 2) * ‖H₂ z‖ := by ring
  have hterm2 : ‖b‖ ≤ (7 * B2 * CH4) * ‖H₂ z‖ := by
    calc
      ‖b‖ = 7 * (‖H₂ z‖ ^ 2) * ‖H₄ z‖ := by simp [b, mul_assoc, norm_pow]
      _ ≤ 7 * ((B2 * ‖H₂ z‖) * CH4) := by
        have h' : (‖H₂ z‖ ^ 2) * ‖H₄ z‖ ≤ (B2 * ‖H₂ z‖) * CH4 :=
          mul_le_mul hH2sq hH4u (norm_nonneg _) (mul_nonneg hB2 (norm_nonneg _))
        linarith
      _ = (7 * B2 * CH4) * ‖H₂ z‖ := by ring
  have hterm3 : ‖c‖ ≤ (2 * B2 ^ 2) * ‖H₂ z‖ := by
    have : ‖c‖ = 2 * ‖H₂ z‖ ^ 3 := by simp [c, norm_pow]
    linarith
  linarith

private theorem exists_bound_norm_ψS_resToImagAxis_exp_Ici_one_aux
    (CH2 B2 CH4 cH3 cH4 : ℝ)
    (hH2 : ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ CH2 * Real.exp (-Real.pi * t))
    (hB2 : ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ B2)
    (hH4u : ∀ t : ℝ, 1 ≤ t → ‖H₄.resToImagAxis t‖ ≤ CH4)
    (hH3l : ∀ t : ℝ, 1 ≤ t → cH3 ≤ ‖H₃.resToImagAxis t‖)
    (hH4l : ∀ t : ℝ, 1 ≤ t → cH4 ≤ ‖H₄.resToImagAxis t‖)
    (hcH3 : 0 < cH3) (hcH4 : 0 < cH4) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * Real.exp (-Real.pi * t) := by
  have hCH4_nonneg : 0 ≤ CH4 := (norm_nonneg _).trans (hH4u 1 le_rfl)
  have hB2_nonneg : 0 ≤ B2 := (norm_nonneg _).trans (hB2 1 le_rfl)
  let A : ℝ := 7 * CH4 ^ 2 + 7 * B2 * CH4 + 2 * B2 ^ 2
  have hA_nonneg : 0 ≤ A := by
    have h1 : 0 ≤ 7 * CH4 ^ 2 := by positivity
    have h2 : 0 ≤ 7 * B2 * CH4 := by
      have : 0 ≤ 7 * B2 := by positivity
      exact mul_nonneg this hCH4_nonneg
    have h3 : 0 ≤ 2 * B2 ^ 2 := by positivity
    dsimp [A]
    exact add_nonneg (add_nonneg h1 h2) h3
  let D : ℝ := ((cH3 ^ 4) * (cH4 ^ 4))⁻¹
  let CψS : ℝ := (65536 : ℝ) * (A * CH2) * D
  refine ⟨CψS, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  let z : ℍ := ⟨Complex.I * t, by simpa using! ht0⟩
  have hψ : ψS.resToImagAxis t = ψS z := by
    simp [Function.resToImagAxis, ResToImagAxis, ht0, z]
  have hfac : ψS z =
      -((256 : ℂ) ^ (2 : ℕ)) *
        (7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3) /
          ((H₃ z) ^ 4 * (H₄ z) ^ 4) :=
    PsiRewrites.ψS_apply_eq_factor z
  have hH2t : ‖H₂ z‖ ≤ CH2 * Real.exp (-Real.pi * t) := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0, z] using! (hH2 t ht)
  have hH2u : ‖H₂ z‖ ≤ B2 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0, z] using! (hB2 t ht)
  have hH4u' : ‖H₄ z‖ ≤ CH4 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0, z] using! (hH4u t ht)
  have hH3l' : cH3 ≤ ‖H₃ z‖ := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0, z] using! (hH3l t ht)
  have hH4l' : cH4 ≤ ‖H₄ z‖ := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0, z] using! (hH4l t ht)
  have hden_pos : 0 < (cH3 ^ 4) * (cH4 ^ 4) :=
    mul_pos (pow_pos hcH3 4) (pow_pos hcH4 4)
  have hden_le :
      (cH3 ^ 4) * (cH4 ^ 4) ≤ ‖(H₃ z) ^ 4 * (H₄ z) ^ 4‖ := by
    have h3 : cH3 ^ 4 ≤ ‖(H₃ z) ^ 4‖ := by
      simpa [norm_pow] using! (pow_le_pow_left₀ hcH3.le hH3l' 4)
    have h4 : cH4 ^ 4 ≤ ‖(H₄ z) ^ 4‖ := by
      simpa [norm_pow] using! (pow_le_pow_left₀ hcH4.le hH4l' 4)
    calc
      (cH3 ^ 4) * (cH4 ^ 4) ≤ ‖(H₃ z) ^ 4‖ * ‖(H₄ z) ^ 4‖ :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = ‖(H₃ z) ^ 4 * (H₄ z) ^ 4‖ := by simp
  have hden_inv :
      ‖(H₃ z) ^ 4 * (H₄ z) ^ 4‖⁻¹ ≤ D := by
    have h := one_div_le_one_div_of_le hden_pos hden_le
    simpa [D, one_div] using! h
  have hnum :
      ‖7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3‖
        ≤ (7 * CH4 ^ 2 + 7 * B2 * CH4 + 2 * B2 ^ 2) * ‖H₂ z‖ := by
    simpa using! psiS_numerator_bound (z := z) (B2 := B2) (CH4 := CH4) hH2u hH4u'
  have hconst : ‖(-((256 : ℂ) ^ (2 : ℕ)) : ℂ)‖ = (65536 : ℝ) := by norm_num
  have hcoef_nonneg : 0 ≤ (65536 : ℝ) * (A * ‖H₂ z‖) := by
    have : (0 : ℝ) ≤ 65536 := by norm_num
    exact mul_nonneg this (mul_nonneg hA_nonneg (norm_nonneg _))
  have hconstnum :
      ‖-((256 : ℂ) ^ (2 : ℕ))‖ *
          ‖7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3‖
        ≤ (65536 : ℝ) * (A * ‖H₂ z‖) := by
    rw [hconst]
    exact mul_le_mul_of_nonneg_left (by simpa [A] using! hnum) (by positivity)
  have hψnorm :
      ‖ψS.resToImagAxis t‖ ≤ (65536 : ℝ) * (A * ‖H₂ z‖) * D := by
    calc
      ‖ψS.resToImagAxis t‖ = ‖ψS z‖ := by
        exact enorm_eq_iff_norm_eq.mp (congrArg enorm hψ)
      _ = ‖-((256 : ℂ) ^ (2 : ℕ)) *
            (7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3) /
              ((H₃ z) ^ 4 * (H₄ z) ^ 4)‖ := by simp [hfac]
      _ = ‖-((256 : ℂ) ^ (2 : ℕ))‖ *
            ‖7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3‖ *
              ‖(H₃ z) ^ 4 * (H₄ z) ^ 4‖⁻¹ := by
            simp [div_eq_mul_inv, mul_assoc]
      _ ≤ (65536 : ℝ) * (A * ‖H₂ z‖) * D := by
        have h1 :
            (‖-((256 : ℂ) ^ (2 : ℕ))‖ *
                  ‖7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3‖) *
                ‖(H₃ z) ^ 4 * (H₄ z) ^ 4‖⁻¹
              ≤ ((65536 : ℝ) * (A * ‖H₂ z‖)) * ‖(H₃ z) ^ 4 * (H₄ z) ^ 4‖⁻¹ :=
          mul_le_mul_of_nonneg_right hconstnum (inv_nonneg.2 (norm_nonneg _))
        exact le_mul_of_le_mul_of_nonneg_left h1 hden_inv hcoef_nonneg
  have hden_nonneg : 0 ≤ D := by
    simpa [D] using! inv_nonneg.2 (le_of_lt hden_pos)
  have hA_mul : A * ‖H₂ z‖ ≤ A * (CH2 * Real.exp (-Real.pi * t)) :=
    mul_le_mul_of_nonneg_left hH2t hA_nonneg
  have hA_mul' :
      (A * ‖H₂ z‖) * D ≤ (A * (CH2 * Real.exp (-Real.pi * t))) * D :=
    mul_le_mul_of_nonneg_right hA_mul hden_nonneg
  have h65536 : (0 : ℝ) ≤ 65536 := by norm_num
  have hA_mul'' :
      (65536 : ℝ) * ((A * ‖H₂ z‖) * D) ≤
        (65536 : ℝ) * ((A * (CH2 * Real.exp (-Real.pi * t))) * D) :=
    mul_le_mul_of_nonneg_left hA_mul' h65536
  calc
    ‖ψS.resToImagAxis t‖ ≤ (65536 : ℝ) * (A * ‖H₂ z‖) * D := hψnorm
    _ ≤ (65536 : ℝ) * (A * (CH2 * Real.exp (-Real.pi * t))) * D := by
      simpa [D, mul_assoc, mul_left_comm, mul_comm] using! hA_mul''
    _ = CψS * Real.exp (-Real.pi * t) := by
      dsimp [CψS]
      simp [mul_assoc, mul_left_comm, mul_comm]

/--
Exponential decay bound for `ψS` on the imaginary axis: there is `C` with
`‖ψS.resToImagAxis t‖ ≤ C * exp(-π t)` for `t ≥ 1`.
-/
public theorem exists_bound_norm_ψS_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * Real.exp (-Real.pi * t) := by
  rcases exists_bound_norm_H₂_resToImagAxis_exp_Ici_one with ⟨CH2, hH2⟩
  have hCH2_nonneg : 0 ≤ CH2 := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖H₂.resToImagAxis 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := CH2) (norm_nonneg _) (by positivity) ?_
    simpa using! (hH2 1 (le_rfl : (1 : ℝ) ≤ 1))
  rcases exists_bounds_norm_resToImagAxis_Ici_one (F := H₃) (hF0 := H₃_ne_zero) mdifferentiable_H₃
      H₃_tendsto_atImInfty with ⟨CH3, cH3, hcH3, hH3u, hH3l⟩
  rcases exists_bounds_norm_resToImagAxis_Ici_one (F := H₄) (hF0 := H₄_ne_zero) mdifferentiable_H₄
      H₄_tendsto_atImInfty with ⟨CH4, cH4, hcH4, hH4u, hH4l⟩
  have hCH4_nonneg : 0 ≤ CH4 := by
    exact (norm_nonneg _).trans (hH4u 1 (le_rfl : (1 : ℝ) ≤ 1))
  let B2 : ℝ := CH2 * Real.exp (-Real.pi)
  have hB2_nonneg : 0 ≤ B2 := by
    dsimp [B2]
    exact mul_nonneg hCH2_nonneg (Real.exp_nonneg _)
  let A : ℝ := 7 * CH4 ^ 2 + 7 * B2 * CH4 + 2 * B2 ^ 2
  have hA_nonneg : 0 ≤ A := by
    have h1 : 0 ≤ 7 * CH4 ^ 2 := by positivity
    have h2 : 0 ≤ 7 * B2 * CH4 := by
      have : 0 ≤ 7 * B2 := by positivity
      exact mul_nonneg this hCH4_nonneg
    have h3 : 0 ≤ 2 * B2 ^ 2 := by positivity
    dsimp [A]
    exact add_nonneg (add_nonneg h1 h2) h3
  have hB2 : ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ B2 := by
    intro t ht
    have h := hH2 t ht
    have hexp : Real.exp (-Real.pi * t) ≤ Real.exp (-Real.pi : ℝ) := by
      have : (-Real.pi * t) ≤ (-Real.pi : ℝ) := by nlinarith [Real.pi_pos, ht]
      exact Real.exp_le_exp.2 this
    simpa [B2, mul_assoc] using! h.trans (mul_le_mul_of_nonneg_left hexp hCH2_nonneg)
  exact
    exists_bound_norm_ψS_resToImagAxis_exp_Ici_one_aux CH2 B2 CH4 cH3 cH4
      hH2 hB2 hH4u hH3l hH4l hcH3 hcH4

/-- A uniform bound on `‖ψS.resToImagAxis t‖` for `t ≥ 1`. -/
public theorem exists_bound_norm_ψS_resToImagAxis_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C := by
  rcases exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := C) (norm_nonneg _) (by positivity) ?_
    simpa using! (hC 1 (le_rfl : (1 : ℝ) ≤ 1))
  refine ⟨C, ?_⟩
  intro t ht
  have h := hC t ht
  have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
  have hexp_le : Real.exp (-Real.pi * t) ≤ 1 := by
    have : (-Real.pi * t : ℝ) ≤ 0 := by nlinarith [Real.pi_pos, ht0]
    simpa using! (Real.exp_le_one_iff.2 this)
  nlinarith

end SpherePacking.Dim24.PsiExpBounds

end
