import E8Leech.TransferAssembly

/-!
# Transfer scales for every exponent below `1/12`

The density exponent is the larger of the existing `25/78` and the manuscript's
`(1 + 12 * γ) / 6`. This retains the existing periodic diameter and probability
constants even when `γ` is small. Its quarter is strictly larger than `γ`, and
it remains strictly below `1/3`. All thresholds precede the process law.
-/

noncomputable section
namespace E8Leech

open Filter

def generalDensityExponent (γ : ℝ) : ℝ :=
  max (25 / 78) ((1 + 12 * γ) / 6)

theorem generalDensityExponent_bounds {γ : ℝ} (hγ : γ < 1 / 12) :
    (25 / 78 : ℝ) ≤ generalDensityExponent γ ∧
      generalDensityExponent γ < 1 / 3 ∧ γ < generalDensityExponent γ / 4 := by
  refine ⟨le_max_left _ _, max_lt (by norm_num) (by linarith), ?_⟩
  have h := le_max_right (25 / 78 : ℝ) ((1 + 12 * γ) / 6)
  change γ < max (25 / 78 : ℝ) ((1 + 12 * γ) / 6) / 4
  linarith

/-- The existing logarithmic-radius bounds absorb any fixed exponential coefficient. -/
theorem general_brr_position_error_exp_neg {p γ c u : ℝ}
    (_hp : 0 < p) (hmargin : γ < p / 4) (hc : 0 ≤ c) (hu : 1 < u)
    (hlog : 2 * p * c / (p / 4 - γ) ≤ Real.log u)
    (hupper : observationRadius ((Real.exp (-u)) ^ p) ≤
      2 * p * observationRadius (Real.exp (-u))) :
    Real.exp (c * observationRadius ((Real.exp (-u)) ^ p)) *
      ((Real.exp (-u)) ^ p) ^ (1 / 4 : ℝ) ≤ (Real.exp (-u)) ^ γ := by
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hm : 0 < p / 4 - γ := by linarith
  have hlog' := (div_le_iff₀ hm).mp hlog
  have he : c * observationRadius ((Real.exp (-u)) ^ p) ≤ (p / 4 - γ) * u := by
    apply (mul_le_mul_of_nonneg_left hupper hc).trans
    rw [observationRadius_exp_neg]
    have heq : c * (2 * p * (u / Real.log u)) = (2 * p * c * u) / Real.log u := by ring
    rw [heq]
    apply (div_le_iff₀ hlu).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog') (by linarith : 0 ≤ u)]
  rw [← Real.rpow_mul (Real.exp_pos _).le]
  simp only [exp_neg_rpow] at he ⊢
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

theorem eventually_general_brr_scale_parameters (p γ c η₀ : ℝ)
    (hpmin : (25 / 78 : ℝ) ≤ p) (hpmax : p < 1 / 3)
    (hmargin : γ < p / 4) (hc : 0 ≤ c) (hη₀ : 0 < η₀) :
    ∀ᶠ u : ℝ in atTop,
      0 < (Real.exp (-u)) ^ p ∧ (Real.exp (-u)) ^ p < η₀ ∧
      0 < observationRadius ((Real.exp (-u)) ^ p) ∧
      (25 / 156 : ℝ) * observationRadius (Real.exp (-u)) ≤
        observationRadius ((Real.exp (-u)) ^ p) ∧
      observationRadius ((Real.exp (-u)) ^ p) ≤
        (2 / 3 : ℝ) * observationRadius (Real.exp (-u)) ∧
      Real.exp (c * observationRadius ((Real.exp (-u)) ^ p)) *
        ((Real.exp (-u)) ^ p) ^ (1 / 4 : ℝ) ≤ (Real.exp (-u)) ^ γ := by
  have hp : 0 < p := by linarith
  filter_upwards [eventually_scaled_observationRadius_bounds p 1 hp (by linarith) le_rfl,
    eventually_scaled_excess_small p 1 η₀ hp zero_lt_one hη₀,
    eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop (Real.exp (2 * p * c / (p / 4 - γ)))] with u hw hη hu hcu
  simp only [one_mul] at hw hη
  have hu1 : 1 < u := lt_of_lt_of_le (by simp : 1 < Real.exp 1) hu
  have hR := (observationRadius_exp_neg_pos hu1).le
  have hlo : (25 / 156 : ℝ) * observationRadius (Real.exp (-u)) ≤
      observationRadius ((Real.exp (-u)) ^ p) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ p / 2 - 25 / 156) hR, hw.2.1]
  have hhi : observationRadius ((Real.exp (-u)) ^ p) ≤
      (2 / 3 : ℝ) * observationRadius (Real.exp (-u)) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 / 3 - 2 * p) hR, hw.2.2]
  have hlog : 2 * p * c / (p / 4 - γ) ≤ Real.log u := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hcu
  exact ⟨hη.1, hη.2, hw.1, hlo, hhi,
    general_brr_position_error_exp_neg hp hmargin hc hu1 hlog hw.2.2⟩

theorem exists_small_general_brr_scale_parameters (p γ c η₀ : ℝ)
    (hpmin : (25 / 78 : ℝ) ≤ p) (hpmax : p < 1 / 3)
    (hmargin : γ < p / 4) (hc : 0 ≤ c) (hη₀ : 0 < η₀) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        0 < δ ^ p ∧ δ ^ p < η₀ ∧ 0 < observationRadius (δ ^ p) ∧
        (25 / 156 : ℝ) * observationRadius δ ≤ observationRadius (δ ^ p) ∧
        observationRadius (δ ^ p) ≤ (2 / 3 : ℝ) * observationRadius δ ∧
        Real.exp (c * observationRadius (δ ^ p)) * (δ ^ p) ^ (1 / 4 : ℝ) ≤ δ ^ γ := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_general_brr_scale_parameters p γ c η₀ hpmin hpmax hmargin hc hη₀)
  let U := max M (Real.exp 1 + 1)
  have hEU : Real.exp 1 < U := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  refine ⟨Real.exp (-U), Real.exp_pos _, Real.exp_lt_exp.mpr (by linarith), ?_⟩
  intro δ hδ hsmall
  have hlog : Real.log δ < -U := by
    simpa only [Real.log_exp] using Real.log_lt_log hδ hsmall
  have h := hM (-Real.log δ) (by linarith [le_max_left M (Real.exp 1 + 1)])
  simpa only [neg_neg, Real.exp_log hδ] using h

structure GeneralTransferScaleData (d : ℕ) (A E B c η₀ γ δ : ℝ) : Prop where
  cutoff_pos : 0 < δ ^ (1 / 3 : ℝ)
  cutoff_half : δ ^ (1 / 3 : ℝ) ≤ 1 / 2
  radius_pos : 0 < observationRadius δ
  eta_pos : 0 < δ ^ generalDensityExponent γ
  eta_small : δ ^ generalDensityExponent γ < η₀
  eta_radius_pos : 0 < observationRadius (δ ^ generalDensityExponent γ)
  contains : observationRadius (δ ^ generalDensityExponent γ) ≤
    (1 - δ ^ (1 / 3 : ℝ))⁻¹ * observationRadius δ
  diameter : 2 * ((1 - δ ^ (1 / 3 : ℝ))⁻¹ * observationRadius δ) ≤
    (624 / 25 : ℝ) * observationRadius (δ ^ generalDensityExponent γ)
  error : 2 * (E * Real.exp (c * observationRadius (δ ^ generalDensityExponent γ)) *
    (δ ^ generalDensityExponent γ) ^ (1 / 4 : ℝ)) +
    4 * δ ^ (1 / 3 : ℝ) * observationRadius δ ≤ transferConstant E B * δ ^ γ
  stability : B * observationRadius (δ ^ generalDensityExponent γ) ^ (-1 / 2 : ℝ) ≤
    7 * B * observationRadius δ ^ (-1 / 2 : ℝ)
  loss : B * observationRadius (δ ^ generalDensityExponent γ) ^ (-1 / 2 : ℝ) ≤
    transferConstant E B * observationRadius δ ^ (-1 / 2 : ℝ)
  markov : ((A + (d : ℝ) + 1) * δ ^ (1 / 3 : ℝ)) /
    δ ^ generalDensityExponent γ ≤ observationRadius δ ^ (-1 / 2 : ℝ)
  deletion : ENNReal.ofReal (A * δ ^ (1 / 3 : ℝ)) *
    MeasureTheory.volume (Metric.closedBall (0 : Ambient d) (observationRadius δ)) ≤
    ENNReal.ofReal (observationRadius δ ^ (-1 / 2 : ℝ))

theorem exists_uniform_general_transfer_parameters (d : ℕ) (A E B c η₀ γ : ℝ)
    (hγ : γ < 1 / 12) (hA : 0 ≤ A) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hη₀ : 0 < η₀) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → GeneralTransferScaleData d A E B c η₀ γ δ := by
  have hp := generalDensityExponent_bounds hγ
  obtain ⟨δ₁, h₁, hs₁, hb⟩ := exists_small_general_brr_scale_parameters
    (generalDensityExponent γ) γ c η₀ hp.1 hp.2.1 hp.2.2 hc hη₀
  obtain ⟨δ₂, h₂, _hs₂, hr⟩ := exists_small_scale_error_bound
    (1 / 3) γ (1 / 4) (by linarith) (by norm_num)
  obtain ⟨δ₃, h₃, _hs₃, hm⟩ := exists_small_window_probability_bound
    (A + (d : ℝ) + 1) 0 (1 / 3 - generalDensityExponent γ) 1
    (by positivity) (by norm_num) (by linarith [hp.2.1]) zero_lt_one
  obtain ⟨δ₄, h₄, _hs₄, hd⟩ := exists_small_deleted_volume_probability_bound d A 1
    hA zero_lt_one
  let δ₀ := min (min δ₁ δ₂) (min (min δ₃ δ₄) (1 / 8))
  have hle1 : δ₀ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hle2 : δ₀ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hle3 : δ₀ ≤ δ₃ := (min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_left _ _))
  have hle4 : δ₀ ≤ δ₄ := (min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_right _ _))
  have hle8 : δ₀ ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ₀, lt_min (lt_min h₁ h₂) (lt_min (lt_min h₃ h₄) (by norm_num)),
    hle1.trans_lt hs₁, ?_⟩
  intro δ hδ hsmall
  have hb' := hb δ hδ (hsmall.trans_le hle1)
  have hr' := hr δ hδ (hsmall.trans_le hle2)
  have hm' := hm δ hδ (hsmall.trans_le hle3)
  simp only [Real.rpow_zero, mul_one, one_mul] at hm'
  have hR := observationRadius_pos hδ (hsmall.trans_le (hle1.trans hs₁.le))
  have ht0 := (Real.rpow_pos_of_pos hδ (1 / 3 : ℝ))
  have ht := one_third_cutoff_le_half hδ.le (hsmall.le.trans hle8)
  have ha := inverse_contraction_bounds ht0.le ht
  have hprob := mul_le_mul_of_nonneg_left (brr_probability_radius_le hR hb'.2.2.2.1) hB
  have hprob' : B * observationRadius (δ ^ generalDensityExponent γ) ^ (-1 / 2 : ℝ) ≤
      7 * B * observationRadius δ ^ (-1 / 2 : ℝ) := by nlinarith [hprob]
  refine ⟨ht0, ht, hR, hb'.1, hb'.2.1, hb'.2.2.1, ?_, ?_, ?_, hprob', ?_, ?_, ?_⟩
  · nlinarith [hb'.2.2.2.2.1,
      mul_nonneg (sub_nonneg.mpr ha.1) hR.le]
  · nlinarith [hb'.2.2.2.1,
      mul_nonneg (sub_nonneg.mpr ha.2) hR.le]
  · have he := mul_le_mul_of_nonneg_left hb'.2.2.2.2.2 hE
    have hpδ := (Real.rpow_pos_of_pos hδ γ).le
    dsimp [transferConstant]
    nlinarith [mul_nonneg hB hpδ]
  · dsimp [transferConstant]
    nlinarith [Real.rpow_nonneg hR.le (-1 / 2 : ℝ)]
  · rw [Real.rpow_sub hδ] at hm'
    simpa only [mul_div_assoc] using hm'
  · simpa only [one_mul] using hd δ hδ (hsmall.trans_le hle4)

end E8Leech
