import E8Leech.JointTranslation

/-!
# Stationary averaging with a configuration-dependent invariant density

The averaging window may depend measurably on a translation-invariant feature
of the configuration. Tonelli and stationarity still preserve every measurable
nonnegative observable, without conditional measures or a countable label.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

theorem stationary_lintegral_invariant_density_average {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (w : Configuration (Ambient d) × Ambient d → ℝ≥0∞) (hw : Measurable w)
    (hinv : ∀ a c, w (translate a c, a) = w (c, a))
    (hnorm : ∀ᵐ c ∂μ, (∫⁻ a, w (c, a)) = 1)
    (F : Configuration (Ambient d) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ c, (∫⁻ a, w (c, a) * F (translate a c) ∂volume) ∂μ) = ∫⁻ c, F c ∂μ := by
  have hprod : Measurable (fun p : Configuration (Ambient d) × Ambient d =>
      w p * F (translate p.2 p.1)) := hw.mul (hF.comp measurable_translate_joint)
  have hfix (a : Ambient d) :
      (∫⁻ c, w (c, a) * F (translate a c) ∂μ) = ∫⁻ c, w (c, a) * F c ∂μ := by
    have hG : Measurable (fun c => w (c, a) * F c) :=
      (hw.comp (measurable_id.prodMk measurable_const)).mul hF
    calc
      _ = ∫⁻ c, w (translate a c, a) * F (translate a c) ∂μ :=
        lintegral_congr fun c => by rw [hinv]
      _ = _ := (hμ a).lintegral_comp hG
  have hprod0 : Measurable (fun p : Configuration (Ambient d) × Ambient d =>
      w p * F p.1) := hw.mul (hF.comp measurable_fst)
  calc
    _ = ∫⁻ a, (∫⁻ c, w (c, a) * F (translate a c) ∂μ) ∂volume :=
      lintegral_lintegral_swap (f := fun c a => w (c, a) * F (translate a c)) hprod.aemeasurable
    _ = ∫⁻ a, (∫⁻ c, w (c, a) * F c ∂μ) ∂volume := lintegral_congr hfix
    _ = ∫⁻ c, (∫⁻ a, w (c, a) * F c ∂volume) ∂μ :=
      (lintegral_lintegral_swap (f := fun c a => w (c, a) * F c) hprod0.aemeasurable).symm
    _ = ∫⁻ c, (∫⁻ a, w (c, a)) * F c ∂μ := by
      apply lintegral_congr
      intro c
      have hrow : Measurable (fun a => w (c, a)) :=
        hw.comp (measurable_const.prodMk measurable_id)
      exact lintegral_mul_const (F c) hrow
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hnorm] with c hc
      rw [hc, one_mul]

end E8Leech
