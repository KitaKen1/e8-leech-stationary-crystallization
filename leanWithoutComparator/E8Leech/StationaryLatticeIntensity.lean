import E8Leech.AffineLatticeCountBound
import E8Leech.ConfigurationCountRigidity

/-!
# Intensity one for a stationary containing-lattice process

Only a uniform upper lattice count is needed: containment of an intensity-one
process gives the lower intensity bound, and growing balls give the upper one.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal

theorem intensity_le_one_of_enlarged_ball_bound {d : ℕ} (C : ℝ) (hC : 0 ≤ C)
    {ρ : ℝ≥0∞}
    (hball : ∀ R : ℝ, ρ * volume (closedBall (0 : Ambient d) R) ≤
      volume (closedBall (0 : Ambient d) (R + C))) : ρ ≤ 1 := by
  have hv0 : volume (closedBall (0 : Ambient d) 1) ≠ 0 :=
    (measure_closedBall_pos volume 0 (by norm_num)).ne'
  have hρtop : ρ ≠ ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_left
      (ne_top_of_le_ne_top (measure_closedBall_lt_top (μ := volume)).ne (hball 1)) hv0).ne
  have hω : 0 < volume.real (closedBall (0 : Ambient d) 1) :=
    ENNReal.toReal_pos hv0 (measure_closedBall_lt_top (μ := volume)).ne
  have hd : Module.finrank ℝ (Ambient d) = d := by simp [Ambient]
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => (1 + C * (n : ℝ)⁻¹) ^ d) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      (hi.const_mul C)).pow d
  have hr : ρ.toReal ≤ 1 := by
    apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hRn : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
    have hh := ENNReal.toReal_mono (measure_closedBall_lt_top (μ := volume)).ne (hball n)
    rw [ENNReal.toReal_mul] at hh
    change ρ.toReal * volume.real (closedBall (0 : Ambient d) (n : ℝ)) ≤
      volume.real (closedBall (0 : Ambient d) ((n : ℝ) + C)) at hh
    rw [Measure.addHaar_real_closedBall' volume 0 (r := (n : ℝ)) hRn.le,
      Measure.addHaar_real_closedBall' volume 0 (r := (n : ℝ) + C) (by linarith), hd] at hh
    have he : (1 + C * (n : ℝ)⁻¹) ^ d * (n : ℝ) ^ d = ((n : ℝ) + C) ^ d := by
      rw [← mul_pow]
      congr 1
      field_simp
    have hb : ρ.toReal * ((n : ℝ) ^ d * volume.real (closedBall (0 : Ambient d) 1)) ≤
        (1 + C * (n : ℝ)⁻¹) ^ d *
          ((n : ℝ) ^ d * volume.real (closedBall (0 : Ambient d) 1)) := by
      calc
        _ ≤ ((n : ℝ) + C) ^ d * volume.real (closedBall (0 : Ambient d) 1) := hh
        _ = _ := by rw [← he, mul_assoc]
    exact le_of_mul_le_mul_right hb (mul_pos (pow_pos hRn d) hω)
  exact (ENNReal.toReal_le_toReal hρtop (by simp)).mp (by simpa using hr)

theorem hasIntensity_one_of_stationary_affine_lattice_container {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hρ : HasIntensity μ 1)
    (F : Configuration (Ambient d) → Configuration (Ambient d)) (hF : Measurable F)
    (hstat : IsStationary (μ.map F))
    (hgood : ∀ᵐ c ∂μ, c.support ⊆ (F c).support ∧
      ∃ Φ : Ambient d ≃ᵢ Ambient d, (F c).support ⊆ Φ '' (Λ : Set (Ambient d))) :
    HasIntensity (μ.map F) 1 := by
  let ν := μ.map F
  let C := ∑ i, ‖b i‖
  have hupper (R : ℝ) : (∫⁻ c, (F c).count (closedBall 0 R) ∂μ) ≤
      volume (closedBall (0 : Ambient d) (R + C)) := by
    calc
      _ ≤ ∫⁻ _c, volume (closedBall (0 : Ambient d) (R + C)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hgood] with c hc
        obtain ⟨Φ, hΦ⟩ := hc.2
        exact count_closedBall_le_of_affine_lattice_containment b Λ hle hcov (F c) Φ hΦ R
      _ = _ := by simp
  have hfinite : IsFiniteMeasureOnCompacts (meanCountingMeasure ν) := by
    refine ⟨fun K hK => ?_⟩
    obtain ⟨R, hr⟩ := hK.isBounded.subset_closedBall (0 : Ambient d)
    calc
      meanCountingMeasure ν K ≤ meanCountingMeasure ν (closedBall 0 R) := measure_mono hr
      _ = ∫⁻ c, (F c).count (closedBall 0 R) ∂μ := by
        rw [meanCountingMeasure_apply _ measurableSet_closedBall,
          lintegral_map (Configuration.measurable_count measurableSet_closedBall) hF]
      _ ≤ volume (closedBall (0 : Ambient d) (R + C)) := hupper R
      _ < ∞ := measure_closedBall_lt_top
  let := hfinite
  have hν := hasIntensity_of_stationary ν hstat
  have hball (R : ℝ) : processIntensity ν * volume (closedBall (0 : Ambient d) R) ≤
      volume (closedBall (0 : Ambient d) (R + C)) := by
    rw [← hν _ measurableSet_closedBall,
      lintegral_map (Configuration.measurable_count measurableSet_closedBall) hF]
    exact hupper R
  have hleone := intensity_le_one_of_enlarged_ball_bound C
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) hball
  have honele : 1 ≤ processIntensity ν := by
    rw [processIntensity, lintegral_map (Configuration.measurable_count (measurable_unitWindow d)) hF]
    calc
      1 = ∫⁻ c, c.count (unitWindow d) ∂μ := (expected_count_unitWindow μ 1 hρ).symm
      _ ≤ ∫⁻ c, (F c).count (unitWindow d) ∂μ :=
        lintegral_mono_ae (hgood.mono fun c hc => Configuration.count_mono_support hc.1 _)
  have he : processIntensity ν = 1 := le_antisymm hleone honele
  rwa [he] at hν

end E8Leech
