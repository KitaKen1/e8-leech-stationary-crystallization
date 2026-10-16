import E8Leech.PotentialCrystallization
import E8Leech.WindowScales
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Almost-sure local crystallization at zero excess

Select a sufficiently fast sequence of scales so that the failure bounds
are geometric, the observation radii exceed n, and the errors are at most
1/(n+1). Borel-Cantelli is applied to the measurable good subevents of the
quantitative theorem. No measurability of the full existential success
event is assumed. The density lower bounds are retained for later uniqueness.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Filter Topology
open scoped ENNReal

theorem observationRadius_exp_neg_tendsto_atTop :
    Tendsto (fun u : ℝ => observationRadius (Real.exp (-u))) atTop atTop := by
  have hr : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hrpos : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hr, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    exact div_pos (Real.log_pos hu) (by linarith only [hu])
  have ht := hrpos.inv_tendsto_nhdsGT_zero
  change Tendsto (fun u : ℝ => (Real.log u / u)⁻¹) atTop atTop at ht
  simpa only [inv_div, observationRadius_exp_neg] using ht

/-- Convert the quantitative good-event lower bound to an upper bound on its complement. -/
theorem probability_compl_le_of_ofReal_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {G : Set Ω} (hG : MeasurableSet G)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hprob : ENNReal.ofReal (1 - a) ≤ μ G) : μ Gᶜ ≤ ENNReal.ofReal a := by
  apply (ENNReal.add_le_add_iff_left (measure_ne_top μ G)).mp
  rw [prob_add_prob_compl hG]
  calc
    (1 : ℝ≥0∞) = ENNReal.ofReal (1 - a) + ENNReal.ofReal a := by
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr ha1) ha]
      simp
    _ ≤ μ G + ENNReal.ofReal a := add_le_add hprob le_rfl

/-- One measurable probability-one event with eventual local crystallization along growing
windows, vanishing errors and vanishing density losses. -/
theorem zero_excess_localCrystal_sequence {d : ℕ} {Λ : Set (Ambient d)}
    {P : Ambient d → Ambient d → ℝ≥0∞} (htarget : PotentialCrystallizationTarget Λ P)
    (hbase : latticePotentialEnergy Λ P ≠ ∞)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy P μ = latticePotentialEnergy Λ P) :
    ∃ R ε loss : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto loss atTop (𝓝 0) ∧
      ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧ μ H = 1 ∧
        ∀ c ∈ H, ∀ᶠ n in atTop, LocalCrystal Λ c (R n) (ε n) (loss n) := by
  obtain ⟨C, hC, δ₀, hδ₀, hcritical, htarget⟩ := htarget
  have hδ : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have he₀ := ((Real.continuousAt_rpow_const (0 : ℝ) (1 / 13 : ℝ)
    (Or.inr (by norm_num))).tendsto.comp hδ).const_mul C
  have he : Tendsto (fun u : ℝ => C * Real.exp (-u) ^ (1 / 13 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow (by norm_num : (1 / 13 : ℝ) ≠ 0), mul_zero] using he₀
  have hl : Tendsto (fun u : ℝ => C * observationRadius (Real.exp (-u)) ^ (-1 / 2 : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        observationRadius_exp_neg_tendsto_atTop).const_mul C
  have hchoose : ∀ n : ℕ, ∃ u : ℝ, Real.exp (-u) < δ₀ ∧
      (n : ℝ) ≤ observationRadius (Real.exp (-u)) ∧
      C * Real.exp (-u) ^ (1 / 13 : ℝ) ≤ 1 / ((n : ℝ) + 1) ∧
      C * observationRadius (Real.exp (-u)) ^ (-1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    have hεn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hln : 0 < (1 / 2 : ℝ) ^ n := by positivity
    obtain ⟨u, huδ, huR, huε, hul⟩ :=
      ((hδ.eventually (eventually_lt_nhds hδ₀)).and
        ((observationRadius_exp_neg_tendsto_atTop.eventually (eventually_ge_atTop (n : ℝ))).and
          ((he.eventually (eventually_lt_nhds hεn)).and
            (hl.eventually (eventually_lt_nhds hln))))).exists
    exact ⟨u, huδ, huR, huε.le, hul.le⟩
  choose u huδ huR huε hul using hchoose
  let R : ℕ → ℝ := fun n => observationRadius (Real.exp (-u n))
  let ε : ℕ → ℝ := fun n => C * Real.exp (-u n) ^ (1 / 13 : ℝ)
  let loss : ℕ → ℝ := fun n => C * R n ^ (-1 / 2 : ℝ)
  have hR : Tendsto R atTop atTop := tendsto_atTop_mono huR tendsto_natCast_atTop_atTop
  have hεpos : ∀ n, 0 ≤ ε n := fun n =>
    mul_nonneg hC.le (Real.rpow_nonneg (Real.exp_pos _).le _)
  have hlpos : ∀ n, 0 ≤ loss n := fun n =>
    mul_nonneg hC.le (Real.rpow_nonneg
      (observationRadius_pos (Real.exp_pos _) ((huδ n).trans hcritical)).le _)
  have hε : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero hεpos huε tendsto_one_div_add_atTop_nhds_zero_nat
  have hloss : Tendsto loss atTop (𝓝 0) := squeeze_zero hlpos hul
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1))
  have hexcess : ∀ n, HasPotentialExcessAtMost P μ (latticePotentialEnergy Λ P)
      (ENNReal.ofReal (Real.exp (-u n))) := by
    intro n
    refine ⟨hbase, ?_⟩
    rw [henergy]
    exact le_self_add
  choose G hG hlocal hprob using fun n =>
    htarget μ inferInstance hμ hρ (Real.exp (-u n)) (Real.exp_pos _) (huδ n) (hexcess n)
  have hfail : ∀ n, μ (G n)ᶜ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro n
    apply probability_compl_le_of_ofReal_lower_bound μ (hG n) (by positivity)
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    exact (ENNReal.ofReal_le_ofReal (by linarith only [hul n])).trans (hprob n)
  have hsummable : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hfailfinite : ∑' n, μ (G n)ᶜ ≠ ∞ :=
    ne_top_of_le_ne_top hsummable.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hfail)
  have hae : ∀ᵐ c ∂μ, ∀ᶠ n in atTop, c ∈ G n := by
    simpa only [mem_compl_iff, not_not] using ae_eventually_notMem hfailfinite
  let H : Set (Configuration (Ambient d)) := liminf G atTop
  have hH : MeasurableSet H := MeasurableSet.measurableSet_liminf hG
  have hHae : H ∈ ae μ := by
    change ∀ᵐ c ∂μ, c ∈ H
    filter_upwards [hae] with c hc
    exact mem_liminf_iff_eventually_mem.mpr hc
  refine ⟨R, ε, loss, hR, hε, hloss, H, hH, (mem_ae_iff_prob_eq_one hH).mp hHae, ?_⟩
  intro c hc
  have hcG : ∀ᶠ n in atTop, c ∈ G n := mem_liminf_iff_eventually_mem.mp hc
  exact hcG.mono fun n hn => hlocal n hn

end E8Leech
