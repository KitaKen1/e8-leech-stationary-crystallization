import E8Leech.StationaryIntensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Equal intensities remove every point of a contained difference

Finite counts in an exhausting sequence of compact balls determine equality
when one support contains the other. Equal finite expected counts force those
counts to agree almost surely, without allowing density-zero missing points.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Metric
open scoped ENNReal

theorem Configuration.count_mono_support {d : ℕ} {c k : Configuration (Ambient d)}
    (h : c.support ⊆ k.support) (W : Set (Ambient d)) : c.count W ≤ k.count W :=
  measure_mono (inter_subset_inter_left W h)

theorem Configuration.eq_of_subset_of_closedBall_counts {d : ℕ}
    (c k : Configuration (Ambient d)) (hsub : c.support ⊆ k.support)
    (hcount : ∀ n : ℕ, c.count (closedBall 0 (n : ℝ)) = k.count (closedBall 0 (n : ℝ))) : c = k := by
  classical
  apply Configuration.ext
  apply Set.Subset.antisymm hsub
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (dist x 0)
  have hc := c.finite_on_compacts _ (isCompact_closedBall (0 : Ambient d) (n : ℝ))
  have hk := k.finite_on_compacts _ (isCompact_closedBall (0 : Ambient d) (n : ℝ))
  have hcard : hc.toFinset.card = hk.toFinset.card := by
    have he := hcount n
    rw [Configuration.count, Configuration.count, Measure.count_apply_finite _ hc,
      Measure.count_apply_finite _ hk] at he
    exact_mod_cast he
  have hfin : hc.toFinset = hk.toFinset := Finset.eq_of_subset_of_card_le
    (fun y hy => hc.mem_toFinset.mp hy |>.imp (fun h => hsub h) id |> hk.mem_toFinset.mpr)
    hcard.ge
  have hm : x ∈ hc.toFinset := hfin ▸ hk.mem_toFinset.mpr ⟨hx, hn.le⟩
  exact (hc.mem_toFinset.mp hm).1

theorem ae_eq_of_support_subset_of_equal_intensity {d : ℕ}
    (μ : Measure (Configuration (Ambient d)))
    (F : Configuration (Ambient d) → Configuration (Ambient d)) (hF : Measurable F)
    (hsub : ∀ᵐ c ∂μ, c.support ⊆ (F c).support)
    {ρ : ℝ≥0∞} (hρtop : ρ ≠ ∞) (hρ : HasIntensity μ ρ)
    (hρF : HasIntensity (μ.map F) ρ) : ∀ᵐ c ∂μ, c = F c := by
  have he : ∀ n : ℕ, ∀ᵐ c ∂μ,
      c.count (closedBall 0 (n : ℝ)) = (F c).count (closedBall 0 (n : ℝ)) := by
    intro n
    have hc := hρ (closedBall 0 (n : ℝ)) measurableSet_closedBall
    have hk := hρF (closedBall 0 (n : ℝ)) measurableSet_closedBall
    rw [lintegral_map (Configuration.measurable_count measurableSet_closedBall) hF] at hk
    exact ae_eq_of_ae_le_of_lintegral_le
      (hsub.mono fun c h => Configuration.count_mono_support h _)
      (hc ▸ ENNReal.mul_ne_top hρtop (measure_closedBall_lt_top (μ := volume)).ne)
      ((Configuration.measurable_count measurableSet_closedBall).comp hF).aemeasurable
      (hk.trans hc.symm).le
  filter_upwards [hsub, ae_all_iff.mpr he] with c hc he
  exact Configuration.eq_of_subset_of_closedBall_counts c (F c) hc he

theorem exists_measurable_probability_one_of_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {P : Ω → Prop} (hP : ∀ᵐ ω ∂μ, P ω) :
    ∃ H : Set Ω, MeasurableSet H ∧ μ H = 1 ∧ ∀ ω ∈ H, P ω := by
  obtain ⟨N, hsub, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  refine ⟨Nᶜ, hN.compl, ?_, fun ω hω => ?_⟩
  · rw [measure_compl hN (measure_ne_top μ N), measure_univ, hzero, tsub_zero]
  · exact not_not.mp fun h => hω (hsub h)

end E8Leech
