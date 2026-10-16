import E8Leech.CountableIsometries
import E8Leech.ConditionalCrystallization

/-!
# Joint Borel BRR events from separate deterministic centre estimates

A pointwise periodic input may provide a different exceptional centre set for
each configuration, without any measurable choice of these sets. The canonical
countable-isometry envelope is jointly measurable. Its low-deficit failures have
each centre section contained in a supplied exceptional set, so product Fubini
gives the original failure budget. The error coefficient changes from E to E+1.
Actual periodic density optimality and quantitative BRR geometry remain inputs.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

/-- Deterministic periodic stability with an exceptional centre set for each configuration.
No joint event or measurable choice of centre sets is a field of this input. -/
structure SectionwisePeriodicStabilityInput {d : ℕ} (Λ : Set (Ambient d))
    (r E B c η₀ : ℝ) : Prop where
  packing : ∀ (z : Configuration (Ambient d)) (L t : ℝ), r < L →
    ∀ ht : t < 1, guardDensity (expandAfterDeletion z r t ht) L r ≤ 1
  centres : ∀ (L t R η : ℝ) (hr : 0 < r) (hL : r < L) (ht : t < 1),
    0 ≤ R → r + 2 * R ≤ L → 0 < η → η < η₀ →
    0 < observationRadius η → observationRadius η ≤ R →
    2 * R ≤ (624 / 25 : ℝ) * observationRadius η →
    ∀ z : Configuration (Ambient d), expandedGuardDeficit z L r t ht < ENNReal.ofReal η →
      ∃ S : Set (Ambient d),
        (∀ u, u ∉ S → LocalCrystal Λ
          (translate (-u) (guardedExpandedConfiguration z L r t hr hL ht))
          R (E * Real.exp (c * observationRadius η) * η ^ (1 / 4 : ℝ))
          (B * observationRadius η ^ (-1 / 2 : ℝ))) ∧
        uniformPeriodCell d L S ≤ ENNReal.ofReal (B * observationRadius η ^ (-1 / 2 : ℝ))

theorem periodicStabilityInput_of_sectionwise {d : ℕ} {Λ : Set (Ambient d)}
    (hΛ : IsClosed Λ) (hne : Λ.Nonempty) (r E B c η₀ : ℝ)
    (hinput : SectionwisePeriodicStabilityInput Λ r E B c η₀) :
    PeriodicStabilityInput Λ r (E + 1) B c η₀ := by
  refine ⟨hinput.packing, ?_⟩
  intro μ hprob L t R η hr hL ht hR hw hη hηsmall hRη hcontains hdiam
  let _ := hprob
  let ν := uniformPeriodCell d L
  let _ : IsProbabilityMeasure ν := uniformPeriodCell_probability d L (hr.trans hL)
  let f : Configuration (Ambient d) × Ambient d → Configuration (Ambient d) :=
    fun p => translate (-p.2) (guardedExpandedConfiguration p.1 L r t hr hL ht)
  have hf : Measurable f := measurable_translate_param _ _
    ((measurable_guardedExpandedConfiguration L r t hr hL ht).comp measurable_fst)
    measurable_snd.neg
  let margin := Real.exp (c * observationRadius η) * η ^ (1 / 4 : ℝ)
  have hmargin : 0 < margin :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hη _)
  obtain ⟨H, hH, hlower, hupper⟩ := exists_measurable_localCrystal_envelope_param hΛ hne
    f hf R (E * Real.exp (c * observationRadius η) * η ^ (1 / 4 : ℝ))
    (B * observationRadius η ^ (-1 / 2 : ℝ)) margin hmargin
  let S : Set (Configuration (Ambient d) × Ambient d) :=
    Hᶜ ∩ {p | expandedGuardDeficit p.1 L r t ht < ENNReal.ofReal η}
  have hS : MeasurableSet S := hH.compl.inter
    (measurableSet_lt ((measurable_expandedGuardDeficit L r t ht).comp measurable_fst)
      measurable_const)
  refine ⟨H, S, hH, ?_, ?_, ?_⟩
  · intro p hp
    have hg := hupper hp
    have heq : E * Real.exp (c * observationRadius η) * η ^ (1 / 4 : ℝ) + margin =
        (E + 1) * Real.exp (c * observationRadius η) * η ^ (1 / 4 : ℝ) := by
      dsimp [margin]
      ring
    rw [heq] at hg
    exact hg
  · intro p hp
    by_cases hd : ENNReal.ofReal η ≤ expandedGuardDeficit p.1 L r t ht
    · exact Or.inl hd
    · exact Or.inr ⟨hp, lt_of_not_ge hd⟩
  · change (μ.prod ν) S ≤ ENNReal.ofReal (B * observationRadius η ^ (-1 / 2 : ℝ))
    rw [Measure.prod_apply hS]
    calc
      _ ≤ ∫⁻ _, ENNReal.ofReal (B * observationRadius η ^ (-1 / 2 : ℝ)) ∂μ := by
        apply lintegral_mono
        intro z
        change ν (Prod.mk z ⁻¹' S) ≤ ENNReal.ofReal (B * observationRadius η ^ (-1 / 2 : ℝ))
        by_cases hz : expandedGuardDeficit z L r t ht < ENNReal.ofReal η
        · obtain ⟨Sz, hgood, hmeasure⟩ :=
            hinput.centres L t R η hr hL ht hR hw hη hηsmall hRη hcontains hdiam z hz
          apply (measure_mono (show Prod.mk z ⁻¹' S ⊆ Sz from ?_)).trans hmeasure
          intro u hu
          by_contra hnot
          exact hu.1 (hlower (hgood u hnot))
        · have hempty : Prod.mk z ⁻¹' S = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro u hu
            exact hz hu.2
          rw [hempty, measure_empty]
          exact zero_le
      _ = _ := by simp

theorem stationaryCrystallizationFor_of_sectionwise_inputs {d : ℕ}
    (Λ : Set (Ambient d)) (hclosed : IsClosed Λ) (hne : Λ.Nonempty)
    (hsub : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (r E B c η₀ : ℝ) (hr : 0 < r) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hη₀ : 0 < η₀)
    (hperiodic : SectionwisePeriodicStabilityInput Λ r E B c η₀)
    (hanalytic : ∀ s : ℝ, (d : ℝ) < s → ∃ A δA : ℝ,
      0 ≤ A ∧ 0 < δA ∧ AnalyticUnitCostInput Λ s r A δA) :
    StationaryCrystallizationFor Λ := by
  exact stationaryCrystallizationFor_of_inputs Λ hsub r (E + 1) B c η₀ hr
    (by linarith) hB hc hη₀
    (periodicStabilityInput_of_sectionwise hclosed hne r E B c η₀ hperiodic) hanalytic

end E8Leech
