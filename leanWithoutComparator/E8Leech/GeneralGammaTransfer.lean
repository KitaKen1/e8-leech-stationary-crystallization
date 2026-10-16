import E8Leech.GeneralGammaScales
import E8Leech.SectionwiseBRR

/-!
# Quantitative stationary crystallization for a variable exponent

The geometric and measure-theoretic transfer is the existing original-point
transfer, with the density scale and final error supplied by GeneralGammaScales.
The analytic and periodic inputs are unchanged. A measurable good subevent is
retained, and all constants precede the law and excess parameter.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

def StationaryCrystallizationForExponent {d : ℕ} (Λ : Set (Ambient d)) (γ : ℝ) : Prop :=
  ∀ s : ℝ, (d : ℝ) < s →
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient d)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          HasRieszExcessAtMost s μ (latticeRieszEnergy Λ s) (ENNReal.ofReal δ) →
          ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
            G ⊆ {z | LocalCrystal Λ z (observationRadius δ)
              (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G

def StationaryCrystallizationForAllExponents {d : ℕ} (Λ : Set (Ambient d)) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 1 / 12 → StationaryCrystallizationForExponent Λ γ

theorem stationaryCrystallizationForExponent_one_thirteenth {d : ℕ} (Λ : Set (Ambient d)) :
    StationaryCrystallizationForExponent Λ (1 / 13) ↔ StationaryCrystallizationFor Λ := Iff.rfl

theorem measurable_crystallization_of_general_transfer_inputs {d : ℕ}
    (Λ : Set (Ambient d)) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (r A E B c η₀ γ δ : ℝ) (hr : 0 < r)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hs : GeneralTransferScaleData d A E B c η₀ γ δ)
    (hperiodic : PeriodicStabilityInput Λ r E B c η₀)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (κ cost : ℝ≥0∞) (V : Ambient d → Ambient d → ℝ≥0∞)
    (hκ0 : κ ≠ 0) (hκtop : κ ≠ ∞)
    (hcostratio : cost / κ ≤ ENNReal.ofReal (A * δ ^ (1 / 3 : ℝ)))
    (hV : ∀ x y, x ≠ y → dist x y < r * (1 - δ ^ (1 / 3 : ℝ)) → κ ≤ V x y)
    (hcost : (∫⁻ z, orderedWindowEnergy V z (unitWindow d) ∂μ) ≤ cost) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      G ⊆ {z | LocalCrystal Λ z (observationRadius δ)
        (transferConstant E B * δ ^ γ)
        (transferConstant E B * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
      ENNReal.ofReal (1 - transferConstant E B * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G := by
  let t := δ ^ (1 / 3 : ℝ)
  let R := observationRadius δ
  let η := δ ^ generalDensityExponent γ
  let q := R ^ (-1 / 2 : ℝ)
  let a := (1 - t)⁻¹
  let ε := (A + (d : ℝ) + 1) * t
  let p := B * observationRadius η ^ (-1 / 2 : ℝ)
  have ht0 : 0 ≤ t := hs.cutoff_pos.le
  have ht : t ≤ 1 / 2 := hs.cutoff_half
  have ht1 : t < 1 := by linarith
  have hq : 0 < q := Real.rpow_pos_of_pos hs.radius_pos _
  by_cases hnontrivial : 0 < 1 - transferConstant E B * q
  · have hRad : 0 ≤ a * R := mul_nonneg (inv_pos.mpr (by linarith)).le hs.radius_pos.le
    obtain ⟨L, hL, hw, hguard, hboundary⟩ :=
      exists_finite_period_length d r (a * R) t q hr hRad hs.cutoff_pos hq
    have hpacking := fun z => hperiodic.packing z L t hL ht1
    have hdel := (deletedIntensity_le_of_cost μ (r * (1 - t)) κ cost hκ0 hκtop
      V hV hcost).trans hcostratio
    have hmean0 := expected_expandedGuardDeficit_le_of_deletedIntensity μ hμ hρ
      L r t hr hL ht0 ht1 (ENNReal.ofReal (A * t)) ENNReal.ofReal_ne_top hdel hpacking
    have hAt : 0 ≤ A * t := mul_nonneg hA ht0
    have hmean : (∫⁻ z, expandedGuardDeficit z L r t ht1 ∂μ) ≤ ENNReal.ofReal ε := by
      rw [ENNReal.toReal_ofReal hAt] at hmean0
      apply hmean0.trans (ENNReal.ofReal_le_ofReal ?_)
      dsimp [ε]
      nlinarith
    obtain ⟨H, S, hH, hgood, hcover, hS⟩ := hperiodic.events μ inferInstance
      L t (a * R) η hr hL ht1 hRad hw hs.eta_pos hs.eta_small
      hs.eta_radius_pos hs.contains hs.diameter
    have hm0 : 0 ≤ ε / η := div_nonneg (by dsimp [ε]; positivity) hs.eta_pos.le
    have hp0 : 0 ≤ p := mul_nonneg hB (Real.rpow_nonneg hs.eta_radius_pos.le _)
    have hb0 : 0 ≤ (d : ℝ) * (r + 2 * (a * R)) / L :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (hr.trans hL).le
    have hbudgetpos : 0 < 1 - (7 * B + 3) * q := by
      dsimp [transferConstant] at hnontrivial
      nlinarith
    have hbudget := ennreal_strict_transfer_budget hB hq hm0 hp0 hb0
      hs.markov hs.stability hboundary hbudgetpos
    rw [ENNReal.ofReal_div_of_pos hs.eta_pos] at hbudget
    have he : 0 ≤ E * Real.exp (c * observationRadius η) * η ^ (1 / 4 : ℝ) :=
      mul_nonneg (mul_nonneg hE (Real.exp_pos _).le) (Real.rpow_nonneg hs.eta_pos.le _)
    obtain ⟨G, hG, hGgood, hGprob⟩ :=
      measurable_good_event_periodization_restoration_of_unit_cost Λ hΛ μ hμ hρ
        L r t R (E * Real.exp (c * observationRadius η) * η ^ (1 / 4 : ℝ)) p
        hr hL ht0 ht hs.radius_pos.le he hw
        (ENNReal.ofReal η) (ENNReal.ofReal ε) (ENNReal.ofReal p)
        (ENNReal.ofReal (1 - (7 * B + 3) * q))
        (ENNReal.ofReal_ne_zero_iff.mpr hs.eta_pos) ENNReal.ofReal_ne_top
        hmean H S hH hgood hcover hS hbudget κ cost hκ0 hκtop V hV hcost
    refine ⟨G, hG, ?_, ?_⟩
    · intro z hz
      exact localCrystal_mono_loss (localCrystal_mono_error (hGgood hz) hs.error) hs.loss
    · have hD : cost / κ * volume (Metric.closedBall (0 : Ambient d) R) ≤ ENNReal.ofReal q :=
        (mul_le_mul' hcostratio le_rfl).trans hs.deletion
      exact (ennreal_restored_transfer_budget hE hB hq.le hD).trans hGprob
  · refine ⟨∅, MeasurableSet.empty, Set.empty_subset _, ?_⟩
    rw [ENNReal.ofReal_eq_zero.mpr (not_lt.mp hnontrivial)]
    exact zero_le

/-- The exact target quantifiers for one potential, conditional only on the
explicit analytic and periodic proof inputs. -/
theorem quantitative_crystallization_of_inputs_general {d : ℕ}
    (Λ : Set (Ambient d)) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (s r A E B c η₀ δA γ : ℝ) (hr : 0 < r) (hγ : γ < 1 / 12)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hη₀ : 0 < η₀) (hδA : 0 < δA)
    (hanalytic : AnalyticUnitCostInput Λ s r A δA)
    (hperiodic : PeriodicStabilityInput Λ r E B c η₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient d)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          HasRieszExcessAtMost s μ (latticeRieszEnergy Λ s) (ENNReal.ofReal δ) →
          ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
            G ⊆ {z | LocalCrystal Λ z (observationRadius δ)
              (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G := by
  obtain ⟨δ₁, h₁, hs₁, hp⟩ := exists_uniform_general_transfer_parameters d A E B c η₀ γ hγ hA hE hB hc hη₀
  refine ⟨transferConstant E B, transferConstant_pos hE hB, min δ₁ δA,
    lt_min h₁ hδA, lt_of_le_of_lt (min_le_left _ _) hs₁, ?_⟩
  intro μ hprob hμ hρ δ hδ hsmall hexcess
  let _ := hprob
  obtain ⟨κ, cost, V, hκ0, hκtop, hratio, hV, hcost⟩ :=
    hanalytic.cost μ hprob hμ hρ δ hδ (hsmall.trans_le (min_le_right _ _)) hexcess
  exact measurable_crystallization_of_general_transfer_inputs Λ hΛ r A E B c η₀ γ δ hr hA hE hB
    hδ (hp δ hδ (hsmall.trans_le (min_le_left _ _))) hperiodic μ hμ hρ
    κ cost V hκ0 hκtop hratio hV hcost

theorem stationaryCrystallizationForExponent_of_inputs {d : ℕ}
    (Λ : Set (Ambient d)) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (r E B c η₀ γ : ℝ) (hr : 0 < r) (hγ : γ < 1 / 12)
    (hE : 0 ≤ E) (hB : 0 ≤ B) (hc : 0 ≤ c) (hη₀ : 0 < η₀)
    (hperiodic : PeriodicStabilityInput Λ r E B c η₀)
    (hanalytic : ∀ s : ℝ, (d : ℝ) < s → ∃ A δA : ℝ,
      0 ≤ A ∧ 0 < δA ∧ AnalyticUnitCostInput Λ s r A δA) :
    StationaryCrystallizationForExponent Λ γ := by
  intro s hs
  obtain ⟨A, δA, hA, hδA, hinput⟩ := hanalytic s hs
  exact quantitative_crystallization_of_inputs_general Λ hΛ s r A E B c η₀ δA γ
    hr hγ hA hE hB hc hη₀ hδA hinput hperiodic

theorem stationaryCrystallizationForAllExponents_of_sectionwise_inputs {d : ℕ}
    (Λ : Set (Ambient d)) (hclosed : IsClosed Λ) (hne : Λ.Nonempty)
    (hsub : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (r E B c η₀ : ℝ) (hr : 0 < r) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hη₀ : 0 < η₀)
    (hperiodic : SectionwisePeriodicStabilityInput Λ r E B c η₀)
    (hanalytic : ∀ s : ℝ, (d : ℝ) < s → ∃ A δA : ℝ,
      0 ≤ A ∧ 0 < δA ∧ AnalyticUnitCostInput Λ s r A δA) :
    StationaryCrystallizationForAllExponents Λ := by
  intro γ _hγ hγlt
  exact stationaryCrystallizationForExponent_of_inputs Λ hsub r (E + 1) B c η₀ γ hr hγlt
    (by linarith) hB hc hη₀
    (periodicStabilityInput_of_sectionwise hclosed hne r E B c η₀ hperiodic) hanalytic

end E8Leech
