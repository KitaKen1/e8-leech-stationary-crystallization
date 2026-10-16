import E8Leech.GeneralGammaTransfer
import E8Leech.PotentialCrystallization

/-!
# General-exponent transfer for potential energy

The geometric transfer only needs a unit cost. It applies unchanged to
Gaussian and positive-mixture energies for every exponent below 1/12.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

def PotentialCrystallizationTargetForExponent {d : ℕ} (Λ : Set (Ambient d))
    (P : Ambient d → Ambient d → ℝ≥0∞) (γ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
    ∀ μ : Measure (Configuration (Ambient d)),
      IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        HasPotentialExcessAtMost P μ (latticePotentialEnergy Λ P) (ENNReal.ofReal δ) →
        ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
          G ⊆ {z | LocalCrystal Λ z (observationRadius δ)
            (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
          ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G

theorem potentialCrystallizationTargetForExponent_one_thirteenth {d : ℕ}
    (Λ : Set (Ambient d)) (P : Ambient d → Ambient d → ℝ≥0∞) :
    PotentialCrystallizationTargetForExponent Λ P (1 / 13) ↔
      PotentialCrystallizationTarget Λ P := Iff.rfl

theorem potentialCrystallizationTargetForExponent_of_inputs {d : ℕ}
    (Λ : Set (Ambient d)) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (P : Ambient d → Ambient d → ℝ≥0∞)
    (r A E B c η₀ δA γ : ℝ) (hr : 0 < r) (hγ : γ < 1 / 12)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hη₀ : 0 < η₀) (hδA : 0 < δA)
    (hanalytic : PotentialUnitCostInput Λ P r A δA)
    (hperiodic : PeriodicStabilityInput Λ r E B c η₀) :
    PotentialCrystallizationTargetForExponent Λ P γ := by
  obtain ⟨δ₁, h₁, hs₁, hp⟩ := exists_uniform_general_transfer_parameters
    d A E B c η₀ γ hγ hA hE hB hc hη₀
  refine ⟨transferConstant E B, transferConstant_pos hE hB, min δ₁ δA,
    lt_min h₁ hδA, lt_of_le_of_lt (min_le_left _ _) hs₁, ?_⟩
  intro μ hprob hμ hρ δ hδ hsmall hexcess
  let _ := hprob
  obtain ⟨κ, cost, V, hκ0, hκtop, hratio, hV, hcost⟩ :=
    hanalytic.cost μ hprob hμ hρ δ hδ (hsmall.trans_le (min_le_right _ _)) hexcess
  exact measurable_crystallization_of_general_transfer_inputs Λ hΛ r A E B c η₀ γ δ hr hA hE hB
    hδ (hp δ hδ (hsmall.trans_le (min_le_left _ _))) hperiodic μ hμ hρ
    κ cost V hκ0 hκtop hratio hV hcost

theorem potentialCrystallizationTargetForExponent_of_sectionwise_inputs {d : ℕ}
    (Λ : Set (Ambient d)) (hclosed : IsClosed Λ) (hne : Λ.Nonempty)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (P : Ambient d → Ambient d → ℝ≥0∞)
    (r A E B c η₀ δA γ : ℝ) (hr : 0 < r) (hγ : γ < 1 / 12)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hη₀ : 0 < η₀) (hδA : 0 < δA)
    (hanalytic : PotentialUnitCostInput Λ P r A δA)
    (hperiodic : SectionwisePeriodicStabilityInput Λ r E B c η₀) :
    PotentialCrystallizationTargetForExponent Λ P γ :=
  potentialCrystallizationTargetForExponent_of_inputs Λ hΛ P r A (E + 1) B c η₀ δA γ hr hγ hA
    (by linarith) hB hc hη₀ hδA hanalytic
    (periodicStabilityInput_of_sectionwise hclosed hne r E B c η₀ hperiodic)

end E8Leech
