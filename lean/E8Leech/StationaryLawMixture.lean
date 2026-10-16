import E8Leech.IsometricLatticeEnergy
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Mixing stationary point-process laws

A measurable probability mixture preserves stationarity, common intensity,
and the common value of any measurable nonnegative interaction energy.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

theorem isProbabilityMeasure_bind_laws {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (σ : Measure Ω) [IsProbabilityMeasure σ] (κ : Ω → Measure X) (hκ : Measurable κ)
    (hprob : ∀ ω, IsProbabilityMeasure (κ ω)) : IsProbabilityMeasure (σ.bind κ) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ hκ.aemeasurable]
  have hh (ω : Ω) : κ ω univ = 1 := (hprob ω).measure_univ
  simp_rw [hh]
  simp

theorem isStationary_bind_laws {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure Ω) (κ : Ω → Measure (Configuration (Ambient d))) (hκ : Measurable κ)
    (hstat : ∀ ω, IsStationary (κ ω)) : IsStationary (σ.bind κ) := by
  intro a
  refine ⟨measurable_translate a, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply (measurable_translate a) hA,
    Measure.bind_apply (measurable_translate a hA) hκ.aemeasurable,
    Measure.bind_apply hA hκ.aemeasurable]
  apply lintegral_congr
  intro ω
  exact (hstat ω a).measure_preimage hA.nullMeasurableSet

theorem hasIntensity_bind_laws {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure Ω) [IsProbabilityMeasure σ]
    (κ : Ω → Measure (Configuration (Ambient d))) (hκ : Measurable κ)
    (ρ : ℝ≥0∞) (hρ : ∀ ω, HasIntensity (κ ω) ρ) : HasIntensity (σ.bind κ) ρ := by
  intro W hW
  rw [Measure.lintegral_bind hκ.aemeasurable
    (Configuration.measurable_count hW).aemeasurable]
  simp_rw [fun ω => hρ ω W hW]
  simp

theorem potentialEnergy_bind_laws {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure Ω) [IsProbabilityMeasure σ]
    (κ : Ω → Measure (Configuration (Ambient d))) (hκ : Measurable κ)
    (P : Ambient d → Ambient d → ℝ≥0∞) (hP : Measurable (Function.uncurry P))
    (L : ℝ≥0∞) (hL : ∀ ω, potentialEnergy P (κ ω) = L) :
    potentialEnergy P (σ.bind κ) = L := by
  unfold potentialEnergy at hL ⊢
  rw [Measure.lintegral_bind hκ.aemeasurable
    (measurable_orderedWindowEnergy hP (measurable_unitWindow d)).aemeasurable]
  simp_rw [hL]
  simp

end E8Leech
