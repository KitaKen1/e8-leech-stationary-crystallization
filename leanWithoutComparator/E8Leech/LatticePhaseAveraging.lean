import E8Leech.OrientationMixtureLaw
import E8Leech.JointTranslation

/-!
# Uniform phase is forced by stationarity on one lattice orbit

Averaging a configuration through a fundamental domain removes its initial
phase. Tonelli and stationarity then identify the entire law, without a
measurable choice of a lattice point or of a phase representative.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem volume_fundamentalDomain_eq_one {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1) :
    volume D = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hD, Measure.real] at hcov
  exact (ENNReal.toReal_eq_one_iff _).mp hcov

theorem latticeShiftLaw_eq_of_fundamentalDomains {D E : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hE : IsAddFundamentalDomain Λ E volume) :
    latticeShiftLaw Λ D = latticeShiftLaw Λ E := by
  apply Measure.ext
  intro A hA
  have hm := measurable_latticeShift Λ
  rw [latticeShiftLaw, latticeShiftLaw, Measure.map_apply hm hA, Measure.map_apply hm hA,
    Measure.restrict_apply (hm hA), Measure.restrict_apply (hm hA)]
  apply hD.measure_set_eq hE (hm hA)
  intro ℓ
  ext u
  change latticeShift Λ ((ℓ : Ambient d) + u) ∈ A ↔ latticeShift Λ u ∈ A
  rw [latticeShift_add_lattice]

theorem lintegral_latticeShift_add_phase {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume)
    (F : Configuration (Ambient d) → ℝ≥0∞) (u : Ambient d) :
    (∫⁻ a in D, F (latticeShift Λ (a + u))) = ∫⁻ a in D, F (latticeShift Λ a) := by
  have : VAddCommClass (Ambient d) Λ (Ambient d) := ⟨fun a ℓ x => by
    simp only [Submodule.vadd_def, vadd_eq_add]
    exact add_left_comm _ _ _⟩
  calc
    _ = ∫⁻ a in D, F (latticeShift Λ (u + a)) :=
      lintegral_congr fun a => by rw [add_comm a u]
    _ = ∫⁻ a in u +ᵥ D, F (latticeShift Λ a) :=
      (measurePreserving_add_left volume u).setLIntegral_comp_emb
        (Homeomorph.addLeft u).measurableEmbedding (fun a => F (latticeShift Λ a)) D
    _ = _ := (hD.vadd_of_comm u).setLIntegral_eq hD _ (by
      intro ℓ a
      change F (latticeShift Λ ((ℓ : Ambient d) + a)) = _
      rw [latticeShift_add_lattice])

theorem lintegral_translate_latticeShift {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume)
    (F : Configuration (Ambient d) → ℝ≥0∞) (hF : Measurable F) (u : Ambient d) :
    (∫⁻ a in D, F (translate a (latticeShift Λ u))) =
      ∫⁻ c, F c ∂latticeShiftLaw Λ D := by
  simp_rw [translate_latticeShift]
  rw [lintegral_latticeShift_add_phase Λ hD]
  exact (lintegral_map hF (measurable_latticeShift Λ)).symm

omit Λ [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem stationary_lintegral_average_translates
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (F : Configuration (Ambient d) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ c, ∫⁻ a, F (translate a c) ∂ν ∂μ) = ∫⁻ c, F c ∂μ := by
  have hm : Measurable (fun p : Configuration (Ambient d) × Ambient d =>
      F (translate p.2 p.1)) := hF.comp measurable_translate_joint
  rw [lintegral_lintegral_swap (f := fun c a => F (translate a c)) hm.aemeasurable]
  simp_rw [fun a => (hμ a).lintegral_comp hF]
  simp

theorem lintegral_eq_latticeShiftLaw_of_ae_latticeShift {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = latticeShift Λ u)
    (F : Configuration (Ambient d) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ c, F c ∂μ) = μ univ * ∫⁻ c, F c ∂latticeShiftLaw Λ D := by
  have : IsProbabilityMeasure (volume.restrict D) := by
    constructor
    rw [Measure.restrict_apply_univ, volume_fundamentalDomain_eq_one Λ hD hcov]
  calc
    _ = ∫⁻ c, (∫⁻ a in D, F (translate a c) ∂volume) ∂μ :=
      (stationary_lintegral_average_translates μ hμ (volume.restrict D) F hF).symm
    _ = ∫⁻ _ : Configuration (Ambient d), (∫⁻ c, F c ∂latticeShiftLaw Λ D) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hgood] with c hc
      obtain ⟨u, rfl⟩ := hc
      exact lintegral_translate_latticeShift Λ hD F hF u
    _ = _ := by rw [lintegral_const, mul_comm]

theorem eq_smul_latticeShiftLaw_of_ae_latticeShift {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = latticeShift Λ u) :
    μ = μ univ • latticeShiftLaw Λ D := by
  apply Measure.ext
  intro A hA
  have hh := lintegral_eq_latticeShiftLaw_of_ae_latticeShift Λ hD hcov μ hμ hgood
    (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
  simpa only [lintegral_indicator hA, setLIntegral_const, one_mul,
    Measure.smul_apply, smul_eq_mul] using hh

theorem eq_latticeShiftLaw_of_ae_latticeShift {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = latticeShift Λ u) :
    μ = latticeShiftLaw Λ D := by
  simpa only [measure_univ, one_smul] using
    eq_smul_latticeShiftLaw_of_ae_latticeShift Λ hD hcov μ hμ hgood

end E8Leech
