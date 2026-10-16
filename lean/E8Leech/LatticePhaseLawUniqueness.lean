import E8Leech.LatticePhaseAveraging

/-!
# Uniqueness of the stationary phase law at every orthogonal orientation

Every stationary probability law supported almost surely on translations
of one fixed oriented lattice equals its uniform-phase law. The argument
also identifies an s-finite stationary law as its total mass times that law.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

omit [IsZLattice ℝ Λ] in
theorem translate_rotatedLatticeShift (Q : LatticeOrientation d) (a u : Ambient d) :
    translate (Q.isometry a) (rotatedLatticeShift Λ Q u) =
      rotatedLatticeShift Λ Q (a + u) := by
  rw [rotatedLatticeShift, translate_rotateConfiguration,
    Q.isometry.symm_apply_apply, translate_latticeShift]
  rfl

theorem lintegral_translate_rotatedLatticeShift {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (Q : LatticeOrientation d)
    (F : Configuration (Ambient d) → ℝ≥0∞) (hF : Measurable F) (u : Ambient d) :
    (∫⁻ a in D, F (translate (Q.isometry a) (rotatedLatticeShift Λ Q u))) =
      ∫⁻ c, F c ∂rotatedLatticeShiftLaw Λ D Q := by
  simp_rw [translate_rotatedLatticeShift]
  change (∫⁻ a in D, F (rotateConfiguration Q.isometry (latticeShift Λ (a + u)))) = _
  rw [lintegral_latticeShift_add_phase Λ hD (fun c => F (rotateConfiguration Q.isometry c)) u,
    rotatedLatticeShiftLaw, lintegral_map hF (measurable_rotateConfiguration Q.isometry),
    latticeShiftLaw]
  have hFR : Measurable (fun c => F (rotateConfiguration Q.isometry c)) :=
    hF.comp (measurable_rotateConfiguration Q.isometry)
  exact (lintegral_map hFR (measurable_latticeShift Λ)).symm

theorem lintegral_eq_rotatedLatticeShiftLaw_of_ae {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (Q : LatticeOrientation d) (μ : Measure (Configuration (Ambient d))) [SFinite μ]
    (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ Q u)
    (F : Configuration (Ambient d) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ c, F c ∂μ) = μ univ * ∫⁻ c, F c ∂rotatedLatticeShiftLaw Λ D Q := by
  have : IsProbabilityMeasure (volume.restrict D) := by
    constructor
    rw [Measure.restrict_apply_univ, volume_fundamentalDomain_eq_one Λ hD hcov]
  let ν : Measure (Ambient d) := (volume.restrict D).map Q.isometry
  have : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map Q.isometry.continuous.measurable.aemeasurable
  have havg := stationary_lintegral_average_translates μ hμ ν F hF
  have hmap (c : Configuration (Ambient d)) :
      (∫⁻ a, F (translate a c) ∂ν) =
        ∫⁻ a in D, F (translate (Q.isometry a) c) := by
    have hf : Measurable (fun a : Ambient d => F (translate a c)) :=
      hF.comp (measurable_translate_param (fun _ : Ambient d => c) id measurable_const measurable_id)
    exact lintegral_map hf Q.isometry.continuous.measurable
  simp_rw [hmap] at havg
  calc
    _ = ∫⁻ c, (∫⁻ a in D, F (translate (Q.isometry a) c) ∂volume) ∂μ := havg.symm
    _ = ∫⁻ _ : Configuration (Ambient d), (∫⁻ c, F c ∂rotatedLatticeShiftLaw Λ D Q) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hgood] with c hc
      obtain ⟨u, rfl⟩ := hc
      exact lintegral_translate_rotatedLatticeShift Λ hD Q F hF u
    _ = _ := by rw [lintegral_const, mul_comm]

theorem eq_smul_rotatedLatticeShiftLaw_of_ae {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (Q : LatticeOrientation d) (μ : Measure (Configuration (Ambient d))) [SFinite μ]
    (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ Q u) :
    μ = μ univ • rotatedLatticeShiftLaw Λ D Q := by
  apply Measure.ext
  intro A hA
  have hh := lintegral_eq_rotatedLatticeShiftLaw_of_ae Λ hD hcov Q μ hμ hgood
    (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
  simpa only [lintegral_indicator hA, setLIntegral_const, one_mul,
    Measure.smul_apply, smul_eq_mul] using hh

theorem eq_rotatedLatticeShiftLaw_of_ae {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (Q : LatticeOrientation d) (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ Q u) :
    μ = rotatedLatticeShiftLaw Λ D Q := by
  simpa only [measure_univ, one_smul] using
    eq_smul_rotatedLatticeShiftLaw_of_ae Λ hD hcov Q μ hμ hgood

theorem stationary_iff_eq_rotatedLatticeShiftLaw {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (Q : LatticeOrientation d) (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ Q u) :
    IsStationary μ ↔ μ = rotatedLatticeShiftLaw Λ D Q := by
  constructor
  · intro hμ
    exact eq_rotatedLatticeShiftLaw_of_ae Λ hD hcov Q μ hμ hgood
  · rintro rfl
    exact isStationary_rotatedLatticeShiftLaw Λ hD Q

theorem orientationMixtureLaw_dirac (D : Set (Ambient d)) (Q : LatticeOrientation d) :
    orientationMixtureLaw Λ D (Measure.dirac Q) = rotatedLatticeShiftLaw Λ D Q :=
  Measure.dirac_bind (measurable_rotatedLatticeShiftLaw Λ D) Q

theorem rotatedLatticeShiftLaw_eq_of_fundamentalDomains {D E : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hE : IsAddFundamentalDomain Λ E volume)
    (Q : LatticeOrientation d) : rotatedLatticeShiftLaw Λ D Q = rotatedLatticeShiftLaw Λ E Q := by
  unfold rotatedLatticeShiftLaw
  rw [latticeShiftLaw_eq_of_fundamentalDomains Λ hD hE]

theorem orientationMixtureLaw_eq_of_fundamentalDomains {D E : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hE : IsAddFundamentalDomain Λ E volume)
    (σ : Measure (LatticeOrientation d)) : orientationMixtureLaw Λ D σ = orientationMixtureLaw Λ E σ := by
  unfold orientationMixtureLaw
  congr 1
  funext Q
  exact rotatedLatticeShiftLaw_eq_of_fundamentalDomains Λ hD hE Q

omit Λ [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem e8_eq_orientationMixtureLaw_dirac (Q : LatticeOrientation 8)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient 8, c = rotatedLatticeShift e8Lattice Q u) :
    μ = e8OrientationMixtureLaw (Measure.dirac Q) := by
  rw [e8OrientationMixtureLaw, orientationMixtureLaw_dirac]
  exact eq_rotatedLatticeShiftLaw_of_ae e8Lattice
    (ZSpan.isAddFundamentalDomain e8EuclideanBasis volume) e8Lattice_covolume Q μ hμ hgood

omit Λ [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem leech_eq_orientationMixtureLaw_dirac (Q : LatticeOrientation 24)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient 24, c = rotatedLatticeShift leechLattice Q u) :
    μ = leechOrientationMixtureLaw (Measure.dirac Q) := by
  have hD : IsAddFundamentalDomain leechLattice
      (ZSpan.fundamentalDomain leechEuclideanBasis) volume := by
    rw [leechLattice_eq_span]
    exact ZSpan.isAddFundamentalDomain leechEuclideanBasis volume
  rw [leechOrientationMixtureLaw, orientationMixtureLaw_dirac]
  exact eq_rotatedLatticeShiftLaw_of_ae leechLattice hD leechLattice_covolume Q μ hμ hgood

end E8Leech
