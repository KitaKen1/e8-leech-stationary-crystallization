import E8Leech.AeInvariantDensityAveraging
import E8Leech.GeneralOrientationClassification

/-! # Stationary phase averaging with an invariant orientation probability kernel -/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem lintegral_orientationMixture_of_invariant_kernel {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hDm : MeasurableSet D)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (κ : Kernel (Configuration (Ambient d)) (LatticeOrientation d)) [IsMarkovKernel κ]
    (hinv : ∀ a, ∀ᵐ c ∂μ, κ (translate a c) = κ c)
    (hgood : ∀ᵐ c ∂μ, ∀ᵐ Q ∂κ c, ∃ u : Ambient d, c = rotatedLatticeShift Λ Q u)
    (F : Configuration (Ambient d) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ c, F c ∂μ) =
      ∫⁻ Q, (∫⁻ c, F c ∂rotatedLatticeShiftLaw Λ D Q) ∂μ.bind κ := by
  let η : Kernel (LatticeOrientation d) (Configuration (Ambient d)) :=
    ⟨rotatedLatticeShiftLaw Λ D, measurable_rotatedLatticeShiftLaw Λ D⟩
  have hη (Q : LatticeOrientation d) : IsFiniteMeasure (η Q) := by
    let := isProbabilityMeasure_rotatedLatticeShiftLaw Λ hD hcov Q
    change IsFiniteMeasure (rotatedLatticeShiftLaw Λ D Q)
    infer_instance
  have hJ : Measurable (fun Q : LatticeOrientation d =>
      ∫⁻ c, F c ∂rotatedLatticeShiftLaw Λ D Q) :=
    measurable_lintegral_of_finite_fibers η hη (hF.comp measurable_snd)
  rw [Measure.lintegral_bind κ.measurable.aemeasurable hJ.aemeasurable]
  let w : Configuration (Ambient d) × Ambient d → ℝ≥0∞ :=
    fun p => ∫⁻ Q, orientationPhaseDensity D Q p.2 ∂κ p.1
  have hw : Measurable w := measurable_lintegral_finite_fibers_param κ
    (fun _ => inferInstance) Prod.fst measurable_fst
    ((measurable_orientationPhaseDensity hDm).comp (measurable_snd.prodMk measurable_fst.snd))
  have hwi (a : Ambient d) : ∀ᵐ c ∂μ, w (translate a c, a) = w (c, a) := by
    filter_upwards [hinv a] with c hc
    change (∫⁻ Q, orientationPhaseDensity D Q a ∂κ (translate a c)) = _
    rw [hc]
  have hwn : ∀ᵐ c ∂μ, (∫⁻ a, w (c, a)) = 1 := ae_of_all _ fun c => by
    have hd : Measurable (fun p : Ambient d × LatticeOrientation d =>
        orientationPhaseDensity D p.2 p.1) :=
      (measurable_orientationPhaseDensity hDm).comp measurable_swap
    change (∫⁻ a, (∫⁻ Q, orientationPhaseDensity D Q a ∂κ c)) = 1
    rw [lintegral_lintegral_swap hd.aemeasurable]
    simp_rw [lintegral_orientationPhaseDensity hDm,
      volume_fundamentalDomain_eq_one Λ hD hcov]
    simp
  have havg := stationary_lintegral_ae_invariant_density_average μ hμ w hw hwi hwn F hF
  calc
    _ = ∫⁻ c, (∫⁻ a, w (c, a) * F (translate a c)) ∂μ := havg.symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hgood] with c hc
      have hd : Measurable (fun p : Ambient d × LatticeOrientation d =>
          orientationPhaseDensity D p.2 p.1 * F (translate p.1 c)) :=
        ((measurable_orientationPhaseDensity hDm).comp measurable_swap).mul
          (hF.comp (measurable_translate_joint.comp (measurable_const.prodMk measurable_fst)))
      calc
        _ = ∫⁻ a, (∫⁻ Q, orientationPhaseDensity D Q a * F (translate a c) ∂κ c) := by
          apply lintegral_congr
          intro a
          exact (lintegral_mul_const (F (translate a c))
            ((measurable_orientationPhaseDensity hDm).comp
              (measurable_id.prodMk measurable_const))).symm
        _ = ∫⁻ Q, (∫⁻ a, orientationPhaseDensity D Q a * F (translate a c)) ∂κ c :=
          lintegral_lintegral_swap hd.aemeasurable
        _ = _ := by
          apply lintegral_congr_ae
          filter_upwards [hc] with Q hQ
          obtain ⟨u, hu⟩ := hQ
          rw [hu]
          exact lintegral_phaseDensity_translate_rotatedLatticeShift Λ hD hDm Q u F hF

theorem eq_orientationMixtureLaw_of_invariant_kernel_measurable_domain {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hDm : MeasurableSet D)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (κ : Kernel (Configuration (Ambient d)) (LatticeOrientation d)) [IsMarkovKernel κ]
    (hinv : ∀ a, ∀ᵐ c ∂μ, κ (translate a c) = κ c)
    (hgood : ∀ᵐ c ∂μ, ∀ᵐ Q ∂κ c, ∃ u : Ambient d, c = rotatedLatticeShift Λ Q u) :
    μ = orientationMixtureLaw Λ D (μ.bind κ) := by
  apply Measure.ext
  intro A hA
  rw [orientationMixtureLaw, Measure.bind_apply hA
    (measurable_rotatedLatticeShiftLaw Λ D).aemeasurable]
  have hh := lintegral_orientationMixture_of_invariant_kernel Λ hD hDm hcov μ hμ κ hinv hgood
    (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
  simpa only [lintegral_indicator hA, setLIntegral_const, one_mul] using hh

theorem eq_orientationMixtureLaw_of_invariant_kernel {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (κ : Kernel (Configuration (Ambient d)) (LatticeOrientation d)) [IsMarkovKernel κ]
    (hinv : ∀ a, ∀ᵐ c ∂μ, κ (translate a c) = κ c)
    (hgood : ∀ᵐ c ∂μ, ∀ᵐ Q ∂κ c, ∃ u : Ambient d, c = rotatedLatticeShift Λ Q u) :
    μ = orientationMixtureLaw Λ D (μ.bind κ) := by
  let b := (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  have hE : IsAddFundamentalDomain Λ (ZSpan.fundamentalDomain b) volume :=
    ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ Λ) volume
  calc
    _ = orientationMixtureLaw Λ (ZSpan.fundamentalDomain b) (μ.bind κ) :=
      eq_orientationMixtureLaw_of_invariant_kernel_measurable_domain Λ hE
        (ZSpan.fundamentalDomain_measurableSet b) hcov μ hμ κ hinv hgood
    _ = _ := orientationMixtureLaw_eq_of_fundamentalDomains Λ hE hD (μ.bind κ)

end E8Leech
