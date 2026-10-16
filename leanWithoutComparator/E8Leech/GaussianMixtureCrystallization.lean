import E8Leech.MeasurableQuadraticSlack

/-!
# Gaussian-mixture crystallization without atoms or a density

Positive mass anywhere off π suffices. Countably tested quadratic lower bounds
select a measurable positive-mass parameter set with a common coefficient.
The full mixture gap retains the entire lattice baseline, including mass at π.
Only measures supported on π in the positive half-line remain excluded.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Real SchwartzMap

theorem measurable_e8SlackProfile_parameter (hP : E8KernelNonneg) (u : ℝ) :
    Measurable (fun α => e8SlackProfile hP (α, u)) := by
  have hf := (measurable_e8CertFamily_re hP).comp
    (measurable_id.prodMk (measurable_const (a := u • e8Unit)))
  exact (by fun_prop : Measurable (fun α : ℝ => Real.exp (-α * u ^ 2))).sub hf

theorem measurable_leechSlackProfile_parameter (u : ℝ) :
    Measurable (fun α => leechSlackProfile (α, u)) := by
  have hf := measurable_leechCertFamily_re.comp
    (measurable_id.prodMk (measurable_const (a := u • leechUnit)))
  exact (by fun_prop : Measurable (fun α : ℝ => Real.exp (-α * u ^ 2))).sub hf

theorem potentialUnitCostInput_of_positiveGaussianMixture_radial_quadratic {d : ℕ}
    (ν : Measure ℝ) (Λ : Set (Ambient d)) (β : ℝ)
    (hmass : ν (Ioi 0 \ {β}) ≠ 0) (f : ℝ → 𝓢(Ambient d, ℂ))
    (φ : ℝ × ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hm : ∀ u : ℝ, Measurable (fun α => φ (α, u)))
    (hc : ∀ α : ℝ, Continuous (fun u => φ (α, u)))
    (hnorm : ∀ α (v : Ambient d), φ (α, ‖v‖) = gaussianKernel α v - (f α v).re)
    (hq : ∀ α : ℝ, 0 < α → α ≠ β → ∃ k : ℝ, 0 < k ∧
      ∀ u ∈ Icc 0 r, k * (r - u) ^ 2 ≤ φ (α, u))
    (hgap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 →
      latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) +
        potentialEnergy (potentialMixture (ν.restrict (Ioi 0))
          (gaussianCertificateSlackAwayFrom β f)) μ ≤
        potentialEnergy (positiveGaussianMixturePotential ν) μ) :
    ∃ A : ℝ, 0 < A ∧ PotentialUnitCostInput Λ (positiveGaussianMixturePotential ν) r A (1 / 8) := by
  obtain ⟨k, hk, A, hA, hsub, hνA, hquad⟩ :=
    exists_positive_mass_uniform_quadratic_slack ν (Ioi 0 \ {β})
      (measurableSet_Ioi.diff (measurableSet_singleton β)) hmass φ hr.le hm
      (fun α _ => hc α) (fun α hα => hq α hα.1 hα.2)
  have hApos : A ⊆ Ioi 0 := hsub.trans sdiff_subset
  have hrestrict : (ν.restrict (Ioi 0)) A ≠ 0 := by
    rwa [Measure.restrict_apply hA, inter_eq_left.mpr hApos]
  apply potentialUnitCostInput_of_mixture_quadratic_on_set (ν.restrict (Ioi 0)) Λ
    (positiveGaussianMixturePotential ν) (gaussianCertificateSlackAwayFrom β f) A hA hrestrict hk hr
  · intro α hα x y hxy
    have hαβ : α ≠ β := (hsub hα).2
    simp only [gaussianCertificateSlackAwayFrom, if_neg hαβ]
    apply ENNReal.ofReal_le_ofReal
    have h := hquad α hα ‖x - y‖ ⟨norm_nonneg _, by simpa only [dist_eq_norm] using hxy⟩
    simpa only [hnorm, dist_eq_norm, gaussianSchwartzSlackPotential] using h
  · exact hgap

theorem e8_positiveGaussianMixture_potentialUnitCostInput
    (ν : Measure ℝ) (hν : ν (Ioi 0 \ {π}) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞) :
    ∃ A : ℝ, 0 < A ∧
      PotentialUnitCostInput e8Set (positiveGaussianMixturePotential ν) (Real.sqrt 2) A (1 / 8) := by
  have hpositive : ν (Ioi 0) ≠ 0 := fun h => hν (measure_mono_null sdiff_subset h)
  exact potentialUnitCostInput_of_positiveGaussianMixture_radial_quadratic ν e8Set π hν
    (e8CertFamily e8KernelNonneg) (e8SlackProfile e8KernelNonneg) (Real.sqrt_pos.mpr (by norm_num))
    (measurable_e8SlackProfile_parameter e8KernelNonneg)
    (continuous_e8SlackProfile_radius e8KernelNonneg) (e8SlackProfile_norm e8KernelNonneg)
    (fun _ hα hαπ => e8_gaussian_full_quadratic_slack e8KernelNonneg hα hαπ)
    (fun μ hprob hμ hρ => by
      let _ := hprob
      exact e8_positiveGaussianMixture_gap ν hpositive hbase μ hμ hρ)

theorem leech_positiveGaussianMixture_potentialUnitCostInput
    (ν : Measure ℝ) (hν : ν (Ioi 0 \ {π}) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞) :
    ∃ A : ℝ, 0 < A ∧
      PotentialUnitCostInput leechSet (positiveGaussianMixturePotential ν) 2 A (1 / 8) := by
  have hpositive : ν (Ioi 0) ≠ 0 := fun h => hν (measure_mono_null sdiff_subset h)
  exact potentialUnitCostInput_of_positiveGaussianMixture_radial_quadratic ν leechSet π hν
    leechCertFamily leechSlackProfile (by norm_num) measurable_leechSlackProfile_parameter
    continuous_leechSlackProfile_radius leechSlackProfile_norm
    (fun _ hα hαπ => leech_gaussian_full_quadratic_slack hα hαπ)
    (fun μ hprob hμ hρ => by
      let _ := hprob
      exact leech_positiveGaussianMixture_gap ν hpositive hbase μ hμ hρ)

theorem e8_positiveGaussianMixture_crystallization_general
    (ν : Measure ℝ) (hν : ν (Ioi 0 \ {π}) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    {γ : ℝ} (hγ : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent e8Set (positiveGaussianMixturePotential ν) γ := by
  obtain ⟨A, hA, hinput⟩ := e8_positiveGaussianMixture_potentialUnitCostInput ν hν hbase
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, hperiodic⟩ := e8_sectionwisePeriodicStabilityInput
  exact potentialCrystallizationTargetForExponent_of_sectionwise_inputs e8Set isClosed_e8Set
    ⟨0, zero_mem_e8⟩ (fun _ hx _ hy => e8Set_sub hx hy) (positiveGaussianMixturePotential ν)
    (Real.sqrt 2) A E B c η₀ (1 / 8) γ (Real.sqrt_pos.mpr (by norm_num)) hγ hA.le
    hE hB hc hη₀ (by norm_num) hinput hperiodic

theorem leech_positiveGaussianMixture_crystallization_general
    (ν : Measure ℝ) (hν : ν (Ioi 0 \ {π}) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    {γ : ℝ} (hγ : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent leechSet (positiveGaussianMixturePotential ν) γ := by
  obtain ⟨A, hA, hinput⟩ := leech_positiveGaussianMixture_potentialUnitCostInput ν hν hbase
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, hperiodic⟩ := leech_sectionwisePeriodicStabilityInput_holds
  exact potentialCrystallizationTargetForExponent_of_sectionwise_inputs leechSet isClosed_leechSet
    ⟨0, zero_mem_leechSet⟩ (fun _ hx _ hy => leechSet_sub hx hy) (positiveGaussianMixturePotential ν)
    2 A E B c η₀ (1 / 8) γ (by norm_num) hγ hA.le hE hB hc hη₀ (by norm_num) hinput hperiodic

theorem e8_positiveGaussianMixture_crystallization
    (ν : Measure ℝ) (hν : ν (Ioi 0 \ {π}) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞) :
    PotentialCrystallizationTarget e8Set (positiveGaussianMixturePotential ν) :=
  e8_positiveGaussianMixture_crystallization_general ν hν hbase (by norm_num)

theorem leech_positiveGaussianMixture_crystallization
    (ν : Measure ℝ) (hν : ν (Ioi 0 \ {π}) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞) :
    PotentialCrystallizationTarget leechSet (positiveGaussianMixturePotential ν) :=
  leech_positiveGaussianMixture_crystallization_general ν hν hbase (by norm_num)

/-- An atomless nonzero positive mixing measure automatically has mass off π. -/
theorem positive_parameter_mass_off_singleton (ν : Measure ℝ) [NullSingletonClass ν]
    (hν : ν (Ioi 0) ≠ 0) (β : ℝ) : ν (Ioi 0 \ {β}) ≠ 0 := by
  rw [measure_sdiff_null' (measure_mono_null inter_subset_right (measure_singleton β))]
  exact hν

theorem e8_atomless_positiveGaussianMixture_crystallization_general
    (ν : Measure ℝ) [NullSingletonClass ν] (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    {γ : ℝ} (hγ : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent e8Set (positiveGaussianMixturePotential ν) γ :=
  e8_positiveGaussianMixture_crystallization_general ν
    (positive_parameter_mass_off_singleton ν hν π) hbase hγ

theorem leech_atomless_positiveGaussianMixture_crystallization_general
    (ν : Measure ℝ) [NullSingletonClass ν] (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    {γ : ℝ} (hγ : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent leechSet (positiveGaussianMixturePotential ν) γ :=
  leech_positiveGaussianMixture_crystallization_general ν
    (positive_parameter_mass_off_singleton ν hν π) hbase hγ

end E8Leech
