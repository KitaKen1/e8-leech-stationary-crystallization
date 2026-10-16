import E8Leech.GaussianE8QuadraticSlack
import E8Leech.GaussianLeechQuadraticSlack
import E8Leech.GeneralGammaPotentialTransfer

/-!
# Actual Gaussian-mixture crystallization from a positive nonexceptional atom

A single positive atom away from π supplies a positive quadratic cost. The
remaining mixing measure is arbitrary, and its entire lattice baseline is
retained, including any mass at π. Constants precede the law and excess.
This covers finite positive mixtures with at least one nonexceptional component;
atomless mixtures and mixtures concentrated at π remain separate obligations.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Real SchwartzMap

theorem potentialUnitCostInput_of_positiveGaussianMixture_atom {d : ℕ}
    (ν : Measure ℝ) (Λ : Set (Ambient d)) {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hbase : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞)
    (β : ℝ) (f : ℝ → 𝓢(Ambient d, ℂ)) {α k r : ℝ}
    (hα : 0 < α) (hαβ : α ≠ β) (hmass : ν {α} ≠ 0) (hk : 0 < k) (hr : 0 < r)
    (hquad : ∀ v : Ambient d, ‖v‖ ≤ r →
      k * (r - ‖v‖) ^ 2 ≤ gaussianKernel α v - (f α v).re)
    (hgap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 →
      latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) +
        potentialEnergy (potentialMixture (ν.restrict (Ioi 0))
          (gaussianCertificateSlackAwayFrom β f)) μ ≤
        potentialEnergy (positiveGaussianMixturePotential ν) μ) :
    ∃ A : ℝ, 0 < A ∧ PotentialUnitCostInput Λ (positiveGaussianMixturePotential ν) r A (1 / 8) := by
  have hmtop : ν {α} ≠ ∞ := by
    simpa only [Icc_self] using
      positive_parameter_interval_mass_ne_top_of_lattice ν hz hne hbase hα le_rfl
  let K := (ENNReal.ofReal k * ν {α}).toReal
  have hK : 0 < K := positiveMixtureIntervalCoefficient_pos hk hmass hmtop
  have hproduct : ENNReal.ofReal k * ν {α} ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmtop
  refine ⟨(K * r ^ 2)⁻¹, by positivity,
    potentialUnitCostInput_of_full_quadratic_slack Λ (positiveGaussianMixturePotential ν)
      (potentialMixture (ν.restrict (Ioi 0)) (gaussianCertificateSlackAwayFrom β f)) hK hr ?_ ?_⟩
  · intro μ hprob hμ hρ _
    exact hgap μ hprob hμ hρ
  · intro x y hxy
    have hl := potentialMixture_lower_on_parameter_set (ν.restrict (Ioi 0))
      (gaussianCertificateSlackAwayFrom β f) (A := {α}) (measurableSet_singleton α)
      (ENNReal.ofReal (k * (r - dist x y) ^ 2)) x y (fun θ hθ => by
        have hθα : θ = α := hθ
        subst θ
        simp only [gaussianCertificateSlackAwayFrom, if_neg hαβ]
        apply ENNReal.ofReal_le_ofReal
        simpa only [gaussianSchwartzSlackPotential, dist_eq_norm] using
          hquad (x - y) (by simpa only [dist_eq_norm] using hxy))
    have hsubset : ({α} : Set ℝ) ⊆ Ioi 0 := singleton_subset_iff.mpr hα
    rw [Measure.restrict_apply (measurableSet_singleton α),
      inter_eq_left.mpr hsubset, ENNReal.ofReal_mul hk.le] at hl
    rw [ENNReal.ofReal_mul hK.le, show ENNReal.ofReal K = ENNReal.ofReal k * ν {α} from
      ENNReal.ofReal_toReal hproduct]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hl

theorem e8_positiveGaussianMixture_potentialUnitCostInput_of_atom
    (ν : Measure ℝ) (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) (hmass : ν {α} ≠ 0) :
    ∃ A : ℝ, 0 < A ∧
      PotentialUnitCostInput e8Set (positiveGaussianMixturePotential ν) (Real.sqrt 2) A (1 / 8) := by
  obtain ⟨z, hz, hne, -⟩ := e8Set_minimum_attained
  obtain ⟨k, hk, hquad⟩ := e8_gaussian_full_quadratic_slack_norm e8KernelNonneg hα hαπ
  have hν : ν (Ioi 0) ≠ 0 := ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hmass)
    (measure_mono (singleton_subset_iff.mpr hα)))
  exact potentialUnitCostInput_of_positiveGaussianMixture_atom ν e8Set hz hne hbase π
    (e8CertFamily e8KernelNonneg) hα hαπ hmass hk (Real.sqrt_pos.mpr (by norm_num)) hquad
    (fun μ hprob hμ hρ => by
      let _ := hprob
      exact e8_positiveGaussianMixture_gap ν hν hbase μ hμ hρ)

theorem leech_positiveGaussianMixture_potentialUnitCostInput_of_atom
    (ν : Measure ℝ) (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) (hmass : ν {α} ≠ 0) :
    ∃ A : ℝ, 0 < A ∧
      PotentialUnitCostInput leechSet (positiveGaussianMixturePotential ν) 2 A (1 / 8) := by
  obtain ⟨z, hz, hne, -⟩ := leechSet_minimum_attained
  obtain ⟨k, hk, hquad⟩ := leech_gaussian_full_quadratic_slack_norm hα hαπ
  have hν : ν (Ioi 0) ≠ 0 := ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hmass)
    (measure_mono (singleton_subset_iff.mpr hα)))
  exact potentialUnitCostInput_of_positiveGaussianMixture_atom ν leechSet hz hne hbase π
    leechCertFamily hα hαπ hmass hk (by norm_num) hquad (fun μ hprob hμ hρ => by
      let _ := hprob
      exact leech_positiveGaussianMixture_gap ν hν hbase μ hμ hρ)

theorem e8_positiveGaussianMixture_crystallization_of_atom_general
    (ν : Measure ℝ) (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    {α γ : ℝ} (hα : 0 < α) (hαπ : α ≠ π) (hmass : ν {α} ≠ 0) (hγ : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent e8Set (positiveGaussianMixturePotential ν) γ := by
  obtain ⟨A, hA, hinput⟩ := e8_positiveGaussianMixture_potentialUnitCostInput_of_atom ν hbase hα hαπ hmass
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, hperiodic⟩ := e8_sectionwisePeriodicStabilityInput
  exact potentialCrystallizationTargetForExponent_of_sectionwise_inputs e8Set isClosed_e8Set
    ⟨0, zero_mem_e8⟩ (fun _ hx _ hy => e8Set_sub hx hy) (positiveGaussianMixturePotential ν)
    (Real.sqrt 2) A E B c η₀ (1 / 8) γ (Real.sqrt_pos.mpr (by norm_num)) hγ hA.le
    hE hB hc hη₀ (by norm_num) hinput hperiodic

theorem leech_positiveGaussianMixture_crystallization_of_atom_general
    (ν : Measure ℝ) (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    {α γ : ℝ} (hα : 0 < α) (hαπ : α ≠ π) (hmass : ν {α} ≠ 0) (hγ : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent leechSet (positiveGaussianMixturePotential ν) γ := by
  obtain ⟨A, hA, hinput⟩ := leech_positiveGaussianMixture_potentialUnitCostInput_of_atom ν hbase hα hαπ hmass
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, hperiodic⟩ := leech_sectionwisePeriodicStabilityInput_holds
  exact potentialCrystallizationTargetForExponent_of_sectionwise_inputs leechSet isClosed_leechSet
    ⟨0, zero_mem_leechSet⟩ (fun _ hx _ hy => leechSet_sub hx hy) (positiveGaussianMixturePotential ν)
    2 A E B c η₀ (1 / 8) γ (by norm_num) hγ hA.le hE hB hc hη₀ (by norm_num) hinput hperiodic

theorem e8_positiveGaussianMixture_crystallization_of_atom
    (ν : Measure ℝ) (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) (hmass : ν {α} ≠ 0) :
    PotentialCrystallizationTarget e8Set (positiveGaussianMixturePotential ν) :=
  e8_positiveGaussianMixture_crystallization_of_atom_general ν hbase hα hαπ hmass (by norm_num)

theorem leech_positiveGaussianMixture_crystallization_of_atom
    (ν : Measure ℝ) (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) (hmass : ν {α} ≠ 0) :
    PotentialCrystallizationTarget leechSet (positiveGaussianMixturePotential ν) :=
  leech_positiveGaussianMixture_crystallization_of_atom_general ν hbase hα hαπ hmass (by norm_num)

end E8Leech
