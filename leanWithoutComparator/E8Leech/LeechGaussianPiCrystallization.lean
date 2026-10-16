import E8Leech.LeechUniformSlackNearPi
import E8Leech.GaussianGapRightLimit

/-!
# The Leech Gaussian at π and all positive Leech Gaussian mixtures

A common quadratic cost survives the right-parameter limit at π. Insert this
cost at the exceptional parameter of a new measurable slack family. The full
mixture gap then handles an atom at π, completing the Leech theorem for every
nonzero positive mixing measure with finite lattice energy.
No exceptional Schwartz witness is constructed or assumed.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Real SchwartzMap

theorem exists_leech_pi_quadratic_gap :
    ∃ k : ℝ, 0 < k ∧ ∀ μ : Measure (Configuration (Ambient 24)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 →
      latticePotentialEnergy leechSet (gaussianPotential π) +
        potentialEnergy (quadraticClosePairPotential k 2) μ ≤
        potentialEnergy (gaussianPotential π) μ := by
  obtain ⟨b, k, hb, hk, hlower⟩ := leech_uniform_quadratic_slack_right_pi
  refine ⟨k, hk, ?_⟩
  intro μ hprob hμ hρ
  let _ := hprob
  apply gaussian_gap_of_right_parameter_interval leechSet μ
    (quadraticClosePairPotential k 2) hb
  intro α hα
  have hα0 : 0 < α := Real.pi_pos.trans hα.1
  have hαπ : α ≠ π := hα.1.ne'
  have hV : ∀ x y : Ambient 24, quadraticClosePairPotential k 2 x y ≤
      gaussianSchwartzSlackPotential α (leechCertFamily α) x y := by
    intro x y
    by_cases hxy : dist x y ≤ (2 : ℝ)
    · rw [quadraticClosePairPotential_of_dist_le k _ hxy]
      apply ENNReal.ofReal_le_ofReal
      have h := hlower α hα ‖x - y‖ ⟨norm_nonneg _, by simpa only [dist_eq_norm] using hxy⟩
      simpa only [leechSlackProfile_norm, dist_eq_norm, gaussianSchwartzSlackPotential] using h
    · simp only [quadraticClosePairPotential, max_eq_left (by linarith : (2 : ℝ) - dist x y ≤ 0),
        zero_pow (by norm_num : 2 ≠ 0), mul_zero, ENNReal.ofReal_zero, zero_le]
  exact (add_le_add le_rfl (potentialEnergy_mono hV μ)).trans (leech_gaussian_gap hα0 hαπ μ hμ hρ)

def leechPiCostCoefficient : ℝ := exists_leech_pi_quadratic_gap.choose

def leechPiSlack : Ambient 24 → Ambient 24 → ℝ≥0∞ :=
  quadraticClosePairPotential leechPiCostCoefficient 2

theorem leechPiCostCoefficient_pos : 0 < leechPiCostCoefficient :=
  exists_leech_pi_quadratic_gap.choose_spec.1

theorem measurable_leechPiSlack : Measurable (Function.uncurry leechPiSlack) :=
  measurable_quadraticClosePairPotential _ _

theorem leech_gaussian_pi_gap (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy leechSet (gaussianPotential π) + potentialEnergy leechPiSlack μ ≤
      potentialEnergy (gaussianPotential π) μ :=
  exists_leech_pi_quadratic_gap.choose_spec.2 μ inferInstance hμ hρ

theorem leechPiSlack_quadratic_lower {x y : Ambient 24} (hxy : dist x y ≤ (2 : ℝ)) :
    ENNReal.ofReal (leechPiCostCoefficient * ((2 : ℝ) - dist x y) ^ 2) ≤ leechPiSlack x y := by
  rw [leechPiSlack, quadraticClosePairPotential_of_dist_le _ _ hxy]

theorem leech_gaussian_pi_potentialUnitCostInput :
    ∃ A : ℝ, 0 < A ∧ PotentialUnitCostInput leechSet (gaussianPotential π) 2 A (1 / 8) := by
  have hk := leechPiCostCoefficient_pos
  have hr : 0 < (2 : ℝ) := (by norm_num : (0 : ℝ) < 2)
  refine ⟨(leechPiCostCoefficient * 2 ^ 2)⁻¹, by positivity,
    potentialUnitCostInput_of_full_quadratic_slack leechSet (gaussianPotential π) leechPiSlack hk hr ?_
      (fun _ _ hxy => leechPiSlack_quadratic_lower hxy)⟩
  intro μ hprob hμ hρ _
  let _ := hprob
  exact leech_gaussian_pi_gap μ hμ hρ

/-- A complete measurable family of energy slacks, with a positive quadratic cost at π. -/
def leechGaussianSlackComplete (α : ℝ) (x y : Ambient 24) : ℝ≥0∞ :=
  if α = π then leechPiSlack x y else gaussianSchwartzSlackPotential α (leechCertFamily α) x y

theorem measurable_leechGaussianSlackComplete :
    Measurable (fun p : ℝ × (Ambient 24 × Ambient 24) => leechGaussianSlackComplete p.1 p.2.1 p.2.2) := by
  unfold leechGaussianSlackComplete
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    (measurable_leechPiSlack.comp measurable_snd)
    (measurable_gaussianSchwartzSlackPotential_family _ measurable_leechCertFamily_re)

theorem leech_positiveGaussianMixture_complete_gap (ν : Measure ℝ)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) +
      potentialEnergy (potentialMixture (ν.restrict (Ioi 0)) leechGaussianSlackComplete) μ ≤
      potentialEnergy (positiveGaussianMixturePotential ν) μ := by
  obtain ⟨z, hz, hne, -⟩ := leechSet_minimum_attained
  let := sigmaFinite_positive_parameter_restrict_of_lattice ν hz hne hbase
  apply expected_potentialMixture_gap (ν.restrict (Ioi 0)) μ gaussianPotential
    leechGaussianSlackComplete (measurable_gaussianPotential_joint 24)
    measurable_leechGaussianSlackComplete leechSet countable_leechSet
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  by_cases hαπ : α = π
  · subst α
    have heq : leechGaussianSlackComplete π = leechPiSlack := by
      funext x y
      simp [leechGaussianSlackComplete]
    rw [heq]
    simpa only [potentialEnergy] using leech_gaussian_pi_gap μ hμ hρ
  · have heq : leechGaussianSlackComplete α =
        gaussianSchwartzSlackPotential α (leechCertFamily α) := by
      funext x y
      simp only [leechGaussianSlackComplete, if_neg hαπ]
    rw [heq]
    simpa only [potentialEnergy] using
      leech_gaussian_gap hα hαπ μ hμ hρ

theorem leech_positiveGaussianMixture_potentialUnitCostInput_pi_atom
    (ν : Measure ℝ) (hmass : ν {π} ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞) :
    ∃ A : ℝ, 0 < A ∧
      PotentialUnitCostInput leechSet (positiveGaussianMixturePotential ν) 2 A (1 / 8) := by
  have hmass' : (ν.restrict (Ioi 0)) {π} ≠ 0 := by
    have hsub : ({π} : Set ℝ) ⊆ Ioi 0 := singleton_subset_iff.mpr Real.pi_pos
    rwa [Measure.restrict_apply (measurableSet_singleton π), inter_eq_left.mpr hsub]
  apply potentialUnitCostInput_of_mixture_quadratic_on_set (ν.restrict (Ioi 0)) leechSet
    (positiveGaussianMixturePotential ν) leechGaussianSlackComplete {π} (measurableSet_singleton π)
    hmass' leechPiCostCoefficient_pos (by norm_num)
  · intro α hα x y hxy
    have hαπ : α = π := hα
    subst α
    simpa [leechGaussianSlackComplete] using leechPiSlack_quadratic_lower hxy
  · intro μ hprob hμ hρ
    let _ := hprob
    exact leech_positiveGaussianMixture_complete_gap ν hbase μ hμ hρ

theorem leech_positiveGaussianMixture_potentialUnitCostInput_all
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞) :
    ∃ A : ℝ, 0 < A ∧
      PotentialUnitCostInput leechSet (positiveGaussianMixturePotential ν) 2 A (1 / 8) := by
  by_cases haway : ν (Ioi 0 \ {π}) ≠ 0
  · exact leech_positiveGaussianMixture_potentialUnitCostInput ν haway hbase
  · have hmass : ν {π} ≠ 0 := by
      intro hz
      apply hν
      apply measure_mono_null (t := (Ioi 0 \ {π}) ∪ {π})
      · intro α hα
        by_cases hαπ : α = π
        · exact Or.inr hαπ
        · exact Or.inl ⟨hα, hαπ⟩
      · exact measure_union_null (not_ne_iff.mp haway) hz
    exact leech_positiveGaussianMixture_potentialUnitCostInput_pi_atom ν hmass hbase

theorem leech_positiveGaussianMixture_crystallization_all_general
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    {γ : ℝ} (hγ : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent leechSet (positiveGaussianMixturePotential ν) γ := by
  obtain ⟨A, hA, hinput⟩ := leech_positiveGaussianMixture_potentialUnitCostInput_all ν hν hbase
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, hperiodic⟩ := leech_sectionwisePeriodicStabilityInput_holds
  exact potentialCrystallizationTargetForExponent_of_sectionwise_inputs leechSet isClosed_leechSet
    ⟨0, zero_mem_leechSet⟩ (fun _ hx _ hy => leechSet_sub hx hy) (positiveGaussianMixturePotential ν)
    2 A E B c η₀ (1 / 8) γ (by norm_num) hγ hA.le
    hE hB hc hη₀ (by norm_num) hinput hperiodic

theorem leech_positiveGaussianMixture_crystallization_all
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞) :
    PotentialCrystallizationTarget leechSet (positiveGaussianMixturePotential ν) :=
  leech_positiveGaussianMixture_crystallization_all_general ν hν hbase (by norm_num)

theorem leech_gaussian_crystallization_all_general {α γ : ℝ} (hα : 0 < α) (hγ : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent leechSet (gaussianPotential α) γ := by
  have hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential (Measure.dirac α)) ≠ ∞ := by
    rw [positiveGaussianMixturePotential_dirac hα]
    exact leech_gaussian_lattice_energy_ne_top hα
  simpa only [positiveGaussianMixturePotential_dirac hα] using
    leech_positiveGaussianMixture_crystallization_all_general (Measure.dirac α) (by simp [hα]) hbase hγ

end E8Leech
