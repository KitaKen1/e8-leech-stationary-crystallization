import E8Leech.E8UniformSlackNearPi
import E8Leech.GaussianGapRightLimit

/-!
# The E8 Gaussian at π and all positive E8 Gaussian mixtures

A common quadratic cost survives the right-parameter limit at π. Insert this
cost at the exceptional parameter of a new measurable slack family. The full
mixture gap then handles an atom at π, completing the E8 theorem for every
nonzero positive mixing measure with finite lattice energy.
No exceptional Schwartz witness is constructed or assumed.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Real SchwartzMap

theorem exists_e8_pi_quadratic_gap :
    ∃ k : ℝ, 0 < k ∧ ∀ μ : Measure (Configuration (Ambient 8)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 →
      latticePotentialEnergy e8Set (gaussianPotential π) +
        potentialEnergy (quadraticClosePairPotential k (Real.sqrt 2)) μ ≤
        potentialEnergy (gaussianPotential π) μ := by
  obtain ⟨b, k, hb, hk, hlower⟩ := e8_uniform_quadratic_slack_right_pi
  refine ⟨k, hk, ?_⟩
  intro μ hprob hμ hρ
  let _ := hprob
  apply gaussian_gap_of_right_parameter_interval e8Set μ
    (quadraticClosePairPotential k (Real.sqrt 2)) hb
  intro α hα
  have hα0 : 0 < α := Real.pi_pos.trans hα.1
  have hαπ : α ≠ π := hα.1.ne'
  have hV : ∀ x y : Ambient 8, quadraticClosePairPotential k (Real.sqrt 2) x y ≤
      gaussianSchwartzSlackPotential α (e8CertFamily e8KernelNonneg α) x y := by
    intro x y
    by_cases hxy : dist x y ≤ Real.sqrt 2
    · rw [quadraticClosePairPotential_of_dist_le k _ hxy]
      apply ENNReal.ofReal_le_ofReal
      have h := hlower α hα ‖x - y‖ ⟨norm_nonneg _, by simpa only [dist_eq_norm] using hxy⟩
      simpa only [e8SlackProfile_norm, dist_eq_norm, gaussianSchwartzSlackPotential] using h
    · simp only [quadraticClosePairPotential, max_eq_left (by linarith : Real.sqrt 2 - dist x y ≤ 0),
        zero_pow (by norm_num : 2 ≠ 0), mul_zero, ENNReal.ofReal_zero, zero_le]
  exact (add_le_add le_rfl (potentialEnergy_mono hV μ)).trans (e8_gaussian_gap hα0 hαπ μ hμ hρ)

def e8PiCostCoefficient : ℝ := exists_e8_pi_quadratic_gap.choose

def e8PiSlack : Ambient 8 → Ambient 8 → ℝ≥0∞ :=
  quadraticClosePairPotential e8PiCostCoefficient (Real.sqrt 2)

theorem e8PiCostCoefficient_pos : 0 < e8PiCostCoefficient :=
  exists_e8_pi_quadratic_gap.choose_spec.1

theorem measurable_e8PiSlack : Measurable (Function.uncurry e8PiSlack) :=
  measurable_quadraticClosePairPotential _ _

theorem e8_gaussian_pi_gap (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy e8Set (gaussianPotential π) + potentialEnergy e8PiSlack μ ≤
      potentialEnergy (gaussianPotential π) μ :=
  exists_e8_pi_quadratic_gap.choose_spec.2 μ inferInstance hμ hρ

theorem e8PiSlack_quadratic_lower {x y : Ambient 8} (hxy : dist x y ≤ Real.sqrt 2) :
    ENNReal.ofReal (e8PiCostCoefficient * (Real.sqrt 2 - dist x y) ^ 2) ≤ e8PiSlack x y := by
  rw [e8PiSlack, quadraticClosePairPotential_of_dist_le _ _ hxy]

theorem e8_gaussian_pi_potentialUnitCostInput :
    ∃ A : ℝ, 0 < A ∧ PotentialUnitCostInput e8Set (gaussianPotential π) (Real.sqrt 2) A (1 / 8) := by
  have hk := e8PiCostCoefficient_pos
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨(e8PiCostCoefficient * (Real.sqrt 2) ^ 2)⁻¹, by positivity,
    potentialUnitCostInput_of_full_quadratic_slack e8Set (gaussianPotential π) e8PiSlack hk hr ?_
      (fun _ _ hxy => e8PiSlack_quadratic_lower hxy)⟩
  intro μ hprob hμ hρ _
  let _ := hprob
  exact e8_gaussian_pi_gap μ hμ hρ

/-- A complete measurable family of energy slacks, with a positive quadratic cost at π. -/
def e8GaussianSlackComplete (α : ℝ) (x y : Ambient 8) : ℝ≥0∞ :=
  if α = π then e8PiSlack x y else gaussianSchwartzSlackPotential α (e8CertFamily e8KernelNonneg α) x y

theorem measurable_e8GaussianSlackComplete :
    Measurable (fun p : ℝ × (Ambient 8 × Ambient 8) => e8GaussianSlackComplete p.1 p.2.1 p.2.2) := by
  unfold e8GaussianSlackComplete
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    (measurable_e8PiSlack.comp measurable_snd)
    (measurable_gaussianSchwartzSlackPotential_family _ (measurable_e8CertFamily_re e8KernelNonneg))

theorem e8_positiveGaussianMixture_complete_gap (ν : Measure ℝ)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) +
      potentialEnergy (potentialMixture (ν.restrict (Ioi 0)) e8GaussianSlackComplete) μ ≤
      potentialEnergy (positiveGaussianMixturePotential ν) μ := by
  obtain ⟨z, hz, hne, -⟩ := e8Set_minimum_attained
  let := sigmaFinite_positive_parameter_restrict_of_lattice ν hz hne hbase
  apply expected_potentialMixture_gap (ν.restrict (Ioi 0)) μ gaussianPotential
    e8GaussianSlackComplete (measurable_gaussianPotential_joint 8)
    measurable_e8GaussianSlackComplete e8Set countable_e8Set
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  by_cases hαπ : α = π
  · subst α
    have heq : e8GaussianSlackComplete π = e8PiSlack := by
      funext x y
      simp [e8GaussianSlackComplete]
    rw [heq]
    simpa only [potentialEnergy] using e8_gaussian_pi_gap μ hμ hρ
  · have heq : e8GaussianSlackComplete α =
        gaussianSchwartzSlackPotential α (e8CertFamily e8KernelNonneg α) := by
      funext x y
      simp only [e8GaussianSlackComplete, if_neg hαπ]
    rw [heq]
    simpa only [potentialEnergy] using
      e8_gaussian_gap hα hαπ μ hμ hρ

theorem e8_positiveGaussianMixture_potentialUnitCostInput_pi_atom
    (ν : Measure ℝ) (hmass : ν {π} ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞) :
    ∃ A : ℝ, 0 < A ∧
      PotentialUnitCostInput e8Set (positiveGaussianMixturePotential ν) (Real.sqrt 2) A (1 / 8) := by
  have hmass' : (ν.restrict (Ioi 0)) {π} ≠ 0 := by
    have hsub : ({π} : Set ℝ) ⊆ Ioi 0 := singleton_subset_iff.mpr Real.pi_pos
    rwa [Measure.restrict_apply (measurableSet_singleton π), inter_eq_left.mpr hsub]
  apply potentialUnitCostInput_of_mixture_quadratic_on_set (ν.restrict (Ioi 0)) e8Set
    (positiveGaussianMixturePotential ν) e8GaussianSlackComplete {π} (measurableSet_singleton π)
    hmass' e8PiCostCoefficient_pos (Real.sqrt_pos.mpr (by norm_num))
  · intro α hα x y hxy
    have hαπ : α = π := hα
    subst α
    simpa [e8GaussianSlackComplete] using e8PiSlack_quadratic_lower hxy
  · intro μ hprob hμ hρ
    let _ := hprob
    exact e8_positiveGaussianMixture_complete_gap ν hbase μ hμ hρ

theorem e8_positiveGaussianMixture_potentialUnitCostInput_all
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞) :
    ∃ A : ℝ, 0 < A ∧
      PotentialUnitCostInput e8Set (positiveGaussianMixturePotential ν) (Real.sqrt 2) A (1 / 8) := by
  by_cases haway : ν (Ioi 0 \ {π}) ≠ 0
  · exact e8_positiveGaussianMixture_potentialUnitCostInput ν haway hbase
  · have hmass : ν {π} ≠ 0 := by
      intro hz
      apply hν
      apply measure_mono_null (t := (Ioi 0 \ {π}) ∪ {π})
      · intro α hα
        by_cases hαπ : α = π
        · exact Or.inr hαπ
        · exact Or.inl ⟨hα, hαπ⟩
      · exact measure_union_null (not_ne_iff.mp haway) hz
    exact e8_positiveGaussianMixture_potentialUnitCostInput_pi_atom ν hmass hbase

theorem e8_positiveGaussianMixture_crystallization_all_general
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    {γ : ℝ} (hγ : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent e8Set (positiveGaussianMixturePotential ν) γ := by
  obtain ⟨A, hA, hinput⟩ := e8_positiveGaussianMixture_potentialUnitCostInput_all ν hν hbase
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, hperiodic⟩ := e8_sectionwisePeriodicStabilityInput
  exact potentialCrystallizationTargetForExponent_of_sectionwise_inputs e8Set isClosed_e8Set
    ⟨0, zero_mem_e8⟩ (fun _ hx _ hy => e8Set_sub hx hy) (positiveGaussianMixturePotential ν)
    (Real.sqrt 2) A E B c η₀ (1 / 8) γ (Real.sqrt_pos.mpr (by norm_num)) hγ hA.le
    hE hB hc hη₀ (by norm_num) hinput hperiodic

theorem e8_positiveGaussianMixture_crystallization_all
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞) :
    PotentialCrystallizationTarget e8Set (positiveGaussianMixturePotential ν) :=
  e8_positiveGaussianMixture_crystallization_all_general ν hν hbase (by norm_num)

theorem e8_gaussian_crystallization_all_general {α γ : ℝ} (hα : 0 < α) (hγ : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent e8Set (gaussianPotential α) γ := by
  have hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential (Measure.dirac α)) ≠ ∞ := by
    rw [positiveGaussianMixturePotential_dirac hα]
    exact e8_gaussian_lattice_energy_ne_top hα
  simpa only [positiveGaussianMixturePotential_dirac hα] using
    e8_positiveGaussianMixture_crystallization_all_general (Measure.dirac α) (by simp [hα]) hbase hγ

end E8Leech
