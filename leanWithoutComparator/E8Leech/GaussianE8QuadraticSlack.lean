import E8Leech.GaussianSlackDuality
import E8Leech.GaussianSeparatedKernelBlock
import E8Leech.GaussianMixtureGap

/-!
# Full-radius quadratic slack for every nonexceptional E8 Gaussian

Actual Fourier duality supplies the origin, a separated positive kernel block
supplies the interior and the quadratic behavior at the shortest radius, and
spatial compactness pastes the two bounds. No Riesz-energy assumption is used.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Real SchwartzMap FourierTransform

theorem continuous_e8SlackProfile_radius (hP : E8KernelNonneg) (α : ℝ) :
    Continuous (fun u : ℝ => e8SlackProfile hP (α, u)) := by
  simp only [e8SlackProfile]
  exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-α * u ^ 2))).sub
    (Complex.continuous_re.comp ((e8CertFamily hP α).continuous.comp
      (continuous_id.smul continuous_const)))

theorem e8_gaussian_slack_interior_pos (hP : E8KernelNonneg) {α u : ℝ}
    (hα : 0 < α) (hαπ : α ≠ π) (hu : 0 < u) (hur : u < Real.sqrt 2) :
    0 < e8SlackProfile hP (α, u) := by
  obtain ⟨B, hB, hblock⟩ := e8_gaussian_separated_block_lower hα le_rfl
  have hq : π / α ∈ Icc (π / α) (π / α) := ⟨le_rfl, le_rfl⟩
  have hq1 : π / α ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq hα.ne').mp h).symm
  have hu2 : u ^ 2 < 2 := by
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hI := laplace_factor_lower_from_shifted_block
    (gaussianSeparatedBlockStart_pos α α) (by linarith only [hu2] : u ^ 2 ≤ 4)
    (fun t ht => hP _ t (div_pos Real.pi_pos hα) ht) (hblock _ hq)
    (integrableOn_e8DualKernel (div_pos Real.pi_pos hα) hq1 hu.ne')
  have hIpos : 0 < ∫ t in Ioi (0 : ℝ), e8DualKernel (π / α, t) *
      Real.exp (-π * u ^ 2 * t) := (mul_pos hB (Real.exp_pos _)).trans_le hI
  have hsin : 0 < Real.sin (π * u ^ 2 / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  rw [e8SlackProfile_eq hP hα hαπ hu]
  exact mul_pos (by positivity) (mul_pos (by positivity) hIpos)

theorem e8_gaussian_full_quadratic_slack (hP : E8KernelNonneg) {α : ℝ}
    (hα : 0 < α) (hαπ : α ≠ π) :
    ∃ k : ℝ, 0 < k ∧ ∀ u ∈ Icc (0 : ℝ) (Real.sqrt 2),
      k * (Real.sqrt 2 - u) ^ 2 ≤ e8SlackProfile hP (α, u) := by
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hq1 : π / α ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq hα.ne').mp h).symm
  have hc : Continuous (fun p : ℝ × ℝ => e8SlackProfile hP (α, p.2)) :=
    (continuous_e8SlackProfile_radius hP α).comp continuous_snd
  have hreg := gaussian_separated_rectangle_regular hα le_rfl
  obtain ⟨k, hk, hlower⟩ := uniform_full_quadratic_slack_of_shifted_laplace_kernel
    4 hα le_rfl hr (Or.inl (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)))
    (gaussianSeparatedBlockStart_pos α α) (e8SlackProfile hP) e8DualKernel
    (hc.continuousOn.congr (fun p hp => by
      have hpα : p.1 = α := le_antisymm hp.1.2 hp.1.1
      change e8SlackProfile hP (p.1, p.2) = e8SlackProfile hP (α, p.2)
      rw [hpα]))
    (fun β hβ => by
      have hβα : β = α := le_antisymm hβ.2 hβ.1
      subst β
      simpa only [e8SlackProfile, zero_smul, pow_two, mul_zero, neg_zero,
        Real.exp_zero, gaussianKernel, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
        e8_gaussian_slack_origin_pos hP hα hαπ)
    (fun β hβ u hu hur => by
      have hβα : β = α := le_antisymm hβ.2 hβ.1
      subst β
      exact e8_gaussian_slack_interior_pos hP hα hαπ hu hur)
    (continuousOn_e8DualKernel_separated hα le_rfl)
    (fun p hp => ckmrvEightHatKernel_pos
      ((div_pos Real.pi_pos hα).trans_le hp.1.1)
      ((gaussianSeparatedBlockStart_pos α α).trans_le hp.2.1)
      (sub_ne_zero.mp (hreg hp)))
    (fun q hq t ht => hP q t ((div_pos Real.pi_pos hα).trans_le hq.1) ht)
    (fun β hβ u hu => by
      have hβα : β = α := le_antisymm hβ.2 hβ.1
      subst β
      exact integrableOn_e8DualKernel (div_pos Real.pi_pos hα) hq1
        (ne_of_gt (by linarith only [hu.1, hr])))
    (fun β hβ u hu => by
      have hβα : β = α := le_antisymm hβ.2 hβ.1
      subst β
      exact e8SlackProfile_eq hP hα hαπ (by linarith only [hu.1, hr]))
  exact ⟨k, hk, fun u hu => hlower α ⟨le_rfl, le_rfl⟩ u hu⟩

theorem e8_gaussian_full_quadratic_slack_norm (hP : E8KernelNonneg) {α : ℝ}
    (hα : 0 < α) (hαπ : α ≠ π) :
    ∃ k : ℝ, 0 < k ∧ ∀ v : Ambient 8, ‖v‖ ≤ Real.sqrt 2 →
      k * (Real.sqrt 2 - ‖v‖) ^ 2 ≤ gaussianKernel α v - (e8CertFamily hP α v).re := by
  obtain ⟨k, hk, h⟩ := e8_gaussian_full_quadratic_slack hP hα hαπ
  exact ⟨k, hk, fun v hv => by simpa only [e8SlackProfile_norm] using h ‖v‖ ⟨norm_nonneg v, hv⟩⟩

theorem e8_gaussian_gap {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy e8Set (gaussianPotential α) +
      potentialEnergy (gaussianSchwartzSlackPotential α (e8CertFamily e8KernelNonneg α)) μ ≤
      potentialEnergy (gaussianPotential α) μ := by
  have hbase : latticePotentialEnergy e8Set
      (positiveGaussianMixturePotential (Measure.dirac α)) ≠ ∞ := by
    rw [positiveGaussianMixturePotential_dirac hα]
    exact e8_gaussian_lattice_energy_ne_top hα
  have h := e8_positiveGaussianMixture_gap (Measure.dirac α) (by simp [hα]) hbase μ hμ hρ
  have hv : e8GaussianMixtureSlack (Measure.dirac α) =
      gaussianSchwartzSlackPotential α (e8CertFamily e8KernelNonneg α) := by
    funext x y
    simp [e8GaussianMixtureSlack, potentialMixture, restrict_dirac, hα,
      gaussianCertificateSlackAwayFrom, hαπ]
  simpa only [positiveGaussianMixturePotential_dirac hα, hv] using h

theorem e8_gaussian_potentialUnitCostInput {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) :
    ∃ A : ℝ, 0 < A ∧
      PotentialUnitCostInput e8Set (gaussianPotential α) (Real.sqrt 2) A (1 / 8) := by
  obtain ⟨k, hk, hquad⟩ := e8_gaussian_full_quadratic_slack_norm e8KernelNonneg hα hαπ
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨(k * (Real.sqrt 2) ^ 2)⁻¹, by positivity,
    potentialUnitCostInput_of_full_quadratic_slack e8Set (gaussianPotential α)
      (gaussianSchwartzSlackPotential α (e8CertFamily e8KernelNonneg α)) hk hr ?_ ?_⟩
  · intro μ hprob hμ hρ _
    let _ := hprob
    exact e8_gaussian_gap hα hαπ μ hμ hρ
  · intro x y hxy
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [dist_eq_norm] using hquad (x - y) (by simpa only [dist_eq_norm] using hxy))

/-- Quantitative crystallization for a single Gaussian, with no Riesz-energy hypothesis. -/
theorem e8_gaussian_crystallization {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) :
    PotentialCrystallizationTarget e8Set (gaussianPotential α) := by
  obtain ⟨A, hA, hinput⟩ := e8_gaussian_potentialUnitCostInput hα hαπ
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, hperiodic⟩ := e8_sectionwisePeriodicStabilityInput
  exact potentialCrystallizationTarget_of_sectionwise_inputs e8Set isClosed_e8Set
    ⟨0, zero_mem_e8⟩ (fun _ hx _ hy => e8Set_sub hx hy) (gaussianPotential α)
    (Real.sqrt 2) A E B c η₀ (1 / 8) (Real.sqrt_pos.mpr (by norm_num)) hA.le
    hE hB hc hη₀ (by norm_num) hinput hperiodic

end E8Leech
