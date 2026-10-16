import E8Leech.GaussianSlackDuality
import E8Leech.GaussianSeparatedKernelBlock
import E8Leech.GaussianMixtureGap
import E8Leech.LeechStrictCuspLead

/-!
# Full-radius quadratic slack for every nonexceptional Leech Gaussian

Strict cusp positivity handles the small-radius truncated profile, while the
separated positive block handles the Laplace range. The resulting Gaussian
unit cost and crystallization theorem require no Riesz-energy hypothesis.
-/

noncomputable section
set_option maxHeartbeats 600000
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Real SchwartzMap FourierTransform

theorem leechHatProfile_re_pos_small {q b : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    (hb : 0 < b) (hbmax : b ≤ 2 * π) : 0 < (leechAxisRadialProfile (-1) q b).re := by
  have hfin : volume ({q, q⁻¹} : Set ℝ) = 0 := (Set.toFinite {q, q⁻¹}).measure_zero _
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({q, q⁻¹} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hfin
  have hI₁ : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, leechDualKernel (q, t) * Real.exp (-b * t) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioc] with t ht ht01
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    exact mul_nonneg (leechKernelInequalities.hat_nonneg q t hq ht01.1 ht.1 ht.2)
      (Real.exp_pos _).le
  have hI₂ : 0 ≤ ∫ t in Ioi (1 : ℝ), (leechDualKernel (q, t) -
      ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
        Real.exp (2 * π * t)) * Real.exp (-b * t) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioi] with t ht ht1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    exact mul_nonneg (sub_nonneg.mpr
      (leechKernelInequalities.hat_trunc q t hq hq1 ht1.le ht.1 ht.2)) (Real.exp_pos _).le
  have hR : |(b - 2 * π) / 2| < π := abs_lt.mpr ⟨by linarith, by linarith [Real.pi_pos]⟩
  obtain ⟨σ, hσ, hσlow⟩ := exists_sinc_lower (abs_nonneg ((b - 2 * π) / 2)) hR
  have hsinc : 0 < Real.sinc ((b - 2 * π) / 2) :=
    hσ.trans_le (hσlow _ ⟨neg_abs_le _, le_abs_self _⟩)
  have hbr : 0 < (leechAxisCusp (-1) q 0).re +
      ((leechAxisCusp (-1) q 1).re + 1 * (leechAxisCusp (-1) q 0).re) * (b - 2 * π) := by
    have hs := (leechAxisCusp_sum_neg hq).le
    have hp := mul_nonneg_of_nonpos_of_nonpos hs (sub_nonpos.mpr hbmax)
    nlinarith [leechAxisCusp_lead_pos_all hq]
  rw [leechHatProfile_re_eq hq hq1 hb]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) (add_nonneg hI₁ hI₂))
    (mul_pos (mul_pos (pow_pos hsinc 2) (Real.exp_pos _)) hbr)

theorem leechDualKernelReg_eq_of_regular {q t : ℝ} (hq : 0 < q)
    (hreg : (imagPt q, imagPt t) ∈ ckmrvRegularLocus) :
    leechDualKernelReg (q, t) = leechDualKernel (q, t) := by
  have hJ : kleinModularJ (imagPt q) ≠ kleinModularJ (imagPt t) := sub_ne_zero.mp hreg
  apply leechDualKernelReg_of_ne
  · intro h
    exact hJ (by rw [h])
  · intro h
    exact hJ (by rw [h, Kron.kleinModularJ_imagPt_inv hq])

theorem integrableOn_leechDualKernelReg {q u : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    (hu : 2 < u ^ 2) :
    IntegrableOn (fun t => leechDualKernelReg (q, t) * Real.exp (-π * u ^ 2 * t)) (Ioi 0) := by
  apply (integrableOn_leechDualKernel hq hq1 hu).congr_fun_ae
  filter_upwards [ae_restrict_of_ae (leechDualKernelReg_ae q)] with t ht
  rw [ht]

theorem leechSlackProfile_eq_laplace_reg {α u : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (hu0 : 0 ≤ u) (hu : 2 < u ^ 2) :
    leechSlackProfile (α, u) = (π / α) ^ 12 * (4 * Real.sin (π * u ^ 2 / 2) ^ 2 *
      ∫ t in Ioi (0 : ℝ), leechDualKernelReg (π / α, t) * Real.exp (-π * u ^ 2 * t)) := by
  rw [leechSlackProfile_eq_laplace hα hαπ hu0 hu]
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (leechDualKernelReg_ae (π / α))] with t ht
  rw [ht]

theorem continuous_leechSlackProfile_radius (α : ℝ) :
    Continuous (fun u : ℝ => leechSlackProfile (α, u)) := by
  simp only [leechSlackProfile]
  exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-α * u ^ 2))).sub
    (Complex.continuous_re.comp ((leechCertFamily α).continuous.comp
      (continuous_id.smul continuous_const)))

theorem leech_gaussian_slack_interior_pos {α u : ℝ}
    (hα : 0 < α) (hαπ : α ≠ π) (hu : 0 < u) (hur : u < 2) :
    0 < leechSlackProfile (α, u) := by
  have hq0 : 0 < π / α := div_pos Real.pi_pos hα
  have hq1 : π / α ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq hα.ne').mp h).symm
  by_cases hu2 : u ^ 2 ≤ 2
  · rw [leechSlackProfile_eq hα hαπ hu.le]
    exact mul_pos (by positivity) (leechHatProfile_re_pos_small hq0 hq1 (by positivity)
      (by nlinarith [Real.pi_pos]))
  · have hu2' : 2 < u ^ 2 := lt_of_not_ge hu2
    obtain ⟨B, hB, hblock⟩ := leech_gaussian_separated_block_lower hα le_rfl
    have hq : π / α ∈ Icc (π / α) (π / α) := ⟨le_rfl, le_rfl⟩
    have hblockreg : ∀ t ∈ Icc (gaussianSeparatedBlockStart α α)
        (gaussianSeparatedBlockStart α α + 1), B ≤ leechDualKernelReg (π / α, t) := by
      intro t ht
      have hs : ckmrvImaginaryPair (π / α, t) ∈ ckmrvRegularLocus :=
        gaussian_separated_rectangle_regular (a := α) (b := α) hα le_rfl ⟨hq, ht⟩
      rw [leechDualKernelReg_eq_of_regular (q := π / α) (t := t) hq0 hs]
      exact hblock _ hq t ht
    have hI := laplace_factor_lower_from_shifted_block (gaussianSeparatedBlockStart_pos α α)
      (by nlinarith : u ^ 2 ≤ 4)
      (fun t ht => leechDualKernelReg_nonneg leechKernelInequalities hq0 ht)
      hblockreg (integrableOn_leechDualKernelReg hq0 hq1 hu2')
    have hIpos : 0 < ∫ t in Ioi (0 : ℝ), leechDualKernelReg (π / α, t) *
        Real.exp (-π * u ^ 2 * t) := (mul_pos hB (Real.exp_pos _)).trans_le hI
    have hu4 : u ^ 2 < 4 := by nlinarith
    have hangle : π < π * u ^ 2 / 2 ∧ π * u ^ 2 / 2 < 2 * π := by
      constructor <;> nlinarith [mul_lt_mul_of_pos_left hu2' Real.pi_pos,
        mul_lt_mul_of_pos_left hu4 Real.pi_pos]
    have hsin : Real.sin (π * u ^ 2 / 2) ≠ 0 := by
      have hs := Real.sin_pos_of_pos_of_lt_pi
        (sub_pos.mpr hangle.1) (by linarith only [hangle.2] : π * u ^ 2 / 2 - π < π)
      rw [Real.sin_sub_pi] at hs
      exact (neg_pos.mp hs).ne
    rw [leechSlackProfile_eq_laplace_reg hα hαπ hu.le hu2']
    exact mul_pos (by positivity) (mul_pos (by positivity) hIpos)

theorem leech_gaussian_full_quadratic_slack {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) :
    ∃ k : ℝ, 0 < k ∧ ∀ u ∈ Icc (0 : ℝ) 2,
      k * (2 - u) ^ 2 ≤ leechSlackProfile (α, u) := by
  have hq0 : 0 < π / α := div_pos Real.pi_pos hα
  have hq1 : π / α ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq hα.ne').mp h).symm
  have hc : Continuous (fun p : ℝ × ℝ => leechSlackProfile (α, p.2)) :=
    (continuous_leechSlackProfile_radius α).comp continuous_snd
  have hreg := gaussian_separated_rectangle_regular hα le_rfl
  have heq : ∀ p ∈ Icc (π / α) (π / α) ×ˢ
      Icc (gaussianSeparatedBlockStart α α) (gaussianSeparatedBlockStart α α + 1),
      leechDualKernelReg p = leechDualKernel p := by
    intro p hp
    exact leechDualKernelReg_eq_of_regular (q := p.1) (t := p.2)
      (hq0.trans_le hp.1.1) (hreg hp)
  obtain ⟨k, hk, hlower⟩ := uniform_full_quadratic_slack_of_shifted_laplace_kernel
    12 hα le_rfl (by norm_num : (0 : ℝ) < 2) (Or.inr (by norm_num : (2 : ℝ) ^ 2 = 4))
    (gaussianSeparatedBlockStart_pos α α) leechSlackProfile leechDualKernelReg
    (hc.continuousOn.congr (fun p hp => by
      have hpα : p.1 = α := le_antisymm hp.1.2 hp.1.1
      change leechSlackProfile (p.1, p.2) = leechSlackProfile (α, p.2)
      rw [hpα]))
    (fun β hβ => by
      have hβα : β = α := le_antisymm hβ.2 hβ.1
      subst β
      simpa only [leechSlackProfile, zero_smul, pow_two, mul_zero, neg_zero,
        Real.exp_zero, gaussianKernel, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
        leech_gaussian_slack_origin_pos hα hαπ)
    (fun β hβ u hu hur => by
      have hβα : β = α := le_antisymm hβ.2 hβ.1
      subst β
      exact leech_gaussian_slack_interior_pos hα hαπ hu hur)
    ((continuousOn_leechDualKernel_separated hα le_rfl).congr heq)
    (fun p hp => by
      rw [heq p hp]
      exact ckmrvLeechHatKernel_pos (hq0.trans_le hp.1.1)
        ((gaussianSeparatedBlockStart_pos α α).trans_le hp.2.1) (sub_ne_zero.mp (hreg hp)))
    (fun q hq t ht => leechDualKernelReg_nonneg leechKernelInequalities (hq0.trans_le hq.1) ht)
    (fun β hβ u hu => by
      have hβα : β = α := le_antisymm hβ.2 hβ.1
      subst β
      exact integrableOn_leechDualKernelReg hq0 hq1 (by nlinarith [hu.1]))
    (fun β hβ u hu => by
      have hβα : β = α := le_antisymm hβ.2 hβ.1
      subst β
      exact leechSlackProfile_eq_laplace_reg hα hαπ (by linarith [hu.1])
        (by nlinarith [hu.1]))
  exact ⟨k, hk, fun u hu => hlower α ⟨le_rfl, le_rfl⟩ u hu⟩

theorem leech_gaussian_full_quadratic_slack_norm {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) :
    ∃ k : ℝ, 0 < k ∧ ∀ v : Ambient 24, ‖v‖ ≤ 2 →
      k * (2 - ‖v‖) ^ 2 ≤ gaussianKernel α v - (leechCertFamily α v).re := by
  obtain ⟨k, hk, h⟩ := leech_gaussian_full_quadratic_slack hα hαπ
  exact ⟨k, hk, fun v hv => by simpa only [leechSlackProfile_norm] using h ‖v‖ ⟨norm_nonneg v, hv⟩⟩

theorem leech_gaussian_gap {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy leechSet (gaussianPotential α) +
      potentialEnergy (gaussianSchwartzSlackPotential α (leechCertFamily α)) μ ≤
      potentialEnergy (gaussianPotential α) μ := by
  have hbase : latticePotentialEnergy leechSet
      (positiveGaussianMixturePotential (Measure.dirac α)) ≠ ∞ := by
    rw [positiveGaussianMixturePotential_dirac hα]
    exact leech_gaussian_lattice_energy_ne_top hα
  have h := leech_positiveGaussianMixture_gap (Measure.dirac α) (by simp [hα]) hbase μ hμ hρ
  have hv : leechGaussianMixtureSlack (Measure.dirac α) =
      gaussianSchwartzSlackPotential α (leechCertFamily α) := by
    funext x y
    simp [leechGaussianMixtureSlack, potentialMixture, restrict_dirac, hα,
      gaussianCertificateSlackAwayFrom, hαπ]
  simpa only [positiveGaussianMixturePotential_dirac hα, hv] using h

theorem leech_gaussian_potentialUnitCostInput {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) :
    ∃ A : ℝ, 0 < A ∧ PotentialUnitCostInput leechSet (gaussianPotential α) 2 A (1 / 8) := by
  obtain ⟨k, hk, hquad⟩ := leech_gaussian_full_quadratic_slack_norm hα hαπ
  refine ⟨(k * 2 ^ 2)⁻¹, by positivity,
    potentialUnitCostInput_of_full_quadratic_slack leechSet (gaussianPotential α)
      (gaussianSchwartzSlackPotential α (leechCertFamily α)) hk (by norm_num) ?_ ?_⟩
  · intro μ hprob hμ hρ _
    let _ := hprob
    exact leech_gaussian_gap hα hαπ μ hμ hρ
  · intro x y hxy
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [dist_eq_norm] using hquad (x - y) (by simpa only [dist_eq_norm] using hxy))

theorem leech_gaussian_crystallization {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) :
    PotentialCrystallizationTarget leechSet (gaussianPotential α) := by
  obtain ⟨A, hA, hinput⟩ := leech_gaussian_potentialUnitCostInput hα hαπ
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, hperiodic⟩ := leech_sectionwisePeriodicStabilityInput_holds
  exact potentialCrystallizationTarget_of_sectionwise_inputs leechSet isClosed_leechSet
    ⟨0, zero_mem_leechSet⟩ (fun _ hx _ hy => leechSet_sub hx hy) (gaussianPotential α)
    2 A E B c η₀ (1 / 8) (by norm_num) hA.le hE hB hc hη₀ (by norm_num) hinput hperiodic

end E8Leech
