import E8Leech.LeechCrystallization
import E8Leech.PotentialCrystallization

/-!
# The actual Gaussian lattice lower bound, including the exceptional parameter

The existing CKMRV certificates apply for `α ≠ π`. To fill `α = π`, approach
from larger parameters. The process Gaussian energy can only decrease, while
every finite lattice sum converges to its value at `π`. Taking the supremum over
finite sums proves the full lower bound without a certificate at the excluded
parameter. Positive mixtures then follow by nonnegative integration.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem gaussianPotential_antitone {d : ℕ} {a b : ℝ} (hab : a ≤ b)
    (x y : Ambient d) : gaussianPotential b x y ≤ gaussianPotential a x y := by
  unfold gaussianPotential gaussianKernel
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖x - y‖]

theorem gaussianPotentialEnergy_antitone {d : ℕ} (μ : Measure (Configuration (Ambient d))) :
    Antitone (fun α : ℝ => potentialEnergy (gaussianPotential α) μ) := by
  intro a b hab
  exact lintegral_mono fun c => orderedWindowEnergy_mono_potential
    (gaussianPotential_antitone hab) c (unitWindow d)

/-- A Gaussian lower bound on the right of one parameter extends to that parameter. -/
theorem gaussian_baseline_of_right_parameters {d : ℕ}
    (Λ : Set (Ambient d)) (μ : Measure (Configuration (Ambient d))) (β : ℝ)
    (h : ∀ α : ℝ, β < α → latticePotentialEnergy Λ (gaussianPotential α) ≤
      potentialEnergy (gaussianPotential α) μ) :
    latticePotentialEnergy Λ (gaussianPotential β) ≤ potentialEnergy (gaussianPotential β) μ := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hseq : Tendsto (fun n : ℕ => β + ((n : ℝ) + 1)⁻¹) atTop (𝓝 β) := by
    simpa using tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp hnat)
  rw [latticePotentialEnergy, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hc : Continuous (fun α : ℝ => ∑ y ∈ s,
      if (y : Ambient d) = 0 then 0 else gaussianPotential α 0 (y : Ambient d)) := by
    apply continuous_finsetSum
    intro y _
    split_ifs
    · exact continuous_const
    · unfold gaussianPotential gaussianKernel
      exact ENNReal.continuous_ofReal.comp (by fun_prop)
  apply le_of_tendsto (hc.tendsto β |>.comp hseq)
  apply Eventually.of_forall
  intro n
  have hn : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
  calc
    _ ≤ latticePotentialEnergy Λ (gaussianPotential (β + ((n : ℝ) + 1)⁻¹)) :=
      ENNReal.sum_le_tsum _
    _ ≤ potentialEnergy (gaussianPotential (β + ((n : ℝ) + 1)⁻¹)) μ := h _ (by linarith)
    _ ≤ _ := gaussianPotentialEnergy_antitone μ (by linarith)

/-- The complete Gaussian baseline from certificates off one positive parameter. -/
theorem gaussian_baseline_of_certificates_except {d : ℕ}
    (Λ : Set (Ambient d)) (β : ℝ)
    (hfinite : ∀ α : ℝ, 0 < α → latticePotentialEnergy Λ (gaussianPotential α) ≠ ∞)
    (hcert : ∀ α : ℝ, 0 < α → α ≠ β →
      ∃ f : SchwartzMap (Ambient d) ℂ, GaussianSchwartzCertificate Λ α f)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (hsecond : (∫⁻ c, c.count (unitWindow d) ^ 2 ∂μ) ≠ ∞) :
    ∀ α : ℝ, 0 < α → latticePotentialEnergy Λ (gaussianPotential α) ≤
      potentialEnergy (gaussianPotential α) μ := by
  have hregular : ∀ α : ℝ, 0 < α → α ≠ β →
      latticePotentialEnergy Λ (gaussianPotential α) ≤ potentialEnergy (gaussianPotential α) μ := by
    intro α hα hαβ
    obtain ⟨f, hf⟩ := hcert α hα hαβ
    exact (le_add_right le_rfl).trans
      (hf.expected_gap_of_second_moment μ hμ hρ hsecond (hfinite α hα))
  intro α hα
  by_cases heq : α = β
  · subst α
    exact gaussian_baseline_of_right_parameters Λ μ β fun a ha =>
      hregular a (hα.trans ha) (ne_of_gt ha)
  · exact hregular α hα heq

theorem e8_gaussian_baseline {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (hsecond : (∫⁻ c, c.count (unitWindow 8) ^ 2 ∂μ) ≠ ∞) :
    latticePotentialEnergy e8Set (gaussianPotential α) ≤ potentialEnergy (gaussianPotential α) μ := by
  apply gaussian_baseline_of_certificates_except e8Set Real.pi
    (fun _ ha => e8_gaussian_lattice_energy_ne_top ha) ?_ μ hμ hρ hsecond α hα
  intro a ha hapi
  exact ⟨e8CertFamily e8KernelNonneg a, e8CertFamily_cert e8KernelNonneg ha hapi⟩

theorem leech_gaussian_baseline {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (hsecond : (∫⁻ c, c.count (unitWindow 24) ^ 2 ∂μ) ≠ ∞) :
    latticePotentialEnergy leechSet (gaussianPotential α) ≤
      potentialEnergy (gaussianPotential α) μ := by
  apply gaussian_baseline_of_certificates_except leechSet Real.pi
    (fun _ ha => leech_gaussian_lattice_energy_ne_top ha) ?_ μ hμ hρ hsecond α hα
  intro a ha hapi
  exact ⟨leechCertFamily a, leechCertFamily_cert leechKernelInequalities leechFourierIdentities
    ha hapi⟩

end E8Leech
