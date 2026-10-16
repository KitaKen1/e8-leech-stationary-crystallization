import E8Leech.GaussianBaseline
import E8Leech.GaussianCertificateMeasurable

/-!
# Actual Gaussian-mixture gaps for E8 and Leech

Integrate the actual CKMRV certificates away from π and retain the full Gaussian
baseline at π. The mixing measure may have atoms, including an atom at π, and
needs neither a density nor a Riesz-energy hypothesis. The slack contribution
at π is zero; its strict quantitative cost is a separate remaining obligation.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Classical SchwartzMap

def gaussianCertificateSlackAwayFrom {d : ℕ} (β : ℝ)
    (f : ℝ → 𝓢(Ambient d, ℂ)) (α : ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  if α = β then 0 else gaussianSchwartzSlackPotential α (f α) x y

theorem measurable_gaussianCertificateSlackAwayFrom {d : ℕ} (β : ℝ)
    (f : ℝ → 𝓢(Ambient d, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient d => (f p.1 p.2).re)) :
    Measurable (fun p : ℝ × (Ambient d × Ambient d) =>
      gaussianCertificateSlackAwayFrom β f p.1 p.2.1 p.2.2) := by
  unfold gaussianCertificateSlackAwayFrom
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    measurable_const (measurable_gaussianSchwartzSlackPotential_family f hf)

theorem expected_positiveGaussianMixture_gap_of_certificates_except {d : ℕ}
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hbase : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞)
    (hgaussian : ∀ α : ℝ, 0 < α → latticePotentialEnergy Λ (gaussianPotential α) ≠ ∞)
    (β : ℝ) (f : ℝ → 𝓢(Ambient d, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient d => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → α ≠ β → GaussianSchwartzCertificate Λ α (f α))
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) +
      potentialEnergy (potentialMixture (ν.restrict (Ioi 0))
        (gaussianCertificateSlackAwayFrom β f)) μ ≤
      potentialEnergy (positiveGaussianMixturePotential ν) μ := by
  by_cases henergy : potentialEnergy (positiveGaussianMixturePotential ν) μ = ∞
  · rw [henergy]
    exact le_top
  let := sigmaFinite_positive_parameter_restrict_of_lattice ν hz hne hbase
  have hsecond := expected_unit_count_sq_ne_top_of_positiveGaussianMixture ν hν hz hne hbase
    μ 1 hρ (by simp) henergy
  have hbaseline := gaussian_baseline_of_certificates_except Λ β hgaussian
    (fun α hα hαβ => ⟨f α, hcert α hα hαβ⟩) μ hμ hρ hsecond
  apply expected_potentialMixture_gap (ν.restrict (Ioi 0)) μ gaussianPotential
    (gaussianCertificateSlackAwayFrom β f) (measurable_gaussianPotential_joint d)
    (measurable_gaussianCertificateSlackAwayFrom β f hf) Λ hΛ
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
  change latticePotentialEnergy Λ (gaussianPotential α) +
    potentialEnergy (gaussianCertificateSlackAwayFrom β f α) μ ≤
      potentialEnergy (gaussianPotential α) μ
  by_cases hαβ : α = β
  · have hv : gaussianCertificateSlackAwayFrom β f α = 0 := by
      funext x y
      simp [gaussianCertificateSlackAwayFrom, hαβ]
    have hz : potentialEnergy (0 : Ambient d → Ambient d → ℝ≥0∞) μ = 0 := by
      simp [potentialEnergy, orderedWindowEnergy]
    rw [hv, hz, add_zero]
    exact hbaseline α hα
  · have hv : gaussianCertificateSlackAwayFrom β f α = gaussianSchwartzSlackPotential α (f α) := by
      funext x y
      simp [gaussianCertificateSlackAwayFrom, hαβ]
    rw [hv]
    simpa only [potentialEnergy] using
      (hcert α hα hαβ).expected_gap_of_second_moment μ hμ hρ hsecond (hgaussian α hα)

def e8GaussianMixtureSlack (ν : Measure ℝ) : Ambient 8 → Ambient 8 → ℝ≥0∞ :=
  potentialMixture (ν.restrict (Ioi 0))
    (gaussianCertificateSlackAwayFrom Real.pi (e8CertFamily e8KernelNonneg))

def leechGaussianMixtureSlack (ν : Measure ℝ) : Ambient 24 → Ambient 24 → ℝ≥0∞ :=
  potentialMixture (ν.restrict (Ioi 0))
    (gaussianCertificateSlackAwayFrom Real.pi leechCertFamily)

theorem e8_positiveGaussianMixture_gap (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) +
      potentialEnergy (e8GaussianMixtureSlack ν) μ ≤
      potentialEnergy (positiveGaussianMixturePotential ν) μ := by
  obtain ⟨z, hz, hne, _⟩ := e8Set_minimum_attained
  exact expected_positiveGaussianMixture_gap_of_certificates_except ν hν e8Set countable_e8Set
    hz hne hbase (fun _ hα => e8_gaussian_lattice_energy_ne_top hα) Real.pi
    (e8CertFamily e8KernelNonneg) (measurable_e8CertFamily_re e8KernelNonneg)
    (fun _ hα hαπ => e8CertFamily_cert e8KernelNonneg hα hαπ) μ hμ hρ

theorem leech_positiveGaussianMixture_gap (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) +
      potentialEnergy (leechGaussianMixtureSlack ν) μ ≤
      potentialEnergy (positiveGaussianMixturePotential ν) μ := by
  obtain ⟨z, hz, hne, _⟩ := leechSet_minimum_attained
  exact expected_positiveGaussianMixture_gap_of_certificates_except ν hν leechSet countable_leechSet
    hz hne hbase (fun _ hα => leech_gaussian_lattice_energy_ne_top hα) Real.pi
    leechCertFamily measurable_leechCertFamily_re
    (fun _ hα hαπ => leechCertFamily_cert leechKernelInequalities leechFourierIdentities hα hαπ)
    μ hμ hρ

theorem e8_positiveGaussianMixture_baseline (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≤
      potentialEnergy (positiveGaussianMixturePotential ν) μ :=
  (le_add_right le_rfl).trans (e8_positiveGaussianMixture_gap ν hν hbase μ hμ hρ)

theorem leech_positiveGaussianMixture_baseline (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≤
      potentialEnergy (positiveGaussianMixturePotential ν) μ :=
  (le_add_right le_rfl).trans (leech_positiveGaussianMixture_gap ν hν hbase μ hμ hρ)

/-- A positive-parameter atom is exactly a single Gaussian potential. -/
theorem positiveGaussianMixturePotential_dirac {d : ℕ} {α : ℝ} (hα : 0 < α) :
    positiveGaussianMixturePotential (d := d) (Measure.dirac α) = gaussianPotential α := by
  funext x y
  simp [positiveGaussianMixturePotential, potentialMixture, restrict_dirac, hα]

/-- The exceptional atom has zero retained slack, while its full baseline is still included. -/
theorem gaussianCertificateSlackAwayFrom_atom {d : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : ℝ → 𝓢(Ambient d, ℂ)) :
    potentialMixture ((Measure.dirac β).restrict (Ioi 0))
      (gaussianCertificateSlackAwayFrom β f) = 0 := by
  funext x y
  simp [potentialMixture, restrict_dirac, hβ,
    gaussianCertificateSlackAwayFrom]

end E8Leech
