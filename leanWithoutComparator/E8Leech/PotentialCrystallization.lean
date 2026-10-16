import E8Leech.PositiveMixtureCertificates
import E8Leech.SectionwiseBRR
import E8Leech.ShiftedLaplaceSlack

/-!
# The full quantitative target and transfer for positive Gaussian mixtures

The potential may be extended-valued. The finite lattice baseline is retained,
constants precede the law and excess, and the measurable event contains all
original points in the closed observation ball. The geometric transfer does not
use a Riesz representation. Actual function certificates, compact quadratic
slack and periodic packing/BRR geometry remain explicit proof inputs.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Classical SchwartzMap FourierTransform

def potentialEnergy {d : ℕ} (P : Ambient d → Ambient d → ℝ≥0∞)
    (μ : Measure (Configuration (Ambient d))) : ℝ≥0∞ :=
  ∫⁻ z, orderedWindowEnergy P z (unitWindow d) ∂μ

def HasPotentialExcessAtMost {d : ℕ} (P : Ambient d → Ambient d → ℝ≥0∞)
    (μ : Measure (Configuration (Ambient d))) (L δ : ℝ≥0∞) : Prop :=
  L ≠ ∞ ∧ potentialEnergy P μ ≤ L + δ

def PotentialCrystallizationTarget {d : ℕ} (Λ : Set (Ambient d))
    (P : Ambient d → Ambient d → ℝ≥0∞) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
    ∀ μ : Measure (Configuration (Ambient d)),
      IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        HasPotentialExcessAtMost P μ (latticePotentialEnergy Λ P) (ENNReal.ofReal δ) →
        ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
          G ⊆ {z | LocalCrystal Λ z (observationRadius δ)
            (C * δ ^ (1 / 13 : ℝ)) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
          ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G

structure PotentialUnitCostInput {d : ℕ} (Λ : Set (Ambient d))
    (P : Ambient d → Ambient d → ℝ≥0∞) (r A δA : ℝ) : Prop where
  cost : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
    IsStationary μ → HasIntensity μ 1 →
    ∀ δ : ℝ, 0 < δ → δ < δA →
    HasPotentialExcessAtMost P μ (latticePotentialEnergy Λ P) (ENNReal.ofReal δ) →
    ∃ κ cost : ℝ≥0∞, ∃ V : Ambient d → Ambient d → ℝ≥0∞,
      κ ≠ 0 ∧ κ ≠ ∞ ∧ cost / κ ≤ ENNReal.ofReal (A * δ ^ (1 / 3 : ℝ)) ∧
      (∀ x y, x ≠ y → dist x y < r * (1 - δ ^ (1 / 3 : ℝ)) → κ ≤ V x y) ∧
      (∫⁻ z, orderedWindowEnergy V z (unitWindow d) ∂μ) ≤ cost

theorem potentialEnergy_riesz {d : ℕ} (s : ℝ)
    (μ : Measure (Configuration (Ambient d))) : potentialEnergy (rieszPotential s) μ = rieszEnergy s μ := rfl

theorem hasPotentialExcessAtMost_riesz_iff {d : ℕ} (s : ℝ)
    (μ : Measure (Configuration (Ambient d))) (L δ : ℝ≥0∞) :
    HasPotentialExcessAtMost (rieszPotential s) μ L δ ↔ HasRieszExcessAtMost s μ L δ := Iff.rfl

theorem stationaryCrystallizationFor_iff_potentialTargets {d : ℕ} (Λ : Set (Ambient d)) :
    StationaryCrystallizationFor Λ ↔
      ∀ s : ℝ, (d : ℝ) < s → PotentialCrystallizationTarget Λ (rieszPotential s) := Iff.rfl

theorem potentialEnergy_ne_top_of_excess {d : ℕ}
    {P : Ambient d → Ambient d → ℝ≥0∞} {μ : Measure (Configuration (Ambient d))}
    {L δ : ℝ≥0∞} (hδ : δ ≠ ∞) (hexcess : HasPotentialExcessAtMost P μ L δ) :
    potentialEnergy P μ ≠ ∞ :=
  ne_of_lt (hexcess.2.trans_lt (ENNReal.add_ne_top.mpr ⟨hexcess.1, hδ⟩).lt_top)

theorem expected_potential_slack_le_of_excess {d : ℕ}
    {P V : Ambient d → Ambient d → ℝ≥0∞} {μ : Measure (Configuration (Ambient d))}
    {L δ : ℝ≥0∞} (hexcess : HasPotentialExcessAtMost P μ L δ)
    (hgap : L + potentialEnergy V μ ≤ potentialEnergy P μ) : potentialEnergy V μ ≤ δ :=
  ENNReal.le_of_add_le_add_left hexcess.1 (hgap.trans hexcess.2)

theorem potentialUnitCostInput_of_quadratic_slack {d : ℕ}
    (Λ : Set (Ambient d)) (P V : Ambient d → Ambient d → ℝ≥0∞)
    (k r : ℝ) (hk : 0 < k)
    (hgap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 → potentialEnergy P μ ≠ ∞ →
      latticePotentialEnergy Λ P + potentialEnergy V μ ≤ potentialEnergy P μ)
    (hlower : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ x y, x ≠ y →
      dist x y < r * (1 - t) → ENNReal.ofReal (k * t ^ 2) ≤ V x y) :
    PotentialUnitCostInput Λ P r k⁻¹ (1 / 8) := by
  constructor
  intro μ hprob hμ hρ δ hδ hsmall hexcess
  let _ := hprob
  let t := δ ^ (1 / 3 : ℝ)
  have ht : 0 < t := Real.rpow_pos_of_pos hδ _
  have hhalf : t ≤ 1 / 2 := one_third_cutoff_le_half hδ.le hsmall.le
  have hkt : 0 < k * t ^ 2 := mul_pos hk (pow_pos ht 2)
  refine ⟨ENNReal.ofReal (k * t ^ 2), ENNReal.ofReal δ, V,
    ENNReal.ofReal_ne_zero_iff.mpr hkt, ENNReal.ofReal_ne_top, ?_, hlower t ht hhalf, ?_⟩
  · exact (quadratic_slack_cost_ratio hk ht (one_third_cutoff_cube hδ.le)).le
  · exact expected_potential_slack_le_of_excess hexcess
      (hgap μ hprob hμ hρ (potentialEnergy_ne_top_of_excess ENNReal.ofReal_ne_top hexcess))

theorem potentialCrystallizationTarget_of_inputs {d : ℕ}
    (Λ : Set (Ambient d)) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (P : Ambient d → Ambient d → ℝ≥0∞)
    (r A E B c η₀ δA : ℝ) (hr : 0 < r)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hη₀ : 0 < η₀) (hδA : 0 < δA)
    (hanalytic : PotentialUnitCostInput Λ P r A δA)
    (hperiodic : PeriodicStabilityInput Λ r E B c η₀) :
    PotentialCrystallizationTarget Λ P := by
  obtain ⟨δ₁, h₁, hs₁, hp⟩ := exists_uniform_transfer_parameters d A E B c η₀ hA hE hB hc hη₀
  refine ⟨transferConstant E B, transferConstant_pos hE hB, min δ₁ δA,
    lt_min h₁ hδA, lt_of_le_of_lt (min_le_left _ _) hs₁, ?_⟩
  intro μ hprob hμ hρ δ hδ hsmall hexcess
  let _ := hprob
  obtain ⟨κ, cost, V, hκ0, hκtop, hratio, hV, hcost⟩ :=
    hanalytic.cost μ hprob hμ hρ δ hδ (hsmall.trans_le (min_le_right _ _)) hexcess
  exact measurable_crystallization_of_transfer_inputs Λ hΛ r A E B c η₀ δ hr hA hE hB
    hδ (hp δ hδ (hsmall.trans_le (min_le_left _ _))) hperiodic μ hμ hρ
    κ cost V hκ0 hκtop hratio hV hcost

theorem potentialCrystallizationTarget_of_sectionwise_inputs {d : ℕ}
    (Λ : Set (Ambient d)) (hclosed : IsClosed Λ) (hne : Λ.Nonempty)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (P : Ambient d → Ambient d → ℝ≥0∞)
    (r A E B c η₀ δA : ℝ) (hr : 0 < r)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hη₀ : 0 < η₀) (hδA : 0 < δA)
    (hanalytic : PotentialUnitCostInput Λ P r A δA)
    (hperiodic : SectionwisePeriodicStabilityInput Λ r E B c η₀) :
    PotentialCrystallizationTarget Λ P :=
  potentialCrystallizationTarget_of_inputs Λ hΛ P r A (E + 1) B c η₀ δA hr hA
    (by linarith) hB hc hη₀ hδA hanalytic
    (periodicStabilityInput_of_sectionwise hclosed hne r E B c η₀ hperiodic)

theorem potentialUnitCostInput_of_full_quadratic_slack {d : ℕ}
    (Λ : Set (Ambient d)) (P V : Ambient d → Ambient d → ℝ≥0∞)
    {k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hgap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 → potentialEnergy P μ ≠ ∞ →
      latticePotentialEnergy Λ P + potentialEnergy V μ ≤ potentialEnergy P μ)
    (hquad : ∀ x y, dist x y ≤ r → ENNReal.ofReal (k * (r - dist x y) ^ 2) ≤ V x y) :
    PotentialUnitCostInput Λ P r (k * r ^ 2)⁻¹ (1 / 8) := by
  apply potentialUnitCostInput_of_quadratic_slack Λ P V (k * r ^ 2) r
    (mul_pos hk (pow_pos hr 2)) hgap
  intro t ht _hhalf x y _hne hclose
  have hur : dist x y ≤ r := by nlinarith only [hclose, mul_pos hr ht]
  exact (ENNReal.ofReal_le_ofReal
    (full_quadratic_slack_close_pair_cost hr hk.le ht hclose le_rfl)).trans (hquad x y hur)

theorem positiveMixtureIntervalCoefficient_pos {k : ℝ} {m : ℝ≥0∞}
    (hk : 0 < k) (hm0 : m ≠ 0) (hmtop : m ≠ ∞) :
    0 < (ENNReal.ofReal k * m).toReal := by
  exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hk) hm0)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmtop)

theorem potentialUnitCostInput_of_compact_positiveGaussianMixture {d : ℕ}
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hbase : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞)
    (hgaussian : ∀ α : ℝ, 0 < α → latticePotentialEnergy Λ (gaussianPotential α) ≠ ∞)
    (f : ℝ → 𝓢(Ambient d, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient d => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate Λ α (f α))
    {a b k r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hmass : ν (Icc a b) ≠ 0)
    (hk : 0 < k) (hr : 0 < r)
    (hquad : ∀ α ∈ Icc a b, ∀ v : Ambient d, ‖v‖ ≤ r →
      k * (r - ‖v‖) ^ 2 ≤ gaussianKernel α v - (f α v).re) :
    PotentialUnitCostInput Λ (positiveGaussianMixturePotential ν) r
      ((ENNReal.ofReal k * ν (Icc a b)).toReal * r ^ 2)⁻¹ (1 / 8) := by
  have hmfinite := positive_parameter_interval_mass_ne_top_of_lattice ν hz hne hbase ha hab
  let K := (ENNReal.ofReal k * ν (Icc a b)).toReal
  have hK : 0 < K := positiveMixtureIntervalCoefficient_pos hk hmass hmfinite
  let V := potentialMixture (ν.restrict (Icc a b))
    (fun α => gaussianSchwartzSlackPotential α (f α))
  apply potentialUnitCostInput_of_full_quadratic_slack Λ (positiveGaussianMixturePotential ν) V hK hr
  · intro μ hprob hμ hρ henergy
    let _ := hprob
    exact expected_compact_positiveGaussianMixture_gap_of_schwartz_family ν hν μ hμ hρ
      Λ hΛ hz hne hbase henergy hgaussian f hf hcert ha
  · intro x y hxy
    have hl := compact_positiveGaussianMixture_slack_quadratic_lower ν a b k r hk.le f hquad x y hxy
    have heq : ENNReal.ofReal K = ENNReal.ofReal k * ν (Icc a b) :=
      ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmfinite)
    rw [ENNReal.ofReal_mul hK.le, heq]
    exact hl

theorem positiveGaussianMixture_crystallization_of_certificates {d : ℕ}
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (Λ : Set (Ambient d)) (hclosed : IsClosed Λ) (hΛ : Λ.Countable)
    (hsub : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ) {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hbase : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞)
    (hgaussian : ∀ α : ℝ, 0 < α → latticePotentialEnergy Λ (gaussianPotential α) ≠ ∞)
    (f : ℝ → 𝓢(Ambient d, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient d => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate Λ α (f α))
    (r E B c η₀ : ℝ) (hr : 0 < r) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hη₀ : 0 < η₀)
    (hperiodic : SectionwisePeriodicStabilityInput Λ r E B c η₀)
    (hslack : ∀ a b : ℝ, 0 < a → a ≤ b → ∃ k : ℝ, 0 < k ∧
      ∀ α ∈ Icc a b, ∀ v : Ambient d, ‖v‖ ≤ r →
        k * (r - ‖v‖) ^ 2 ≤ gaussianKernel α v - (f α v).re) :
    PotentialCrystallizationTarget Λ (positiveGaussianMixturePotential ν) := by
  obtain ⟨a, b, ha, hab, hmass⟩ := exists_positive_parameter_interval ν hν
  obtain ⟨k, hk, hquad⟩ := hslack a b ha hab
  have hmfinite := positive_parameter_interval_mass_ne_top_of_lattice ν hz hne hbase ha hab
  have hK := positiveMixtureIntervalCoefficient_pos hk hmass hmfinite
  exact potentialCrystallizationTarget_of_sectionwise_inputs Λ hclosed ⟨z, hz⟩ hsub
    (positiveGaussianMixturePotential ν) r _ E B c η₀ (1 / 8) hr (by positivity)
    hE hB hc hη₀ (by norm_num)
    (potentialUnitCostInput_of_compact_positiveGaussianMixture ν hν Λ hΛ hz hne hbase hgaussian
      f hf hcert ha hab hmass hk hr hquad) hperiodic

theorem e8_positiveGaussianMixture_crystallization_of_certificates
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (f : ℝ → 𝓢(Ambient 8, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient 8 => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate e8Set α (f α))
    (E B c η₀ : ℝ) (hE : 0 ≤ E) (hB : 0 ≤ B) (hc : 0 ≤ c) (hη₀ : 0 < η₀)
    (hperiodic : SectionwisePeriodicStabilityInput e8Set (Real.sqrt 2) E B c η₀)
    (hslack : ∀ a b : ℝ, 0 < a → a ≤ b → ∃ k : ℝ, 0 < k ∧
      ∀ α ∈ Icc a b, ∀ v : Ambient 8, ‖v‖ ≤ Real.sqrt 2 →
        k * (Real.sqrt 2 - ‖v‖) ^ 2 ≤ gaussianKernel α v - (f α v).re) :
    PotentialCrystallizationTarget e8Set (positiveGaussianMixturePotential ν) := by
  obtain ⟨z, hz, hne, _⟩ := e8Set_minimum_attained
  exact positiveGaussianMixture_crystallization_of_certificates ν hν e8Set isClosed_e8Set
    countable_e8Set (fun _ hx _ hy => e8Set_sub hx hy) hz hne hbase
    (fun _ hα => e8_gaussian_lattice_energy_ne_top hα) f hf hcert
    (Real.sqrt 2) E B c η₀ (Real.sqrt_pos.mpr (by norm_num)) hE hB hc hη₀ hperiodic hslack

theorem leech_positiveGaussianMixture_crystallization_of_certificates
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (f : ℝ → 𝓢(Ambient 24, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient 24 => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate leechSet α (f α))
    (E B c η₀ : ℝ) (hE : 0 ≤ E) (hB : 0 ≤ B) (hc : 0 ≤ c) (hη₀ : 0 < η₀)
    (hperiodic : SectionwisePeriodicStabilityInput leechSet 2 E B c η₀)
    (hslack : ∀ a b : ℝ, 0 < a → a ≤ b → ∃ k : ℝ, 0 < k ∧
      ∀ α ∈ Icc a b, ∀ v : Ambient 24, ‖v‖ ≤ 2 →
        k * (2 - ‖v‖) ^ 2 ≤ gaussianKernel α v - (f α v).re) :
    PotentialCrystallizationTarget leechSet (positiveGaussianMixturePotential ν) := by
  obtain ⟨z, hz, hne, _⟩ := leechSet_minimum_attained
  exact positiveGaussianMixture_crystallization_of_certificates ν hν leechSet isClosed_leechSet
    countable_leechSet (fun _ hx _ hy => leechSet_sub hx hy) hz hne hbase
    (fun _ hα => leech_gaussian_lattice_energy_ne_top hα) f hf hcert
    2 E B c η₀ (by norm_num) hE hB hc hη₀ hperiodic hslack

/-- The shifted kernel representation supplies the actual mixture cost input. -/
theorem exists_potentialUnitCostInput_of_shifted_positiveGaussianMixture_kernel {d : ℕ}
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0)
    (hbase : latticePotentialEnergy Λ (positiveGaussianMixturePotential ν) ≠ ∞)
    (hgaussian : ∀ α : ℝ, 0 < α → latticePotentialEnergy Λ (gaussianPotential α) ≠ ∞)
    (f : ℝ → 𝓢(Ambient d, ℂ))
    (hf : Measurable (fun p : ℝ × Ambient d => (f p.1 p.2).re))
    (hcert : ∀ α : ℝ, 0 < α → GaussianSchwartzCertificate Λ α (f α))
    (m : ℕ) {a b r V : ℝ} (ha : 0 < a) (hab : a ≤ b) (hmass : ν (Icc a b) ≠ 0)
    (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4) (hV : 0 < V)
    (φ K : ℝ × ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc a b ×ˢ Icc 0 (7 / 8 * r)))
    (horigin : ∀ α ∈ Icc a b, 0 < φ (α, 0))
    (hinterior : ∀ α ∈ Icc a b, ∀ u : ℝ, 0 < u → u < r → 0 < φ (α, u))
    (hK : ContinuousOn K (Icc (Real.pi / b) (Real.pi / a) ×ˢ Icc V (V + 1)))
    (hKpos : ∀ p ∈ Icc (Real.pi / b) (Real.pi / a) ×ˢ Icc V (V + 1), 0 < K p)
    (hKnonneg : ∀ q ∈ Icc (Real.pi / b) (Real.pi / a), ∀ v : ℝ, 0 < v → 0 ≤ K (q, v))
    (hint : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      IntegrableOn (fun v => K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))
        (Ioi (0 : ℝ)) volume)
    (hfactor : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = (Real.pi / α) ^ m * (4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ v in Ioi (0 : ℝ), K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v)))
    (hradial : ∀ α ∈ Icc a b, ∀ v : Ambient d, ‖v‖ ≤ r →
      φ (α, ‖v‖) = gaussianKernel α v - (f α v).re) :
    ∃ A : ℝ, 0 < A ∧ PotentialUnitCostInput Λ (positiveGaussianMixturePotential ν) r A (1 / 8) := by
  obtain ⟨k, hk, hl⟩ := uniform_full_quadratic_slack_of_shifted_laplace_kernel
    m ha hab hr hroot hV φ K hφ horigin hinterior hK hKpos hKnonneg hint hfactor
  have hquad : ∀ α ∈ Icc a b, ∀ v : Ambient d, ‖v‖ ≤ r →
      k * (r - ‖v‖) ^ 2 ≤ gaussianKernel α v - (f α v).re := by
    intro α hα v hv
    rw [← hradial α hα v hv]
    exact hl α hα ‖v‖ ⟨norm_nonneg _, hv⟩
  have hmfinite := positive_parameter_interval_mass_ne_top_of_lattice ν hz hne hbase ha hab
  have hKcoef := positiveMixtureIntervalCoefficient_pos hk hmass hmfinite
  exact ⟨_, inv_pos.mpr (mul_pos hKcoef (pow_pos hr 2)),
    potentialUnitCostInput_of_compact_positiveGaussianMixture ν hν Λ hΛ hz hne hbase hgaussian
      f hf hcert ha hab hmass hk hr hquad⟩

end E8Leech
