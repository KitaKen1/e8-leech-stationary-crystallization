import E8Leech.LatticeCompactLimit
import E8Leech.ZeroExcessLocalCrystals
import E8Leech.E8GaussianPiCrystallization
import E8Leech.LeechGaussianPiCrystallization

/-!
# Zero-excess configurations lie in one isometric lattice

Combine the measurable probability-one sequence of local crystals with
compactness after recentering. The density lower bound along growing balls
is retained for the next uniqueness step. This proves containment, not yet
equality, uniqueness, measurable selection or the Haar classification.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- Containment in one affine lattice, with a lower asymptotic density of one along
some diverging sequence of closed balls. This is a predicate, with no measurability claim. -/
def FullDensityLatticeContainment {d : ℕ} (Λ : Set (Ambient d))
    (c : Configuration (Ambient d)) : Prop :=
  (∃ Φ : Ambient d ≃ᵢ Ambient d, c.support ⊆ Φ '' Λ) ∧
  ∃ R loss : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto loss atTop (𝓝 0) ∧
    ∀ᶠ n in atTop,
      ENNReal.ofReal (1 - loss n) * volume (Metric.closedBall (0 : Ambient d) (R n)) ≤
        c.count (Metric.closedBall 0 (R n))

theorem zero_excess_lattice_containment {d : ℕ} {Λ : Set (Ambient d)}
    {P : Ambient d → Ambient d → ℝ≥0∞} (htarget : PotentialCrystallizationTarget Λ P)
    (hclosed : IsClosed Λ) (hne : Λ.Nonempty) (hsub : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (hbase : latticePotentialEnergy Λ P ≠ ∞)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy P μ = latticePotentialEnergy Λ P) :
    ∃ H : Set (Configuration (Ambient d)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment Λ c := by
  obtain ⟨R, ε, loss, hR, hε, hloss, H, hH, hprob, hlocal⟩ :=
    zero_excess_localCrystal_sequence htarget hbase μ hμ hρ henergy
  refine ⟨H, hH, hprob, fun c hc => ⟨?_, R, loss, hR, hloss, ?_⟩⟩
  · exact exists_containing_isometry_of_localCrystal_sequence hclosed hne hsub
      c R ε loss hR hε (hlocal c hc)
  · exact (hlocal c hc).mono fun n hn => hn.2

theorem e8_zero_excess_riesz_lattice_containment {s : ℝ} (hs : (8 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : rieszEnergy s μ = latticeRieszEnergy e8Set s) :
    ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment e8Set c := by
  have ht : PotentialCrystallizationTarget e8Set (rieszPotential s) :=
    (stationaryCrystallizationFor_iff_potentialTargets e8Set).mp e8CrystallizationTarget_holds s hs
  apply zero_excess_lattice_containment ht isClosed_e8Set ⟨0, zero_mem_e8⟩
    (fun _ hx _ hy => e8Set_sub hx hy) _ μ hμ hρ
  · simpa only [potentialEnergy_riesz, latticePotentialEnergy_riesz] using henergy
  · simpa only [latticePotentialEnergy_riesz] using e8_latticeRieszEnergy_ne_top hs

theorem leech_zero_excess_riesz_lattice_containment {s : ℝ} (hs : (24 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : rieszEnergy s μ = latticeRieszEnergy leechSet s) :
    ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment leechSet c := by
  have ht : PotentialCrystallizationTarget leechSet (rieszPotential s) :=
    (stationaryCrystallizationFor_iff_potentialTargets leechSet).mp leechCrystallizationTarget_holds s hs
  apply zero_excess_lattice_containment ht isClosed_leechSet ⟨0, zero_mem_leechSet⟩
    (fun _ hx _ hy => leechSet_sub hx hy) _ μ hμ hρ
  · simpa only [potentialEnergy_riesz, latticePotentialEnergy_riesz] using henergy
  · simpa only [latticePotentialEnergy_riesz] using leech_latticeRieszEnergy_ne_top hs

theorem e8_zero_excess_positiveGaussianMixture_lattice_containment
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν)) :
    ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment e8Set c :=
  zero_excess_lattice_containment (e8_positiveGaussianMixture_crystallization_all ν hν hbase)
    isClosed_e8Set ⟨0, zero_mem_e8⟩ (fun _ hx _ hy => e8Set_sub hx hy) hbase μ hμ hρ henergy

theorem leech_zero_excess_positiveGaussianMixture_lattice_containment
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν)) :
    ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment leechSet c :=
  zero_excess_lattice_containment (leech_positiveGaussianMixture_crystallization_all ν hν hbase)
    isClosed_leechSet ⟨0, zero_mem_leechSet⟩ (fun _ hx _ hy => leechSet_sub hx hy) hbase μ hμ hρ henergy

theorem e8_zero_excess_gaussian_lattice_containment {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy e8Set (gaussianPotential α)) :
    ∃ H : Set (Configuration (Ambient 8)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment e8Set c := by
  have ht : PotentialCrystallizationTarget e8Set (gaussianPotential α) :=
    e8_gaussian_crystallization_all_general hα (by norm_num)
  exact zero_excess_lattice_containment ht isClosed_e8Set ⟨0, zero_mem_e8⟩
    (fun _ hx _ hy => e8Set_sub hx hy) (e8_gaussian_lattice_energy_ne_top hα) μ hμ hρ henergy

theorem leech_zero_excess_gaussian_lattice_containment {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1)
    (henergy : potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy leechSet (gaussianPotential α)) :
    ∃ H : Set (Configuration (Ambient 24)), MeasurableSet H ∧ μ H = 1 ∧
      ∀ c ∈ H, FullDensityLatticeContainment leechSet c := by
  have ht : PotentialCrystallizationTarget leechSet (gaussianPotential α) :=
    leech_gaussian_crystallization_all_general hα (by norm_num)
  exact zero_excess_lattice_containment ht isClosed_leechSet ⟨0, zero_mem_leechSet⟩
    (fun _ hx _ hy => leechSet_sub hx hy) (leech_gaussian_lattice_energy_ne_top hα) μ hμ hρ henergy

end E8Leech
