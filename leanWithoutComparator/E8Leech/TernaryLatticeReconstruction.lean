import E8Leech.ZeroExcessUniqueContainer
import E8Leech.LatticeShiftLaw

/-! # Direct reconstruction of the containing lattice as `c - c + c` -/

noncomputable section
namespace E8Leech
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal

def ternarySupport {d : ℕ} (c : Configuration (Ambient d)) : Set (Ambient d) :=
  {x | ∃ u ∈ c.support, ∃ v ∈ c.support, ∃ w ∈ c.support, u - v + w = x}

theorem support_subset_ternarySupport {d : ℕ} (c : Configuration (Ambient d)) :
    c.support ⊆ ternarySupport c := by
  intro x hx
  exact ⟨x, hx, x, hx, x, hx, by simp⟩

theorem ternarySupport_translate {d : ℕ} (a : Ambient d) (c : Configuration (Ambient d)) :
    ternarySupport (translate a c) = (fun x => a + x) '' ternarySupport c := by
  ext x
  constructor
  · rintro ⟨u, ⟨u', hu', rfl⟩, v, ⟨v', hv', rfl⟩, w, ⟨w', hw', rfl⟩, he⟩
    refine ⟨u' - v' + w', ⟨u', hu', v', hv', w', hw', rfl⟩, ?_⟩
    change a + u' - (a + v') + (a + w') = x at he
    convert he using 1; abel
  · rintro ⟨y, ⟨u, hu, v, hv, w, hw, rfl⟩, rfl⟩
    refine ⟨a + u, ⟨u, hu, rfl⟩, a + v, ⟨v, hv, rfl⟩,
      a + w, ⟨w, hw, rfl⟩, ?_⟩
    abel

theorem ternarySupport_eq_isometry_image_of_density {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (Φ : Ambient d ≃ᵢ Ambient d) (c : Configuration (Ambient d))
    (hc : c.support ⊆ Φ '' (Λ : Set (Ambient d)))
    (R loss : ℕ → ℝ) (hR : Tendsto R atTop atTop) (hloss : Tendsto loss atTop (𝓝 0))
    (hden : ∀ᶠ n in atTop,
      ENNReal.ofReal (1 - loss n) * volume (closedBall (0 : Ambient d) (R n)) ≤
        c.count (closedBall 0 (R n))) :
    ternarySupport c = Φ '' (Λ : Set (Ambient d)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨u, hu, v, hv, w, hw, rfl⟩
    exact sub_add_mem_isometry_image_lattice Λ Φ (hc hu) (hc hv) (hc hw)
  · obtain ⟨a, ha, y, -, -⟩ := exists_difference_of_density_in_affine_lattice b Λ hle hcov
      Φ c hc R loss hR hloss hden Λ.zero_mem
    obtain ⟨z₀, hz₀, heq₀⟩ := hc ha
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨u, hu, v, hv, heq⟩ := exists_difference_of_density_in_affine_lattice b Λ hle hcov
      Φ c hc R loss hR hloss hden (Λ.sub_mem hz hz₀)
    refine ⟨u, hu, v, hv, a, ha, ?_⟩
    rw [heq, ← heq₀]
    exact isometry_recenter_apply Φ z z₀

theorem ternarySupport_isometry_image_of_fullDensity {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (c : Configuration (Ambient d)) (hc : FullDensityLatticeContainment (Λ : Set (Ambient d)) c) :
    ∃ Φ : Ambient d ≃ᵢ Ambient d, ternarySupport c = Φ '' (Λ : Set (Ambient d)) := by
  obtain ⟨⟨Φ, hΦ⟩, R, loss, hR, hloss, hden⟩ := hc
  exact ⟨Φ, ternarySupport_eq_isometry_image_of_density b Λ hle hcov Φ c hΦ R loss hR hloss hden⟩

theorem e8_ternarySupport_isometry_image_of_fullDensity (c : Configuration (Ambient 8))
    (hc : FullDensityLatticeContainment e8Set c) :
    ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, ternarySupport c = Φ '' e8Set := by
  have hc' : FullDensityLatticeContainment (e8Lattice : Set (Ambient 8)) c := by
    simpa only [coe_e8Lattice] using hc
  simpa only [coe_e8Lattice] using ternarySupport_isometry_image_of_fullDensity
    e8EuclideanBasis e8Lattice le_rfl e8Lattice_covolume c hc'

theorem leech_ternarySupport_isometry_image_of_fullDensity (c : Configuration (Ambient 24))
    (hc : FullDensityLatticeContainment leechSet c) :
    ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, ternarySupport c = Φ '' leechSet := by
  have hc' : FullDensityLatticeContainment (leechLattice : Set (Ambient 24)) c := by
    simpa only [coe_leechLattice] using hc
  have hle : Submodule.span ℤ (Set.range leechEuclideanBasis) ≤ leechLattice := by
    rw [leechLattice_eq_span]
  simpa only [coe_leechLattice] using ternarySupport_isometry_image_of_fullDensity
    leechEuclideanBasis leechLattice hle leechLattice_covolume c hc'

end E8Leech
