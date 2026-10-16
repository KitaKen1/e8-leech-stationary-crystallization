import E8Leech.AffineLatticeDifferences

/-!
# Uniqueness of the containing affine lattice

The density lower bound retained by Z1 forces the configuration differences
to contain every vector of either containing lattice. A common point then
identifies the two affine lattices as sets. Isometry parameters themselves
are not unique, and no measurable selector is asserted in this module.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal

theorem sub_add_mem_isometry_image_lattice {d : ℕ}
    (Λ : Submodule ℤ (Ambient d)) (Φ : Ambient d ≃ᵢ Ambient d)
    {x y a : Ambient d} (hx : x ∈ Φ '' (Λ : Set (Ambient d)))
    (hy : y ∈ Φ '' (Λ : Set (Ambient d))) (ha : a ∈ Φ '' (Λ : Set (Ambient d))) :
    x - y + a ∈ Φ '' (Λ : Set (Ambient d)) := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨w, hw, rfl⟩ := ha
  refine ⟨u - v + w, Λ.add_mem (Λ.sub_mem hu hv) hw, ?_⟩
  have h1 := isometry_recenter_apply Φ u v
  have h2 := isometry_recenter_apply Φ (u - v + w) w
  rw [add_sub_cancel_right] at h2
  rw [← h2, ← h1]
  abel

theorem isometry_image_lattice_subset_of_density {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (Λ' : Submodule ℤ (Ambient d))
    (Φ Ψ : Ambient d ≃ᵢ Ambient d) (c : Configuration (Ambient d))
    (hc : c.support ⊆ Φ '' (Λ : Set (Ambient d)))
    (hc' : c.support ⊆ Ψ '' (Λ' : Set (Ambient d)))
    (R loss : ℕ → ℝ) (hR : Tendsto R atTop atTop) (hloss : Tendsto loss atTop (𝓝 0))
    (hden : ∀ᶠ n in atTop,
      ENNReal.ofReal (1 - loss n) * volume (closedBall (0 : Ambient d) (R n)) ≤
        c.count (closedBall 0 (R n))) :
    Φ '' (Λ : Set (Ambient d)) ⊆ Ψ '' (Λ' : Set (Ambient d)) := by
  obtain ⟨a, ha, y, -, -⟩ := exists_difference_of_density_in_affine_lattice b Λ hle hcov
    Φ c hc R loss hR hloss hden Λ.zero_mem
  obtain ⟨z₀, hz₀, heq₀⟩ := hc ha
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨u, hu, v, hv, heq⟩ := exists_difference_of_density_in_affine_lattice b Λ hle hcov
    Φ c hc R loss hR hloss hden (Λ.sub_mem hz hz₀)
  have hm := sub_add_mem_isometry_image_lattice Λ' Ψ (hc' hu) (hc' hv) (hc' ha)
  have he : u - v + a = Φ z := by
    rw [heq, ← heq₀]
    exact isometry_recenter_apply Φ z z₀
  rwa [he] at hm

theorem isometry_image_lattice_eq_of_density {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (Φ Ψ : Ambient d ≃ᵢ Ambient d) (c : Configuration (Ambient d))
    (hc : c.support ⊆ Φ '' (Λ : Set (Ambient d)))
    (hc' : c.support ⊆ Ψ '' (Λ : Set (Ambient d)))
    (R loss : ℕ → ℝ) (hR : Tendsto R atTop atTop) (hloss : Tendsto loss atTop (𝓝 0))
    (hden : ∀ᶠ n in atTop,
      ENNReal.ofReal (1 - loss n) * volume (closedBall (0 : Ambient d) (R n)) ≤
        c.count (closedBall 0 (R n))) :
    Φ '' (Λ : Set (Ambient d)) = Ψ '' (Λ : Set (Ambient d)) :=
  Set.Subset.antisymm
    (isometry_image_lattice_subset_of_density b Λ hle hcov Λ Φ Ψ c hc hc' R loss hR hloss hden)
    (isometry_image_lattice_subset_of_density b Λ hle hcov Λ Ψ Φ c hc' hc R loss hR hloss hden)

theorem exists_unique_lattice_container_of_fullDensity {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (c : Configuration (Ambient d)) (hc : FullDensityLatticeContainment (Λ : Set (Ambient d)) c) :
    ∃! Γ : Set (Ambient d), (∃ Φ : Ambient d ≃ᵢ Ambient d,
      Γ = Φ '' (Λ : Set (Ambient d))) ∧ c.support ⊆ Γ := by
  obtain ⟨⟨Φ, hΦ⟩, R, loss, hR, hloss, hden⟩ := hc
  refine ⟨Φ '' (Λ : Set (Ambient d)), ⟨⟨Φ, rfl⟩, hΦ⟩, ?_⟩
  rintro Γ ⟨⟨Ψ, rfl⟩, hΨ⟩
  exact isometry_image_lattice_eq_of_density b Λ hle hcov Ψ Φ c hΨ hΦ R loss hR hloss hden

end E8Leech
