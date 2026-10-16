import E8Leech.ZeroExcessMeasurableContainer
import E8Leech.LatticePointCount

/-! # A uniform count upper bound for every affine image of a covolume-one lattice -/

noncomputable section
namespace E8Leech
open Set MeasureTheory Metric
open scoped ENNReal

theorem count_closedBall_le_of_affine_lattice_containment {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (c : Configuration (Ambient d)) (Φ : Ambient d ≃ᵢ Ambient d)
    (hc : c.support ⊆ Φ '' (Λ : Set (Ambient d))) (R : ℝ) :
    c.count (closedBall 0 R) ≤ volume (closedBall (0 : Ambient d) (R + ∑ i, ‖b i‖)) := by
  classical
  have hfin := c.finite_on_compacts _ (isCompact_closedBall (0 : Ambient d) R)
  let S := hfin.toFinset
  let T := S.image Φ.symm
  have hcard : T.card = S.card := Finset.card_image_of_injective _ Φ.symm.injective
  have hT : ∀ t ∈ T, t ∈ Λ := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨z, hz, he⟩ := hc (hfin.mem_toFinset.mp hx).1
    change Φ.symm x ∈ (Λ : Set (Ambient d))
    rw [← he, IsometryEquiv.symm_apply_apply]
    exact hz
  have hball : ∀ t ∈ T, t ∈ closedBall (Φ.symm 0) R := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    rw [mem_closedBall, Φ.symm.dist_eq]
    exact mem_closedBall.mp (hfin.mem_toFinset.mp hx).2
  have hcnt := card_mul_covolume_le b Λ hle T hT hball
  rw [hcov, mul_one, hcard,
    Measure.addHaar_real_closedBall_center volume (Φ.symm 0)] at hcnt
  rw [Configuration.count, Measure.count_apply_finite _ hfin]
  have hh := ENNReal.ofReal_le_ofReal hcnt
  simpa only [S, ENNReal.ofReal_natCast, measureReal_def,
    ENNReal.ofReal_toReal (measure_closedBall_lt_top (μ := volume)).ne] using hh

end E8Leech
