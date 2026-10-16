import E8Leech.LatticeDensitySaturation

/-! # Every vector of a containing lattice is a configuration difference -/

noncomputable section
namespace E8Leech
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal

theorem exists_difference_of_density_in_affine_lattice {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (Φ : Ambient d ≃ᵢ Ambient d) (c : Configuration (Ambient d))
    (hc : c.support ⊆ Φ '' (Λ : Set (Ambient d)))
    (R loss : ℕ → ℝ) (hR : Tendsto R atTop atTop) (hloss : Tendsto loss atTop (𝓝 0))
    (hden : ∀ᶠ n in atTop,
      ENNReal.ofReal (1 - loss n) * volume (closedBall (0 : Ambient d) (R n)) ≤
        c.count (closedBall 0 (R n)))
    {v : Ambient d} (hv : v ∈ Λ) :
    ∃ x ∈ c.support, ∃ y ∈ c.support, x - y = Φ.toRealLinearIsometryEquiv v := by
  classical
  have hC : 0 ≤ ‖v‖ + ∑ i, ‖b i‖ :=
    add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have he := eventually_enlarged_ball_lt_twice_density (‖v‖ + ∑ i, ‖b i‖) hC
    (Φ.symm 0) R loss hR hloss
  obtain ⟨n, hn, hvol, hlossn⟩ :=
    (hden.and (he.and (hloss.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))))).exists
  have hfin := c.finite_on_compacts _ (isCompact_closedBall (0 : Ambient d) (R n))
  let S := hfin.toFinset
  let T := S.image Φ.symm
  have hcard : T.card = S.card := Finset.card_image_of_injective _ Φ.symm.injective
  have hsource : ∀ t ∈ T, Φ t ∈ c.support := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    simpa only [IsometryEquiv.apply_symm_apply] using (hfin.mem_toFinset.mp hx).1
  have hT : ∀ t ∈ T, t ∈ Λ := by
    intro t ht
    obtain ⟨z, hz, heq⟩ := hc (hsource t ht)
    have : z = t := Φ.injective heq
    exact this ▸ hz
  have hball : ∀ t ∈ T, t ∈ closedBall (Φ.symm 0) (R n) := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    rw [mem_closedBall, Φ.symm.dist_eq]
    exact mem_closedBall.mp (hfin.mem_toFinset.mp hx).2
  have hcountreal : (1 - loss n) * volume.real (closedBall (0 : Ambient d) (R n)) ≤
      (T.card : ℝ) := by
    have hh := ENNReal.toReal_mono (c.count_ne_top_of_compact (isCompact_closedBall _ _)) hn
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), Configuration.count,
      Measure.count_apply_finite _ hfin, ENNReal.toReal_natCast] at hh
    simpa only [hcard, S, measureReal_def] using hh
  have hcount : volume.real (closedBall (Φ.symm 0) (R n + ‖v‖ + ∑ i, ‖b i‖)) <
      2 * (T.card : ℝ) := by
    rw [add_assoc]
    nlinarith [hvol]
  by_cases hv0 : v = 0
  · have hpos : 0 < T.card := by
      have hh := measureReal_nonneg (μ := volume)
        (s := closedBall (Φ.symm 0) (R n + ‖v‖ + ∑ i, ‖b i‖))
      have : (0 : ℝ) < T.card := by linarith
      exact_mod_cast this
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
    exact ⟨Φ t, hsource t ht, Φ t, hsource t ht, by simp [hv0]⟩
  · obtain ⟨t, ht, t', ht', -, heq⟩ := ne_of_count_translate b Λ hle hcov T hT hball
      hcount hv le_rfl hv0
    refine ⟨Φ t, hsource t ht, Φ t', hsource t' ht', ?_⟩
    rw [← heq]
    exact (eq_sub_iff_add_eq.mpr (isometry_recenter_apply Φ t t')).symm

end E8Leech
