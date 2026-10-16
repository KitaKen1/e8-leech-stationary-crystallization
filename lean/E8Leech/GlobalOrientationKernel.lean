import E8Leech.ConfigurationAnchorKernel
import E8Leech.LatticeOrientationCandidates

/-! # A global measurable orientation probability kernel

Average normalized finite orientation candidates over an occupied window.
On exact lattices the result is independent of the averaging window and anchor.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {d : ℕ} (b : Module.Basis (Fin d) ℝ (Ambient d))

def anchoredOrientationProbability :
    Kernel (Configuration (Ambient d) × Ambient d) (LatticeOrientation d) :=
  normalizedFiniteKernel (anchoredOrientationKernel b) ⟨LinearIsometryEquiv.refl ℝ (Ambient d)⟩

instance : IsMarkovKernel (anchoredOrientationProbability b) :=
  normalizedFiniteKernel_isMarkov (anchoredOrientationKernel b) (anchoredOrientationKernel_finite b) _

def globalOrientationKernel : Kernel (Configuration (Ambient d)) (LatticeOrientation d) where
  toFun c := (configurationAnchorKernel d c).bind (fun x => anchoredOrientationProbability b (c, x))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have hrow (c : Configuration (Ambient d)) :
        Measurable (fun x => anchoredOrientationProbability b (c, x)) :=
      (anchoredOrientationProbability b).measurable.comp measurable_prodMk_left
    simp_rw [Measure.bind_apply hS (hrow _).aemeasurable]
    exact measurable_lintegral_of_finite_fibers (configurationAnchorKernel d)
      (fun _ => inferInstance) ((anchoredOrientationProbability b).measurable_coe hS)

instance : IsMarkovKernel (globalOrientationKernel b) where
  isProbabilityMeasure c := isProbabilityMeasure_bind_laws (configurationAnchorKernel d c)
    (fun x => anchoredOrientationProbability b (c, x))
    ((anchoredOrientationProbability b).measurable.comp measurable_prodMk_left)
    (fun _ => inferInstance)

theorem anchoredOrientationProbability_translate (a : Ambient d)
    (c : Configuration (Ambient d)) (x : Ambient d) :
    anchoredOrientationProbability b (translate a c, a + x) = anchoredOrientationProbability b (c, x) :=
  normalizedFiniteKernel_eq_of_fiber_eq _ _ (anchoredOrientationKernel_translate b a c x)

variable (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
variable (hb : Λ = Submodule.span ℤ (Set.range b))

include hb in
theorem anchoredOrientationProbability_anchor_independent (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    {x y : Ambient d} (hx : x ∈ c.support) (hy : y ∈ c.support) :
    anchoredOrientationProbability b (c, x) = anchoredOrientationProbability b (c, y) :=
  normalizedFiniteKernel_eq_of_fiber_eq _ _
    (anchoredOrientationKernel_anchor_independent b Λ hb c Φ hc hx hy)

include hb in
theorem globalOrientationKernel_eq_at_anchor (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    {x : Ambient d} (hx : x ∈ c.support) :
    globalOrientationKernel b c = anchoredOrientationProbability b (c, x) := by
  have he : (fun y => anchoredOrientationProbability b (c, y)) =ᵐ[configurationAnchorKernel d c]
      (fun _ => anchoredOrientationProbability b (c, x)) := by
    filter_upwards [configurationAnchorKernel_ae_mem_support c ⟨x, hx⟩] with y hy
    exact anchoredOrientationProbability_anchor_independent b Λ hb c Φ hc hy hx
  change (configurationAnchorKernel d c).bind _ = _
  rw [Measure.bind_congr_right he, Measure.bind_const, measure_univ, one_smul]

include hb in
theorem globalOrientationKernel_translate_of_exact (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    (a : Ambient d) : globalOrientationKernel b (translate a c) = globalOrientationKernel b c := by
  have hx : Φ 0 ∈ c.support := hc ▸ ⟨0, Λ.zero_mem, rfl⟩
  have hax : a + Φ 0 ∈ (translate a c).support := ⟨Φ 0, hx, rfl⟩
  have htrans : (translate a c).support =
      (Φ.trans (IsometryEquiv.addLeft a)) '' (Λ : Set (Ambient d)) := by
    change (fun x => a + x) '' c.support = _
    rw [hc, image_image]
    rfl
  rw [globalOrientationKernel_eq_at_anchor b Λ hb _ _ htrans hax,
    globalOrientationKernel_eq_at_anchor b Λ hb c Φ hc hx,
    anchoredOrientationProbability_translate]

include hb in
theorem globalOrientationKernel_ae_mem_candidates (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    {x : Ambient d} (hx : x ∈ c.support) :
    ∀ᵐ Q ∂globalOrientationKernel b c, Q ∈ orientationCandidatePoints b c x := by
  rw [globalOrientationKernel_eq_at_anchor b Λ hb c Φ hc hx, ae_iff]
  exact normalizedFiniteKernel_null_of_ne _ _ (c, x)
    (anchoredOrientationKernel_univ_ne_zero_of_exact b Λ hb c Φ hc hx)
    (anchoredOrientationKernel_compl_eq_zero b c x)

include hb in
theorem globalOrientationKernel_ae_recovers_lattice (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d))) :
    ∀ᵐ Q ∂globalOrientationKernel b c,
      ∃ u : Ambient d, c = rotatedLatticeShift Λ Q u := by
  have hx : Φ 0 ∈ c.support := hc ▸ ⟨0, Λ.zero_mem, rfl⟩
  filter_upwards [globalOrientationKernel_ae_mem_candidates b Λ hb c Φ hc hx] with Q hQ
  have he := orientationCandidate_recovers_lattice b Λ hb c Φ hc hx Q
    ((mem_orientationCandidatePoints b c (Φ 0) Q).mp hQ)
  refine ⟨Q.isometry.symm (Φ 0), Configuration.ext ?_⟩
  rw [he]
  change (fun v => Φ 0 + Q.isometry v) '' (Λ : Set (Ambient d)) =
    Q.isometry '' ((fun v => Q.isometry.symm (Φ 0) + v) '' (Λ : Set (Ambient d)))
  rw [image_image]
  congr 1
  funext v
  simp only [map_add, LinearIsometryEquiv.apply_symm_apply]

omit Λ [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem globalOrientationKernel_mixing_isProbability
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.bind (globalOrientationKernel b)) :=
  isProbabilityMeasure_bind_laws μ _ (globalOrientationKernel b).measurable (fun _ => inferInstance)

end E8Leech
