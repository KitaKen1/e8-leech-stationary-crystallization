import E8Leech.Target
import E8Leech.LeechLattice
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Finite bidirectional matching through distance to the full lattice

Nearest points in a nonempty closed set exist in a proper metric space. For a finite
observed set, their image is already a finite witness for BOTH directions of matching.
No injectivity, measurable choice of nearest points, or enumeration of finite lattice
subsets is needed. Fixed-isometry tests and countable unions of such tests are Borel.
Compact rotation/phase minimization and density of a chosen countable family are separate
proof obligations; this file does not assert the full existential event is Borel.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

/-- A finite witness inside the reference set, with both directions of approximation. -/
def FiniteLatticeMatch {A : Type*} [MetricSpace A] (Λ X : Set A)
    (Φ : A ≃ᵢ A) (error : ℝ) : Prop :=
  ∃ Z : Finset A, (↑Z : Set A) ⊆ Λ ∧
    (∀ x ∈ X, ∃ z ∈ Z, dist x (Φ z) ≤ error) ∧
    (∀ z ∈ Z, ∃ x ∈ X, dist (Φ z) x ≤ error)

theorem finiteLatticeMatch_iff_infDist {A : Type*} [MetricSpace A] [ProperSpace A]
    {Λ X : Set A} (hΛ : IsClosed Λ) (hne : Λ.Nonempty) (hX : X.Finite)
    (Φ : A ≃ᵢ A) (error : ℝ) :
    FiniteLatticeMatch Λ X Φ error ↔
      ∀ x ∈ X, Metric.infDist (Φ.symm x) Λ ≤ error := by
  constructor
  · rintro ⟨Z, hZ, hforward, _⟩ x hx
    obtain ⟨z, hz, hd⟩ := hforward x hx
    have heq : dist (Φ.symm x) z = dist x (Φ z) := by
      simpa using (Φ.dist_eq (Φ.symm x) z).symm
    exact (Metric.infDist_le_dist_of_mem (hZ hz)).trans (heq ▸ hd)
  · intro h
    choose f hf hdist using fun x : A => hΛ.exists_infDist_eq_dist hne (Φ.symm x)
    refine ⟨hX.toFinset.image f, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
      exact hf x
    · intro x hx
      refine ⟨f x, Finset.mem_image.mpr ⟨x, hX.mem_toFinset.mpr hx, rfl⟩, ?_⟩
      have heq : dist x (Φ (f x)) = dist (Φ.symm x) (f x) := by
        simpa using Φ.dist_eq (Φ.symm x) (f x)
      rw [heq, ← hdist x]
      exact h x hx
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      refine ⟨x, hX.mem_toFinset.mp hx, ?_⟩
      have heq : dist (Φ (f x)) x = dist (Φ.symm x) (f x) := by
        simpa only [Φ.apply_symm_apply, dist_comm] using Φ.dist_eq (Φ.symm x) (f x)
      rw [heq, ← hdist x]
      exact h x (hX.mem_toFinset.mp hx)

theorem isClosed_e8Set : IsClosed e8Set := by
  rw [← coe_e8Lattice]
  let : DiscreteTopology e8Lattice.toAddSubgroup := inferInstanceAs (DiscreteTopology e8Lattice)
  exact AddSubgroup.isClosed_of_discrete (H := e8Lattice.toAddSubgroup)

theorem isClosed_leechSet : IsClosed leechSet := by
  rw [← coe_leechLattice]
  let : DiscreteTopology leechLattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology leechLattice)
  exact AddSubgroup.isClosed_of_discrete (H := leechLattice.toAddSubgroup)

theorem localCrystal_iff_infDist {d : ℕ} {Λ : Set (Ambient d)}
    (hΛ : IsClosed Λ) (hne : Λ.Nonempty) (c : Configuration (Ambient d))
    (R error loss : ℝ) :
    LocalCrystal Λ c R error loss ↔
      (∃ Φ : Ambient d ≃ᵢ Ambient d,
        ∀ x ∈ c.support ∩ Metric.closedBall 0 R,
          Metric.infDist (Φ.symm x) Λ ≤ error) ∧
      ENNReal.ofReal (1 - loss) * volume (Metric.closedBall (0 : Ambient d) R) ≤
        c.count (Metric.closedBall 0 R) := by
  have hfinite := c.finite_on_compacts _ (isCompact_closedBall (0 : Ambient d) R)
  change (∃ Φ, FiniteLatticeMatch Λ (c.support ∩ Metric.closedBall 0 R) Φ error) ∧ _ ↔ _
  simp only [finiteLatticeMatch_iff_infDist hΛ hne hfinite]

theorem e8_localCrystal_iff_infDist (c : Configuration (Ambient 8)) (R error loss : ℝ) :
    LocalCrystal e8Set c R error loss ↔
      (∃ Φ : Ambient 8 ≃ᵢ Ambient 8,
        ∀ x ∈ c.support ∩ Metric.closedBall 0 R,
          Metric.infDist (Φ.symm x) e8Set ≤ error) ∧
      ENNReal.ofReal (1 - loss) * volume (Metric.closedBall (0 : Ambient 8) R) ≤
        c.count (Metric.closedBall 0 R) :=
  localCrystal_iff_infDist isClosed_e8Set ⟨0, zero_mem_e8⟩ c R error loss

theorem leech_localCrystal_iff_infDist (c : Configuration (Ambient 24)) (R error loss : ℝ) :
    LocalCrystal leechSet c R error loss ↔
      (∃ Φ : Ambient 24 ≃ᵢ Ambient 24,
        ∀ x ∈ c.support ∩ Metric.closedBall 0 R,
          Metric.infDist (Φ.symm x) leechSet ≤ error) ∧
      ENNReal.ofReal (1 - loss) * volume (Metric.closedBall (0 : Ambient 24) R) ≤
        c.count (Metric.closedBall 0 R) :=
  localCrystal_iff_infDist isClosed_leechSet ⟨0, zero_mem_leechSet⟩ c R error loss

theorem pointwise_infDist_iff_count_zero {d : ℕ} (Λ : Set (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (c : Configuration (Ambient d)) (R error : ℝ) :
    (∀ x ∈ c.support ∩ Metric.closedBall 0 R,
      Metric.infDist (Φ.symm x) Λ ≤ error) ↔
      c.count (Metric.closedBall 0 R ∩ {x | error < Metric.infDist (Φ.symm x) Λ}) = 0 := by
  rw [Configuration.count_eq_zero_iff, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h x hx
    exact (h x ⟨hx.1, hx.2.1⟩).not_gt hx.2.2
  · intro h x hx
    exact le_of_not_gt (fun hd => h x ⟨hx.1, hx.2, hd⟩)

theorem measurableSet_pointwise_infDist {d : ℕ} (Λ : Set (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (R error : ℝ) :
    MeasurableSet {c : Configuration (Ambient d) |
      ∀ x ∈ c.support ∩ Metric.closedBall 0 R,
        Metric.infDist (Φ.symm x) Λ ≤ error} := by
  have hwindow : MeasurableSet
      (Metric.closedBall (0 : Ambient d) R ∩ {x | error < Metric.infDist (Φ.symm x) Λ}) :=
    Metric.isClosed_closedBall.measurableSet.inter
      (isOpen_lt continuous_const ((Metric.continuous_infDist_pt Λ).comp
        Φ.symm.continuous)).measurableSet
  have hm := Configuration.measurable_count hwindow
  have heq : {c : Configuration (Ambient d) |
      ∀ x ∈ c.support ∩ Metric.closedBall 0 R,
        Metric.infDist (Φ.symm x) Λ ≤ error} =
      (fun c : Configuration (Ambient d) => c.count
        (Metric.closedBall 0 R ∩ {x | error < Metric.infDist (Φ.symm x) Λ})) ⁻¹' {0} := by
    ext c
    exact pointwise_infDist_iff_count_zero Λ Φ c R error
  rw [heq]
  exact hm (measurableSet_singleton 0)

theorem measurableSet_fixed_finiteLatticeMatch {d : ℕ} {Λ : Set (Ambient d)}
    (hΛ : IsClosed Λ) (hne : Λ.Nonempty) (Φ : Ambient d ≃ᵢ Ambient d)
    (R error : ℝ) :
    MeasurableSet {c : Configuration (Ambient d) |
      FiniteLatticeMatch Λ (c.support ∩ Metric.closedBall 0 R) Φ error} := by
  have heq : {c : Configuration (Ambient d) |
      FiniteLatticeMatch Λ (c.support ∩ Metric.closedBall 0 R) Φ error} =
      {c : Configuration (Ambient d) |
        ∀ x ∈ c.support ∩ Metric.closedBall 0 R,
          Metric.infDist (Φ.symm x) Λ ≤ error} := by
    ext c
    exact finiteLatticeMatch_iff_infDist hΛ hne
      (c.finite_on_compacts _ (isCompact_closedBall (0 : Ambient d) R)) Φ error
  rw [heq]
  exact measurableSet_pointwise_infDist Λ Φ R error

theorem measurableSet_countable_finiteLatticeMatch {d : ℕ} {Λ : Set (Ambient d)}
    (hΛ : IsClosed Λ) (hne : Λ.Nonempty) (Φ : ℕ → Ambient d ≃ᵢ Ambient d)
    (R error : ℝ) :
    MeasurableSet {c : Configuration (Ambient d) |
      ∃ n, FiniteLatticeMatch Λ (c.support ∩ Metric.closedBall 0 R) (Φ n) error} := by
  simpa only [← Set.iUnion_ofPred] using
    MeasurableSet.iUnion (fun n => measurableSet_fixed_finiteLatticeMatch hΛ hne (Φ n) R error)

theorem measurableSet_count_density_lower {d : ℕ} (R loss : ℝ) :
    MeasurableSet {c : Configuration (Ambient d) |
      ENNReal.ofReal (1 - loss) * volume (Metric.closedBall (0 : Ambient d) R) ≤
        c.count (Metric.closedBall 0 R)} := by
  exact measurableSet_le measurable_const
    (Configuration.measurable_count Metric.isClosed_closedBall.measurableSet)

/-- Countable candidates give an actual measurable good subevent of the original target. -/
theorem measurable_countable_match_good_subevent {d : ℕ} {Λ : Set (Ambient d)}
    (hΛ : IsClosed Λ) (hne : Λ.Nonempty) (Φ : ℕ → Ambient d ≃ᵢ Ambient d)
    (R error loss : ℝ) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      (∀ c, c ∈ G ↔
        (∃ n, FiniteLatticeMatch Λ (c.support ∩ Metric.closedBall 0 R) (Φ n) error) ∧
        ENNReal.ofReal (1 - loss) * volume (Metric.closedBall (0 : Ambient d) R) ≤
          c.count (Metric.closedBall 0 R)) ∧
      G ⊆ {c | LocalCrystal Λ c R error loss} := by
  refine ⟨{c | (∃ n, FiniteLatticeMatch Λ (c.support ∩ Metric.closedBall 0 R) (Φ n) error) ∧
      ENNReal.ofReal (1 - loss) * volume (Metric.closedBall (0 : Ambient d) R) ≤
        c.count (Metric.closedBall 0 R)}, ?_, fun _ => Iff.rfl, ?_⟩
  · exact (measurableSet_countable_finiteLatticeMatch hΛ hne Φ R error).inter
      (measurableSet_count_density_lower R loss)
  · rintro c ⟨⟨n, hn⟩, hdensity⟩
    exact ⟨⟨Φ n, hn⟩, hdensity⟩

end E8Leech
