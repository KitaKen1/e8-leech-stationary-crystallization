import E8Leech.UniformCenter
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Observation centres near finitely many periodic representatives

Unfolding a fundamental domain counts all lattice translates. The volume of
centres whose closed observation ball meets a marked periodic orbit is bounded
by the number of marked representatives times the observation-ball volume.
-/
noncomputable section
namespace E8Leech
open Set MeasureTheory Metric
open scoped ENNReal Pointwise BigOperators

variable {d : ℕ} (Λ : Submodule ℤ (Ambient d))

/-- All observation centres within `R` of any marked periodic copy. -/
def periodicBallNeighborhood {ι : Type*} (s : Finset ι) (v : ι → Ambient d) (R : ℝ) :
    Set (Ambient d) := ⋃ b ∈ s, ⋃ ℓ : Λ, closedBall (v b + ℓ) R

theorem mem_periodicBallNeighborhood {ι : Type*} {s : Finset ι}
    {v : ι → Ambient d} {R : ℝ} {u : Ambient d} :
    u ∈ periodicBallNeighborhood Λ s v R ↔
      ∃ b ∈ s, ∃ ℓ : Λ, dist u (v b + ℓ) ≤ R := by
  simp only [periodicBallNeighborhood, mem_iUnion, mem_closedBall, exists_prop]

theorem measurable_periodicBallNeighborhood [Countable Λ] {ι : Type*}
    (s : Finset ι) (v : ι → Ambient d) (R : ℝ) :
    MeasurableSet (periodicBallNeighborhood Λ s v R) :=
  s.measurableSet_biUnion (fun _ _ => MeasurableSet.iUnion (fun _ => measurableSet_closedBall))

theorem not_mem_periodicBallNeighborhood {ι : Type*} {s : Finset ι}
    {v : ι → Ambient d} {R : ℝ} {u : Ambient d}
    (hu : u ∉ periodicBallNeighborhood Λ s v R) {b : ι} (hb : b ∈ s) (ℓ : Λ) :
    v b + ℓ ∉ closedBall u R := by
  intro h
  apply hu
  apply (mem_periodicBallNeighborhood Λ).mpr
  exact ⟨b, hb, ℓ, by simpa only [mem_closedBall, dist_comm] using h⟩

theorem periodic_closedBall_unfold [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    (b : Ambient d) (R : ℝ) :
    (∑' ℓ : Λ, volume (closedBall (b + ℓ) R ∩ D)) = volume (closedBall (0 : Ambient d) R) := by
  have : VAddInvariantMeasure Λ (Ambient d) volume :=
    inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup (Ambient d) volume)
  have : IsIsometricVAdd Λ (Ambient d) := ⟨fun ℓ => isometry_add_left (ℓ : Ambient d)⟩
  simpa only [Metric.vadd_closedBall, Submodule.vadd_def, vadd_eq_add, add_comm,
    Measure.addHaar_closedBall_center] using (hD.measure_eq_tsum (closedBall b R)).symm

theorem periodicBallNeighborhood_volume_le [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    {ι : Type*} (s : Finset ι) (v : ι → Ambient d) (R : ℝ) :
    volume (periodicBallNeighborhood Λ s v R ∩ D) ≤
      (s.card : ℝ≥0∞) * volume (closedBall (0 : Ambient d) R) := by
  have he : periodicBallNeighborhood Λ s v R ∩ D =
      ⋃ b ∈ s, ⋃ ℓ : Λ, closedBall (v b + ℓ) R ∩ D := by
    ext u
    simp only [periodicBallNeighborhood, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨⟨b, hb, ℓ, hu⟩, huD⟩
      exact ⟨b, hb, ℓ, hu, huD⟩
    · rintro ⟨b, hb, ℓ, hu, huD⟩
      exact ⟨⟨b, hb, ℓ, hu⟩, huD⟩
  rw [he]
  calc
    _ ≤ ∑ b ∈ s, volume (⋃ ℓ : Λ, closedBall (v b + ℓ) R ∩ D) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ b ∈ s, ∑' ℓ : Λ, volume (closedBall (v b + ℓ) R ∩ D) :=
      Finset.sum_le_sum (fun _ _ => measure_iUnion_le _)
    _ = _ := by simp only [periodic_closedBall_unfold Λ hD, Finset.sum_const, nsmul_eq_mul]

/-- Uniform probability on an arbitrary bounded lattice fundamental domain. -/
def uniformFundamentalDomain (D : Set (Ambient d)) : Measure (Ambient d) :=
  (volume D)⁻¹ • volume.restrict D

theorem uniformFundamentalDomain_apply (D : Set (Ambient d)) {A : Set (Ambient d)}
    (hA : MeasurableSet A) :
    uniformFundamentalDomain D A = volume (A ∩ D) / volume D := by
  rw [uniformFundamentalDomain, Measure.smul_apply, Measure.restrict_apply hA]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem uniformFundamentalDomain_probability [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    (hDb : Bornology.IsBounded D) : IsProbabilityMeasure (uniformFundamentalDomain D) := by
  constructor
  rw [uniformFundamentalDomain_apply D MeasurableSet.univ, univ_inter]
  have hc := ZLattice.covolume_pos Λ volume
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hD, Measure.real] at hc
  have hz : volume D ≠ 0 := by
    intro he
    rw [he, ENNReal.toReal_zero] at hc
    exact (lt_irrefl 0) hc
  exact ENNReal.div_self hz (ne_of_lt hDb.measure_lt_top)

theorem uniform_periodicBallNeighborhood_le [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    {ι : Type*} (s : Finset ι) (v : ι → Ambient d) (R : ℝ) :
    uniformFundamentalDomain D (periodicBallNeighborhood Λ s v R) ≤
      ((s.card : ℝ≥0∞) / volume D) * volume (closedBall (0 : Ambient d) R) := by
  rw [uniformFundamentalDomain_apply D (measurable_periodicBallNeighborhood Λ s v R)]
  calc
    _ ≤ ((s.card : ℝ≥0∞) * volume (closedBall (0 : Ambient d) R)) / volume D :=
      ENNReal.div_le_div_right (periodicBallNeighborhood_volume_le Λ hD s v R) _
    _ = _ := by simp only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- Multiplicity, counting every representative and every periodic copy in a
closed observation ball. No injectivity is required for this counting identity. -/
def periodicBallMultiplicity {ι : Type*} (s : Finset ι) (v : ι → Ambient d) (R : ℝ)
    (u : Ambient d) : ℝ≥0∞ :=
  ∑ b ∈ s, ∑' ℓ : Λ, (closedBall (v b + ℓ) R).indicator (fun _ => 1) u

theorem measurable_periodicBallMultiplicity [Countable Λ] {ι : Type*}
    (s : Finset ι) (v : ι → Ambient d) (R : ℝ) :
    Measurable (periodicBallMultiplicity Λ s v R) :=
  s.measurable_fun_sum (fun _ _ => Measurable.tsum
    (fun _ => measurable_const.indicator measurableSet_closedBall))

theorem lintegral_periodicBallMultiplicity [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    {ι : Type*} (s : Finset ι) (v : ι → Ambient d) (R : ℝ) :
    (∫⁻ u in D, periodicBallMultiplicity Λ s v R u) =
      (s.card : ℝ≥0∞) * volume (closedBall (0 : Ambient d) R) := by
  unfold periodicBallMultiplicity
  rw [lintegral_finsetSum s (fun _ _ => Measurable.tsum
    (fun _ => measurable_const.indicator measurableSet_closedBall))]
  have hi : ∀ b, (∫⁻ u in D, ∑' ℓ : Λ,
      (closedBall (v b + ℓ) R).indicator (fun _ => (1 : ℝ≥0∞)) u) =
      volume (closedBall (0 : Ambient d) R) := by
    intro b
    rw [lintegral_tsum (fun _ => (measurable_const.indicator measurableSet_closedBall).aemeasurable)]
    simp only [lintegral_indicator measurableSet_closedBall, setLIntegral_const,
      one_mul, Measure.restrict_apply measurableSet_closedBall]
    exact periodic_closedBall_unfold Λ hD (v b) R
  simp only [hi, Finset.sum_const, nsmul_eq_mul]
end E8Leech
