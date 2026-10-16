import E8Leech.PeriodicObservation
import SpherePacking.CohnElkies.LPBoundReindex

/-!
# Exact local point-count averages in a periodic packing

Unique representatives identify actual centres with representative/lattice pairs.
Unfolding therefore gives the average count, not just a multiplicity envelope.
The empty packing is included explicitly.
-/
noncomputable section
namespace E8Leech
open Set MeasureTheory Metric SpherePacking
open scoped ENNReal BigOperators

def periodicCentreCount {d : ℕ} (P : PeriodicSpherePacking d) (R : ℝ) (u : Ambient d) : ℝ≥0∞ :=
  ∑' x : P.centers, (closedBall (x : Ambient d) R).indicator (fun _ => 1) u

theorem periodicCentreCount_eq_representative_sum {d : ℕ} (P : PeriodicSpherePacking d)
    {D : Set (Ambient d)} (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D)
    (R : ℝ) (u : Ambient d) :
    periodicCentreCount P R u = ∑' (v : ↥(P.centers ∩ D)) (ℓ : P.lattice),
      (closedBall ((v : Ambient d) + ℓ) R).indicator (fun _ => 1) u := by
  classical
  by_cases hn : P.centers.Nonempty
  · have : Nonempty P.centers := ⟨⟨hn.choose, hn.choose_spec⟩⟩
    let e := CohnElkies.centersInterProdEquiv P hD
    have he : ∀ p : ↥(P.centers ∩ D) × P.lattice,
        (e p : Ambient d) = (p.1 : Ambient d) + p.2 := by
      intro p
      change p.2 +ᵥ (p.1 : Ambient d) = (p.1 : Ambient d) + p.2
      simp only [Submodule.vadd_def, vadd_eq_add, add_comm]
    unfold periodicCentreCount
    rw [← e.tsum_eq (fun x : P.centers => (closedBall (x : Ambient d) R).indicator
      (fun _ => (1 : ℝ≥0∞)) u)]
    simp only [he]
    exact ENNReal.tsum_prod'
  · have : IsEmpty P.centers := ⟨fun x => hn ⟨x, x.property⟩⟩
    have : IsEmpty ↥(P.centers ∩ D) := ⟨fun x => hn ⟨x, x.property.1⟩⟩
    simp only [periodicCentreCount, tsum_empty]

theorem measurable_periodicCentreCount {d : ℕ} (hd : 0 < d) (P : PeriodicSpherePacking d)
    {D : Set (Ambient d)} (hDb : Bornology.IsBounded D)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) (R : ℝ) :
    Measurable (periodicCentreCount P R) := by
  have : Finite ↥(P.centers ∩ D) := finite_centers_inter_of_isBounded P D hDb hd
  have he : periodicCentreCount P R = fun u => ∑' (v : ↥(P.centers ∩ D)) (ℓ : P.lattice),
      (closedBall ((v : Ambient d) + ℓ) R).indicator (fun _ => (1 : ℝ≥0∞)) u := by
    funext u
    exact periodicCentreCount_eq_representative_sum P hD R u
  rw [he]
  exact Measurable.tsum (fun _ => Measurable.tsum
    (fun _ => measurable_const.indicator measurableSet_closedBall))

theorem lintegral_periodicCentreCount {d : ℕ} (hd : 0 < d) (P : PeriodicSpherePacking d)
    {D : Set (Ambient d)} (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) (R : ℝ) :
    (∫⁻ u in D, periodicCentreCount P R u) =
      (P.numReps' hd hDb : ℝ≥0∞) * volume (closedBall (0 : Ambient d) R) := by
  classical
  let : Fintype ↥(P.centers ∩ D) := P.instFintypeNumReps' hd hDb
  have hf : IsAddFundamentalDomain P.lattice D volume :=
    IsAddFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have he : periodicCentreCount P R =
      periodicBallMultiplicity P.lattice Finset.univ (fun v : ↥(P.centers ∩ D) => (v : Ambient d)) R := by
    funext u
    rw [periodicCentreCount_eq_representative_sum P hD R u, tsum_fintype]
    rfl
  rw [he, lintegral_periodicBallMultiplicity P.lattice hf]
  simp only [Finset.card_univ, PeriodicSpherePacking.numReps']

theorem lintegral_uniform_periodicCentreCount {d : ℕ} (hd : 0 < d) (P : PeriodicSpherePacking d)
    {D : Set (Ambient d)} (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) (R : ℝ) :
    (∫⁻ u, periodicCentreCount P R u ∂uniformFundamentalDomain D) =
      ((P.numReps' hd hDb : ℝ≥0∞) / volume D) * volume (closedBall (0 : Ambient d) R) := by
  rw [uniformFundamentalDomain, lintegral_smul_measure,
    lintegral_periodicCentreCount hd P hDb hDm hD R]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
end E8Leech
