import E8Leech.E8CountProbability
import E8Leech.LeechLocalCount

/-!
# The number of centres in most observation balls in dimension 24 (BRR, estimate (4.4))

The rank 24 version of `E8CountProbability`. For a periodic packing in dimension 24 with
separation at least `2` and density at least `1 - ε`, the number of centres in the ball `B(u,R)`
is bounded above for every `u` by `leechWindowBound R` (`leech_card_window_le`), and its average
over a fundamental domain is `N·vol(B_R)/covol ≥ (1-ε)·vol(B_R)`. The reverse Markov inequality
bounds the probability of the centres with few points (`leech_periodic_count_probability`).
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set SpherePacking
open scoped ENNReal

/-- The upper bound for the number of points of a `2`-separated set in a ball of radius `R` of
`ℝ²⁴`. -/
def leechWindowBound (R : ℝ) : ℝ :=
  volume.real (closedBall (0 : Ambient 24) (R + 2 + leechBasisNormSum)) +
    ((2 * R + 4) ^ 24 - (2 * R + 2 - 2 * leechBasisNormSum) ^ 24)

theorem leech_periodicCentreCount_le_windowBound {P : PeriodicSpherePacking 24}
    (hP : 2 ≤ P.separation) {R : ℝ} (hR : leechBasisNormSum ≤ R) (u : Ambient 24) :
    periodicCentreCount P R u ≤ ENNReal.ofReal (leechWindowBound R) := by
  have hfin := finite_centers_inter_closedBall P u R
  have hmem : ∀ x, x ∈ hfin.toFinset ↔ x ∈ P.centers ∧ x ∈ closedBall u R := fun x =>
    hfin.mem_toFinset
  rw [periodicCentreCount_eq_card P R u hfin.toFinset hmem]
  have h := leech_card_window_le (S := P.centers)
    (fun x hx y hy hne => hP.trans (P.centers_dist' x y hx hy hne)) (u := u) hR hfin.toFinset
    (fun x hx => ((hmem x).mp hx).1) (fun x hx => ((hmem x).mp hx).2)
  have h2 : (hfin.toFinset.card : ℝ≥0∞) = ENNReal.ofReal (hfin.toFinset.card : ℝ) := by simp
  rw [h2]
  exact ENNReal.ofReal_le_ofReal h

/-- **The count for most centres** in dimension 24. -/
theorem leech_periodic_count_probability {P : PeriodicSpherePacking 24} {D : Set (Ambient 24)}
    (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D) (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hε1 : ε ≤ 1)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) / ZLattice.covolume P.lattice volume)
    {R t : ℝ} (hR : leechBasisNormSum ≤ R) (ht0 : 0 ≤ t) (htU : t < leechWindowBound R) :
    uniformFundamentalDomain D {u | periodicCentreCount P R u < ENNReal.ofReal t} ≤
      ENNReal.ofReal
        ((leechWindowBound R - (1 - ε) * volume.real (closedBall (0 : Ambient 24) R)) /
          (leechWindowBound R - t)) := by
  have hf : IsAddFundamentalDomain P.lattice D volume :=
    IsAddFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hprob : IsProbabilityMeasure (uniformFundamentalDomain D) :=
    uniformFundamentalDomain_probability P.lattice hf hDb
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have hv : volume D = ENNReal.ofReal (ZLattice.covolume P.lattice volume) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hf, Measure.real,
      ENNReal.ofReal_toReal (ne_of_lt hDb.measure_lt_top)]
  have hV0 : 0 ≤ volume.real (closedBall (0 : Ambient 24) R) := measureReal_nonneg
  have hint := lintegral_uniform_periodicCentreCount (d := 24) (by norm_num) P hDb hDm hD R
  have hm : ENNReal.ofReal ((1 - ε) * volume.real (closedBall (0 : Ambient 24) R)) ≤
      ∫⁻ u, periodicCentreCount P R u ∂uniformFundamentalDomain D := by
    rw [hint, hv]
    have hn : (P.numReps' (by norm_num) hDb : ℝ≥0∞) =
        ENNReal.ofReal (P.numReps' (by norm_num) hDb : ℝ) := by simp
    rw [hn, ← ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_mul (sub_nonneg.mpr hε1)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal hε) ?_
    rw [Measure.real, ENNReal.ofReal_toReal measure_closedBall_lt_top.ne]
  exact measure_lt_le_of_le_of_lintegral_ge (uniformFundamentalDomain D)
    (measurable_periodicCentreCount (by norm_num) P hDb hD R)
    (mul_nonneg (sub_nonneg.mpr hε1) hV0) ht0 htU
    (fun u => leech_periodicCentreCount_le_windowBound hP hR u) hm

end E8Leech
