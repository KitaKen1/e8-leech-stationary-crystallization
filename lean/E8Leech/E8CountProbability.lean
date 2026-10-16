import E8Leech.E8LocalCount
import E8Leech.E8BadObservationCenters
import E8Leech.PeriodicPointCounting

/-!
# The number of centres in most observation balls (BRR, estimate (4.4))

For a periodic packing in dimension eight with separation at least `√2` and density at least
`1 - ε`, the number of centres in the ball `B(u,R)` is bounded above for every `u` by
`windowBound R` (`card_window_le`), and its average over a fundamental domain is exactly
`N·vol(B_R)/covol ≥ (1-ε)·vol(B_R)`. The reverse Markov inequality bounds the probability of the
centres with few points (`e8_periodic_count_probability`).

* `measure_lt_le_of_le_of_lintegral_ge`: the reverse Markov inequality.
* `periodicCentreCount_eq_card`: the count as the cardinality of a window.
* `periodicCentreCount_le_windowBound`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set SpherePacking
open scoped ENNReal

/-- **Reverse Markov inequality.** A function bounded above by `U` with integral at least `m` over
a probability space is less than `t < U` with probability at most `(U - m)/(U - t)`. -/
theorem measure_lt_le_of_le_of_lintegral_ge {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {f : α → ℝ≥0∞} (hf : Measurable f) {U m t : ℝ} (hm0 : 0 ≤ m)
    (ht0 : 0 ≤ t) (htU : t < U) (hfU : ∀ x, f x ≤ ENNReal.ofReal U)
    (hm : ENNReal.ofReal m ≤ ∫⁻ x, f x ∂ν) :
    ν {x | f x < ENNReal.ofReal t} ≤ ENNReal.ofReal ((U - m) / (U - t)) := by
  have hconst : ∫⁻ _x, ENNReal.ofReal U ∂ν = ENNReal.ofReal U := by
    rw [lintegral_const, measure_univ, mul_one]
  have hfin : ∫⁻ x, f x ∂ν ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((lintegral_mono hfU).trans hconst.le)
  have hsub : ∫⁻ x, (ENNReal.ofReal U - f x) ∂ν = ENNReal.ofReal U - ∫⁻ x, f x ∂ν := by
    rw [lintegral_sub hf hfin (Filter.Eventually.of_forall hfU), hconst]
  have hint : ∫⁻ x, (ENNReal.ofReal U - f x) ∂ν ≤ ENNReal.ofReal (U - m) := by
    rw [hsub, ENNReal.ofReal_sub _ hm0]
    exact tsub_le_tsub_left hm _
  have hbad : {x | f x < ENNReal.ofReal t} ⊆
      {x | ENNReal.ofReal (U - t) ≤ ENNReal.ofReal U - f x} := by
    intro x hx
    have hx' : f x < ENNReal.ofReal t := hx
    show ENNReal.ofReal (U - t) ≤ ENNReal.ofReal U - f x
    rw [ENNReal.ofReal_sub _ ht0]
    exact tsub_le_tsub_left hx'.le _
  have hmarkov := mul_meas_ge_le_lintegral (μ := ν) (hf.const_sub (ENNReal.ofReal U))
    (ENNReal.ofReal (U - t))
  have hUt : 0 < U - t := sub_pos.mpr htU
  have hpos : ENNReal.ofReal (U - t) ≠ 0 := (ENNReal.ofReal_pos.mpr hUt).ne'
  rw [ENNReal.ofReal_div_of_pos hUt, ENNReal.le_div_iff_mul_le (Or.inl hpos)
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  calc ENNReal.ofReal (U - t) * ν {x | f x < ENNReal.ofReal t}
      ≤ ENNReal.ofReal (U - t) * ν {x | ENNReal.ofReal (U - t) ≤ ENNReal.ofReal U - f x} :=
        mul_le_mul' le_rfl (measure_mono hbad)
    _ ≤ ∫⁻ x, (ENNReal.ofReal U - f x) ∂ν := hmarkov
    _ ≤ ENNReal.ofReal (U - m) := hint

/-- The count of centres in a ball is the cardinality of the window. -/
theorem periodicCentreCount_eq_card {d : ℕ} (P : PeriodicSpherePacking d) (R : ℝ)
    (u : Ambient d) (W : Finset (Ambient d))
    (hW : ∀ x, x ∈ W ↔ x ∈ P.centers ∧ x ∈ closedBall u R) :
    periodicCentreCount P R u = (W.card : ℝ≥0∞) := by
  classical
  have hterm : ∀ x : P.centers, (closedBall (x : Ambient d) R).indicator (fun _ => (1 : ℝ≥0∞)) u =
      ({y : P.centers | (y : Ambient d) ∈ closedBall u R} : Set P.centers).indicator
        (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases h : (x : Ambient d) ∈ closedBall u R
    · have h' : u ∈ closedBall (x : Ambient d) R := by
        rw [mem_closedBall, dist_comm]
        exact mem_closedBall.mp h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem (show x ∈ {y : P.centers |
        (y : Ambient d) ∈ closedBall u R} from h)]
    · have h' : u ∉ closedBall (x : Ambient d) R := by
        intro hu
        apply h
        rw [mem_closedBall, dist_comm]
        exact mem_closedBall.mp hu
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem (show x ∉ {y : P.centers |
        (y : Ambient d) ∈ closedBall u R} from h)]
  have himg : (Subtype.val : P.centers → Ambient d) ''
      {y : P.centers | (y : Ambient d) ∈ closedBall u R} = (W : Set (Ambient d)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hW _).mpr ⟨y.2, hy⟩
    · intro hx
      have h := (hW x).mp hx
      exact ⟨⟨x, h.1⟩, h.2, rfl⟩
  unfold periodicCentreCount
  rw [tsum_congr hterm, ← tsum_subtype, ENNReal.tsum_set_one,
    ← Subtype.val_injective.encard_image, himg, Set.encard_coe_eq_coe_finsetCard]
  rfl

/-- The upper bound for the number of points of a `√2`-separated set in a ball of radius `R`. -/
def windowBound (R : ℝ) : ℝ :=
  volume.real (closedBall (0 : Ambient 8) (R + Real.sqrt 2 + e8BasisNormSum)) +
    ((2 * R + 2 + Real.sqrt 2) ^ 8 - (2 * R + 2 - 2 * e8BasisNormSum) ^ 8)

/-- The centres of a periodic packing in a ball form a finite set. -/
theorem finite_centers_inter_closedBall {d : ℕ} (P : PeriodicSpherePacking d) (u : Ambient d)
    (R : ℝ) : (P.centers ∩ closedBall u R).Finite :=
  separated_inter_compact_finite P.separation_pos
    (fun x hx y hy hne => P.centers_dist' x y hx hy hne) (isCompact_closedBall u R)

theorem periodicCentreCount_le_windowBound {P : PeriodicSpherePacking 8}
    (hP : Real.sqrt 2 ≤ P.separation) {R : ℝ} (hR : e8BasisNormSum ≤ R) (u : Ambient 8) :
    periodicCentreCount P R u ≤ ENNReal.ofReal (windowBound R) := by
  have hfin := finite_centers_inter_closedBall P u R
  have hmem : ∀ x, x ∈ hfin.toFinset ↔ x ∈ P.centers ∧ x ∈ closedBall u R := fun x =>
    hfin.mem_toFinset
  rw [periodicCentreCount_eq_card P R u hfin.toFinset hmem]
  have h := card_window_le (S := P.centers)
    (fun x hx y hy hne => hP.trans (P.centers_dist' x y hx hy hne)) (u := u) hR hfin.toFinset
    (fun x hx => ((hmem x).mp hx).1) (fun x hx => ((hmem x).mp hx).2)
  have h2 : (hfin.toFinset.card : ℝ≥0∞) = ENNReal.ofReal (hfin.toFinset.card : ℝ) := by simp
  rw [h2]
  exact ENNReal.ofReal_le_ofReal h

/-- **The count for most centres.** -/
theorem e8_periodic_count_probability {P : PeriodicSpherePacking 8} {D : Set (Ambient 8)}
    (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D) (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hε1 : ε ≤ 1)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) / ZLattice.covolume P.lattice volume)
    {R t : ℝ} (hR : e8BasisNormSum ≤ R) (ht0 : 0 ≤ t) (htU : t < windowBound R) :
    uniformFundamentalDomain D {u | periodicCentreCount P R u < ENNReal.ofReal t} ≤
      ENNReal.ofReal ((windowBound R - (1 - ε) * volume.real (closedBall (0 : Ambient 8) R)) /
        (windowBound R - t)) := by
  have hf : IsAddFundamentalDomain P.lattice D volume :=
    IsAddFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hprob : IsProbabilityMeasure (uniformFundamentalDomain D) :=
    uniformFundamentalDomain_probability P.lattice hf hDb
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have hv : volume D = ENNReal.ofReal (ZLattice.covolume P.lattice volume) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hf, Measure.real,
      ENNReal.ofReal_toReal (ne_of_lt hDb.measure_lt_top)]
  have hV0 : 0 ≤ volume.real (closedBall (0 : Ambient 8) R) := measureReal_nonneg
  have hint := lintegral_uniform_periodicCentreCount (d := 8) (by norm_num) P hDb hDm hD R
  have hm : ENNReal.ofReal ((1 - ε) * volume.real (closedBall (0 : Ambient 8) R)) ≤
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
    (fun u => periodicCentreCount_le_windowBound hP hR u) hm

end E8Leech
