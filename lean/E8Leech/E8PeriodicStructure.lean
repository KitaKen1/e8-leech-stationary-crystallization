import E8Leech.PeriodicSaturation
import E8Leech.E8CountProbability
import E8Leech.SaturatedWindow

/-!
# Local `E8` structure of an almost optimal periodic packing (BRR, Theorem 1.5 for `E8`)

For a periodic packing `P` in dimension eight with separation at least `√2` and density at least
`1 - ε`, and a radius `R ≥ 6000`, there is a set `S` of observation centres of small probability
in a fundamental domain such that for every `u ∉ S`

* the centres of `P` in `B(u,R)` are within `46 η R` of `p₀ + Φ(E8)` for a linear isometry `Φ`,
  where `η = α ε^{1/4}` is the error of the even shells, and
* the number of centres in `B(u,R)` is at least `t`.

(`e8_periodic_window_structure`.) The exceptional set is the union of the bad observation centres
of the saturated packing (probability `≤ 2√ε·vol(B_R)`), the balls around the centres added by
the saturation (`≤ ε·vol(B_R)`), and the centres with fewer than `t` points (reverse Markov).
Outside it the windows of `P` and of its saturation agree, and
`exists_isometry_near_e8Set_of_saturated` applies to the saturation.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set SpherePacking
open scoped ENNReal

/-- **Local `E8` structure of an almost optimal periodic packing.** -/
theorem e8_periodic_window_structure {P : PeriodicSpherePacking 8} {D : Set (Ambient 8)}
    (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D) (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) (hne : P.centers.Nonempty) {ε : ℝ}
    (hεpos : 0 < ε) (hε1 : ε ≤ 1)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) / ZLattice.covolume P.lattice volume)
    {R α t : ℝ} (hR : 6000 ≤ R) (hRρ : e8BasisNormSum ≤ R) (hα0 : 0 ≤ α)
    (hshell : ∀ z : Ambient 8, Real.sqrt 2 ≤ ‖z‖ → ‖z‖ ≤ 2 * R →
      ∃ k : ℤ, 1 ≤ k ∧ |‖z‖ ^ 2 - 2 * k| ≤ α * Real.sqrt |(_root_.g z).re|)
    (hsmall : α * ε ^ (1 / 4 : ℝ) * R ^ 2 ≤ 1 / 10 ^ 29)
    (ht : 9 / 10 * volume.real (closedBall (0 : Ambient 8) R) ≤ t) (htU : t < windowBound R) :
    ∃ S : Set (Ambient 8),
      uniformFundamentalDomain D S ≤
        ENNReal.ofReal (2 * Real.sqrt ε) * volume (closedBall (0 : Ambient 8) R) +
          ENNReal.ofReal ε * volume (closedBall (0 : Ambient 8) R) +
          ENNReal.ofReal ((windowBound R -
            (1 - ε) * volume.real (closedBall (0 : Ambient 8) R)) / (windowBound R - t)) ∧
      ∀ u ∉ S,
        (∃ (Φ : Ambient 8 ≃ₗᵢ[ℝ] Ambient 8) (p₀ : Ambient 8),
          ∀ x ∈ P.centers ∩ closedBall u R, ∃ z ∈ e8Set,
            ‖(x - p₀) - Φ z‖ ≤ 46 * (α * ε ^ (1 / 4 : ℝ)) * R) ∧
        ENNReal.ofReal t ≤ periodicCentreCount P R u := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hV0 : 0 ≤ volume.real (closedBall (0 : Ambient 8) R) := measureReal_nonneg
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  -- the saturation
  obtain ⟨M, hPM, hinv, hsep, hsat⟩ := exists_saturated_superset P hs2 hP hne
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have hN := ncard_added_representatives (by norm_num : 0 < 8) P hs2 hsep hinv hPM hDb
  have hε' : 1 - ε ≤
      ((P.withCenters M (Real.sqrt 2) hs2 hsep hinv).numReps' (by norm_num) hDb : ℝ) /
        ZLattice.covolume P.lattice volume := by
    refine hε.trans (div_le_div_of_nonneg_right ?_ hc.le)
    have h : P.numReps' (by norm_num) hDb ≤
        (P.withCenters M (Real.sqrt 2) hs2 hsep hinv).numReps' (by norm_num) hDb := by omega
    exact_mod_cast h
  -- the three exceptional sets
  have h1 := e8_bad_observation_centres_probability_le
    (P := P.withCenters M (Real.sqrt 2) hs2 hsep hinv) hDb hDm le_rfl hD hεpos hε' R
  obtain ⟨s, hs, h2⟩ := e8_added_neighborhood_probability_le hDb hDm hD hsep hinv hPM hε R
  have h3 := e8_periodic_count_probability
    (P := P.withCenters M (Real.sqrt 2) hs2 hsep hinv) hDb hDm le_rfl hD hε1 hε' hRρ ht0 htU
  refine ⟨e8BadObservationCenters (P := P.withCenters M (Real.sqrt 2) hs2 hsep hinv) hDb le_rfl
      hD hεpos R ∪ periodicBallNeighborhood P.lattice s (fun b => b) R ∪
      {u | periodicCentreCount (P.withCenters M (Real.sqrt 2) hs2 hsep hinv) R u <
        ENNReal.ofReal t}, ?_, ?_⟩
  · exact (measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (add_le_add h1 h2)) h3)
  · intro u hu
    have hu1 : u ∉ e8BadObservationCenters (P := P.withCenters M (Real.sqrt 2) hs2 hsep hinv)
        hDb le_rfl hD hεpos R := fun h => hu (Or.inl (Or.inl h))
    have hu2 : u ∉ periodicBallNeighborhood P.lattice s (fun b => b) R :=
      fun h => hu (Or.inl (Or.inr h))
    have hu3 : ¬ periodicCentreCount (P.withCenters M (Real.sqrt 2) hs2 hsep hinv) R u <
        ENNReal.ofReal t := fun h => hu (Or.inr h)
    -- the windows agree
    have hwin : M ∩ closedBall u R = P.centers ∩ closedBall u R :=
      centers_inter_closedBall_eq_of_not_mem hD hs2 hsep hinv hPM s hs hu2
    have hfin : (M ∩ closedBall u R).Finite :=
      finite_centers_inter_closedBall (P.withCenters M (Real.sqrt 2) hs2 hsep hinv) u R
    have hcount' : periodicCentreCount (P.withCenters M (Real.sqrt 2) hs2 hsep hinv) R u =
        (hfin.toFinset.card : ℝ≥0∞) :=
      periodicCentreCount_eq_card _ R u hfin.toFinset fun x => hfin.mem_toFinset
    have hcount : periodicCentreCount P R u = (hfin.toFinset.card : ℝ≥0∞) :=
      periodicCentreCount_eq_card P R u hfin.toFinset fun x => by
        rw [hfin.mem_toFinset, hwin]
        rfl
    have htc : ENNReal.ofReal t ≤ (hfin.toFinset.card : ℝ≥0∞) := by
      rw [← hcount']
      exact not_lt.mp hu3
    have htc' : t ≤ (hfin.toFinset.card : ℝ) := by
      have h := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.natCast_ne_top _)).mp htc
      rwa [ENNReal.toReal_natCast] at h
    refine ⟨?_, by rw [hcount]; exact htc⟩
    -- the even shells of the saturated packing
    have hpair : ∀ x ∈ M ∩ closedBall u R, ∀ y ∈ M ∩ closedBall u R,
        ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ α * ε ^ (1 / 4 : ℝ) := fun x hx y hy =>
      e8_good_center_pair_shell (P := P.withCenters M (Real.sqrt 2) hs2 hsep hinv) hDb le_rfl hD
        hεpos hα0 hshell hu1 hx.1 hx.2 hy.1 hy.2
    have hη0 : 0 ≤ α * ε ^ (1 / 4 : ℝ) := mul_nonneg hα0 (Real.rpow_nonneg hεpos.le _)
    obtain ⟨Φ, p₀, hΦ⟩ := exists_isometry_near_e8Set_of_saturated (S := M) (u := u) hR hη0
      hsmall hfin hpair hsep (fun y _ => hsat y) (ht.trans htc')
    exact ⟨Φ, p₀, fun x hx => hΦ x (by rw [hwin]; exact hx)⟩

end E8Leech
