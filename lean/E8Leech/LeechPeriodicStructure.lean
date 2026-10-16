import E8Leech.PeriodicSaturation
import E8Leech.LeechObservationShells
import E8Leech.LeechCountProbability
import E8Leech.LocalLeechWindow

/-!
# Local Leech structure of an almost optimal periodic packing (BRR, Theorem 1.5, dimension 24)

The rank 24 version of `E8PeriodicStructure`, given the characterization of the Leech lattice
(`LeechCharacterization`). For a periodic packing `P` in dimension 24 with separation at least `2`
and density at least `1 - ε`, and a radius `R ≥ 200000`, there is a set `S` of observation centres
of small probability in a fundamental domain such that for every `u ∉ S`

* the centres of `P` in `B(u,R)` are within `13 η R` of `p₀ + Φ(Λ₂₄)` for a linear isometry `Φ`,
  where `η = α ε^{1/4}` is the error of the even shells, and
* the number of centres in `B(u,R)` is at least `t`.

(`leech_periodic_window_structure`.) The exceptional set is the union of the bad observation
centres of the saturated packing (probability `≤ 2√ε·vol(B_R)`), the balls around the centres
added by the saturation (`≤ ε·vol(B_R)`), and the centres with fewer than `t` points (reverse
Markov). Outside it the windows of `P` and of its saturation agree, and
`exists_isometry_near_leechSet_of_saturated` applies to the saturation.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set SpherePacking
open scoped ENNReal

/-- In dimension 24 a saturation adds at most `ε·covol` representatives to a packing of density
at least `1 - ε`. -/
theorem leech_added_representatives_card_le {P : PeriodicSpherePacking 24}
    {D : Set (Ambient 24)} (hDb : Bornology.IsBounded D)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D)
    {M : Set (Ambient 24)} (hsep : ∀ x ∈ M, ∀ y ∈ M, x ≠ y → (2 : ℝ) ≤ dist x y)
    (hinv : ∀ ℓ ∈ P.lattice, ∀ a ∈ M, ℓ + a ∈ M) (hPM : P.centers ⊆ M) {ε : ℝ}
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) / ZLattice.covolume P.lattice volume) :
    (((M ∩ D) \ P.centers).ncard : ℝ) ≤ ε * ZLattice.covolume P.lattice volume := by
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h1 := ncard_added_representatives (by norm_num : 0 < 24) P h2pos hsep hinv hPM hDb
  have h2 : ((P.withCenters M 2 h2pos hsep hinv).numReps' (by norm_num) hDb : ℝ) ≤
      ZLattice.covolume P.lattice volume :=
    leech_periodic_numReps_le_covolume (P := P.withCenters M 2 h2pos hsep hinv) hDb le_rfl hD
  have h3 : (1 - ε) * ZLattice.covolume P.lattice volume ≤
      (P.numReps' (by norm_num) hDb : ℝ) := (le_div_iff₀ hc).mp hε
  have h4 : (((M ∩ D) \ P.centers).ncard : ℝ) + (P.numReps' (by norm_num) hDb : ℝ) =
      ((P.withCenters M 2 h2pos hsep hinv).numReps' (by norm_num) hDb : ℝ) := by
    exact_mod_cast h1
  linarith

/-- Outside the balls around the orbit of the added representatives, the windows of a packing
and of an enlargement of its set of centres agree (dimension 24). -/
theorem leech_centers_inter_closedBall_eq_of_not_mem {P : PeriodicSpherePacking 24}
    {D : Set (Ambient 24)} (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {M : Set (Ambient 24)}
    {r : ℝ} (hr : 0 < r) (hsep : ∀ x ∈ M, ∀ y ∈ M, x ≠ y → r ≤ dist x y)
    (hinv : ∀ ℓ ∈ P.lattice, ∀ a ∈ M, ℓ + a ∈ M) (hPM : P.centers ⊆ M)
    (s : Finset (Ambient 24)) (hs : ∀ x, x ∈ (M ∩ D) \ P.centers → x ∈ s) {u : Ambient 24}
    {R : ℝ} (hu : u ∉ periodicBallNeighborhood P.lattice s (fun b => b) R) :
    M ∩ closedBall u R = P.centers ∩ closedBall u R := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxM, hxR⟩
    refine ⟨?_, hxR⟩
    obtain ⟨v, ℓ, rfl⟩ :=
      exists_leech_periodic_rep_translate (P := P.withCenters M r hr hsep hinv) hD hxM
    by_cases hv : (v : Ambient 24) ∈ P.centers
    · have h := P.lattice_action ℓ.2 hv
      rwa [add_comm] at h
    · exact absurd hxR (not_mem_periodicBallNeighborhood P.lattice hu (hs _ ⟨v.2, hv⟩) ℓ)
  · exact fun x hx => ⟨hPM hx.1, hx.2⟩

/-- The balls around the orbit of the added representatives have small probability. -/
theorem leech_added_neighborhood_probability_le {P : PeriodicSpherePacking 24}
    {D : Set (Ambient 24)} (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {M : Set (Ambient 24)}
    (hsep : ∀ x ∈ M, ∀ y ∈ M, x ≠ y → (2 : ℝ) ≤ dist x y)
    (hinv : ∀ ℓ ∈ P.lattice, ∀ a ∈ M, ℓ + a ∈ M) (hPM : P.centers ⊆ M) {ε : ℝ}
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) / ZLattice.covolume P.lattice volume)
    (R : ℝ) :
    ∃ s : Finset (Ambient 24), (∀ x, x ∈ (M ∩ D) \ P.centers → x ∈ s) ∧
      uniformFundamentalDomain D (periodicBallNeighborhood P.lattice s (fun b => b) R) ≤
        ENNReal.ofReal ε * volume (closedBall (0 : Ambient 24) R) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hfin : (M ∩ D).Finite :=
    finite_centers_inter (P.withCenters M 2 h2pos hsep hinv) (by norm_num) hDb
  have hfinA : ((M ∩ D) \ P.centers).Finite := hfin.subset Set.sdiff_subset
  refine ⟨hfinA.toFinset, fun x hx => hfinA.mem_toFinset.mpr hx, ?_⟩
  have hf : IsAddFundamentalDomain P.lattice D volume :=
    IsAddFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have hv : volume D = ENNReal.ofReal (ZLattice.covolume P.lattice volume) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hf, Measure.real,
      ENNReal.ofReal_toReal (ne_of_lt hDb.measure_lt_top)]
  have hcard : (hfinA.toFinset.card : ℝ) ≤ ε * ZLattice.covolume P.lattice volume := by
    rw [← Set.ncard_eq_toFinset_card _ hfinA]
    exact leech_added_representatives_card_le hDb hD hsep hinv hPM hε
  have he : (hfinA.toFinset.card : ℝ≥0∞) / volume D ≤ ENNReal.ofReal ε := by
    have hn : (hfinA.toFinset.card : ℝ≥0∞) = ENNReal.ofReal (hfinA.toFinset.card : ℝ) := by simp
    rw [hn, hv, ← ENNReal.ofReal_div_of_pos hc]
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hc).mpr hcard)
  exact (uniform_periodicBallNeighborhood_le P.lattice hf hfinA.toFinset (fun b => b) R).trans
    (mul_le_mul' he le_rfl)

/-- **Local Leech structure of an almost optimal periodic packing**, given the characterization
of the Leech lattice. -/
theorem leech_periodic_window_structure (hLeech : LeechCharacterization)
    {P : PeriodicSpherePacking 24} {D : Set (Ambient 24)}
    (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D) (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) (hne : P.centers.Nonempty) {ε : ℝ}
    (hεpos : 0 < ε) (hε1 : ε ≤ 1)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) / ZLattice.covolume P.lattice volume)
    {R α t : ℝ} (hR : 200000 ≤ R) (hRρ : leechBasisNormSum ≤ R) (hα0 : 0 ≤ α)
    (hshell : ∀ z : Ambient 24, 2 ≤ ‖z‖ → ‖z‖ ≤ 2 * R →
      ∃ k : ℤ, 2 ≤ k ∧ |‖z‖ ^ 2 - 2 * k| ≤ α * Real.sqrt |(Dim24.f z).re|)
    (hsmall : α * ε ^ (1 / 4 : ℝ) * R ^ 2 ≤ 1 / 10 ^ 115)
    (ht : 9 / 10 * volume.real (closedBall (0 : Ambient 24) R) ≤ t)
    (htU : t < leechWindowBound R) :
    ∃ S : Set (Ambient 24),
      uniformFundamentalDomain D S ≤
        ENNReal.ofReal (2 * Real.sqrt ε) * volume (closedBall (0 : Ambient 24) R) +
          ENNReal.ofReal ε * volume (closedBall (0 : Ambient 24) R) +
          ENNReal.ofReal ((leechWindowBound R -
            (1 - ε) * volume.real (closedBall (0 : Ambient 24) R)) / (leechWindowBound R - t)) ∧
      ∀ u ∉ S,
        (∃ (Φ : Ambient 24 ≃ₗᵢ[ℝ] Ambient 24) (p₀ : Ambient 24),
          ∀ x ∈ P.centers ∩ closedBall u R, ∃ z ∈ leechSet,
            ‖(x - p₀) - Φ z‖ ≤ 13 * (α * ε ^ (1 / 4 : ℝ)) * R) ∧
        ENNReal.ofReal t ≤ periodicCentreCount P R u := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hV0 : 0 ≤ volume.real (closedBall (0 : Ambient 24) R) := measureReal_nonneg
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  -- the saturation
  obtain ⟨M, hPM, hinv, hsep, hsat⟩ := exists_saturated_superset P h2pos hP hne
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have hN := ncard_added_representatives (by norm_num : 0 < 24) P h2pos hsep hinv hPM hDb
  have hε' : 1 - ε ≤
      ((P.withCenters M 2 h2pos hsep hinv).numReps' (by norm_num) hDb : ℝ) /
        ZLattice.covolume P.lattice volume := by
    refine hε.trans (div_le_div_of_nonneg_right ?_ hc.le)
    have h : P.numReps' (by norm_num) hDb ≤
        (P.withCenters M 2 h2pos hsep hinv).numReps' (by norm_num) hDb := by omega
    exact_mod_cast h
  -- the three exceptional sets
  have h1 := leech_bad_observation_centres_probability_le
    (P := P.withCenters M 2 h2pos hsep hinv) hDb hDm le_rfl hD hεpos hε' R
  obtain ⟨s, hs, h2⟩ := leech_added_neighborhood_probability_le hDb hDm hD hsep hinv hPM hε R
  have h3 := leech_periodic_count_probability
    (P := P.withCenters M 2 h2pos hsep hinv) hDb hDm le_rfl hD hε1 hε' hRρ ht0 htU
  refine ⟨leechBadObservationCenters (P := P.withCenters M 2 h2pos hsep hinv) hDb le_rfl
      hD hεpos R ∪ periodicBallNeighborhood P.lattice s (fun b => b) R ∪
      {u | periodicCentreCount (P.withCenters M 2 h2pos hsep hinv) R u <
        ENNReal.ofReal t}, ?_, ?_⟩
  · exact (measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (add_le_add h1 h2)) h3)
  · intro u hu
    have hu1 : u ∉ leechBadObservationCenters (P := P.withCenters M 2 h2pos hsep hinv)
        hDb le_rfl hD hεpos R := fun h => hu (Or.inl (Or.inl h))
    have hu2 : u ∉ periodicBallNeighborhood P.lattice s (fun b => b) R :=
      fun h => hu (Or.inl (Or.inr h))
    have hu3 : ¬ periodicCentreCount (P.withCenters M 2 h2pos hsep hinv) R u <
        ENNReal.ofReal t := fun h => hu (Or.inr h)
    -- the windows agree
    have hwin : M ∩ closedBall u R = P.centers ∩ closedBall u R :=
      leech_centers_inter_closedBall_eq_of_not_mem hD h2pos hsep hinv hPM s hs hu2
    have hfin : (M ∩ closedBall u R).Finite :=
      finite_centers_inter_closedBall (P.withCenters M 2 h2pos hsep hinv) u R
    have hcount' : periodicCentreCount (P.withCenters M 2 h2pos hsep hinv) R u =
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
      leech_good_center_pair_shell (P := P.withCenters M 2 h2pos hsep hinv) hDb le_rfl hD
        hεpos hα0 hshell hu1 hx.1 hx.2 hy.1 hy.2
    have hη0 : 0 ≤ α * ε ^ (1 / 4 : ℝ) := mul_nonneg hα0 (Real.rpow_nonneg hεpos.le _)
    obtain ⟨Φ, p₀, hΦ⟩ := exists_isometry_near_leechSet_of_saturated hLeech (S := M) (u := u)
      hR hη0 hsmall hfin hpair hsep (fun y _ => hsat y) (ht.trans htc')
    exact ⟨Φ, p₀, fun x hx => hΦ x (by rw [hwin]; exact hx)⟩

end E8Leech
