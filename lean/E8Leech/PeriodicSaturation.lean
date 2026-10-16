import E8Leech.E8GoodObservationShells

/-!
# Saturation of a periodic packing (BRR, Step 1)

A periodic packing with separation at least `r` and a nonempty set of centres is contained in a
periodic packing with the same lattice that is still `r`-separated and saturated: every point of
the space is at distance less than `r` from a centre (`exists_saturated_superset`, by Zorn's
lemma). `PeriodicSpherePacking.withCenters` is the packing with the same lattice and a given
invariant separated set of centres; its lattice is the old one by definition.

The centres added by the saturation are few when the density is almost optimal: they are the
orbit of the added representatives, whose number is at most `ε·covol` in dimension eight
(`e8_added_representatives_card_le`), and outside the balls around them the windows of the two
packings agree (`centers_inter_closedBall_eq_of_not_mem`).
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set SpherePacking
open scoped ENNReal

/-- A separated invariant superset of the centres that is maximal, hence saturated. -/
theorem exists_saturated_superset {d : ℕ} (P : PeriodicSpherePacking d) {r : ℝ} (hr : 0 < r)
    (hP : r ≤ P.separation) (hne : P.centers.Nonempty) :
    ∃ M : Set (Ambient d), P.centers ⊆ M ∧ (∀ ℓ ∈ P.lattice, ∀ a ∈ M, ℓ + a ∈ M) ∧
      (∀ x ∈ M, ∀ y ∈ M, x ≠ y → r ≤ dist x y) ∧ ∀ y, ∃ x ∈ M, dist x y < r := by
  let 𝒜 : Set (Set (Ambient d)) := {A | P.centers ⊆ A ∧ (∀ ℓ ∈ P.lattice, ∀ a ∈ A, ℓ + a ∈ A) ∧
    ∀ x ∈ A, ∀ y ∈ A, x ≠ y → r ≤ dist x y}
  have h0 : P.centers ∈ 𝒜 :=
    ⟨subset_rfl, fun ℓ hℓ a ha => P.lattice_action hℓ ha,
      fun x hx y hy hne => hP.trans (P.centers_dist' x y hx hy hne)⟩
  have hchain : ∀ c ⊆ 𝒜, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ 𝒜, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hch hcne
    refine ⟨⋃₀ c, ⟨?_, ?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨s, hs⟩ := hcne
      exact (hc hs).1.trans (Set.subset_sUnion_of_mem hs)
    · rintro ℓ hℓ a ⟨s, hs, has⟩
      exact ⟨s, hs, (hc hs).2.1 ℓ hℓ a has⟩
    · rintro x ⟨s₁, hs₁, hx⟩ y ⟨s₂, hs₂, hy⟩ hxy
      rcases hch.total hs₁ hs₂ with h | h
      · exact (hc hs₂).2.2 x (h hx) y hy hxy
      · exact (hc hs₁).2.2 x hx y (h hy) hxy
  obtain ⟨M, hPM, hmax⟩ := zorn_subset_nonempty 𝒜 hchain P.centers h0
  obtain ⟨hM1, hM2, hM3⟩ := hmax.1
  refine ⟨M, hPM, hM2, hM3, fun y => ?_⟩
  by_contra hcon
  have hfar : ∀ x ∈ M, r ≤ dist x y := fun x hx => by
    by_contra hlt
    exact hcon ⟨x, hx, lt_of_not_ge hlt⟩
  obtain ⟨x₀, hx₀⟩ := hne
  -- nonzero lattice vectors have norm at least `r`
  have hlat : ∀ ℓ ∈ P.lattice, ℓ ≠ 0 → r ≤ ‖ℓ‖ := by
    intro ℓ hℓ hℓ0
    have h1 := P.centers_dist' (ℓ + x₀) x₀ (P.lattice_action hℓ hx₀) hx₀
      (fun e => hℓ0 (by simpa using e))
    rw [dist_eq_norm, add_sub_cancel_right] at h1
    exact hP.trans h1
  -- the orbit of `y` can be added
  have hM' : M ∪ {z | ∃ ℓ ∈ P.lattice, z = ℓ + y} ∈ 𝒜 := by
    refine ⟨hPM.trans Set.subset_union_left, ?_, ?_⟩
    · rintro ℓ hℓ a (ha | ⟨ℓ', hℓ', rfl⟩)
      · exact Or.inl (hM2 ℓ hℓ a ha)
      · exact Or.inr ⟨ℓ + ℓ', P.lattice.add_mem hℓ hℓ', by abel⟩
    · rintro x (hx | ⟨ℓ, hℓ, rfl⟩) z (hz | ⟨ℓ', hℓ', rfl⟩) hxz
      · exact hM3 x hx z hz hxz
      · have h1 := hfar (-ℓ' + x) (hM2 (-ℓ') (P.lattice.neg_mem hℓ') x hx)
        rw [dist_eq_norm] at h1 ⊢
        have e : x - (ℓ' + y) = -ℓ' + x - y := by abel
        rw [e]
        exact h1
      · have h1 := hfar (-ℓ + z) (hM2 (-ℓ) (P.lattice.neg_mem hℓ) z hz)
        rw [dist_eq_norm] at h1 ⊢
        have e : ℓ + y - z = -(-ℓ + z - y) := by abel
        rw [e, norm_neg]
        exact h1
      · have hne' : ℓ - ℓ' ≠ 0 := fun e => hxz (by rw [sub_eq_zero.mp e])
        have h1 := hlat (ℓ - ℓ') (P.lattice.sub_mem hℓ hℓ') hne'
        rw [dist_eq_norm]
        have e : ℓ + y - (ℓ' + y) = ℓ - ℓ' := by abel
        rw [e]
        exact h1
  have hsub := hmax.2 hM' Set.subset_union_left
  have hy : y ∈ M := hsub (Or.inr ⟨0, P.lattice.zero_mem, by simp⟩)
  have h2 := hfar y hy
  rw [dist_self] at h2
  linarith

/-- The periodic packing with the same lattice and a given invariant separated set of
centres. -/
def _root_.PeriodicSpherePacking.withCenters {d : ℕ} (P : PeriodicSpherePacking d)
    (M : Set (Ambient d)) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ x ∈ M, ∀ y ∈ M, x ≠ y → r ≤ dist x y)
    (hinv : ∀ ℓ ∈ P.lattice, ∀ a ∈ M, ℓ + a ∈ M) : PeriodicSpherePacking d where
  centers := M
  separation := r
  separation_pos := hr
  centers_dist := fun x y hne => hsep x.1 x.2 y.1 y.2 fun e => hne (Subtype.ext e)
  lattice := P.lattice
  lattice_action := fun x y hx hy => hinv x hx y hy
  lattice_discrete := P.lattice_discrete
  lattice_isZLattice := P.lattice_isZLattice

theorem numReps'_eq_ncard {d : ℕ} (P : PeriodicSpherePacking d) (hd : 0 < d)
    {D : Set (Ambient d)} (hDb : Bornology.IsBounded D) :
    P.numReps' hd hDb = (P.centers ∩ D).ncard := by
  have h : P.numReps' hd hDb =
      @Fintype.card ↥(P.centers ∩ D) (P.instFintypeNumReps' hd hDb) := rfl
  rw [h, ← Nat.card_coe_set_eq, @Nat.card_eq_fintype_card _ (P.instFintypeNumReps' hd hDb)]

theorem finite_centers_inter {d : ℕ} (P : PeriodicSpherePacking d) (hd : 0 < d)
    {D : Set (Ambient d)} (hDb : Bornology.IsBounded D) : (P.centers ∩ D).Finite := by
  have h := finite_centers_inter_of_isBounded P D hDb hd
  exact Set.toFinite _

/-- The representatives added by an enlargement of the set of centres. -/
theorem ncard_added_representatives {d : ℕ} (hd : 0 < d) (P : PeriodicSpherePacking d)
    {M : Set (Ambient d)} {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ M, ∀ y ∈ M, x ≠ y → r ≤ dist x y)
    (hinv : ∀ ℓ ∈ P.lattice, ∀ a ∈ M, ℓ + a ∈ M) (hPM : P.centers ⊆ M) {D : Set (Ambient d)}
    (hDb : Bornology.IsBounded D) :
    ((M ∩ D) \ P.centers).ncard + P.numReps' hd hDb =
      (P.withCenters M r hr hsep hinv).numReps' hd hDb := by
  rw [numReps'_eq_ncard, numReps'_eq_ncard]
  have hfin : (M ∩ D).Finite := finite_centers_inter (P.withCenters M r hr hsep hinv) hd hDb
  have hMD : M ∩ D = ((M ∩ D) \ P.centers) ∪ (P.centers ∩ D) := by
    ext x
    constructor
    · intro hx
      by_cases h : x ∈ P.centers
      · exact Or.inr ⟨h, hx.2⟩
      · exact Or.inl ⟨hx, h⟩
    · rintro (⟨hx, _⟩ | ⟨hx, hxD⟩)
      · exact hx
      · exact ⟨hPM hx, hxD⟩
  have hdisj : Disjoint ((M ∩ D) \ P.centers) (P.centers ∩ D) :=
    Set.disjoint_left.mpr fun x hx hx' => hx.2 hx'.1
  have h1 := Set.ncard_union_eq hdisj (hfin.subset Set.sdiff_subset)
    (hfin.subset fun x hx => ⟨hPM hx.1, hx.2⟩)
  rw [← hMD] at h1
  exact h1.symm

/-- In dimension eight a saturation adds at most `ε·covol` representatives to a packing of
density at least `1 - ε`. -/
theorem e8_added_representatives_card_le {P : PeriodicSpherePacking 8} {D : Set (Ambient 8)}
    (hDb : Bornology.IsBounded D) (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D)
    {M : Set (Ambient 8)} (hsep : ∀ x ∈ M, ∀ y ∈ M, x ≠ y → Real.sqrt 2 ≤ dist x y)
    (hinv : ∀ ℓ ∈ P.lattice, ∀ a ∈ M, ℓ + a ∈ M) (hPM : P.centers ⊆ M) {ε : ℝ}
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) / ZLattice.covolume P.lattice volume) :
    (((M ∩ D) \ P.centers).ncard : ℝ) ≤ ε * ZLattice.covolume P.lattice volume := by
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 := ncard_added_representatives (by norm_num : 0 < 8) P hs2 hsep hinv hPM hDb
  have h2 : ((P.withCenters M (Real.sqrt 2) hs2 hsep hinv).numReps' (by norm_num) hDb : ℝ) ≤
      ZLattice.covolume P.lattice volume :=
    e8_periodic_numReps_le_covolume (P := P.withCenters M (Real.sqrt 2) hs2 hsep hinv) hDb le_rfl hD
  have h3 : (1 - ε) * ZLattice.covolume P.lattice volume ≤
      (P.numReps' (by norm_num) hDb : ℝ) := (le_div_iff₀ hc).mp hε
  have h4 : (((M ∩ D) \ P.centers).ncard : ℝ) + (P.numReps' (by norm_num) hDb : ℝ) =
      ((P.withCenters M (Real.sqrt 2) hs2 hsep hinv).numReps' (by norm_num) hDb : ℝ) := by
    exact_mod_cast h1
  linarith

/-- Outside the balls around the orbit of the added representatives, the windows of the two
packings agree. -/
theorem centers_inter_closedBall_eq_of_not_mem {P : PeriodicSpherePacking 8}
    {D : Set (Ambient 8)} (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {M : Set (Ambient 8)}
    {r : ℝ} (hr : 0 < r) (hsep : ∀ x ∈ M, ∀ y ∈ M, x ≠ y → r ≤ dist x y)
    (hinv : ∀ ℓ ∈ P.lattice, ∀ a ∈ M, ℓ + a ∈ M) (hPM : P.centers ⊆ M)
    (s : Finset (Ambient 8)) (hs : ∀ x, x ∈ (M ∩ D) \ P.centers → x ∈ s) {u : Ambient 8}
    {R : ℝ} (hu : u ∉ periodicBallNeighborhood P.lattice s (fun b => b) R) :
    M ∩ closedBall u R = P.centers ∩ closedBall u R := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxM, hxR⟩
    refine ⟨?_, hxR⟩
    obtain ⟨v, ℓ, rfl⟩ :=
      exists_periodic_rep_translate (P := P.withCenters M r hr hsep hinv) hD hxM
    by_cases hv : (v : Ambient 8) ∈ P.centers
    · have h := P.lattice_action ℓ.2 hv
      rwa [add_comm] at h
    · exact absurd hxR (not_mem_periodicBallNeighborhood P.lattice hu (hs _ ⟨v.2, hv⟩) ℓ)
  · exact fun x hx => ⟨hPM hx.1, hx.2⟩

/-- The balls around the orbit of the added representatives have small probability. -/
theorem e8_added_neighborhood_probability_le {P : PeriodicSpherePacking 8}
    {D : Set (Ambient 8)} (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {M : Set (Ambient 8)}
    (hsep : ∀ x ∈ M, ∀ y ∈ M, x ≠ y → Real.sqrt 2 ≤ dist x y)
    (hinv : ∀ ℓ ∈ P.lattice, ∀ a ∈ M, ℓ + a ∈ M) (hPM : P.centers ⊆ M) {ε : ℝ}
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) / ZLattice.covolume P.lattice volume)
    (R : ℝ) :
    ∃ s : Finset (Ambient 8), (∀ x, x ∈ (M ∩ D) \ P.centers → x ∈ s) ∧
      uniformFundamentalDomain D (periodicBallNeighborhood P.lattice s (fun b => b) R) ≤
        ENNReal.ofReal ε * volume (closedBall (0 : Ambient 8) R) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hfin : (M ∩ D).Finite :=
    finite_centers_inter (P.withCenters M (Real.sqrt 2) hs2 hsep hinv) (by norm_num) hDb
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
    exact e8_added_representatives_card_le hDb hD hsep hinv hPM hε
  have he : (hfinA.toFinset.card : ℝ≥0∞) / volume D ≤ ENNReal.ofReal ε := by
    have hn : (hfinA.toFinset.card : ℝ≥0∞) = ENNReal.ofReal (hfinA.toFinset.card : ℝ) := by simp
    rw [hn, hv, ← ENNReal.ofReal_div_of_pos hc]
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hc).mpr hcard)
  exact (uniform_periodicBallNeighborhood_le P.lattice hf hfinA.toFinset (fun b => b) R).trans
    (mul_le_mul' he le_rfl)

end E8Leech
