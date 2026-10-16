import E8Leech.E8BadObservationCenters
import E8Leech.LeechPeriodicDeficit
import E8Leech.BRRGramApproximation

/-!
# Bad observation centres and local shell control for the Leech magic function

The dimension 24 version of `E8BadObservationCenters` and `E8GoodObservationShells`, for periodic
packings of separation at least `2` and the magic function `f` of Sphere-Packing-Lean.

Poisson summation controls the bad representatives (`leech_bad_endpoints_card_sqrt`).
Fundamental-domain unfolding controls the centres whose observation ball meets a periodic
translate of them (`leech_bad_observation_centres_probability_le`). Every point in a good
observation ball has a representative untouched by the bad-pair deletion, so the magic deficit of
all pairs in the ball is small, including pairs across periodic boundaries
(`leech_good_center_pair_magic_small`), and a shell estimate for `f` gives almost even squared
distances (`leech_good_center_pair_shell`).
-/
noncomputable section
namespace E8Leech
open Set MeasureTheory Metric SpherePacking
open scoped BigOperators ENNReal Pointwise InnerProductSpace

theorem leech_periodic_numReps_le_covolume {P : PeriodicSpherePacking 24}
    {D : Set (Ambient 24)} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) :
    (P.numReps' (by norm_num) hDb : ℝ) ≤ ZLattice.covolume P.lattice volume := by
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have ht : 0 ≤ ∑' p : LeechPeriodicPairs P D, leechPeriodicDeficit P D p :=
    tsum_nonneg (leechPeriodicDeficit_nonneg hP hD)
  have hb := leech_periodic_deficit_total_budget hDb hP hD
  have hn : 0 ≤ (P.numReps' (by norm_num) hDb : ℝ) := by positivity
  have he : (P.numReps' (by norm_num) hDb : ℝ) ^ 2 / ZLattice.covolume P.lattice volume ≤
      (P.numReps' (by norm_num) hDb : ℝ) := by linarith
  have hm := (div_le_iff₀ hc).mp he
  by_cases hz : (P.numReps' (by norm_num) hDb : ℝ) = 0
  · simpa only [hz] using hc.le
  · nlinarith

theorem leech_bad_endpoints_card_sqrt {P : PeriodicSpherePacking 24}
    {D : Set (Ambient 24)} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) :
    ((badPairEndpoints
      (leechPeriodicBadPairs hDb hP hD (Real.sqrt_pos.mpr hεpos))).card : ℝ) ≤
      2 * (P.numReps' (by norm_num) hDb : ℝ) * Real.sqrt ε := by
  have hτ := Real.sqrt_pos.mpr hεpos
  have hdiv : ε / Real.sqrt ε = Real.sqrt ε := by
    apply (div_eq_iff hτ.ne').mpr
    simpa only [pow_two] using (Real.sq_sqrt hεpos.le).symm
  have hc : ((badPairEndpoints (leechPeriodicBadPairs hDb hP hD hτ)).card : ℝ) ≤
      2 * ((leechPeriodicBadPairs hDb hP hD hτ).card : ℝ) := by
    exact_mod_cast badPairEndpoints_card_le (leechPeriodicBadPairs hDb hP hD hτ)
  refine hc.trans ?_
  have hb := mul_le_mul_of_nonneg_left (leech_periodic_bad_pairs_card hDb hP hD hτ hε)
    (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_div_assoc, hdiv, mul_assoc] using hb

/-- The observation centres whose ball of radius `R` meets a periodic translate of an endpoint
of a pair with large Leech magic deficit. -/
def leechBadObservationCenters {P : PeriodicSpherePacking 24} {D : Set (Ambient 24)}
    (hDb : Bornology.IsBounded D) (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε) (R : ℝ) :
    Set (Ambient 24) := periodicBallNeighborhood P.lattice
      (badPairEndpoints (leechPeriodicBadPairs hDb hP hD (Real.sqrt_pos.mpr hεpos)))
      (fun x => (x : Ambient 24)) R

theorem measurable_leechBadObservationCenters {P : PeriodicSpherePacking 24}
    {D : Set (Ambient 24)} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε) (R : ℝ) :
    MeasurableSet (leechBadObservationCenters hDb hP hD hεpos R) :=
  measurable_periodicBallNeighborhood P.lattice _ _ R

theorem leech_bad_observation_centres_probability_le {P : PeriodicSpherePacking 24}
    {D : Set (Ambient 24)} (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) (R : ℝ) :
    uniformFundamentalDomain D (leechBadObservationCenters hDb hP hD hεpos R) ≤
      ENNReal.ofReal (2 * Real.sqrt ε) * volume (closedBall (0 : Ambient 24) R) := by
  have hf : IsAddFundamentalDomain P.lattice D volume :=
    IsAddFundamentalDomain.mk' hDm.nullMeasurableSet hD
  let s := badPairEndpoints (leechPeriodicBadPairs hDb hP hD (Real.sqrt_pos.mpr hεpos))
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have hv : volume D = ENNReal.ofReal (ZLattice.covolume P.lattice volume) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hf, Measure.real,
      ENNReal.ofReal_toReal (ne_of_lt hDb.measure_lt_top)]
  have hs : (s.card : ℝ) / ZLattice.covolume P.lattice volume ≤ 2 * Real.sqrt ε := by
    apply (div_le_iff₀ hc).mpr
    refine (leech_bad_endpoints_card_sqrt hDb hP hD hεpos hε).trans ?_
    have hb := mul_le_mul_of_nonneg_right (leech_periodic_numReps_le_covolume hDb hP hD)
      (show 0 ≤ 2 * Real.sqrt ε by positivity)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  have he : (s.card : ℝ≥0∞) / volume D ≤ ENNReal.ofReal (2 * Real.sqrt ε) := by
    have hn : (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := by simp
    rw [hn, hv, ← ENNReal.ofReal_div_of_pos hc]
    exact ENNReal.ofReal_le_ofReal hs
  refine (uniform_periodicBallNeighborhood_le P.lattice hf s
    (fun x => (x : Ambient 24)) R).trans ?_
  exact mul_le_mul' he le_rfl

/-- Decompose a packing centre into a representative and a lattice shift. -/
theorem exists_leech_periodic_rep_translate {P : PeriodicSpherePacking 24}
    {D : Set (Ambient 24)} (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D)
    {x : Ambient 24} (hx : x ∈ P.centers) :
    ∃ v : LeechPeriodicReps P D, ∃ ℓ : P.lattice, x = (v : Ambient 24) + ℓ := by
  obtain ⟨ℓ, hℓ, _⟩ := hD x
  let v : LeechPeriodicReps P D := ⟨ℓ +ᵥ x, P.lattice_action ℓ.property hx, hℓ⟩
  refine ⟨v, -ℓ, ?_⟩
  simp only [v, Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg]
  abel

theorem leech_good_center_pair_magic_small {P : PeriodicSpherePacking 24}
    {D : Set (Ambient 24)} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε)
    {R : ℝ} {u x y : Ambient 24}
    (hu : u ∉ leechBadObservationCenters hDb hP hD hεpos R)
    (hx : x ∈ P.centers) (hxR : x ∈ closedBall u R) (hy : y ∈ P.centers)
    (hxy : x ≠ y) : |(Dim24.f (x - y)).re| < Real.sqrt ε := by
  classical
  obtain ⟨v, ℓ, rfl⟩ := exists_leech_periodic_rep_translate hD hx
  obtain ⟨w, m, rfl⟩ := exists_leech_periodic_rep_translate hD hy
  have hv : v ∉ badPairEndpoints
      (leechPeriodicBadPairs hDb hP hD (Real.sqrt_pos.mpr hεpos)) := by
    intro hb
    exact (not_mem_periodicBallNeighborhood P.lattice hu hb ℓ) hxR
  have hsmall := leech_periodic_good_pair_deficit_lt hDb hP hD
    (Real.sqrt_pos.mpr hεpos) v w hv (ℓ - m)
  have he : (v : Ambient 24) - w + (ℓ - m : P.lattice) =
      (v : Ambient 24) + ℓ - ((w : Ambient 24) + m) := by
    simp only [Submodule.coe_sub]
    abel
  have hd : ¬(v = w ∧ ℓ - m = 0) := by
    rintro ⟨hvw, hℓm⟩
    apply hxy
    exact congrArg₂ (fun a b : Ambient 24 => a + b)
      (congrArg Subtype.val hvw) (congrArg Subtype.val (sub_eq_zero.mp hℓm))
  have hn : -(Dim24.f ((v : Ambient 24) + ℓ - ((w : Ambient 24) + m))).re < Real.sqrt ε := by
    simpa only [leechPeriodicDeficit, hd, ↓reduceIte, he] using hsmall
  have hdist := hP.trans (P.centers_dist' _ _ hx hy hxy)
  have hmin : 2 ≤ ‖(v : Ambient 24) + ℓ - ((w : Ambient 24) + m)‖ := by
    simpa only [dist_eq_norm] using hdist
  have hsign := Dim24.f_cohnElkies₁ ((v : Ambient 24) + ℓ - ((w : Ambient 24) + m)) hmin
  simpa only [abs_of_nonpos hsign] using hn

/-- **Almost even squared distances in a good observation ball** in dimension 24. -/
theorem leech_good_center_pair_shell {P : PeriodicSpherePacking 24}
    {D : Set (Ambient 24)} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε)
    {R α : ℝ} (hα : 0 ≤ α)
    (hshell : ∀ z : Ambient 24, 2 ≤ ‖z‖ → ‖z‖ ≤ 2 * R →
      ∃ k : ℤ, 2 ≤ k ∧ |‖z‖ ^ 2 - 2 * k| ≤ α * Real.sqrt |(Dim24.f z).re|)
    {u : Ambient 24} (hu : u ∉ leechBadObservationCenters hDb hP hD hεpos R)
    {x y : Ambient 24} (hx : x ∈ P.centers) (hxR : x ∈ closedBall u R)
    (hy : y ∈ P.centers) (hyR : y ∈ closedBall u R) :
    ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ α * ε ^ (1 / 4 : ℝ) := by
  by_cases hxy : x = y
  · subst y
    refine ⟨0, ?_⟩
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), Int.cast_zero,
      mul_zero, sub_zero, abs_zero] using
      mul_nonneg hα (Real.rpow_nonneg hεpos.le (1 / 4 : ℝ))
  · have hmin : 2 ≤ ‖x - y‖ := by
      simpa only [dist_eq_norm] using hP.trans (P.centers_dist' _ _ hx hy hxy)
    have hmax : ‖x - y‖ ≤ 2 * R := by
      have hx' : dist x u ≤ R := Metric.mem_closedBall.mp hxR
      have hy' : dist u y ≤ R := by
        simpa only [dist_comm] using Metric.mem_closedBall.mp hyR
      have hd : dist x y ≤ 2 * R := by linarith [dist_triangle x u y]
      simpa only [dist_eq_norm] using hd
    obtain ⟨k, _, hk⟩ := hshell (x - y) hmin hmax
    have hg := (leech_good_center_pair_magic_small hDb hP hD hεpos hu hx hxR hy hxy).le
    have hquarter : Real.sqrt (Real.sqrt ε) = ε ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hεpos.le]
      norm_num
    refine ⟨k, hk.trans ?_⟩
    simpa only [hquarter] using mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) hα

end E8Leech
