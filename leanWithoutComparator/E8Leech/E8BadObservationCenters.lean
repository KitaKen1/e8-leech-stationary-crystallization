import E8Leech.PeriodicObservation
import E8Leech.E8PeriodicShells
import E8Leech.SPLPackingDensity

/-!
# The actual E8 bad-centre volume budget

Poisson controls the bad representatives. Fundamental-domain unfolding controls
centres whose observation ball meets any periodic translate of them. The density
upper bound is derived from the same actual nonnegative magic deficit.
-/
noncomputable section
namespace E8Leech
open Set MeasureTheory Metric SpherePacking
open scoped BigOperators ENNReal Pointwise

theorem e8_periodic_numReps_le_covolume {P : PeriodicSpherePacking 8}
    {D : Set (Ambient 8)} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) :
    (P.numReps' (by norm_num) hDb : ℝ) ≤ ZLattice.covolume P.lattice volume := by
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have ht : 0 ≤ ∑' p : PeriodicPairs P D, e8PeriodicDeficit P D p :=
    tsum_nonneg (e8PeriodicDeficit_nonneg hP hD)
  have hb := e8_periodic_deficit_total_budget hDb hP hD
  have hn : 0 ≤ (P.numReps' (by norm_num) hDb : ℝ) := by positivity
  have he : (P.numReps' (by norm_num) hDb : ℝ) ^ 2 / ZLattice.covolume P.lattice volume ≤
      (P.numReps' (by norm_num) hDb : ℝ) := by linarith
  have hm := (div_le_iff₀ hc).mp he
  by_cases hz : (P.numReps' (by norm_num) hDb : ℝ) = 0
  · simpa only [hz] using hc.le
  · nlinarith

theorem e8_bad_endpoints_card_sqrt {P : PeriodicSpherePacking 8}
    {D : Set (Ambient 8)} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) :
    ((badPairEndpoints (e8PeriodicBadPairs hDb hP hD (Real.sqrt_pos.mpr hεpos))).card : ℝ) ≤
      2 * (P.numReps' (by norm_num) hDb : ℝ) * Real.sqrt ε := by
  have hτ := Real.sqrt_pos.mpr hεpos
  have hdiv : ε / Real.sqrt ε = Real.sqrt ε := by
    apply (div_eq_iff hτ.ne').mpr
    simpa only [pow_two] using (Real.sq_sqrt hεpos.le).symm
  have hc : ((badPairEndpoints (e8PeriodicBadPairs hDb hP hD hτ)).card : ℝ) ≤
      2 * ((e8PeriodicBadPairs hDb hP hD hτ).card : ℝ) := by
    exact_mod_cast badPairEndpoints_card_le (e8PeriodicBadPairs hDb hP hD hτ)
  refine hc.trans ?_
  have hb := mul_le_mul_of_nonneg_left (e8_periodic_bad_pairs_card hDb hP hD hτ hε)
    (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_div_assoc, hdiv, mul_assoc] using hb

def e8BadObservationCenters {P : PeriodicSpherePacking 8} {D : Set (Ambient 8)}
    (hDb : Bornology.IsBounded D) (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε) (R : ℝ) :
    Set (Ambient 8) := periodicBallNeighborhood P.lattice
      (badPairEndpoints (e8PeriodicBadPairs hDb hP hD (Real.sqrt_pos.mpr hεpos)))
      (fun x => (x : Ambient 8)) R

theorem measurable_e8BadObservationCenters {P : PeriodicSpherePacking 8}
    {D : Set (Ambient 8)} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε) (R : ℝ) :
    MeasurableSet (e8BadObservationCenters hDb hP hD hεpos R) :=
  measurable_periodicBallNeighborhood P.lattice _ _ R

theorem e8_bad_observation_centres_probability_le {P : PeriodicSpherePacking 8}
    {D : Set (Ambient 8)} (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) (R : ℝ) :
    uniformFundamentalDomain D (e8BadObservationCenters hDb hP hD hεpos R) ≤
      ENNReal.ofReal (2 * Real.sqrt ε) * volume (closedBall (0 : Ambient 8) R) := by
  have hf : IsAddFundamentalDomain P.lattice D volume :=
    IsAddFundamentalDomain.mk' hDm.nullMeasurableSet hD
  let s := badPairEndpoints (e8PeriodicBadPairs hDb hP hD (Real.sqrt_pos.mpr hεpos))
  have hc : 0 < ZLattice.covolume P.lattice volume := ZLattice.covolume_pos _ _
  have hv : volume D = ENNReal.ofReal (ZLattice.covolume P.lattice volume) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hf, Measure.real,
      ENNReal.ofReal_toReal (ne_of_lt hDb.measure_lt_top)]
  have hs : (s.card : ℝ) / ZLattice.covolume P.lattice volume ≤ 2 * Real.sqrt ε := by
    apply (div_le_iff₀ hc).mpr
    refine (e8_bad_endpoints_card_sqrt hDb hP hD hεpos hε).trans ?_
    have hb := mul_le_mul_of_nonneg_right (e8_periodic_numReps_le_covolume hDb hP hD)
      (show 0 ≤ 2 * Real.sqrt ε by positivity)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  have he : (s.card : ℝ≥0∞) / volume D ≤ ENNReal.ofReal (2 * Real.sqrt ε) := by
    have hn : (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := by simp
    rw [hn, hv, ← ENNReal.ofReal_div_of_pos hc]
    exact ENNReal.ofReal_le_ofReal hs
  refine (uniform_periodicBallNeighborhood_le P.lattice hf s
    (fun x => (x : Ambient 8)) R).trans ?_
  exact mul_le_mul' he le_rfl

theorem e8_bad_observation_centres_periodCell_le {P : PeriodicSpherePacking 8}
    (L : ℝ) (hL : 0 < L) (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ periodCell 8 L)
    {ε : ℝ} (hεpos : 0 < ε)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num)
      (by simpa only [periodCell, coordinateBox, coordCube] using
        PeriodicConstant.isBounded_coordCube (d := 8) L hL) : ℝ) /
      ZLattice.covolume P.lattice volume) (R : ℝ) :
    uniformPeriodCell 8 L (e8BadObservationCenters
      (by simpa only [periodCell, coordinateBox, coordCube] using
        PeriodicConstant.isBounded_coordCube (d := 8) L hL) hP hD hεpos R) ≤
      ENNReal.ofReal (2 * Real.sqrt ε) * volume (closedBall (0 : Ambient 8) R) := by
  exact e8_bad_observation_centres_probability_le
    (by simpa only [periodCell, coordinateBox, coordCube] using
      PeriodicConstant.isBounded_coordCube (d := 8) L hL)
    (measurable_periodCell 8 L) hP hD hεpos hε R
end E8Leech
