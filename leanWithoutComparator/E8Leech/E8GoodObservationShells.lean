import E8Leech.E8BadObservationCenters
import E8Leech.BRRGramApproximation

/-!
# Uniform local E8 shell control outside the actual bad-centre set

Every point in a good observation ball has a representative untouched by
bad-pair deletion. The previously proved actual magic estimate then applies to
all pairs in the ball, including pairs across periodic boundaries.
-/
noncomputable section
namespace E8Leech
open Set MeasureTheory Metric SpherePacking
open scoped ENNReal BigOperators InnerProductSpace

/-- Decompose an actual packing centre into a representative and a lattice shift. -/
theorem exists_periodic_rep_translate {P : PeriodicSpherePacking 8}
    {D : Set (Ambient 8)} (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D)
    {x : Ambient 8} (hx : x ∈ P.centers) :
    ∃ v : PeriodicReps P D, ∃ ℓ : P.lattice, x = (v : Ambient 8) + ℓ := by
  obtain ⟨ℓ, hℓ, _⟩ := hD x
  let v : PeriodicReps P D := ⟨ℓ +ᵥ x, P.lattice_action ℓ.property hx, hℓ⟩
  refine ⟨v, -ℓ, ?_⟩
  simp only [v, Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg]
  abel

theorem e8_good_center_pair_magic_small {P : PeriodicSpherePacking 8}
    {D : Set (Ambient 8)} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε)
    {R : ℝ} {u x y : Ambient 8}
    (hu : u ∉ e8BadObservationCenters hDb hP hD hεpos R)
    (hx : x ∈ P.centers) (hxR : x ∈ closedBall u R) (hy : y ∈ P.centers)
    (hxy : x ≠ y) : |(_root_.g (x - y)).re| < Real.sqrt ε := by
  classical
  obtain ⟨v, ℓ, rfl⟩ := exists_periodic_rep_translate hD hx
  obtain ⟨w, m, rfl⟩ := exists_periodic_rep_translate hD hy
  have hv : v ∉ badPairEndpoints
      (e8PeriodicBadPairs hDb hP hD (Real.sqrt_pos.mpr hεpos)) := by
    intro hb
    exact (not_mem_periodicBallNeighborhood P.lattice hu hb ℓ) hxR
  have hsmall := e8_periodic_good_pair_deficit_lt hDb hP hD
    (Real.sqrt_pos.mpr hεpos) v w hv (ℓ - m)
  have he : (v : Ambient 8) - w + (ℓ - m : P.lattice) =
      (v : Ambient 8) + ℓ - ((w : Ambient 8) + m) := by
    simp only [Submodule.coe_sub]
    abel
  have hd : ¬(v = w ∧ ℓ - m = 0) := by
    rintro ⟨hvw, hℓm⟩
    apply hxy
    exact congrArg₂ (fun a b : Ambient 8 => a + b)
      (congrArg Subtype.val hvw) (congrArg Subtype.val (sub_eq_zero.mp hℓm))
  have hn : -(_root_.g ((v : Ambient 8) + ℓ - ((w : Ambient 8) + m))).re < Real.sqrt ε := by
    simpa only [e8PeriodicDeficit, hd, ↓reduceIte, he] using hsmall
  have hdist := hP.trans (P.centers_dist' _ _ hx hy hxy)
  have hmin : Real.sqrt 2 ≤ ‖(v : Ambient 8) + ℓ - ((w : Ambient 8) + m)‖ := by
    simpa only [dist_eq_norm] using hdist
  have hsign := MagicFunction.g.CohnElkies.g_nonpos_of_norm_sq_ge_two
    ((v : Ambient 8) + ℓ - ((w : Ambient 8) + m))
    (by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2])
  simpa only [abs_of_nonpos hsign] using hn

theorem e8_good_center_pair_shell {P : PeriodicSpherePacking 8}
    {D : Set (Ambient 8)} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε)
    {R α : ℝ} (hα : 0 ≤ α)
    (hshell : ∀ z : Ambient 8, Real.sqrt 2 ≤ ‖z‖ → ‖z‖ ≤ 2 * R →
      ∃ k : ℤ, 1 ≤ k ∧ |‖z‖ ^ 2 - 2 * k| ≤ α * Real.sqrt |(_root_.g z).re|)
    {u : Ambient 8} (hu : u ∉ e8BadObservationCenters hDb hP hD hεpos R)
    {x y : Ambient 8} (hx : x ∈ P.centers) (hxR : x ∈ closedBall u R)
    (hy : y ∈ P.centers) (hyR : y ∈ closedBall u R) :
    ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ α * ε ^ (1 / 4 : ℝ) := by
  by_cases hxy : x = y
  · subst y
    refine ⟨0, ?_⟩
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), Int.cast_zero,
      mul_zero, sub_zero, abs_zero] using
      mul_nonneg hα (Real.rpow_nonneg hεpos.le (1 / 4 : ℝ))
  · have hmin : Real.sqrt 2 ≤ ‖x - y‖ := by
      simpa only [dist_eq_norm] using hP.trans (P.centers_dist' _ _ hx hy hxy)
    have hmax : ‖x - y‖ ≤ 2 * R := by
      have hx' : dist x u ≤ R := Metric.mem_closedBall.mp hxR
      have hy' : dist u y ≤ R := by
        simpa only [dist_comm] using Metric.mem_closedBall.mp hyR
      have hd : dist x y ≤ 2 * R := by linarith [dist_triangle x u y]
      simpa only [dist_eq_norm] using hd
    obtain ⟨k, _, hk⟩ := hshell (x - y) hmin hmax
    have hg := (e8_good_center_pair_magic_small hDb hP hD hεpos hu hx hxR hy hxy).le
    have hquarter : Real.sqrt (Real.sqrt ε) = ε ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hεpos.le]
      norm_num
    refine ⟨k, hk.trans ?_⟩
    simpa only [hquarter] using mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) hα

theorem e8_good_center_shells_and_integer_gram {P : PeriodicSpherePacking 8}
    {D : Set (Ambient 8)} (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℝ, 1 < R →
      ∃ α : ℝ, 1 < α ∧ α ≤ ρ * (2 * R) ^ (3 / 2 : ℝ) * Real.exp (5 * Real.pi * (2 * R) / 4) ∧
        ∃ S : Set (Ambient 8), MeasurableSet S ∧
          uniformFundamentalDomain D S ≤ ENNReal.ofReal (2 * Real.sqrt ε) *
            volume (closedBall (0 : Ambient 8) R) ∧
          ∀ u ∉ S,
            (∀ x ∈ P.centers ∩ closedBall u R, ∀ y ∈ P.centers ∩ closedBall u R,
              ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ α * ε ^ (1 / 4 : ℝ)) ∧
            (∀ a ∈ P.centers ∩ closedBall u R, ∀ x ∈ P.centers ∩ closedBall u R,
              ∀ y ∈ P.centers ∩ closedBall u R, ∃ m : ℤ,
                |⟪x - a, y - a⟫_ℝ - m| ≤ 3 / 2 * (α * ε ^ (1 / 4 : ℝ))) := by
  obtain ⟨ρ, hρ, hbound⟩ := e8_magic_even_shell_exponential_bound
  refine ⟨ρ, hρ, ?_⟩
  intro R hR
  obtain ⟨α, hα, hαb, hshell⟩ := hbound (2 * R) (by linarith)
  let S := e8BadObservationCenters hDb hP hD hεpos R
  refine ⟨α, hα, hαb, S, measurable_e8BadObservationCenters hDb hP hD hεpos R,
    e8_bad_observation_centres_probability_le hDb hDm hP hD hεpos hε R, ?_⟩
  intro u hu
  have hpairs : ∀ x ∈ P.centers ∩ closedBall u R, ∀ y ∈ P.centers ∩ closedBall u R,
      ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ α * ε ^ (1 / 4 : ℝ) := by
    intro x hx y hy
    exact e8_good_center_pair_shell hDb hP hD hεpos (by linarith) hshell hu hx.1 hx.2 hy.1 hy.2
  refine ⟨hpairs, ?_⟩
  intro a ha x hx y hy
  have he : (x - a) - (y - a) = x - y := by abel
  exact exists_integer_inner_approx (hpairs x hx a ha) (hpairs y hy a ha)
    (by simpa only [he] using hpairs x hx y hy)
end E8Leech
