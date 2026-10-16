import SpherePacking.CohnElkies.LPBound
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.RealValued
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.SignConditions
import E8Leech.SeriesDeficit
import E8Leech.E8MagicExponentialBounds
import Mathlib.Tactic.FieldSimp

/-!
# Actual E8 magic deficit in a periodic packing

The diagonal is removed explicitly. Poisson summation bounds the remaining
nonnegative deficit by `N - N² / covolume`, which supplies the bad-pair budget.
-/
noncomputable section
namespace E8Leech
open scoped BigOperators FourierTransform
open SpherePacking MeasureTheory Classical
open MagicFunction.g.CohnElkies

abbrev PeriodicReps (P : PeriodicSpherePacking 8) (D : Set (EuclideanSpace ℝ (Fin 8))) :=
  ↥(P.centers ∩ D)

abbrev PeriodicPairs (P : PeriodicSpherePacking 8) (D : Set (EuclideanSpace ℝ (Fin 8))) :=
  (PeriodicReps P D × PeriodicReps P D) × P.lattice

def e8PeriodicDeficit (P : PeriodicSpherePacking 8) (D : Set (EuclideanSpace ℝ (Fin 8)))
    (p : PeriodicPairs P D) : ℝ :=
  if p.1.1 = p.1.2 ∧ p.2 = 0 then 0 else
    -(_root_.g ((p.1.1 : EuclideanSpace ℝ (Fin 8)) - p.1.2 + p.2)).re

private theorem reps_translate_eq_iff {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))}
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D)
    (x y : PeriodicReps P D) (ℓ : P.lattice) :
    (x : EuclideanSpace ℝ (Fin 8)) - y + ℓ = 0 ↔ x = y ∧ ℓ = 0 := by
  constructor
  · intro h
    obtain ⟨a, _, hu⟩ := hD (x : EuclideanSpace ℝ (Fin 8))
    have h0 : (0 : P.lattice) +ᵥ (x : EuclideanSpace ℝ (Fin 8)) ∈ D := by
      simpa [Submodule.vadd_def] using x.property.2
    have hl : ℓ +ᵥ (x : EuclideanSpace ℝ (Fin 8)) ∈ D := by
      have he : (ℓ : EuclideanSpace ℝ (Fin 8)) + x = y := by
        have ht : (x : EuclideanSpace ℝ (Fin 8)) + ℓ - y = 0 := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
        simpa [add_comm] using sub_eq_zero.mp ht
      simpa [Submodule.vadd_def, he] using y.property.2
    have he : ℓ = 0 := (hu ℓ hl).trans (hu 0 h0).symm
    refine ⟨Subtype.ext ?_, he⟩
    simpa [he] using sub_eq_zero.mp (by simpa [he] using h)
  · rintro ⟨rfl, rfl⟩
    simp

theorem e8PeriodicDeficit_nonneg {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) (p : PeriodicPairs P D) :
    0 ≤ e8PeriodicDeficit P D p := by
  classical
  unfold e8PeriodicDeficit
  split_ifs with hd
  · rfl
  · have hn : (p.1.1 : EuclideanSpace ℝ (Fin 8)) + p.2 ≠ p.1.2 := by
      intro he
      apply hd
      apply (reps_translate_eq_iff hD _ _ _).mp
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using sub_eq_zero.mpr he
    have hc : (p.1.1 : EuclideanSpace ℝ (Fin 8)) + p.2 ∈ P.centers := by
      simpa [add_comm] using P.lattice_action p.2.property p.1.1.property.1
    have hb := hP.trans (P.centers_dist' _ _ hc p.1.2.property.1 hn)
    have hr : Real.sqrt 2 ≤ ‖(p.1.1 : EuclideanSpace ℝ (Fin 8)) - p.1.2 + p.2‖ := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hb
    apply neg_nonneg.mpr
    apply g_nonpos_of_norm_sq_ge_two
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem summable_e8PeriodicDeficit_lattice {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (x y : PeriodicReps P D) :
    Summable (fun ℓ : P.lattice => e8PeriodicDeficit P D ((x, y), ℓ)) := by
  classical
  have hs := CohnElkies.LPBoundSummability.summable_lattice_translate_re
    (Λ := P.lattice) (f := _root_.g) (a := (x : EuclideanSpace ℝ (Fin 8)) - y)
  by_cases hxy : x = y
  · have he : (fun ℓ : P.lattice => e8PeriodicDeficit P D ((x, y), ℓ)) =
        {ℓ : P.lattice | ℓ ≠ 0}.indicator
          (fun ℓ => -(_root_.g ((x : EuclideanSpace ℝ (Fin 8)) - y + ℓ)).re) := by
      funext ℓ
      by_cases hl : ℓ = 0 <;> simp [e8PeriodicDeficit, hxy, hl, Set.indicator]
    rw [he]
    exact hs.neg.indicator _
  · simpa [e8PeriodicDeficit, hxy] using hs.neg

theorem e8PeriodicDeficit_lattice_sum {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (x y : PeriodicReps P D) :
    (∑' ℓ : P.lattice, e8PeriodicDeficit P D ((x, y), ℓ)) =
      (if x = y then 1 else 0) -
        ∑' ℓ : P.lattice, (_root_.g ((x : EuclideanSpace ℝ (Fin 8)) - y + ℓ)).re := by
  classical
  have hs := CohnElkies.LPBoundSummability.summable_lattice_translate_re
    (Λ := P.lattice) (f := _root_.g) (a := (x : EuclideanSpace ℝ (Fin 8)) - y)
  by_cases hxy : x = y
  · subst y
    have hs0 : Summable (fun ℓ : P.lattice => (_root_.g (ℓ : EuclideanSpace ℝ (Fin 8))).re) := by
      simpa only [sub_self, zero_add] using hs
    have he := hs0.tsum_eq_add_tsum_ite (0 : P.lattice)
    have hi : (∑' ℓ : P.lattice, if ℓ = 0 then 0 else
        (_root_.g (ℓ : EuclideanSpace ℝ (Fin 8))).re) =
        -(∑' ℓ : P.lattice, e8PeriodicDeficit P D ((x, x), ℓ)) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro ℓ
      by_cases hl : ℓ = 0 <;> simp [e8PeriodicDeficit, hl]
    have hz : (_root_.g ((0 : P.lattice) : EuclideanSpace ℝ (Fin 8))).re = 1 := by
      simp only [Submodule.coe_zero, g_zero, Complex.one_re]
    rw [hz, hi] at he
    have hout : (∑' ℓ : P.lattice, e8PeriodicDeficit P D ((x, x), ℓ)) =
        1 - ∑' ℓ : P.lattice, (_root_.g (ℓ : EuclideanSpace ℝ (Fin 8))).re := by linarith
    simpa only [ite_true, sub_self, zero_add] using hout
  · simp only [e8PeriodicDeficit, hxy, false_and, ↓reduceIte, zero_sub]
    rw [tsum_neg]

theorem e8_periodic_magic_poisson_lower {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hDb : Bornology.IsBounded D) :
    (P.numReps' (by norm_num) hDb : ℝ) ^ 2 / ZLattice.covolume P.lattice volume ≤
      ∑' (x : PeriodicReps P D) (y : PeriodicReps P D) (ℓ : P.lattice),
        (_root_.g ((x : EuclideanSpace ℝ (Fin 8)) - y + ℓ)).re := by
  have hz : (𝓕 _root_.g) 0 = 1 := by simpa using fourier_g_zero
  simpa only [hz, Complex.one_re, mul_one] using
    periodic_poisson_lower_bound (f := _root_.g) (P := P) g_real_fourier
      fourier_g_nonneg hDb (by norm_num : 0 < 8)

theorem e8_periodic_deficit_budget {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hDb : Bornology.IsBounded D) :
    (∑' (x : PeriodicReps P D) (y : PeriodicReps P D) (ℓ : P.lattice),
      e8PeriodicDeficit P D ((x, y), ℓ)) ≤
      (P.numReps' (by norm_num) hDb : ℝ) -
        (P.numReps' (by norm_num) hDb : ℝ) ^ 2 / ZLattice.covolume P.lattice volume := by
  classical
  let : Fintype (PeriodicReps P D) := P.instFintypeNumReps' (by norm_num) hDb
  simp_rw [e8PeriodicDeficit_lattice_sum, tsum_fintype]
  simp only [Finset.sum_sub_distrib]
  have hdiag : (∑ x : PeriodicReps P D, ∑ y : PeriodicReps P D,
      if x = y then (1 : ℝ) else 0) = (P.numReps' (by norm_num) hDb : ℝ) := by
    simp [PeriodicSpherePacking.numReps']
  rw [hdiag]
  have hl := e8_periodic_magic_poisson_lower (P := P) hDb
  simp only [tsum_fintype] at hl
  simpa only [PeriodicSpherePacking.numReps'] using sub_le_sub_left hl
    (Fintype.card (PeriodicReps P D) : ℝ)

theorem summable_e8PeriodicDeficit {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) :
    Summable (e8PeriodicDeficit P D) := by
  have : Finite (PeriodicReps P D) := finite_centers_inter_of_isBounded P D hDb (by norm_num)
  exact (summable_prod_of_nonneg (e8PeriodicDeficit_nonneg hP hD)).mpr
    ⟨fun p => summable_e8PeriodicDeficit_lattice p.1 p.2, Summable.of_finite⟩

theorem e8_periodic_deficit_total_budget {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) :
    (∑' p : PeriodicPairs P D, e8PeriodicDeficit P D p) ≤
      (P.numReps' (by norm_num) hDb : ℝ) -
        (P.numReps' (by norm_num) hDb : ℝ) ^ 2 / ZLattice.covolume P.lattice volume := by
  let : Fintype (PeriodicReps P D) := P.instFintypeNumReps' (by norm_num) hDb
  rw [(summable_e8PeriodicDeficit hDb hP hD).tsum_prod]
  simpa only [tsum_fintype, Fintype.sum_prod_type] using e8_periodic_deficit_budget (P := P) hDb

theorem e8_periodic_deficit_le_of_density {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ}
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) :
    (∑' p : PeriodicPairs P D, e8PeriodicDeficit P D p) ≤
      (P.numReps' (by norm_num) hDb : ℝ) * ε := by
  refine (e8_periodic_deficit_total_budget hDb hP hD).trans ?_
  have hi := mul_le_mul_of_nonneg_left (sub_le_sub_left hε 1)
    (show 0 ≤ (P.numReps' (by norm_num) hDb : ℝ) by positivity)
  have he : (P.numReps' (by norm_num) hDb : ℝ) -
      (P.numReps' (by norm_num) hDb : ℝ) ^ 2 / ZLattice.covolume P.lattice volume =
      (P.numReps' (by norm_num) hDb : ℝ) *
        (1 - (P.numReps' (by norm_num) hDb : ℝ) / ZLattice.covolume P.lattice volume) := by
    ring
  rw [he]
  simpa only [sub_sub_cancel] using hi

def e8PeriodicBadPairs {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {τ : ℝ} (hτ : 0 < τ) :
    Finset (PeriodicPairs P D) :=
  (finite_large_deficit (e8PeriodicDeficit_nonneg hP hD)
    (summable_e8PeriodicDeficit hDb hP hD) hτ).toFinset

theorem e8_periodic_bad_pairs_card {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε τ : ℝ} (hτ : 0 < τ)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) :
    (e8PeriodicBadPairs hDb hP hD hτ).card ≤
      (P.numReps' (by norm_num) hDb : ℝ) * ε / τ :=
  large_deficit_card_le_budget (e8PeriodicDeficit_nonneg hP hD)
    (summable_e8PeriodicDeficit hDb hP hD) hτ
    (e8_periodic_deficit_le_of_density hDb hP hD hε)

def badPairEndpoints {X Λ : Type*} (s : Finset ((X × X) × Λ)) : Finset X := by
  classical
  exact s.image (fun p => p.1.1) ∪ s.image (fun p => p.1.2)

private theorem mem_badPairEndpoints_fst {X Λ : Type*} {s : Finset ((X × X) × Λ)}
    {p : (X × X) × Λ} (hp : p ∈ s) : p.1.1 ∈ badPairEndpoints s := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem badPairEndpoints_card_le {X Λ : Type*} (s : Finset ((X × X) × Λ)) :
    (badPairEndpoints s).card ≤ 2 * s.card := by
  classical
  exact (Finset.card_union_le _ _).trans (by
    have h1 := Finset.card_image_le (f := fun p : (X × X) × Λ => p.1.1) (s := s)
    have h2 := Finset.card_image_le (f := fun p : (X × X) × Λ => p.1.2) (s := s)
    simpa only [two_mul] using Nat.add_le_add h1 h2)

theorem e8_periodic_good_pair_deficit_lt {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {τ : ℝ} (hτ : 0 < τ)
    (x y : PeriodicReps P D) (hx : x ∉ badPairEndpoints (e8PeriodicBadPairs hDb hP hD hτ))
    (ℓ : P.lattice) : e8PeriodicDeficit P D ((x, y), ℓ) < τ := by
  classical
  by_contra hn
  have hm : ((x, y), ℓ) ∈ e8PeriodicBadPairs hDb hP hD hτ := by
    exact (Set.Finite.mem_toFinset _).mpr (not_lt.mp hn)
  apply hx
  exact mem_badPairEndpoints_fst hm

/-- Removing all endpoints of large deficits gives a common shell coefficient,
valid for every lattice translate of every remaining representative. -/
theorem e8_periodic_good_representatives_shells {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε τ : ℝ} (hτ : 0 < τ)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℝ, 2 < R →
      ∃ α : ℝ, 1 < α ∧ α ≤ ρ * R ^ (3 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4) ∧
        ∃ good : Finset (PeriodicReps P D),
          (P.numReps' (by norm_num) hDb : ℝ) -
              2 * (P.numReps' (by norm_num) hDb : ℝ) * ε / τ ≤ (good.card : ℝ) ∧
          ∀ x ∈ good, ∀ y : PeriodicReps P D, ∀ ℓ : P.lattice,
            (x : EuclideanSpace ℝ (Fin 8)) - y + ℓ ≠ 0 →
            ‖(x : EuclideanSpace ℝ (Fin 8)) - y + ℓ‖ ≤ R →
            ∃ k : ℤ, 1 ≤ k ∧
              |‖(x : EuclideanSpace ℝ (Fin 8)) - y + ℓ‖ ^ 2 - 2 * k| ≤
                α * Real.sqrt τ := by
  classical
  let : Fintype (PeriodicReps P D) := P.instFintypeNumReps' (by norm_num) hDb
  let bad := badPairEndpoints (e8PeriodicBadPairs hDb hP hD hτ)
  let good : Finset (PeriodicReps P D) := Finset.univ \ bad
  have hc : (bad.card : ℝ) ≤ 2 * (P.numReps' (by norm_num) hDb : ℝ) * ε / τ := by
    have hb : (bad.card : ℝ) ≤ 2 * ((e8PeriodicBadPairs hDb hP hD hτ).card : ℝ) := by
      exact_mod_cast badPairEndpoints_card_le (e8PeriodicBadPairs hDb hP hD hτ)
    refine hb.trans ?_
    have hi := mul_le_mul_of_nonneg_left (e8_periodic_bad_pairs_card hDb hP hD hτ hε)
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [mul_div_assoc, mul_assoc] using hi
  have he : (good.card : ℝ) + bad.card = (P.numReps' (by norm_num) hDb : ℝ) := by
    have hn := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
    exact_mod_cast (by simpa only [good, Finset.card_univ, PeriodicSpherePacking.numReps'] using hn)
  obtain ⟨ρ, hρ, hbound⟩ := e8_magic_even_shell_exponential_bound
  refine ⟨ρ, hρ, ?_⟩
  intro R hR
  obtain ⟨α, hα, hαb, hαshell⟩ := hbound R hR
  refine ⟨α, hα, hαb, good, by linarith, ?_⟩
  intro x hx y ℓ hn hRnorm
  have hxgood : x ∉ bad := (Finset.mem_sdiff.mp hx).2
  have hdlt := e8_periodic_good_pair_deficit_lt hDb hP hD hτ x y hxgood ℓ
  have hdiag : ¬(x = y ∧ ℓ = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hn (by simp)
  have hneg : -(_root_.g ((x : EuclideanSpace ℝ (Fin 8)) - y + ℓ)).re < τ := by
    simpa only [e8PeriodicDeficit, hdiag, ↓reduceIte] using hdlt
  have hxy : (x : EuclideanSpace ℝ (Fin 8)) + ℓ ≠ y := by
    intro ht
    apply hn
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using sub_eq_zero.mpr ht
  have hxℓ : (x : EuclideanSpace ℝ (Fin 8)) + ℓ ∈ P.centers := by
    simpa [add_comm] using P.lattice_action ℓ.property x.property.1
  have hmin : Real.sqrt 2 ≤ ‖(x : EuclideanSpace ℝ (Fin 8)) - y + ℓ‖ := by
    simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      hP.trans (P.centers_dist' _ _ hxℓ y.property.1 hxy)
  have hsign := g_nonpos_of_norm_sq_ge_two ((x : EuclideanSpace ℝ (Fin 8)) - y + ℓ)
    (by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2])
  obtain ⟨k, hk, hnear⟩ := hαshell _ hmin hRnorm
  refine ⟨k, hk, hnear.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (by simpa only [abs_of_nonpos hsign] using hneg.le)) (by linarith)
end E8Leech
