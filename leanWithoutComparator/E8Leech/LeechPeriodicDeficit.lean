import SpherePacking.CohnElkies.LPBound
import SpherePacking.Dim24.MagicFunction.F.RealValued
import SpherePacking.Dim24.MagicFunction.F.Sign.SignConditions
import SpherePacking.Dim24.MagicFunction.F.Zero
import E8Leech.E8PeriodicDeficit
import Mathlib.Tactic.FieldSimp

/-!
# The Leech magic deficit in a periodic packing

The dimension 24 version of `E8PeriodicDeficit`, for the magic function `f` of
Sphere-Packing-Lean and packings of separation at least `2`. The diagonal is removed explicitly.
Poisson summation bounds the remaining nonnegative deficit by `N - N² / covolume`, which supplies
the bad-pair budget: at density at least `1 - ε` the total deficit is at most `N ε`, so at most
`N ε / τ` pairs have deficit at least `τ`.
-/
noncomputable section
namespace E8Leech
open scoped BigOperators FourierTransform
open SpherePacking MeasureTheory Classical

abbrev LeechPeriodicReps (P : PeriodicSpherePacking 24)
    (D : Set (EuclideanSpace ℝ (Fin 24))) :=
  ↥(P.centers ∩ D)

abbrev LeechPeriodicPairs (P : PeriodicSpherePacking 24)
    (D : Set (EuclideanSpace ℝ (Fin 24))) :=
  (LeechPeriodicReps P D × LeechPeriodicReps P D) × P.lattice

def leechPeriodicDeficit (P : PeriodicSpherePacking 24) (D : Set (EuclideanSpace ℝ (Fin 24)))
    (p : LeechPeriodicPairs P D) : ℝ :=
  if p.1.1 = p.1.2 ∧ p.2 = 0 then 0 else
    -(Dim24.f ((p.1.1 : EuclideanSpace ℝ (Fin 24)) - p.1.2 + p.2)).re

private theorem leech_reps_translate_eq_iff {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))}
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D)
    (x y : LeechPeriodicReps P D) (ℓ : P.lattice) :
    (x : EuclideanSpace ℝ (Fin 24)) - y + ℓ = 0 ↔ x = y ∧ ℓ = 0 := by
  constructor
  · intro h
    obtain ⟨a, _, hu⟩ := hD (x : EuclideanSpace ℝ (Fin 24))
    have h0 : (0 : P.lattice) +ᵥ (x : EuclideanSpace ℝ (Fin 24)) ∈ D := by
      simpa [Submodule.vadd_def] using x.property.2
    have hl : ℓ +ᵥ (x : EuclideanSpace ℝ (Fin 24)) ∈ D := by
      have he : (ℓ : EuclideanSpace ℝ (Fin 24)) + x = y := by
        have ht : (x : EuclideanSpace ℝ (Fin 24)) + ℓ - y = 0 := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
        simpa [add_comm] using sub_eq_zero.mp ht
      simpa [Submodule.vadd_def, he] using y.property.2
    have he : ℓ = 0 := (hu ℓ hl).trans (hu 0 h0).symm
    refine ⟨Subtype.ext ?_, he⟩
    simpa [he] using sub_eq_zero.mp (by simpa [he] using h)
  · rintro ⟨rfl, rfl⟩
    simp

theorem leechPeriodicDeficit_nonneg {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) (p : LeechPeriodicPairs P D) :
    0 ≤ leechPeriodicDeficit P D p := by
  classical
  unfold leechPeriodicDeficit
  split_ifs with hd
  · rfl
  · have hn : (p.1.1 : EuclideanSpace ℝ (Fin 24)) + p.2 ≠ p.1.2 := by
      intro he
      apply hd
      apply (leech_reps_translate_eq_iff hD _ _ _).mp
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using sub_eq_zero.mpr he
    have hc : (p.1.1 : EuclideanSpace ℝ (Fin 24)) + p.2 ∈ P.centers := by
      simpa [add_comm] using P.lattice_action p.2.property p.1.1.property.1
    have hb := hP.trans (P.centers_dist' _ _ hc p.1.2.property.1 hn)
    have hr : 2 ≤ ‖(p.1.1 : EuclideanSpace ℝ (Fin 24)) - p.1.2 + p.2‖ := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hb
    exact neg_nonneg.mpr (Dim24.f_cohnElkies₁ _ hr)

theorem summable_leechPeriodicDeficit_lattice {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (x y : LeechPeriodicReps P D) :
    Summable (fun ℓ : P.lattice => leechPeriodicDeficit P D ((x, y), ℓ)) := by
  classical
  have hs := CohnElkies.LPBoundSummability.summable_lattice_translate_re
    (Λ := P.lattice) (f := Dim24.f) (a := (x : EuclideanSpace ℝ (Fin 24)) - y)
  by_cases hxy : x = y
  · have he : (fun ℓ : P.lattice => leechPeriodicDeficit P D ((x, y), ℓ)) =
        {ℓ : P.lattice | ℓ ≠ 0}.indicator
          (fun ℓ => -(Dim24.f ((x : EuclideanSpace ℝ (Fin 24)) - y + ℓ)).re) := by
      funext ℓ
      by_cases hl : ℓ = 0 <;> simp [leechPeriodicDeficit, hxy, hl, Set.indicator]
    rw [he]
    exact hs.neg.indicator _
  · simpa [leechPeriodicDeficit, hxy] using hs.neg

theorem leechPeriodicDeficit_lattice_sum {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (x y : LeechPeriodicReps P D) :
    (∑' ℓ : P.lattice, leechPeriodicDeficit P D ((x, y), ℓ)) =
      (if x = y then 1 else 0) -
        ∑' ℓ : P.lattice, (Dim24.f ((x : EuclideanSpace ℝ (Fin 24)) - y + ℓ)).re := by
  classical
  have hs := CohnElkies.LPBoundSummability.summable_lattice_translate_re
    (Λ := P.lattice) (f := Dim24.f) (a := (x : EuclideanSpace ℝ (Fin 24)) - y)
  by_cases hxy : x = y
  · subst y
    have hs0 : Summable (fun ℓ : P.lattice =>
        (Dim24.f (ℓ : EuclideanSpace ℝ (Fin 24))).re) := by
      simpa only [sub_self, zero_add] using hs
    have he := hs0.tsum_eq_add_tsum_ite (0 : P.lattice)
    have hi : (∑' ℓ : P.lattice, if ℓ = 0 then 0 else
        (Dim24.f (ℓ : EuclideanSpace ℝ (Fin 24))).re) =
        -(∑' ℓ : P.lattice, leechPeriodicDeficit P D ((x, x), ℓ)) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro ℓ
      by_cases hl : ℓ = 0 <;> simp [leechPeriodicDeficit, hl]
    have hz : (Dim24.f ((0 : P.lattice) : EuclideanSpace ℝ (Fin 24))).re = 1 := by
      simp only [Submodule.coe_zero, Dim24.f_zero, Complex.one_re]
    rw [hz, hi] at he
    have hout : (∑' ℓ : P.lattice, leechPeriodicDeficit P D ((x, x), ℓ)) =
        1 - ∑' ℓ : P.lattice, (Dim24.f (ℓ : EuclideanSpace ℝ (Fin 24))).re := by linarith
    simpa only [ite_true, sub_self, zero_add] using hout
  · simp only [leechPeriodicDeficit, hxy, false_and, ↓reduceIte, zero_sub]
    rw [tsum_neg]

theorem leech_periodic_magic_poisson_lower {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (hDb : Bornology.IsBounded D) :
    (P.numReps' (by norm_num) hDb : ℝ) ^ 2 / ZLattice.covolume P.lattice volume ≤
      ∑' (x : LeechPeriodicReps P D) (y : LeechPeriodicReps P D) (ℓ : P.lattice),
        (Dim24.f ((x : EuclideanSpace ℝ (Fin 24)) - y + ℓ)).re := by
  have hz : (𝓕 Dim24.f) 0 = 1 := by simpa using Dim24.fourier_f_zero
  have hreal : ∀ x : EuclideanSpace ℝ (Fin 24),
      (↑((𝓕 Dim24.f x).re) : ℂ) = 𝓕 Dim24.f x := fun x => by
    simpa using Dim24.f_real_fourier x
  have hnonneg : ∀ x : EuclideanSpace ℝ (Fin 24), (𝓕 Dim24.f x).re ≥ 0 := fun x => by
    simpa using Dim24.f_cohnElkies₂ x
  simpa only [hz, Complex.one_re, mul_one] using
    periodic_poisson_lower_bound (f := Dim24.f) (P := P) hreal hnonneg hDb
      (by norm_num : 0 < 24)

theorem leech_periodic_deficit_budget {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (hDb : Bornology.IsBounded D) :
    (∑' (x : LeechPeriodicReps P D) (y : LeechPeriodicReps P D) (ℓ : P.lattice),
      leechPeriodicDeficit P D ((x, y), ℓ)) ≤
      (P.numReps' (by norm_num) hDb : ℝ) -
        (P.numReps' (by norm_num) hDb : ℝ) ^ 2 / ZLattice.covolume P.lattice volume := by
  classical
  let : Fintype (LeechPeriodicReps P D) := P.instFintypeNumReps' (by norm_num) hDb
  simp_rw [leechPeriodicDeficit_lattice_sum, tsum_fintype]
  simp only [Finset.sum_sub_distrib]
  have hdiag : (∑ x : LeechPeriodicReps P D, ∑ y : LeechPeriodicReps P D,
      if x = y then (1 : ℝ) else 0) = (P.numReps' (by norm_num) hDb : ℝ) := by
    simp [PeriodicSpherePacking.numReps']
  rw [hdiag]
  have hl := leech_periodic_magic_poisson_lower (P := P) hDb
  simp only [tsum_fintype] at hl
  simpa only [PeriodicSpherePacking.numReps'] using sub_le_sub_left hl
    (Fintype.card (LeechPeriodicReps P D) : ℝ)

theorem summable_leechPeriodicDeficit {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) :
    Summable (leechPeriodicDeficit P D) := by
  have : Finite (LeechPeriodicReps P D) :=
    finite_centers_inter_of_isBounded P D hDb (by norm_num)
  exact (summable_prod_of_nonneg (leechPeriodicDeficit_nonneg hP hD)).mpr
    ⟨fun p => summable_leechPeriodicDeficit_lattice p.1 p.2, Summable.of_finite⟩

theorem leech_periodic_deficit_total_budget {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) :
    (∑' p : LeechPeriodicPairs P D, leechPeriodicDeficit P D p) ≤
      (P.numReps' (by norm_num) hDb : ℝ) -
        (P.numReps' (by norm_num) hDb : ℝ) ^ 2 / ZLattice.covolume P.lattice volume := by
  let : Fintype (LeechPeriodicReps P D) := P.instFintypeNumReps' (by norm_num) hDb
  rw [(summable_leechPeriodicDeficit hDb hP hD).tsum_prod]
  simpa only [tsum_fintype, Fintype.sum_prod_type] using
    leech_periodic_deficit_budget (P := P) hDb

theorem leech_periodic_deficit_le_of_density {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ}
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) :
    (∑' p : LeechPeriodicPairs P D, leechPeriodicDeficit P D p) ≤
      (P.numReps' (by norm_num) hDb : ℝ) * ε := by
  refine (leech_periodic_deficit_total_budget hDb hP hD).trans ?_
  have hi := mul_le_mul_of_nonneg_left (sub_le_sub_left hε 1)
    (show 0 ≤ (P.numReps' (by norm_num) hDb : ℝ) by positivity)
  have he : (P.numReps' (by norm_num) hDb : ℝ) -
      (P.numReps' (by norm_num) hDb : ℝ) ^ 2 / ZLattice.covolume P.lattice volume =
      (P.numReps' (by norm_num) hDb : ℝ) *
        (1 - (P.numReps' (by norm_num) hDb : ℝ) / ZLattice.covolume P.lattice volume) := by
    ring
  rw [he]
  simpa only [sub_sub_cancel] using hi

def leechPeriodicBadPairs {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {τ : ℝ} (hτ : 0 < τ) :
    Finset (LeechPeriodicPairs P D) :=
  (finite_large_deficit (leechPeriodicDeficit_nonneg hP hD)
    (summable_leechPeriodicDeficit hDb hP hD) hτ).toFinset

theorem leech_periodic_bad_pairs_card {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε τ : ℝ} (hτ : 0 < τ)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) :
    (leechPeriodicBadPairs hDb hP hD hτ).card ≤
      (P.numReps' (by norm_num) hDb : ℝ) * ε / τ :=
  large_deficit_card_le_budget (leechPeriodicDeficit_nonneg hP hD)
    (summable_leechPeriodicDeficit hDb hP hD) hτ
    (leech_periodic_deficit_le_of_density hDb hP hD hε)

private theorem leech_mem_badPairEndpoints_fst {X Λ : Type*} {s : Finset ((X × X) × Λ)}
    {p : (X × X) × Λ} (hp : p ∈ s) : p.1.1 ∈ badPairEndpoints s := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem leech_periodic_good_pair_deficit_lt {P : PeriodicSpherePacking 24}
    {D : Set (EuclideanSpace ℝ (Fin 24))} (hDb : Bornology.IsBounded D)
    (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {τ : ℝ} (hτ : 0 < τ)
    (x y : LeechPeriodicReps P D)
    (hx : x ∉ badPairEndpoints (leechPeriodicBadPairs hDb hP hD hτ))
    (ℓ : P.lattice) : leechPeriodicDeficit P D ((x, y), ℓ) < τ := by
  classical
  by_contra hn
  have hm : ((x, y), ℓ) ∈ leechPeriodicBadPairs hDb hP hD hτ := by
    exact (Set.Finite.mem_toFinset _).mpr (not_lt.mp hn)
  apply hx
  exact leech_mem_badPairEndpoints_fst hm

end E8Leech
