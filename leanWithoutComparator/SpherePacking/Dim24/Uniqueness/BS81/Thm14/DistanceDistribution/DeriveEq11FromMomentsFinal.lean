-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.DistanceDistribution.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.InnerMvPoly24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgInnerMoments24Final
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgMoments
import Mathlib.Tactic.Linarith

/-!
# Deriving BS81 equation (11) from moment identities

This file derives the BS81 distance distribution (equation (11)) from:

* the finite support constraint `⟪u,v⟫ ∈ {1, -1, ±1/2, ±1/4, 0}`, and
* the spherical-design moment identities up to degree `4`.

## Main statement
* `dist_eq11_of_design10_and_support`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

open MeasureTheory Polynomial

open Uniqueness.BS81

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Expanding sums over the explicit support finset

`bs81Support24 : Finset ℝ` is a concrete `Finset` literal. To avoid relying on `simp` making
progress through `Finset` sums over `ℝ`, we use a dedicated expansion lemma.
-/

lemma sum_bs81Support24 (f : ℝ → ℝ) :
    (∑ t ∈ bs81Support24, f t) =
      f (1 : ℝ) + f (-1 : ℝ) + f (1 / 2 : ℝ) + f (-1 / 2 : ℝ) +
        f (1 / 4 : ℝ) + f (-1 / 4 : ℝ) + f (0 : ℝ) := by
  have h1 :
      (1 : ℝ) ∉
        ({(-1 : ℝ), (1 / 2 : ℝ), (-1 / 2 : ℝ), (1 / 4 : ℝ), (-1 / 4 : ℝ), (0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hneg1 :
      (-1 : ℝ) ∉ ({(1 / 2 : ℝ), (-1 / 2 : ℝ), (1 / 4 : ℝ), (-1 / 4 : ℝ), (0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hhalf :
      (1 / 2 : ℝ) ∉ ({(-1 / 2 : ℝ), (1 / 4 : ℝ), (-1 / 4 : ℝ), (0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hneghalf :
      (-1 / 2 : ℝ) ∉ ({(1 / 4 : ℝ), (-1 / 4 : ℝ), (0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hquarter :
      (1 / 4 : ℝ) ∉ ({(-1 / 4 : ℝ), (0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hnegquarter : (-1 / 4 : ℝ) ∉ ({(0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_singleton]
  unfold bs81Support24
  rw [Finset.sum_insert h1]
  rw [Finset.sum_insert hneg1]
  rw [Finset.sum_insert hhalf]
  rw [Finset.sum_insert hneghalf]
  rw [Finset.sum_insert hquarter]
  rw [Finset.sum_insert hnegquarter]
  simp [Finset.sum_singleton]
  ac_rfl

/-!
## A homogeneous polynomial encoding `v ↦ ⟪u,v⟫`
-/

attribute [grind =] mvPolyEval24_innerMvPoly24_pow

/-!
## Odd spherical moments vanish by symmetry
-/

lemma sphereAvg24_inner_pow_odd_eq_zero (u : ℝ²⁴) {m : ℕ} (hm : Odd m) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ m) = 0 := by
  let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := LinearIsometryEquiv.neg ℝ (E := ℝ²⁴)
  have hinv :=
    sphereAvg24_comp_linearIsometryEquiv (e := e) (f := fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ m)
  have hflip :
      (fun x : ℝ²⁴ => (⟪e x, u⟫ : ℝ) ^ m) = fun x : ℝ²⁴ => -((⟪x, u⟫ : ℝ) ^ m) := by
    funext x
    have : (⟪e x, u⟫ : ℝ) = -(⟪x, u⟫ : ℝ) := by
      simp [e]
    simpa [this] using! (hm.neg_pow (⟪x, u⟫ : ℝ))
  have : sphereAvg24 (fun x : ℝ²⁴ => -((⟪x, u⟫ : ℝ) ^ m)) =
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ m) := by
    simpa [hflip] using! hinv
  have : -sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ m) =
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ m) := by
    simpa [sphereAvg24_neg] using! this
  linarith

/-!
## Main derivation: solve for the distance distribution
-/

lemma r13_of_e13 (d1 d2 : ℝ)
    (e13 :
      (1 / 2 : ℝ) * d1 + (1 / 4 : ℝ) * d2 = (1 / 8 : ℝ) * d1 + (1 / 64 : ℝ) * d2) :
    (8 : ℝ) * d1 + (5 : ℝ) * d2 = 0 := by
  nlinarith

lemma r35_of_e35 (d1 d2 : ℝ)
    (e35 :
      (1 / 8 : ℝ) * d1 + (1 / 64 : ℝ) * d2 = (1 / 32 : ℝ) * d1 + (1 / 1024 : ℝ) * d2) :
    (32 : ℝ) * d1 + (5 : ℝ) * d2 = 0 := by
  nlinarith

lemma d1_eq_zero_of_r13_r35 (d1 d2 : ℝ)
    (r13 : (8 : ℝ) * d1 + (5 : ℝ) * d2 = 0) (r35 : (32 : ℝ) * d1 + (5 : ℝ) * d2 = 0) :
    d1 = 0 := by
  nlinarith

lemma d2_eq_zero_of_r13_d1 (d1 d2 : ℝ) (r13 : (8 : ℝ) * d1 + (5 : ℝ) * d2 = 0) (hd1 : d1 = 0) :
    d2 = 0 := by
  nlinarith

lemma solve_odd_subsystem (Aneg1 Ahalf Aneghalf Aquarter Anegquarter : ℝ)
    (hm1 :
      1 - Aneg1 + (1 / 2 : ℝ) * (Ahalf - Aneghalf) + (1 / 4 : ℝ) * (Aquarter - Anegquarter) = 0)
    (hm3 :
      1 - Aneg1 + (1 / 8 : ℝ) * (Ahalf - Aneghalf) + (1 / 64 : ℝ) * (Aquarter - Anegquarter) = 0)
    (hm5 :
      1 - Aneg1 + (1 / 32 : ℝ) * (Ahalf - Aneghalf) +
          (1 / 1024 : ℝ) * (Aquarter - Anegquarter) = 0) :
    Ahalf = Aneghalf ∧ Aquarter = Anegquarter ∧ Aneg1 = 1 := by
  grind only

lemma hm2_of_fiberwise
    (C : Set ℝ²⁴) (u : ℝ²⁴) (Cfin : Finset ℝ²⁴)
    (Aneg1 Ahalf Aneghalf Aquarter Anegquarter : ℝ)
    (hAneg1 : Aneg1 = (distCount (n := 24) C u (-1 : ℝ) : ℝ))
    (hAhalf : Ahalf = (distCount (n := 24) C u (1 / 2 : ℝ) : ℝ))
    (hAneghalf : Aneghalf = (distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ))
    (hAquarter : Aquarter = (distCount (n := 24) C u (1 / 4 : ℝ) : ℝ))
    (hAnegquarter : Anegquarter = (distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ))
    (hsum_inner_pow_fiberwise : ∀ m : ℕ,
      (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ m) =
        ∑ t ∈ bs81Support24, (distCount (n := 24) C u t : ℝ) * t ^ m)
    (hsum2 : (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 2) = 8190)
    (hdist1R : (distCount (n := 24) C u (1 : ℝ) : ℝ) = 1) :
    1 + Aneg1 + (1 / 4 : ℝ) * (Ahalf + Aneghalf) +
        (1 / 16 : ℝ) * (Aquarter + Anegquarter) = 8190 := by
  have hfib2 := hsum_inner_pow_fiberwise 2
  rw [sum_bs81Support24 (f := fun t : ℝ => (distCount (n := 24) C u t : ℝ) * t ^ 2)] at hfib2
  grind only

lemma hm4_of_fiberwise
    (C : Set ℝ²⁴) (u : ℝ²⁴) (Cfin : Finset ℝ²⁴)
    (Aneg1 Ahalf Aneghalf Aquarter Anegquarter : ℝ)
    (hAneg1 : Aneg1 = (distCount (n := 24) C u (-1 : ℝ) : ℝ))
    (hAhalf : Ahalf = (distCount (n := 24) C u (1 / 2 : ℝ) : ℝ))
    (hAneghalf : Aneghalf = (distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ))
    (hAquarter : Aquarter = (distCount (n := 24) C u (1 / 4 : ℝ) : ℝ))
    (hAnegquarter : Anegquarter = (distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ))
    (hsum_inner_pow_fiberwise : ∀ m : ℕ,
      (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ m) =
        ∑ t ∈ bs81Support24, (distCount (n := 24) C u t : ℝ) * t ^ m)
    (hsum4 : (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 4) = 945)
    (hdist1R : (distCount (n := 24) C u (1 : ℝ) : ℝ) = 1) :
    1 + Aneg1 + (1 / 16 : ℝ) * (Ahalf + Aneghalf) +
        (1 / 256 : ℝ) * (Aquarter + Anegquarter) = 945 := by
  have hfib4 := hsum_inner_pow_fiberwise 4
  rw [sum_bs81Support24 (f := fun t : ℝ => (distCount (n := 24) C u t : ℝ) * t ^ 4)] at hfib4
  grind only

lemma solve_even_subsystem (Aneg1 Ahalf Aneghalf Aquarter Anegquarter Azero : ℝ)
    (hAhalf : Ahalf = Aneghalf) (hAquarter : Aquarter = Anegquarter) (hAneg1 : Aneg1 = 1)
    (hm2 :
      1 + Aneg1 + (1 / 4 : ℝ) * (Ahalf + Aneghalf) + (1 / 16 : ℝ) * (Aquarter + Anegquarter) = 8190)
    (hm4 :
      1 + Aneg1 + (1 / 16 : ℝ) * (Ahalf + Aneghalf) +
          (1 / 256 : ℝ) * (Aquarter + Anegquarter) = 945)
    (hcountR : Aneg1 + Ahalf + Aneghalf + Aquarter + Anegquarter + Azero = 196559) :
    Ahalf = 4600 ∧ Aquarter = 47104 ∧ Azero = 93150 := by
  grind only

lemma nat_counts_of_real_counts (C : Set ℝ²⁴) (u : ℝ²⁴)
    (hneg1 : (distCount (n := 24) C u (-1 : ℝ) : ℝ) = 1)
    (hhalf : (distCount (n := 24) C u (1 / 2 : ℝ) : ℝ) = 4600)
    (hneghalf : (distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ) = 4600)
    (hquarter : (distCount (n := 24) C u (1 / 4 : ℝ) : ℝ) = 47104)
    (hnegquarter : (distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ) = 47104)
    (hzero : (distCount (n := 24) C u (0 : ℝ) : ℝ) = 93150) :
    distCount (n := 24) C u (-1 : ℝ) = 1 ∧
      distCount (n := 24) C u (1 / 2 : ℝ) = 4600 ∧
      distCount (n := 24) C u (-1 / 2 : ℝ) = 4600 ∧
      distCount (n := 24) C u (1 / 4 : ℝ) = 47104 ∧
      distCount (n := 24) C u (-1 / 4 : ℝ) = 47104 ∧
      distCount (n := 24) C u (0 : ℝ) = 93150 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hneg1
  · exact_mod_cast hhalf
  · exact_mod_cast hneghalf
  · exact_mod_cast hquarter
  · exact_mod_cast hnegquarter
  · exact_mod_cast hzero

/-- Derive BS81 equation (11) from design `t=10` and support. -/
public theorem dist_eq11_of_design10_and_support
    (C : Set ℝ²⁴)
    (hC : IsSphericalCode 24 C (1 / 2 : ℝ))
    (hcard : Set.ncard C = 196560)
    (hD10 : IsBS81SphericalDesign24 10 hC.finite.toFinset)
    (hsupp : ∀ ⦃u v : ℝ²⁴⦄, u ∈ C → v ∈ C → (⟪u, v⟫ : ℝ) ∈ bs81Support24) :
    ∀ ⦃u : ℝ²⁴⦄, u ∈ C →
      distCount (n := 24) C u (1 : ℝ) = 1 ∧
        distCount (n := 24) C u (-1 : ℝ) = 1 ∧
        distCount (n := 24) C u (1 / 2 : ℝ) = 4600 ∧
        distCount (n := 24) C u (-1 / 2 : ℝ) = 4600 ∧
        distCount (n := 24) C u (1 / 4 : ℝ) = 47104 ∧
        distCount (n := 24) C u (-1 / 4 : ℝ) = 47104 ∧
        distCount (n := 24) C u (0 : ℝ) = 93150 := by
  intro u hu
  haveI : DecidableEq ℝ := Classical.decEq _
  haveI : DecidableEq ℝ²⁴ := Classical.decEq _
  -- Shorthand finset.
  let Cfin : Finset ℝ²⁴ := hC.finite.toFinset
  have hcard_fin : Cfin.card = 196560 := by
    -- `Set.ncard_eq_toFinset_card` is oriented as `Set.ncard C = card`.
    simpa [Cfin] using! (Set.ncard_eq_toFinset_card C hC.finite ▸ hcard)
  have hcardR : (Cfin.card : ℝ) = (196560 : ℝ) := by exact_mod_cast hcard_fin
  have hcardR_ne : (Cfin.card : ℝ) ≠ 0 := by
    have h196560 : (196560 : ℝ) ≠ 0 := by norm_num
    rw [hcardR]
    exact h196560
  have hmemCfin : u ∈ Cfin := by
    simpa [Cfin] using! (hC.finite.mem_toFinset.2 hu)
  -- `distCount` as a `Finset.filter` cardinality.
  have distCount_eq_filter_card (t : ℝ) :
      distCount (n := 24) C u t = (Cfin.filter (fun v => (⟪u, v⟫ : ℝ) = t)).card := by
    let S : Set ℝ²⁴ := {v : ℝ²⁴ | v ∈ C ∧ (⟪u, v⟫ : ℝ) = t}
    have hSfin : S.Finite := hC.finite.subset (by intro v hv; exact hv.1)
    have hto : hSfin.toFinset = Cfin.filter (fun v => (⟪u, v⟫ : ℝ) = t) := by
      ext v
      simp [S, Cfin, Set.Finite.mem_toFinset, and_comm]
    have hncard :
        Uniqueness.BS81.distCount (n := 24) C u t = hSfin.toFinset.card := by
      -- `distCount` is `Set.ncard S`.
      simp [Uniqueness.BS81.distCount, S, Set.ncard_eq_toFinset_card (s := S) hSfin]
    simpa [hto] using! hncard
  have card_filter_eq_distCount (t : ℝ) :
      ((Cfin.filter fun v => (⟪u, v⟫ : ℝ) = t).card : ℝ) =
        (distCount (n := 24) C u t : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) (distCount_eq_filter_card t)
    simpa using! this.symm
  -- Step 1: the `t=1` fiber is exactly `{u}`.
  have hdist1 : distCount (n := 24) C u (1 : ℝ) = 1 := by
    have : Cfin.filter (fun v => (⟪u, v⟫ : ℝ) = (1 : ℝ)) = {u} := by
      ext v
      constructor
      · intro hv
        have hvCfin : v ∈ Cfin := (Finset.mem_filter.1 hv).1
        have hvC : v ∈ C := by
          simpa [Cfin] using! (hC.finite.mem_toFinset.1 hvCfin)
        have hinner : (⟪u, v⟫ : ℝ) = 1 := by
          simpa using! (Finset.mem_filter.1 hv).2
        by_cases huv : v = u
        · simp [huv]
        · have hle : (⟪u, v⟫ : ℝ) ≤ (1 / 2 : ℝ) :=
            hC.inner_le hu hvC (by simpa [eq_comm] using! huv)
          linarith
      · intro hv
        have hv' : v = u := Finset.mem_singleton.1 hv
        have huNorm : ‖u‖ = (1 : ℝ) := hC.norm_one hu
        simp_all
    simp [distCount_eq_filter_card, this]
  -- Maps-to hypothesis for fiberwise sums.
  let g : ℝ²⁴ → ℝ := fun v => (⟪u, v⟫ : ℝ)
  have hg : ∀ v ∈ Cfin, g v ∈ bs81Support24 := by
    intro v hv
    have hvC : v ∈ C := by
      simpa [Cfin] using! (hC.finite.mem_toFinset.1 hv)
    simpa [g] using! hsupp hu hvC
  -- Moment equations from the design axiom for `m = 1,2,3,4`.
  rcases hD10 with ⟨hNorm, hEq⟩
  have hsum_inner_pow (m : ℕ) (hm : m ≤ 10) :
      finsetAvg Cfin (fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ m) =
        sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ m) := by
    -- Apply the design identity to `p = (innerMvPoly24 u)^m`.
    have h :=
      hEq m ((innerMvPoly24 u) ^ m) hm (innerMvPoly24_pow_isHomogeneous (u := u) (m := m))
    have hfun :
        (mvPolyEval24 ((innerMvPoly24 u) ^ m)) = fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ m := by
      funext v
      simp [mvPolyEval24_innerMvPoly24_pow]
    simpa [Cfin, hfun] using! h
  have hsum1 : (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 1) = 0 := by
    have havg :=
      hsum_inner_pow 1 (by decide)
    -- `sphereAvg` vanishes for odd moments.
    have hsphere : sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 1) = 0 := by
      simpa [real_inner_comm] using!
        (sphereAvg24_inner_pow_odd_eq_zero (u := u) (m := 1) (by decide))
    -- Unfold `finsetAvg` without triggering simp-lemmas like `inv_mul_eq_zero`.
    have havg' := havg
    dsimp [finsetAvg] at havg'
    rw [hsphere] at havg'
    -- Multiply by the nonzero scalar.
    have : (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 1) = 0 := by
      have hmul := congrArg (fun z : ℝ => (Cfin.card : ℝ) * z) havg'
      -- `(card) * ((card)⁻¹ * s) = s`.
      simpa [mul_assoc, hcardR_ne] using! hmul
    simpa using! this
  have hsum3 : (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 3) = 0 := by
    have havg :=
      hsum_inner_pow 3 (by decide)
    have hsphere : sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 3) = 0 := by
      simpa [real_inner_comm] using!
        (sphereAvg24_inner_pow_odd_eq_zero (u := u) (m := 3) (by decide))
    have havg' := havg
    dsimp [finsetAvg] at havg'
    rw [hsphere] at havg'
    have : (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 3) = 0 := by
      have hmul := congrArg (fun z : ℝ => (Cfin.card : ℝ) * z) havg'
      simpa [mul_assoc, hcardR_ne] using! hmul
    simpa using! this
  have hsum2 : (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 2) = 8190 := by
    have havg :=
      hsum_inner_pow 2 (by decide)
    have huNorm : ‖u‖ = (1 : ℝ) := hC.norm_one hu
    have hsphere :
        sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 2) = (1 / 24 : ℝ) := by
      -- Use the proven inner-product second moment.
      simpa [real_inner_comm] using!
        (sphereAvg24_inner_pow_two_of_norm_one (u := u) huNorm)
    have havg' := havg
    dsimp [finsetAvg] at havg'
    rw [hsphere] at havg'
    have hsum2_card :
        (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 2) = (Cfin.card : ℝ) * (1 / 24 : ℝ) := by
      have hmul := congrArg (fun z : ℝ => (Cfin.card : ℝ) * z) havg'
      simpa [mul_assoc, hcardR_ne] using! hmul
    nlinarith [hsum2_card, hcardR]
  have hsum4 : (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 4) = 945 := by
    have havg :=
      hsum_inner_pow 4 (by decide)
    have huNorm : ‖u‖ = (1 : ℝ) := hC.norm_one hu
    have hsphere :
        sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 4) = (1 / 208 : ℝ) := by
      simpa [real_inner_comm] using!
        (sphereAvg24_inner_pow_four_of_norm_one (u := u) huNorm)
    have havg' := havg
    dsimp [finsetAvg] at havg'
    rw [hsphere] at havg'
    have hsum4_card :
        (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 4) = (Cfin.card : ℝ) * (1 / 208 : ℝ) := by
      have hmul := congrArg (fun z : ℝ => (Cfin.card : ℝ) * z) havg'
      simpa [mul_assoc, hcardR_ne] using! hmul
    nlinarith [hsum4_card, hcardR]
  have hsum5 : (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 5) = 0 := by
    have havg :=
      hsum_inner_pow 5 (by decide)
    have hsphere : sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 5) = 0 := by
      simpa [real_inner_comm] using!
        (sphereAvg24_inner_pow_odd_eq_zero (u := u) (m := 5) (by decide))
    have havg' := havg
    dsimp [finsetAvg] at havg'
    rw [hsphere] at havg'
    have : (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ 5) = 0 := by
      have hmul := congrArg (fun z : ℝ => (Cfin.card : ℝ) * z) havg'
      simpa [mul_assoc, hcardR_ne] using! hmul
    simpa using! this
  -- Fiberwise identity: express each power-moment sum by the distance distribution.
  have hsum_inner_pow_fiberwise (m : ℕ) :
      (Cfin.sum fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ m) =
        ∑ t ∈ bs81Support24, (distCount (n := 24) C u t : ℝ) * t ^ m := by
    have h :=
      (Finset.sum_fiberwise_of_maps_to' (s := Cfin) (t := bs81Support24) (g := g)
        (h := fun v hv => hg v hv) (f := fun t : ℝ => t ^ m))
    -- Rewrite the RHS of `h` as `∑ (v∈Cfin), ⟪u,v⟫^m`.
    have hRHS : (∑ v ∈ Cfin, (g v) ^ m) = Cfin.sum (fun v : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ m) := by
      simp [g]
    -- Rewrite the LHS inner sums as `(card fiber) * t^m`, and then as `distCount * t^m`.
    have hLHS :
        (∑ t ∈ bs81Support24, ∑ v ∈ Cfin with g v = t, t ^ m) =
          ∑ t ∈ bs81Support24, (distCount (n := 24) C u t : ℝ) * t ^ m := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      have hconst :
          (∑ v ∈ Cfin with g v = t, t ^ m) =
            ((Cfin.filter fun v => g v = t).card : ℝ) * (t ^ m) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      have hcard' :
          ((Cfin.filter fun v => g v = t).card : ℝ) =
            (distCount (n := 24) C u t : ℝ) := by
        simpa [g] using! (card_filter_eq_distCount (t := t))
      -- Replace the fiber-card by `distCount`.
      simp [hconst, hcard']
    -- Rewrite `h` using `hLHS` and `hRHS`, then flip.
    have h' := h
    rw [hLHS] at h'
    rw [hRHS] at h'
    exact h'.symm
  -- Total count equation (exclude the `t=1` term using `hdist1`).
  have hcountR :
      (distCount (n := 24) C u (-1 : ℝ) : ℝ) +
          (distCount (n := 24) C u (1 / 2 : ℝ) : ℝ) +
          (distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ) +
          (distCount (n := 24) C u (1 / 4 : ℝ) : ℝ) +
          (distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ) +
          (distCount (n := 24) C u (0 : ℝ) : ℝ) = 196559 := by
    have h0 := hsum_inner_pow_fiberwise 0
    have h0' :
        (Cfin.card : ℝ) =
          ∑ t ∈ bs81Support24, (distCount (n := 24) C u t : ℝ) := by
      -- Simplify `m=0`.
      simpa [pow_zero] using! h0
    -- Expand the support sum and isolate the `t=1` term.
    have hdist1R : (distCount (n := 24) C u (1 : ℝ) : ℝ) = 1 := by exact_mod_cast hdist1
    have h0_expanded :
        (Cfin.card : ℝ) =
          (distCount (n := 24) C u (1 : ℝ) : ℝ) +
            (distCount (n := 24) C u (-1 : ℝ) : ℝ) +
            (distCount (n := 24) C u (1 / 2 : ℝ) : ℝ) +
            (distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ) +
            (distCount (n := 24) C u (1 / 4 : ℝ) : ℝ) +
            (distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ) +
            (distCount (n := 24) C u (0 : ℝ) : ℝ) := by
      -- Use the dedicated support expansion lemma.
      simpa [sum_bs81Support24, add_assoc, add_left_comm, add_comm] using! h0'
    have hrest :
        (distCount (n := 24) C u (-1 : ℝ) : ℝ) +
            (distCount (n := 24) C u (1 / 2 : ℝ) : ℝ) +
            (distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ) +
            (distCount (n := 24) C u (1 / 4 : ℝ) : ℝ) +
            (distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ) +
            (distCount (n := 24) C u (0 : ℝ) : ℝ) = (Cfin.card : ℝ) - 1 := by
      linarith [h0_expanded, hdist1R]
    have hcardR' : (Cfin.card : ℝ) - 1 = (196559 : ℝ) := by linarith [hcardR]
    simpa [hcardR'] using! hrest
  -- Set real abbreviations for the unknown counts.
  set Aneg1 : ℝ := (distCount (n := 24) C u (-1 : ℝ) : ℝ)
  set Ahalf : ℝ := (distCount (n := 24) C u (1 / 2 : ℝ) : ℝ)
  set Aneghalf : ℝ := (distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ)
  set Aquarter : ℝ := (distCount (n := 24) C u (1 / 4 : ℝ) : ℝ)
  set Anegquarter : ℝ := (distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ)
  set Azero : ℝ := (distCount (n := 24) C u (0 : ℝ) : ℝ)
  have hdist1R : (distCount (n := 24) C u (1 : ℝ) : ℝ) = 1 := by exact_mod_cast hdist1
  -- Translate the count equation to the abbreviations.
  have hcountR' : Aneg1 + Ahalf + Aneghalf + Aquarter + Anegquarter + Azero = 196559 := by
    -- `hcountR` is already in this shape after rewriting.
    simpa [Aneg1, Ahalf, Aneghalf, Aquarter, Anegquarter, Azero, add_assoc, add_left_comm,
      add_comm] using! hcountR
  -- Moment `m=1`: `∑ ⟪u,v⟫ = 0`.
  have hm1 :
      1 - Aneg1 + (1 / 2 : ℝ) * (Ahalf - Aneghalf) +
          (1 / 4 : ℝ) * (Aquarter - Anegquarter) = 0 := by
    have hfib1 := hsum_inner_pow_fiberwise 1
    rw [sum_bs81Support24 (f := fun t : ℝ => (distCount (n := 24) C u t : ℝ) * t ^ 1)] at hfib1
    grind only
  -- Moment `m=3`: `∑ ⟪u,v⟫^3 = 0`.
  have hm3 :
      1 - Aneg1 + (1 / 8 : ℝ) * (Ahalf - Aneghalf) +
          (1 / 64 : ℝ) * (Aquarter - Anegquarter) = 0 := by
    have hfib3 := hsum_inner_pow_fiberwise 3
    rw [sum_bs81Support24 (f := fun t : ℝ => (distCount (n := 24) C u t : ℝ) * t ^ 3)] at hfib3
    grind only
  -- Moment `m=5`.
  have hm5 :
      1 - Aneg1 + (1 / 32 : ℝ) * (Ahalf - Aneghalf) +
          (1 / 1024 : ℝ) * (Aquarter - Anegquarter) = 0 := by
      have hfib5 := hsum_inner_pow_fiberwise 5
      rw [sum_bs81Support24 (f := fun t : ℝ => (distCount (n := 24) C u t : ℝ) * t ^ 5)] at hfib5
      grind only
  -- Solve the odd-moment subsystem: antipodal symmetry and `A_{-1}=1`.
  have hodd := solve_odd_subsystem Aneg1 Ahalf Aneghalf Aquarter Anegquarter hm1 hm3 hm5
  have hAhalf : Ahalf = Aneghalf := hodd.1
  have hAquarter : Aquarter = Anegquarter := hodd.2.1
  have hAneg1 : Aneg1 = 1 := hodd.2.2
  -- Moment `m=2`.
  have hm2 :
      1 + Aneg1 + (1 / 4 : ℝ) * (Ahalf + Aneghalf) +
          (1 / 16 : ℝ) * (Aquarter + Anegquarter) = 8190 := by
    exact
      hm2_of_fiberwise (C := C) (u := u) (Cfin := Cfin) (Aneg1 := Aneg1) (Ahalf := Ahalf)
        (Aneghalf := Aneghalf) (Aquarter := Aquarter) (Anegquarter := Anegquarter) (hAneg1 := rfl)
        (hAhalf := rfl) (hAneghalf := rfl) (hAquarter := rfl) (hAnegquarter := rfl)
        (hsum_inner_pow_fiberwise := hsum_inner_pow_fiberwise) (hsum2 := hsum2) (hdist1R := hdist1R)
  -- Moment `m=4`.
  have hm4 :
      1 + Aneg1 + (1 / 16 : ℝ) * (Ahalf + Aneghalf) +
          (1 / 256 : ℝ) * (Aquarter + Anegquarter) = 945 := by
    exact
      hm4_of_fiberwise (C := C) (u := u) (Cfin := Cfin) (Aneg1 := Aneg1) (Ahalf := Ahalf)
        (Aneghalf := Aneghalf) (Aquarter := Aquarter) (Anegquarter := Anegquarter) (hAneg1 := rfl)
        (hAhalf := rfl) (hAneghalf := rfl) (hAquarter := rfl) (hAnegquarter := rfl)
        (hsum_inner_pow_fiberwise := hsum_inner_pow_fiberwise) (hsum4 := hsum4) (hdist1R := hdist1R)
  -- Solve the even subsystem for `A_{±1/2}, A_{±1/4}, A_0`.
  have heven :
      Ahalf = 4600 ∧ Aquarter = 47104 ∧ Azero = 93150 :=
    solve_even_subsystem Aneg1 Ahalf Aneghalf Aquarter Anegquarter Azero hAhalf hAquarter hAneg1
      hm2 hm4 hcountR'
  have hAhalf_val : Ahalf = 4600 := heven.1
  have hAquarter_val : Aquarter = 47104 := heven.2.1
  have hAzero : Azero = 93150 := heven.2.2
  -- Convert back to `Nat` equalities (in a separate lemma to avoid heartbeat timeouts).
  have hneg1R : (distCount (n := 24) C u (-1 : ℝ) : ℝ) = 1 :=
    Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (id (Eq.symm hAneg1))))
  have hhalfR : (distCount (n := 24) C u (1 / 2 : ℝ) : ℝ) = 4600 :=
    Real.ext_cauchy (congrArg Real.cauchy hAhalf_val)
  have hneghalfR : (distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ) = 4600 := by
    have h' : Aneghalf = 4600 := hAhalf.symm.trans hAhalf_val
    dsimp [Aneghalf] at h'
    exact h'
  have hquarterR : (distCount (n := 24) C u (1 / 4 : ℝ) : ℝ) = 47104 := by
    exact Real.ext_cauchy (congrArg Real.cauchy hAquarter_val)
  have hnegquarterR : (distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ) = 47104 := by
    have h' : Anegquarter = 47104 := hAquarter.symm.trans hAquarter_val
    dsimp [Anegquarter] at h'
    exact h'
  have hzeroR : (distCount (n := 24) C u (0 : ℝ) : ℝ) = 93150 :=
    Real.ext_cauchy (congrArg Real.cauchy hAzero)
  have hNat :=
    nat_counts_of_real_counts (C := C) (u := u) hneg1R hhalfR hneghalfR hquarterR hnegquarterR
      hzeroR
  rcases hNat with ⟨hneg1Nat, hhalfNat, hneghalfNat, hquarterNat, hnegquarterNat, hzeroNat⟩
  exact ⟨hdist1, hneg1Nat, hhalfNat, hneghalfNat, hquarterNat, hnegquarterNat, hzeroNat⟩

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
