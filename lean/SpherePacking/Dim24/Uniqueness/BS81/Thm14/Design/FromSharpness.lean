-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.DistanceDistribution.Defs
import SpherePacking.Dim24.Uniqueness.BS81.LP.F24
import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.F24Coefficients
import SpherePacking.Dim24.Uniqueness.BS81.LP.Thm13Certificate
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.DesignEquiv
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Slack
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.DistanceDistribution.DeriveEq11FromMomentsFinal
import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.KernelPSD
import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Kernel
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Design11.OddDegree
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DesignEquivBridge24
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Building the Theorem 14 package from LP sharpness

This file constructs the BS81 Theorem 14 package from LP sharpness, following the standard
"Theorem 5/6 style" equality-case argument:
- use LP sharpness to force inner products into the root set,
- use tightness to get vanishing Gegenbauer sums (hence design),
- solve the distance-distribution linear system,
- and (optionally) build the resulting association-scheme package.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Polynomial

open Uniqueness.BS81

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Step A: from optimality to LP sharpness
-/

theorem sharpness_of_card_eq_bound
    (C : Set ℝ²⁴)
    (hcard : Set.ncard C = 196560) :
    (Set.ncard C : ℝ) = (Uniqueness.BS81.f24.eval (1 : ℝ)) /
      ((Uniqueness.BS81.f24.eval (1 : ℝ)) / 196560) := by
  have hcardR : (Set.ncard C : ℝ) = 196560 := by exact_mod_cast hcard
  have hf : (Uniqueness.BS81.f24.eval (1 : ℝ)) ≠ 0 := by
    -- `f24.eval 1 = 2025/1024`.
    rw [Uniqueness.BS81.f24_eval_one]
    norm_num
  simp_all

/-!
## Step B: design consequence
-/

/-- Nonnegativity of the Gegenbauer double sums, via the PSD zonal kernel. -/
public theorem gegenbauerDoubleSum24_nonneg
    (k : ℕ) (C : Finset ℝ²⁴) (hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ)) :
    0 ≤ gegenbauerDoubleSum24 k C := by
  simpa [gegenbauerDoubleSum24, Uniqueness.BS81.LP.zonalKernel24] using!
    (Uniqueness.BS81.LP.zonalKernel24_psd k) C hC

lemma sharpness_of_optimal
    (C : Set ℝ²⁴)
    (hcard : Set.ncard C = 196560) :
    (Set.ncard C : ℝ) =
      (Uniqueness.BS81.f24.eval (1 : ℝ)) / Uniqueness.BS81.LP.a0_24 := by
  have hcardR : (Set.ncard C : ℝ) = 196560 := by exact_mod_cast hcard
  have hratio :
      (Uniqueness.BS81.f24.eval (1 : ℝ)) / Uniqueness.BS81.LP.a0_24 = 196560 := by
    simpa using! (Uniqueness.BS81.LP.f24_eval_one_div_a0_24 : _)
  simp_all

lemma f24GegenbauerCoeff_pos_of_one_le_of_le_ten
    (k : ℕ) (hk1 : 1 ≤ k) (hk10 : k ≤ 10) :
    0 < Uniqueness.BS81.LP.f24GegenbauerCoeff k := by
  -- Brute-force case split on `k = 0..10` (all listed coefficients are positive rationals).
  -- (The hypothesis `hk1` is only used by callers; the proof works without it.)
  have hklt : k < 11 := Nat.lt_succ_of_le hk10
  have hk0 : 0 ≤ k := Nat.zero_le k
  interval_cases k using hk0, hklt
  all_goals
    norm_num [Uniqueness.BS81.LP.f24GegenbauerCoeff,
      Uniqueness.BS81.LP.f24GegenbauerCoeffNat]

lemma offDiag_f24_eval_eq_zero_of_optimal
    (C : Set ℝ²⁴)
    (hC : IsSphericalCode 24 C (1 / 2 : ℝ))
    (hcard : Set.ncard C = 196560) :
    ∀ ⦃u v : ℝ²⁴⦄, u ∈ C → v ∈ C → u ≠ v → (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ) = 0 := by
  intro u v hu hv huv
  have ha0 : 0 < Uniqueness.BS81.LP.a0_24 :=
    Uniqueness.BS81.LP.a0_24_pos
  have hneg :
      ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) (1 / 2 : ℝ) → (Uniqueness.BS81.f24).eval t ≤ 0 := by
    intro t ht
    simpa using! (Uniqueness.BS81.f24_eval_nonpos_of_mem_Icc t ht)
  have hdual :
      Uniqueness.BS81.IsDelsarteDual24
        (Uniqueness.BS81.f24) Uniqueness.BS81.LP.a0_24 :=
    Uniqueness.BS81.LP.isDelsarteDual24_f24
  have hsharp :
      (Set.ncard C : ℝ) =
        (Uniqueness.BS81.f24).eval (1 : ℝ) / Uniqueness.BS81.LP.a0_24 :=
    sharpness_of_optimal (C := C) hcard
  exact
    Uniqueness.BS81.sharp_bound_forces_inner_in_rootSet
      (C := C) (s := (1 / 2 : ℝ)) (f := Uniqueness.BS81.f24)
      (a0 := Uniqueness.BS81.LP.a0_24) hC ha0 hneg hdual hsharp hu hv huv

lemma mem_bs81Support24_of_f24_eval_eq_zero (t : ℝ)
    (ht : (Uniqueness.BS81.f24).eval t = 0) :
    t ∈ Uniqueness.BS81.Thm14.bs81Support24 := by
  -- Use the explicit factorization of `f24` to enumerate the roots.
  have ht' :
      (t + 1) *
          (t + (1 / 2 : ℝ)) ^ 2 *
            (t + (1 / 4 : ℝ)) ^ 2 *
              t ^ 2 *
                (t - (1 / 4 : ℝ)) ^ 2 *
                  (t - (1 / 2 : ℝ)) = 0 := by
    simpa [Uniqueness.BS81.f24_eval] using! ht
  -- Reassociate to apply `mul_eq_zero` repeatedly.
  grind only [= mem_bs81Support24_iff]

lemma f24_doubleSum_eq_a0_card_sq_of_optimal
    (C : Set ℝ²⁴)
    (hC : IsSphericalCode 24 C (1 / 2 : ℝ))
    (hcard : Set.ncard C = 196560) :
    (Uniqueness.BS81.LP.a0_24) * ((hC.finite.toFinset).card : ℝ) ^ 2 =
      (hC.finite.toFinset).sum (fun u =>
        (hC.finite.toFinset).sum (fun v => (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ))) := by
  let Cfin : Finset ℝ²⁴ := hC.finite.toFinset
  have hmem : ∀ {u : ℝ²⁴}, u ∈ Cfin → u ∈ C := by
    intro u hu
    simpa [Cfin] using! (hC.finite.mem_toFinset.1 hu)
  have hnorm : ∀ u ∈ Cfin, ‖u‖ = (1 : ℝ) := by
    intro u hu
    exact hC.norm_one (hmem hu)
  have hcard_fin : Cfin.card = 196560 := by
    have hn : Set.ncard C = Cfin.card := by
      simpa [Cfin] using! (Set.ncard_eq_toFinset_card C hC.finite)
    -- rewrite via `hn` in `hcard`
    simpa [hn] using! hcard
  have hcardR : (Cfin.card : ℝ) = (196560 : ℝ) := by exact_mod_cast hcard_fin
  have hcardR_ne : (Cfin.card : ℝ) ≠ 0 := by
    -- Rewrite the goal using the explicit cardinality.
    rw [hcardR]
    norm_num
  have ha0_ne : (Uniqueness.BS81.LP.a0_24) ≠ 0 :=
    ne_of_gt Uniqueness.BS81.LP.a0_24_pos
  have hsharp_fin :
      (Cfin.card : ℝ) =
        (Uniqueness.BS81.f24).eval (1 : ℝ) / Uniqueness.BS81.LP.a0_24 := by
    have hn : (Set.ncard C : ℝ) = (Cfin.card : ℝ) := by
      have hn_nat : Set.ncard C = Cfin.card := by
        simpa [Cfin] using! (Set.ncard_eq_toFinset_card C hC.finite)
      exact_mod_cast hn_nat
    simpa [hn] using! (sharpness_of_optimal (C := C) hcard)
  -- From sharpness: `a0 * card = f(1)`.
  have ha0_mul_card : (Uniqueness.BS81.LP.a0_24) * (Cfin.card : ℝ) =
      (Uniqueness.BS81.f24).eval (1 : ℝ) := by
    -- Multiply the sharpness identity by `a0`.
    have : (Uniqueness.BS81.LP.a0_24) *
        ((Uniqueness.BS81.f24).eval (1 : ℝ) / Uniqueness.BS81.LP.a0_24) =
        (Uniqueness.BS81.f24).eval (1 : ℝ) := by
      field_simp [ha0_ne]
    simpa [hsharp_fin] using! this
  have ha0_card_sq :
      (Uniqueness.BS81.LP.a0_24) * (Cfin.card : ℝ) ^ 2 =
        (Cfin.card : ℝ) * (Uniqueness.BS81.f24).eval (1 : ℝ) := by
    calc
      (Uniqueness.BS81.LP.a0_24) * (Cfin.card : ℝ) ^ 2 =
          ((Uniqueness.BS81.LP.a0_24) * (Cfin.card : ℝ)) * (Cfin.card : ℝ) := by
            simp [pow_two, mul_assoc]
      _ = (Uniqueness.BS81.f24).eval (1 : ℝ) * (Cfin.card : ℝ) := by
            simp [ha0_mul_card, mul_assoc]
      _ = (Cfin.card : ℝ) * (Uniqueness.BS81.f24).eval (1 : ℝ) := by
            simp [mul_comm]
  -- Off-diagonal terms vanish pointwise (complementary slackness).
  have hoff :
      ∀ u ∈ Cfin, ∀ v ∈ Cfin, v ≠ u →
        (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ) = 0 := by
    intro u hu v hv hvu
    have huC : u ∈ C := hmem hu
    exact offDiag_f24_eval_eq_zero_of_optimal C hC hcard huC (hmem hv) (id (Ne.symm hvu))
  have hrow (u : ℝ²⁴) (hu : u ∈ Cfin) :
      Cfin.sum (fun v => (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ)) =
        (Uniqueness.BS81.f24).eval (1 : ℝ) := by
    have huNorm : ‖u‖ = (1 : ℝ) := hnorm u hu
    have hinner_self : (⟪u, u⟫ : ℝ) = (1 : ℝ) := by
      exact inner_self_eq_one_of_norm_eq_one (hnorm u hu)
    have hdiag :
        (Uniqueness.BS81.f24).eval (⟪u, u⟫ : ℝ) =
          (Uniqueness.BS81.f24).eval (1 : ℝ) := by
      simpa using! congrArg (fun x : ℝ => (Uniqueness.BS81.f24).eval x) hinner_self
    have herase :
        (Cfin.erase u).sum (fun v => (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro v hv
      have hv' : v ∈ Cfin ∧ v ≠ u :=
        ⟨(Finset.mem_erase.mp hv).2, (Finset.mem_erase.mp hv).1⟩
      exact hoff u hu v hv'.1 hv'.2
    -- Split the sum into diagonal + erase, then use off-diagonal vanishing.
    have hsplit :
        Cfin.sum (fun v => (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ)) =
          (Uniqueness.BS81.f24).eval (⟪u, u⟫ : ℝ) +
            (Cfin.erase u).sum (fun v => (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ)) := by
      simpa using!
        (Finset.add_sum_erase (s := Cfin)
          (f := fun v => (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ))
          (a := u) hu).symm
    calc
      Cfin.sum (fun v => (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ)) =
          (Uniqueness.BS81.f24).eval (⟪u, u⟫ : ℝ) +
            (Cfin.erase u).sum (fun v => (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ)) := hsplit
      _ = (Uniqueness.BS81.f24).eval (⟪u, u⟫ : ℝ) := by
            rw [herase, add_zero]
      _ = (Uniqueness.BS81.f24).eval (1 : ℝ) := hdiag
  have hdouble :
      Cfin.sum (fun u => Cfin.sum (fun v => (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ))) =
        (Cfin.card : ℝ) * (Uniqueness.BS81.f24).eval (1 : ℝ) := by
    calc
      Cfin.sum (fun u => Cfin.sum (fun v => (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ))) =
          Cfin.sum (fun _u => (Uniqueness.BS81.f24).eval (1 : ℝ)) :=
            Finset.sum_congr rfl hrow
      _ = (Cfin.card : ℝ) * (Uniqueness.BS81.f24).eval (1 : ℝ) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
  -- Combine `a0 * card^2 = card * f(1)` with `S = card * f(1)`.
  have : (Uniqueness.BS81.LP.a0_24) * (Cfin.card : ℝ) ^ 2 =
      (Cfin.card : ℝ) * (Uniqueness.BS81.f24).eval (1 : ℝ) := ha0_card_sq
  -- Rewrite the RHS using `hdouble`.
  simpa [Cfin] using! this.trans hdouble.symm

lemma gegenbauerDesign10_of_optimal
    (C : Set ℝ²⁴)
    (hC : IsSphericalCode 24 C (1 / 2 : ℝ))
    (hcard : Set.ncard C = 196560) :
    IsGegenbauerDesign24 10 hC.finite.toFinset := by
  -- Apply the abstract slackness-to-design lemma with the explicit `f24` expansion.
  have hExp :
      (Uniqueness.BS81.f24 : Polynomial ℝ) =
        (Finset.range (10 + 1)).sum (fun k =>
          (Polynomial.C (Uniqueness.BS81.LP.f24GegenbauerCoeff k)) *
            (Uniqueness.BS81.LP.Gegenbauer24 k)) := by
    -- `Finset.range (10+1) = Finset.range 11`.
    simpa using! (Uniqueness.BS81.LP.f24_eq_sum_coeff_mul_gegenbauer24 : _)
  have ha_pos :
      ∀ k : ℕ, 1 ≤ k → k ≤ 10 → 0 < Uniqueness.BS81.LP.f24GegenbauerCoeff k := by
    intro k hk1 hk10
    exact f24GegenbauerCoeff_pos_of_one_le_of_le_ten k hk1 hk10
  have hgegen_nonneg :
      ∀ k : ℕ, k ≤ 10 → 0 ≤ gegenbauerDoubleSum24 k hC.finite.toFinset := by
    intro k _hk
    -- PSD kernel nonnegativity.
    refine Uniqueness.BS81.Thm14.gegenbauerDoubleSum24_nonneg
      (k := k) (C := hC.finite.toFinset) ?_
    intro u hu
    have huC : u ∈ C := by
      simpa using! (hC.finite.mem_toFinset.1 hu)
    exact hC.norm_one huC
  have ha_nonneg :
      ∀ k ≤ 10, 0 ≤ Uniqueness.BS81.LP.f24GegenbauerCoeff k := by
    intro k _hk
    exact Uniqueness.BS81.LP.f24GegenbauerCoeff_nonneg k
  have hsharp :
      (Uniqueness.BS81.LP.f24GegenbauerCoeff 0) *
          ((hC.finite.toFinset).card : ℝ) ^ 2 =
        (hC.finite.toFinset).sum (fun u =>
          (hC.finite.toFinset).sum (fun v =>
            (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ))) := by
    -- `a0_24 = f24GegenbauerCoeff 0` by definition.
    simpa [Uniqueness.BS81.LP.a0_24] using!
      (f24_doubleSum_eq_a0_card_sq_of_optimal (C := C) hC hcard)
  -- Now apply `Slack.isGegenbauerDesign24_of_sharp_expansion` with `t=N=10`.
  exact
    Uniqueness.BS81.Thm14.isGegenbauerDesign24_of_sharp_expansion
      (t := 10) (N := 10) (a := Uniqueness.BS81.LP.f24GegenbauerCoeff)
      (f := Uniqueness.BS81.f24) hExp le_rfl ha_pos
      (Cfin := hC.finite.toFinset) hgegen_nonneg ha_nonneg hsharp

/-- Sharpness at `196560` implies the BS81 design axiom up to degree `10`. -/
public lemma design10_of_optimal
    (C : Set ℝ²⁴)
    (hC : IsSphericalCode 24 C (1 / 2 : ℝ))
    (hcard : Set.ncard C = 196560) :
    IsBS81SphericalDesign24 10 hC.finite.toFinset := by
  have hG : IsGegenbauerDesign24 10 hC.finite.toFinset :=
    gegenbauerDesign10_of_optimal (C := C) hC hcard
  have hCne : (hC.finite.toFinset : Finset ℝ²⁴).Nonempty := by
    have hpos : 0 < Set.ncard C := by
      have : 0 < (196560 : ℕ) := by norm_num
      simp [hcard, this]
    have hneSet : C.Nonempty :=
      (Set.ncard_pos (s := C) (hs := hC.finite)).1 hpos
    rcases hneSet with ⟨u, hu⟩
    exact ⟨u, hC.finite.mem_toFinset.2 hu⟩
  -- Convert from the Gegenbauer-sum characterization.
  refine
    Uniqueness.BS81.Thm14.AdditionTheorem.isBS81SphericalDesign24_of_isGegenbauerDesign24
      (t := 10) (C := hC.finite.toFinset) ?_ hG hCne
  intro u hu
  have huC : u ∈ C := by
    simpa using! (hC.finite.mem_toFinset.1 hu)
  exact hC.norm_one huC

/-- Sharpness at `196560` forces all inner products to lie in `bs81Support24`. -/
public lemma support_of_optimal
    (C : Set ℝ²⁴)
    (hC : IsSphericalCode 24 C (1 / 2 : ℝ))
    (hcard : Set.ncard C = 196560) :
    ∀ ⦃u v : ℝ²⁴⦄, u ∈ C → v ∈ C → (⟪u, v⟫ : ℝ) ∈ bs81Support24 := by
  intro u v hu hv
  by_cases huv : u = v
  · subst huv
    have huNorm : ‖u‖ = (1 : ℝ) := hC.norm_one hu
    have hinner_self : (⟪u, u⟫ : ℝ) = (1 : ℝ) :=
      inner_self_eq_one_of_norm_eq_one huNorm
    -- Avoid `simp` rewriting `⟪u,u⟫` to `‖u‖^2` (which would miss `hinner_self`).
    rw [hinner_self]
    simp [bs81Support24]
  · have h0 :
        (Uniqueness.BS81.f24).eval (⟪u, v⟫ : ℝ) = 0 :=
      offDiag_f24_eval_eq_zero_of_optimal (C := C) hC hcard hu hv huv
    -- Every root of `f24` is one of `{ -1, ±1/2, ±1/4, 0 }`, hence lies in `bs81Support24`.
    exact mem_bs81Support24_of_f24_eval_eq_zero (t := (⟪u, v⟫ : ℝ)) h0

/-- Sharpness at `196560` implies the BS81 design axiom up to degree `11`. -/
public theorem design11_of_optimal
    (C : Set ℝ²⁴)
    (hC : IsSphericalCode 24 C (1 / 2 : ℝ))
    (hcard : Set.ncard C = 196560) :
    IsBS81SphericalDesign24 11 hC.finite.toFinset := by
  let Cfin : Finset ℝ²⁴ := hC.finite.toFinset
  have hnorm : ∀ u ∈ Cfin, ‖u‖ = (1 : ℝ) := by
    intro u hu
    have huC : u ∈ C := by
      simpa [Cfin] using! (hC.finite.mem_toFinset.1 hu)
    exact hC.norm_one huC
  have hG10 : IsGegenbauerDesign24 10 Cfin :=
    gegenbauerDesign10_of_optimal (C := C) hC hcard
  -- Antipodality from the explicit distance distribution: the unique `v` with `⟪u,v⟫ = -1` is
  -- `-u`.
  have hanti : Uniqueness.BS81.Thm14.BuildSteps.IsAntipodalFinset Cfin := by
    intro u hu
    have huC : u ∈ C := by
      simpa [Cfin] using! (hC.finite.mem_toFinset.1 hu)
    have hdist := (Uniqueness.BS81.Thm14.dist_eq11_of_design10_and_support
      (C := C) hC hcard (design10_of_optimal (C := C) hC hcard)
      (support_of_optimal (C := C) hC hcard) huC)
    have hneg1 : distCount (n := 24) C u (-1 : ℝ) = 1 := hdist.2.1
    -- Unfold `distCount` and use `Set.ncard_eq_one` to pick the unique `v`.
    have hS :
        ({v : ℝ²⁴ | v ∈ C ∧ (⟪u, v⟫ : ℝ) = (-1 : ℝ)}).ncard = 1 := by
      simpa [Uniqueness.BS81.distCount] using! hneg1
    rcases (Set.ncard_eq_one.mp hS) with ⟨v, hv⟩
    have hvS : v ∈ ({v : ℝ²⁴ | v ∈ C ∧ (⟪u, v⟫ : ℝ) = (-1 : ℝ)}) := by
      -- `v ∈ {v}` and `S = {v}`.
      simp [hv]
    have hvC : v ∈ C := hvS.1
    have hinner : (⟪u, v⟫ : ℝ) = (-1 : ℝ) := hvS.2
    have huNorm : ‖u‖ = (1 : ℝ) := hC.norm_one huC
    have hvNorm : ‖v‖ = (1 : ℝ) := hC.norm_one hvC
    have huv' : u = -v :=
      (inner_eq_neg_one_iff_of_norm_eq_one huNorm hvNorm).1 (by simpa using! hinner)
    have hv_eq : v = -u := by
      have : -u = v := by simpa using! congrArg Neg.neg huv'
      simpa [eq_comm] using! this
    have hneg_uC : -u ∈ C := by simpa [hv_eq] using! hvC
    -- Convert back to finset membership.
    simpa [Cfin] using! (hC.finite.mem_toFinset.2 hneg_uC)
  have hG11 : IsGegenbauerDesign24 11 Cfin := by
    intro k hk1 hk11
    by_cases hk : k = 11
    · subst hk
      -- `11` is odd, so antipodality forces vanishing.
      have hkOdd : Odd 11 := by decide
      exact BuildSteps.Design11.gegenbauerDoubleSum24_eq_zero_of_antipodal_of_odd
          11 hkOdd Cfin hanti
    · have hklt : k < 11 := lt_of_le_of_ne hk11 hk
      have hk10 : k ≤ 10 := Nat.le_of_lt_succ hklt
      exact hG10 k hk1 hk10
  have hCne : Cfin.Nonempty := by
    have hpos : 0 < Set.ncard C := by
      have : 0 < (196560 : ℕ) := by norm_num
      simp [hcard, this]
    have hneSet : C.Nonempty :=
      (Set.ncard_pos (s := C) (hs := hC.finite)).1 hpos
    rcases hneSet with ⟨u, hu⟩
    exact ⟨u, by simpa [Cfin] using! (hC.finite.mem_toFinset.2 hu)⟩
  exact
    Uniqueness.BS81.Thm14.AdditionTheorem.isBS81SphericalDesign24_of_isGegenbauerDesign24
      (t := 11) (C := Cfin) hnorm hG11 hCne

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
