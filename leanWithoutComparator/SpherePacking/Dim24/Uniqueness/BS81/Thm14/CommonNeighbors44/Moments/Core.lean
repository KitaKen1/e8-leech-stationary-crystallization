-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Auxiliary
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Mixed moments for 44 common neighbors

This file computes spherical mixed moments used in the 44-common-neighbors count (BS81 Lemma
18(ii)). The main outputs are moment identities for an orthogonal pair `u ⟂ v`.

## Main statements
* `CommonNeighbors44MomentsFinal.sphereAvg24_inner_sq_mul_inner_sq_eq`
* `CommonNeighbors44MomentsFinal.sphereAvg24_inner_pow_four_mul_inner_sq_eq`
* `CommonNeighbors44MomentsFinal.sphereAvg24_inner_pow_four_mul_inner_pow_four_eq`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44MomentsFinal

noncomputable section

open scoped RealInnerProductSpace BigOperators ENNReal

open CommonNeighbors44Aux
open MeasureTheory Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Basic measure/integrability helpers
-/

lemma integrable_coord_pow (i : Fin 24) (m : ℕ) :
    Integrable (fun x : S23 => (x.1 i : ℝ) ^ m) sphereMeasure24 := by
  simpa [mul_one] using! (integrable_coord_pow_mul_coord_pow (i := i) (j := i) (m := m) (n := 0))

/-!
## Linearity helpers for `sphereAvg24`
-/

/-!
## One-dimensional moments from the equality-case package
-/

lemma sphereAvg24_inner_pow_four_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4) = (1 / 208 : ℝ) := by
  have hred :=
    (CommonNeighbors44Aux.finsetAvg_inner_pow_eq_sphereAvg (h := h) (u := u) 4 (by decide))
  have hm := CommonNeighbors44Aux.finsetAvg_inner_pow_four_eq (h := h) (hu := hu)
  have : sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 4) = (1 / 208 : ℝ) := by
    simp_all
  simpa [real_inner_comm] using! this

lemma sphereAvg24_inner_pow_six_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 6) = (5 / 5824 : ℝ) := by
  have hred :=
    (CommonNeighbors44Aux.finsetAvg_inner_pow_eq_sphereAvg (h := h) (u := u) 6 (by decide))
  have hm := CommonNeighbors44Aux.finsetAvg_inner_pow_six_eq (h := h) (hu := hu)
  have : sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 6) = (5 / 5824 : ℝ) := by
    simp_all
  simpa [real_inner_comm] using! this

lemma sphereAvg24_inner_pow_eight_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 8) = (1 / 4992 : ℝ) := by
  have hred :=
    (CommonNeighbors44Aux.finsetAvg_inner_pow_eq_sphereAvg (h := h) (u := u) 8 (by decide))
  have hm := CommonNeighbors44Aux.finsetAvg_inner_pow_eight_eq (h := h) (hu := hu)
  have : sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 8) = (1 / 4992 : ℝ) := by
    simp_all
  simpa [real_inner_comm] using! this

/-!
## Reduce unit-vector inner moments to a coordinate moment
-/

lemma exists_orthonormalBasis_first {u : ℝ²⁴} (hu1 : ‖u‖ = (1 : ℝ)) :
    ∃ b : OrthonormalBasis (Fin 24) ℝ ℝ²⁴, b (0 : Fin 24) = u := by
  let s : Set (Fin 24) := {0}
  let v : Fin 24 → ℝ²⁴ := fun i => if i = (0 : Fin 24) then u else 0
  have hv : Orthonormal ℝ (s.restrict v) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩
      have : i = (0 : Fin 24) := by simpa [s] using! hi
      subst this
      simp [Set.restrict, v, hu1]
    · intro i j hij
      exfalso
      exact hij (Subsingleton.elim _ _)
  have hcard : Module.finrank ℝ ℝ²⁴ = Fintype.card (Fin 24) :=
    finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 24)
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq (E := ℝ²⁴) (𝕜 := ℝ) (ι := Fin 24)
      hcard (v := v) (s := s) hv
  refine ⟨b, ?_⟩
  simpa [s, v] using! hb (0 : Fin 24) (by simp [s])

lemma sphereAvg24_coord0_pow_eq_inner_pow {u : ℝ²⁴} (hu1 : ‖u‖ = (1 : ℝ)) (m : ℕ) :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ m) =
      sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ m) := by
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_first (u := u) hu1
  let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := b.repr
  have hinv :=
    sphereAvg24_comp_linearIsometryEquiv (e := e) (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ m)
  have hcoord : ∀ x : ℝ²⁴, (e x) (0 : Fin 24) = (⟪u, x⟫ : ℝ) := by
    intro x
    have : e x (0 : Fin 24) = ⟪b (0 : Fin 24), x⟫ := by
      simpa [e] using! (b.repr_apply_apply x (0 : Fin 24))
    simpa [hb0, real_inner_comm] using! this
  have : sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ m) =
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ m) := by
    simpa [hcoord] using! hinv
  exact this.symm

lemma sphereAvg24_coord0_pow_four_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) = (1 / 208 : ℝ) := by
  have hu1 : ‖u‖ = (1 : ℝ) := h.code.norm_one hu
  have hinner := sphereAvg24_inner_pow_four_eq (h := h) (u := u) hu
  have hinner' : sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 4) = (1 / 208 : ℝ) := by
    simpa [real_inner_comm] using! hinner
  calc
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) =
        sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 4) := by
          simpa using! (sphereAvg24_coord0_pow_eq_inner_pow (u := u) hu1 4)
    _ = (1 / 208 : ℝ) := hinner'

lemma sphereAvg24_coord0_pow_six_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) = (5 / 5824 : ℝ) := by
  have hu1 : ‖u‖ = (1 : ℝ) := h.code.norm_one hu
  have hinner := sphereAvg24_inner_pow_six_eq (h := h) (u := u) hu
  have hinner' : sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 6) = (5 / 5824 : ℝ) := by
    simpa [real_inner_comm] using! hinner
  calc
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) =
        sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 6) := by
          simpa using! (sphereAvg24_coord0_pow_eq_inner_pow (u := u) hu1 6)
    _ = (5 / 5824 : ℝ) := hinner'

lemma sphereAvg24_coord0_pow_eight_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) = (1 / 4992 : ℝ) := by
  have hu1 : ‖u‖ = (1 : ℝ) := h.code.norm_one hu
  have hinner := sphereAvg24_inner_pow_eight_eq (h := h) (u := u) hu
  have hinner' : sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 8) = (1 / 4992 : ℝ) := by
    simpa [real_inner_comm] using! hinner
  calc
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) =
        sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ 8) := by
          simpa using! (sphereAvg24_coord0_pow_eq_inner_pow (u := u) hu1 8)
    _ = (1 / 4992 : ℝ) := hinner'

/-!
## Coordinate symmetry via permutations
-/

lemma sphereAvg24_coord_pow_eq (m : ℕ) (i j : Fin 24) :
    sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ m) = sphereAvg24 (fun x : ℝ²⁴ => (x j) ^ m) := by
  let σ : Fin 24 ≃ Fin 24 := Equiv.swap i j
  let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ :=
    LinearIsometryEquiv.piLpCongrLeft (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (E := ℝ) σ
  -- under the swap, coordinate `j` becomes `i`
  have h := sphereAvg24_comp_linearIsometryEquiv (e := e) (f := fun x : ℝ²⁴ => (x j) ^ m)
  simpa [e, σ, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using! h

lemma sphereAvg24_coord_sq_mul_coord_sq_eq_of_ne (i j : Fin 24) (hij : i ≠ j) :
    sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2) =
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) := by
  -- permutation sending `i ↦ 0` and `j ↦ 1` (two swaps)
  let σ₁ : Equiv.Perm (Fin 24) := Equiv.swap i (0 : Fin 24)
  let σ₂ : Equiv.Perm (Fin 24) := Equiv.swap (σ₁ j) (1 : Fin 24)
  let σ : Equiv.Perm (Fin 24) := σ₁.trans σ₂
  have hσ₁j0 : σ₁ j ≠ (0 : Fin 24) := by
    intro h
    have : j = i := by
      have := congrArg σ₁ h
      simpa [σ₁] using! this
    exact hij this.symm
  have hσi : σ i = (0 : Fin 24) := by
    have h0ne : (0 : Fin 24) ≠ σ₁ j := by
      simpa [ne_comm] using! hσ₁j0
    have hσ₂0 : σ₂ (0 : Fin 24) = (0 : Fin 24) := by
      simp [σ₂, Equiv.swap_apply_of_ne_of_ne, h0ne, show (0 : Fin 24) ≠ (1 : Fin 24) by decide]
    simp [σ, σ₁, σ₂, hσ₂0]
  have hσj : σ j = (1 : Fin 24) := by
    simp [σ, σ₂]
  let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ :=
    LinearIsometryEquiv.piLpCongrLeft (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (E := ℝ) σ
  have hinv :=
    sphereAvg24_comp_linearIsometryEquiv (e := e)
      (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2)
  have hsymm0 : σ.symm (0 : Fin 24) = i := by simpa [hσi] using! (σ.symm_apply_apply i)
  have hsymm1 : σ.symm (1 : Fin 24) = j := by simpa [hσj] using! (σ.symm_apply_apply j)
  simpa [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', hsymm0, hsymm1,
    mul_assoc, mul_left_comm, mul_comm] using! hinv

lemma sphereAvg24_coord0_pow_four_mul_coord_sq_eq (i : Fin 24) (hi0 : i ≠ (0 : Fin 24)) :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2) =
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2) := by
  by_cases hi1 : i = (1 : Fin 24)
  · subst hi1; rfl
  · let σ : Equiv.Perm (Fin 24) := Equiv.swap i (1 : Fin 24)
    have hσ0 : σ (0 : Fin 24) = (0 : Fin 24) := by
      have h0i : (0 : Fin 24) ≠ i := by simpa [ne_comm] using! hi0
      simp [σ, Equiv.swap_apply_of_ne_of_ne, h0i, show (0 : Fin 24) ≠ (1 : Fin 24) by decide]
    let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ :=
      LinearIsometryEquiv.piLpCongrLeft (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (E := ℝ) σ
    have hinv :=
      sphereAvg24_comp_linearIsometryEquiv (e := e)
        (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2)
    have hsymm0 : σ.symm (0 : Fin 24) = (0 : Fin 24) := by
      simpa [hσ0] using! (σ.symm_apply_apply (0 : Fin 24))
    have hsymm1 : σ.symm (1 : Fin 24) = i := by
      have : σ i = (1 : Fin 24) := by simp [σ]
      simpa [this] using! (σ.symm_apply_apply i)
    simpa [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', hsymm0, hsymm1, hσ0,
      mul_assoc, mul_left_comm, mul_comm] using! hinv

lemma sphereAvg24_coord0_pow_six_mul_coord_sq_eq (i : Fin 24) (hi0 : i ≠ (0 : Fin 24)) :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2) =
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
  by_cases hi1 : i = (1 : Fin 24)
  · subst hi1; rfl
  · let σ : Equiv.Perm (Fin 24) := Equiv.swap i (1 : Fin 24)
    have hσ0 : σ (0 : Fin 24) = (0 : Fin 24) := by
      have h0i : (0 : Fin 24) ≠ i := by simpa [ne_comm] using! hi0
      simp [σ, Equiv.swap_apply_of_ne_of_ne, h0i, show (0 : Fin 24) ≠ (1 : Fin 24) by decide]
    let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ :=
      LinearIsometryEquiv.piLpCongrLeft (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (E := ℝ) σ
    have hinv :=
      sphereAvg24_comp_linearIsometryEquiv (e := e)
        (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2)
    have hsymm0 : σ.symm (0 : Fin 24) = (0 : Fin 24) := by
      simpa [hσ0] using! (σ.symm_apply_apply (0 : Fin 24))
    have hsymm1 : σ.symm (1 : Fin 24) = i := by
      have : σ i = (1 : Fin 24) := by simp [σ]
      simpa [this] using! (σ.symm_apply_apply i)
    simpa [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', hsymm0, hsymm1, hσ0,
      mul_assoc, mul_left_comm, mul_comm] using! hinv

/-!
## Coordinate mixed moments
-/

lemma sum_sq_eq_diag_offdiag (x : ℝ²⁴) :
    (∑ i : Fin 24, (x i) ^ 2) ^ 2 =
      (∑ i : Fin 24, (x i) ^ 4) +
        (∑ i : Fin 24, (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2) := by
  let a : Fin 24 → ℝ := fun i => (x i) ^ 2
  calc
    (∑ i : Fin 24, (x i) ^ 2) ^ 2 = (∑ i : Fin 24, a i) ^ 2 := by simp [a]
    _ = (∑ i : Fin 24, a i) * (∑ j : Fin 24, a j) := by simp [pow_two]
    _ = ∑ i : Fin 24, ∑ j : Fin 24, a i * a j := by
          simp [Finset.sum_mul_sum]
    _ = ∑ i : Fin 24, ((a i * a i) + (Finset.univ.erase i).sum fun j => a i * a j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hsplit :
              ∑ j : Fin 24, a i * a j =
                (a i * a i) + (Finset.univ.erase i).sum fun j => a i * a j := by
            -- split off the `j=i` term
            exact
              (Finset.add_sum_erase (s := (Finset.univ : Finset (Fin 24)))
                (f := fun j : Fin 24 => a i * a j) (a := i) (by simp)).symm
          exact hsplit
    _ =
        (∑ i : Fin 24, a i * a i) +
          (∑ i : Fin 24, (Finset.univ.erase i).sum fun j => a i * a j) := by
          simp
    _ =
        (∑ i : Fin 24, (x i) ^ 4) +
          (∑ i : Fin 24, (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2) := by
          -- rewrite each term using `a i = (x i)^2`
          have hdiag : (∑ i : Fin 24, a i * a i) = (∑ i : Fin 24, (x i) ^ 4) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            -- `a i * a i = (x i)^4`
            simpa [a] using! (pow_add (x i) 2 2).symm
          exact (add_left_inj (∑ i, ∑ j ∈ Finset.univ.erase i, a i * a j)).mpr hdiag

lemma sphereAvg24_sum_coord_sq_sq_eq_one :
    sphereAvg24 (fun x : ℝ²⁴ => (∑ i : Fin 24, (x i) ^ 2) ^ 2) = (1 : ℝ) := by
  -- On the sphere: `∑ x_i^2 = ‖x‖^2 = 1`.
  have hpoint : ∀ x : S23, (∑ i : Fin 24, (x.1 i) ^ 2) ^ 2 = (1 : ℝ) := by
    intro x
    have hxmem := x.2
    dsimp [S23] at hxmem
    have hx : ‖(x : ℝ²⁴)‖ = (1 : ℝ) :=
      mem_sphere_zero_iff_norm.mp hxmem
    have hsum : (∑ i : Fin 24, (x.1 i) ^ 2) = (1 : ℝ) := by
      -- `∑ x_i^2 = ⟪x,x⟫ = ‖x‖^2`.
      have : (∑ i : Fin 24, (x.1 i) ^ 2) = ‖(x : ℝ²⁴)‖ ^ 2 :=
        sum_sq_eq_norm_sq ↑x
      simpa [this, hx, pow_two]
    have hsq : (∑ i : Fin 24, (x.1 i) ^ 2) ^ 2 = (1 : ℝ) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hsum
    exact hsq.trans (by simp)
  have hcongr :
      sphereAvg24 (fun x : ℝ²⁴ => (∑ i : Fin 24, (x i) ^ 2) ^ 2) =
        sphereAvg24 (fun _ : ℝ²⁴ => (1 : ℝ)) :=
    sphereAvg24_congr hpoint
  simpa [sphereAvg24_const] using! hcongr.trans (sphereAvg24_const (c := (1 : ℝ)))

lemma sphereAvg24_coord_sq_mul_coord_sq_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) = (1 / 624 : ℝ) := by
  -- Denote `A = E[x0^4]` and `B = E[x0^2 x1^2]`.
  have hA : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) = (1 / 208 : ℝ) :=
    sphereAvg24_coord0_pow_four_eq (h := h) (u := u) hu
  let B : ℝ :=
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2)
  have hone : sphereAvg24 (fun x : ℝ²⁴ => (∑ i : Fin 24, (x i) ^ 2) ^ 2) = (1 : ℝ) :=
    sphereAvg24_sum_coord_sq_sq_eq_one
  have hexpand :
      sphereAvg24 (fun x : ℝ²⁴ => (∑ i : Fin 24, (x i) ^ 2) ^ 2) =
        sphereAvg24 (fun x : ℝ²⁴ => (∑ i : Fin 24, (x i) ^ 4) +
          (∑ i : Fin 24, (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2)) := by
    refine sphereAvg24_congr ?_
    intro x
    simpa using! (sum_sq_eq_diag_offdiag (x := x.1))
  -- linearize the RHS
  have hInt4 :
      Integrable (fun x : S23 => ∑ i : Fin 24, (x.1 i : ℝ) ^ 4) sphereMeasure24 := by
    simpa using!
      (MeasureTheory.integrable_finset_sum (s := (Finset.univ : Finset (Fin 24)))
        (f := fun i : Fin 24 => fun x : S23 => (x.1 i : ℝ) ^ 4)
        (fun i _ => integrable_coord_pow i 4))
  have hIntOff :
      Integrable
        (fun x : S23 => ∑ i : Fin 24, (Finset.univ.erase i).sum fun j =>
          (x.1 i : ℝ) ^ 2 * (x.1 j : ℝ) ^ 2)
        sphereMeasure24 := by
    have hinner :
        ∀ i : Fin 24,
          Integrable (fun x : S23 => (Finset.univ.erase i).sum fun j =>
            (x.1 i : ℝ) ^ 2 * (x.1 j : ℝ) ^ 2)
            sphereMeasure24 := by
      intro i
      simpa using!
        (MeasureTheory.integrable_finset_sum (s := (Finset.univ.erase i))
          (f := fun j : Fin 24 => fun x : S23 => (x.1 i : ℝ) ^ 2 * (x.1 j : ℝ) ^ 2)
          (fun j _ => integrable_coord_pow_mul_coord_pow i j 2 2))
    exact integrable_finset_sum Finset.univ fun i a => hinner i
  have hlin :
      sphereAvg24 (fun x : ℝ²⁴ => (∑ i : Fin 24, (x i) ^ 4) +
          (∑ i : Fin 24, (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2)) =
        sphereAvg24 (fun x : ℝ²⁴ => ∑ i : Fin 24, (x i) ^ 4) +
          sphereAvg24 (fun x : ℝ²⁴ => ∑ i : Fin 24, (Finset.univ.erase i).sum fun j =>
            (x i) ^ 2 * (x j) ^ 2) :=
    sphereAvg24_add (fun x => ∑ i, x.ofLp i ^ 4)
      (fun x => ∑ i, ∑ j ∈ Finset.univ.erase i, x.ofLp i ^ 2 * x.ofLp j ^ 2) hInt4 hIntOff
  have hsum4 :
      sphereAvg24 (fun x : ℝ²⁴ => ∑ i : Fin 24, (x i) ^ 4) =
        ∑ i : Fin 24, sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 4) := by
    simpa using!
      (sphereAvg24_finset_sum (s := (Finset.univ : Finset (Fin 24)))
        (f := fun i : Fin 24 => fun x : ℝ²⁴ => (x i) ^ 4)
        (fun i _ => integrable_coord_pow i 4))
  have hsumOff :
      sphereAvg24 (fun x : ℝ²⁴ => ∑ i : Fin 24, (Finset.univ.erase i).sum fun j =>
        (x i) ^ 2 * (x j) ^ 2) =
        ∑ i : Fin 24, (Finset.univ.erase i).sum fun j =>
          sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2) := by
    have hinner :
        ∀ i : Fin 24,
          sphereAvg24 (fun x : ℝ²⁴ => (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2) =
            (Finset.univ.erase i).sum fun j =>
              sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2) := by
      intro i
      simpa using!
        (sphereAvg24_finset_sum (s := (Finset.univ.erase i))
          (f := fun j : Fin 24 => fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2)
          (fun j _ => integrable_coord_pow_mul_coord_pow i j 2 2))
    -- outer sum
    have :
        sphereAvg24 (fun x : ℝ²⁴ =>
            ∑ i : Fin 24, (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2) =
          ∑ i : Fin 24,
            sphereAvg24 (fun x : ℝ²⁴ =>
              (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2) := by
      -- apply `sphereAvg24_finset_sum` on `Finset.univ` (as a `Finset`)
      simpa using!
        (sphereAvg24_finset_sum (s := (Finset.univ : Finset (Fin 24)))
          (f := fun i : Fin 24 =>
            fun x : ℝ²⁴ => (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2)
          (fun i _ => by
            -- integrability of the inner sum
            simpa using!
              (MeasureTheory.integrable_finset_sum (s := (Finset.univ.erase i))
                (f := fun j : Fin 24 => fun x : S23 => (x.1 i : ℝ) ^ 2 * (x.1 j : ℝ) ^ 2)
                (fun j _ => integrable_coord_pow_mul_coord_pow i j 2 2))))
    -- rewrite each summand using `hinner`
    calc
      sphereAvg24 (fun x : ℝ²⁴ =>
          ∑ i : Fin 24, (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2) =
            ∑ i : Fin 24,
              sphereAvg24 (fun x : ℝ²⁴ =>
                (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2) := this
      _ = ∑ i : Fin 24, (Finset.univ.erase i).sum fun j =>
            sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simpa using! hinner i
  have hdiag :
      (∑ i : Fin 24, sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 4)) =
        (24 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) := by
    have : ∀ i : Fin 24,
        sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 4) =
          sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) := by
      intro i
      simpa using! (sphereAvg24_coord_pow_eq 4 i (0 : Fin 24))
    simp [this]
  have hoff :
      (∑ i : Fin 24, (Finset.univ.erase i).sum fun j =>
          sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2)) =
        (24 : ℝ) * (23 : ℝ) * B := by
    have hpair :
        ∀ i : Fin 24, ∀ j : Fin 24, i ≠ j →
          sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2) = B :=
      fun i j a => sphereAvg24_coord_sq_mul_coord_sq_eq_of_ne i j a
    have : ∀ i : Fin 24,
        ((Finset.univ.erase i).sum fun j =>
            sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2)) = (23 : ℝ) * B := by
      intro i
      have hterm : ∀ j ∈ (Finset.univ.erase i),
          sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2) = B := by
        intro j hj
        have hij : i ≠ j := by
          have : j ≠ i := by simpa [Finset.mem_erase] using! hj
          simpa [ne_comm] using! this
        simpa using! hpair i j hij
      -- sum of a constant over `erase i`
      calc
        (Finset.univ.erase i).sum (fun j : Fin 24 =>
              sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2))
            = (Finset.univ.erase i).sum (fun _ : Fin 24 => (B : ℝ)) := by
                refine Finset.sum_congr rfl (fun j hj => ?_)
                simpa using! hterm j hj
        _ = (23 : ℝ) * B := by
              norm_num
    simp [this, B, mul_assoc]
  have hEq :
      (1 : ℝ) =
        (24 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) +
          (24 : ℝ) * (23 : ℝ) * B := by
    calc
      (1 : ℝ) = sphereAvg24 (fun x : ℝ²⁴ => (∑ i : Fin 24, (x i) ^ 2) ^ 2) := by simp [hone]
      _ = sphereAvg24 (fun x : ℝ²⁴ => (∑ i : Fin 24, (x i) ^ 4) +
            (∑ i : Fin 24, (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2)) := by
            simp [hexpand]
      _ = sphereAvg24 (fun x : ℝ²⁴ => ∑ i : Fin 24, (x i) ^ 4) +
            sphereAvg24 (fun x : ℝ²⁴ =>
              ∑ i : Fin 24, (Finset.univ.erase i).sum fun j => (x i) ^ 2 * (x j) ^ 2) :=
            hlin
      _ = (∑ i : Fin 24, sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 4)) +
            (∑ i : Fin 24, (Finset.univ.erase i).sum fun j =>
              sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2 * (x j) ^ 2)) := by
            rw [hsum4, hsumOff]
            -- goal is now definitional
      _ =
          (24 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) +
            (24 : ℝ) * (23 : ℝ) * B := by
            -- substitute the diagonal/off-diagonal sums; avoid rewriting `erase`-sums by `simp`
            rw [hdiag, hoff]
            -- goal is now definitional
  have : B = (1 / 624 : ℝ) := by nlinarith [hEq, hA]
  simp [B, this]

lemma sphereAvg24_coord0_pow_four_mul_coord1_sq_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2) = (1 / 5824 : ℝ) := by
  have hA4 : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) = (1 / 208 : ℝ) :=
    sphereAvg24_coord0_pow_four_eq (h := h) (u := u) hu
  have hA6 : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) = (5 / 5824 : ℝ) :=
    sphereAvg24_coord0_pow_six_eq (h := h) (u := u) hu
  -- On the sphere: `x0^4 = x0^4 * ∑ x_i^2`.
  have hcongr :
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * ∑ i : Fin 24, (x i) ^ 2) := by
    refine (sphereAvg24_congr (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4)
      (g := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * ∑ i : Fin 24, (x i) ^ 2) ?_)
    intro x
    have hx : (∑ i : Fin 24, (x.1 i) ^ 2) = (1 : ℝ) := by
      -- as in `sphereAvg24_sum_coord_sq_sq_eq_one`
      have hxmem := x.2
      dsimp [S23] at hxmem
      have hx' : ‖(x : ℝ²⁴)‖ = (1 : ℝ) := mem_sphere_zero_iff_norm.mp hxmem
      have : (∑ i : Fin 24, (x.1 i) ^ 2) = ‖(x : ℝ²⁴)‖ ^ 2 := by
        exact sum_sq_eq_norm_sq ↑x
      simpa [this, hx', pow_two]
    simp [hx]
  -- Expand the product and use symmetry for the `i ≠ 0` terms.
  have hsplit :
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * ∑ i : Fin 24, (x i) ^ 2) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) +
          (23 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2)
  := by
    -- rewrite as `x0^6 + ∑_{i≠0} x0^4 * xi^2` and collapse the sum
    let s0 : Finset (Fin 24) := Finset.univ.erase (0 : Fin 24)
    have hpoint (x : ℝ²⁴) :
          (x (0 : Fin 24)) ^ 4 * (∑ i : Fin 24, (x i) ^ 2) =
            (x (0 : Fin 24)) ^ 6 + s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2) := by
        have hsplit :
            (∑ i : Fin 24, (x i) ^ 2) =
              (x (0 : Fin 24)) ^ 2 + s0.sum (fun i : Fin 24 => (x i) ^ 2) := by
          rfl
        have hx0 : (x (0 : Fin 24)) ^ 4 * (x (0 : Fin 24)) ^ 2 = (x (0 : Fin 24)) ^ 6 := by
          ring_nf
        have hmul :
            (x (0 : Fin 24)) ^ 4 * s0.sum (fun i : Fin 24 => (x i) ^ 2) =
              s0.sum (fun i : Fin 24 =>
                (x (0 : Fin 24)) ^ 4 * (x i) ^ 2) :=
          Finset.mul_sum (s := s0) (a := (x (0 : Fin 24)) ^ 4) (f := fun i : Fin 24 => (x i) ^ 2)
        calc
          (x (0 : Fin 24)) ^ 4 * (∑ i : Fin 24, (x i) ^ 2)
              =
                (x (0 : Fin 24)) ^ 4 *
                  ((x (0 : Fin 24)) ^ 2 + s0.sum (fun i : Fin 24 => (x i) ^ 2)) := by
                  simp [hsplit]
          _ = (x (0 : Fin 24)) ^ 4 * (x (0 : Fin 24)) ^ 2 +
                (x (0 : Fin 24)) ^ 4 * s0.sum (fun i : Fin 24 => (x i) ^ 2) := by
                  simp [mul_add]
          _ =
              (x (0 : Fin 24)) ^ 6 +
                s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2) := by
                  rw [hx0, hmul]
    have hcongr' :
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * ∑ i : Fin 24, (x i) ^ 2) =
          sphereAvg24 (fun x : ℝ²⁴ =>
            (x (0 : Fin 24)) ^ 6 +
              s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2)) := by
      exact sphereAvg24_congr fun x => hpoint ↑x
    have hInt6 : Integrable (fun x : S23 => (x.1 (0 : Fin 24) : ℝ) ^ 6) sphereMeasure24 :=
      integrable_coord_pow (0 : Fin 24) 6
    have hsum :
        sphereAvg24 (fun x : ℝ²⁴ =>
            s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2)) =
          s0.sum (fun i : Fin 24 =>
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2)) := by
      simpa [s0] using!
        (sphereAvg24_finset_sum (s := (Finset.univ.erase (0 : Fin 24)))
          (f := fun i : Fin 24 => fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2)
          (fun i _ => integrable_coord_pow_mul_coord_pow (0 : Fin 24) i 4 2))
    have hsymm :
        s0.sum (fun i : Fin 24 =>
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2)) =
          (23 : ℝ) *
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2) := by
      have hterm :
          ∀ i ∈ s0,
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2) =
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2) := by
        intro i hi
        have hi0 : i ≠ (0 : Fin 24) := by
          simpa [s0, Finset.mem_erase] using! hi
        simpa using! sphereAvg24_coord0_pow_four_mul_coord_sq_eq (i := i) hi0
      -- sum of a constant over `s0`
      have hcard : s0.card = 23 := by
        simp [s0]
      calc
        s0.sum (fun i : Fin 24 =>
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2))
            = s0.sum (fun _ : Fin 24 =>
                sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2)) := by
                refine Finset.sum_congr rfl (fun i hi => ?_)
                simpa using! hterm i hi
        _ =
            (23 : ℝ) *
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2) := by
                simp [Finset.sum_const, hcard, nsmul_eq_mul]
    have hlin :
        sphereAvg24 (fun x : ℝ²⁴ =>
            (x (0 : Fin 24)) ^ 6 + s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2)) =
          sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) +
            sphereAvg24 (fun x : ℝ²⁴ =>
              s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2)) := by
      have hIntSum :
          Integrable
            (fun x : S23 =>
              s0.sum (fun i : Fin 24 => (x.1 (0 : Fin 24) : ℝ) ^ 4 * (x.1 i : ℝ) ^ 2))
            sphereMeasure24 := by
        simpa [s0] using!
          (MeasureTheory.integrable_finset_sum (s := (Finset.univ.erase (0 : Fin 24)))
            (f := fun i : Fin 24 =>
              fun x : S23 => (x.1 (0 : Fin 24) : ℝ) ^ 4 * (x.1 i : ℝ) ^ 2)
            (fun i _ => integrable_coord_pow_mul_coord_pow (0 : Fin 24) i 4 2))
      exact sphereAvg24_add (fun x => x.ofLp 0 ^ 6)
          (fun x => ∑ i ∈ s0, x.ofLp 0 ^ 4 * x.ofLp i ^ 2)
          hInt6 hIntSum
    -- finish
    calc
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * ∑ i : Fin 24, (x i) ^ 2)
          = sphereAvg24 (fun x : ℝ²⁴ =>
              (x (0 : Fin 24)) ^ 6 +
                s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2)) := hcongr'
      _ = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) +
            sphereAvg24 (fun x : ℝ²⁴ =>
              s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2)) := hlin
      _ = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) +
            s0.sum (fun i : Fin 24 =>
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x i) ^ 2)) := by
            simp [hsum]
      _ = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) +
            (23 : ℝ) *
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2) := by
            simp [hsymm]
  have hEq :
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) +
          (23 : ℝ) *
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2) := by
    calc
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4)
          = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * ∑ i : Fin 24, (x i) ^ 2) := hcongr
      _ = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) +
            (23 : ℝ) *
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2) := hsplit
  nlinarith [hEq, hA4, hA6]

/-!
We next compute `E[x0^6 x1^2]` and `E[x0^4 x1^4]` using the 8th moment.
-/

lemma sphereAvg24_coord0_pow_six_mul_coord1_sq_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) = (1 / 34944 : ℝ) := by
  have hA6 : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) = (5 / 5824 : ℝ) :=
    sphereAvg24_coord0_pow_six_eq (h := h) (u := u) hu
  have hA8 : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) = (1 / 4992 : ℝ) :=
    sphereAvg24_coord0_pow_eight_eq (h := h) (u := u) hu
  let s0 : Finset (Fin 24) := Finset.univ.erase (0 : Fin 24)
  -- Pointwise expansion.
  have hpoint (x : ℝ²⁴) :
      (x (0 : Fin 24)) ^ 6 * (∑ i : Fin 24, (x i) ^ 2) =
        (x (0 : Fin 24)) ^ 8 + s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2) := by
    have hsplit :
        (∑ i : Fin 24, (x i) ^ 2) =
          (x (0 : Fin 24)) ^ 2 + s0.sum (fun i : Fin 24 => (x i) ^ 2) := by
      rfl
    have hx0 : (x (0 : Fin 24)) ^ 6 * (x (0 : Fin 24)) ^ 2 = (x (0 : Fin 24)) ^ 8 := by
      ring_nf
    have hmul :
        (x (0 : Fin 24)) ^ 6 * s0.sum (fun i : Fin 24 => (x i) ^ 2) =
          s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2) :=
      Finset.mul_sum s0 (fun i => x.ofLp i ^ 2) (x.ofLp 0 ^ 6)
    calc
      (x (0 : Fin 24)) ^ 6 * (∑ i : Fin 24, (x i) ^ 2)
          =
            (x (0 : Fin 24)) ^ 6 *
              ((x (0 : Fin 24)) ^ 2 + s0.sum (fun i : Fin 24 => (x i) ^ 2)) := by
              simp [hsplit]
      _ = (x (0 : Fin 24)) ^ 6 * (x (0 : Fin 24)) ^ 2 +
            (x (0 : Fin 24)) ^ 6 * s0.sum (fun i : Fin 24 => (x i) ^ 2) := by
              simp [mul_add]
      _ = (x (0 : Fin 24)) ^ 8 + s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2) := by
              rw [hx0, hmul]
  -- On the sphere: `∑ x_i^2 = 1`.
  have hcongr :
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * ∑ i : Fin 24, (x i) ^ 2) := by
    refine (sphereAvg24_congr (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6)
      (g := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * ∑ i : Fin 24, (x i) ^ 2) ?_)
    intro x
    have hx : (∑ i : Fin 24, (x.1 i) ^ 2) = (1 : ℝ) := by
      have hxmem := x.2
      dsimp [S23] at hxmem
      have hx' : ‖(x : ℝ²⁴)‖ = (1 : ℝ) := mem_sphere_zero_iff_norm.mp hxmem
      have : (∑ i : Fin 24, (x.1 i) ^ 2) = ‖(x : ℝ²⁴)‖ ^ 2 := by
        exact sum_sq_eq_norm_sq ↑x
      simpa [this, hx', pow_two]
    simp [hx]
  have hcongr' :
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * ∑ i : Fin 24, (x i) ^ 2) =
        sphereAvg24 (fun x : ℝ²⁴ =>
          (x (0 : Fin 24)) ^ 8 + s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2)) := by
    exact sphereAvg24_congr fun x => hpoint ↑x
  have hInt8 : Integrable (fun x : S23 => (x.1 (0 : Fin 24) : ℝ) ^ 8) sphereMeasure24 :=
    integrable_coord_pow (0 : Fin 24) 8
  have hsum :
      sphereAvg24 (fun x : ℝ²⁴ =>
          s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2)) =
        s0.sum (fun i : Fin 24 =>
          sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2)) := by
    simpa [s0] using!
      (sphereAvg24_finset_sum (s := (Finset.univ.erase (0 : Fin 24)))
        (f := fun i : Fin 24 => fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2)
        (fun i _ => integrable_coord_pow_mul_coord_pow (0 : Fin 24) i 6 2))
  have hsymm :
      s0.sum (fun i : Fin 24 =>
          sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2)) =
        (23 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
    have hterm :
        ∀ i ∈ s0,
          sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2) =
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
      intro i hi
      have hi0 : i ≠ (0 : Fin 24) := by
        simpa [s0, Finset.mem_erase] using! hi
      simpa using! sphereAvg24_coord0_pow_six_mul_coord_sq_eq (i := i) hi0
    have hcard : s0.card = 23 := by
      simp [s0]
    calc
      s0.sum (fun i : Fin 24 =>
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2))
          = s0.sum (fun _ : Fin 24 =>
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2)) := by
              refine Finset.sum_congr rfl (fun i hi => ?_)
              simpa using! hterm i hi
      _ = (23 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
            simp [Finset.sum_const, hcard, nsmul_eq_mul]
  have hlin :
      sphereAvg24 (fun x : ℝ²⁴ =>
          (x (0 : Fin 24)) ^ 8 + s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2)) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) +
          sphereAvg24 (fun x : ℝ²⁴ =>
            s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2)) := by
    have hIntSum :
        Integrable
          (fun x : S23 =>
            s0.sum (fun i : Fin 24 => (x.1 (0 : Fin 24) : ℝ) ^ 6 * (x.1 i : ℝ) ^ 2))
          sphereMeasure24 := by
      simpa [s0] using!
        (MeasureTheory.integrable_finset_sum (s := (Finset.univ.erase (0 : Fin 24)))
          (f := fun i : Fin 24 =>
            fun x : S23 => (x.1 (0 : Fin 24) : ℝ) ^ 6 * (x.1 i : ℝ) ^ 2)
          (fun i _ => integrable_coord_pow_mul_coord_pow (0 : Fin 24) i 6 2))
    exact sphereAvg24_add (fun x => x.ofLp 0 ^ 8)
        (fun x => ∑ i ∈ s0, x.ofLp 0 ^ 6 * x.ofLp i ^ 2) hInt8 hIntSum
  have hEq :
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) +
          (23 : ℝ) *
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
    calc
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6)
          = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * ∑ i : Fin 24, (x i) ^ 2) := hcongr
      _ = sphereAvg24 (fun x : ℝ²⁴ =>
            (x (0 : Fin 24)) ^ 8 +
              s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2)) := hcongr'
      _ = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) +
            sphereAvg24 (fun x : ℝ²⁴ =>
              s0.sum (fun i : Fin 24 => (x (0 : Fin 24)) ^ 6 * (x i) ^ 2)) := hlin
      _ = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) +
            (23 : ℝ) *
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
            simp [hsum, hsymm]
  nlinarith [hEq, hA6, hA8]

lemma sphereAvg24_coord0_pow_four_mul_coord1_pow_four_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 4) =
      (1 / 58240 : ℝ) := by
  have hA8 : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) = (1 / 4992 : ℝ) :=
    sphereAvg24_coord0_pow_eight_eq (h := h) (u := u) hu
  have hA62 :
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) =
        (1 / 34944 : ℝ) :=
    sphereAvg24_coord0_pow_six_mul_coord1_sq_eq (h := h) (u := u) hu
  -- Evaluate `E[(x0+x1)^8]` using norm-scaling of the 8th inner moment.
  let w : ℝ²⁴ :=
    EuclideanSpace.single (0 : Fin 24) (1 : ℝ) + EuclideanSpace.single (1 : Fin 24) (1 : ℝ)
  have horth :
      (⟪EuclideanSpace.single (0 : Fin 24) (1 : ℝ),
          EuclideanSpace.single (1 : Fin 24) (1 : ℝ)⟫ : ℝ) = 0 := by
    simp [EuclideanSpace.inner_single_left]
  have hw2' : ‖w‖ * ‖w‖ = (2 : ℝ) := by
    have h' :
        ‖w‖ * ‖w‖ = (1 : ℝ) + 1 := by
      simpa [w] using!
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (x := EuclideanSpace.single (0 : Fin 24) (1 : ℝ))
          (y := EuclideanSpace.single (1 : Fin 24) (1 : ℝ)) horth)
    nlinarith
  have hwne : ‖w‖ ≠ (0 : ℝ) := by
    intro h0
    have : (2 : ℝ) = (0 : ℝ) := by
      simpa [h0] using! hw2'.symm
    exact two_ne_zero this
  have hw2 : ‖w‖ ^ 2 = (2 : ℝ) := by
    simpa [pow_two] using! hw2'
  have hwNorm : ‖w‖ ^ 8 = (16 : ℝ) := by
    calc
      ‖w‖ ^ 8 = (‖w‖ ^ 2) ^ 4 := by
        simpa using! (pow_mul ‖w‖ 2 4)
      _ = (2 : ℝ) ^ 4 := by simp [hw2]
      _ = (16 : ℝ) := by norm_num
  let wunit : ℝ²⁴ := (‖w‖)⁻¹ • w
  have hunit : ‖wunit‖ = (1 : ℝ) := by
    have hnonneg : 0 ≤ (‖w‖ : ℝ)⁻¹ := inv_nonneg.2 (norm_nonneg w)
    calc
      ‖wunit‖ = ‖(‖w‖ : ℝ)⁻¹‖ * ‖w‖ := by simp [wunit, norm_smul]
      _ = (‖w‖ : ℝ)⁻¹ * ‖w‖ := by simp [Real.norm_of_nonneg hnonneg]
      _ = (1 : ℝ) := by simp [hwne]
  have hEw :
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, w⟫ : ℝ) ^ 8) =
        (‖w‖ ^ 8) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) := by
    -- `E[⟪x,w⟫^8] = ‖w‖^8 * E[⟪x,w/‖w‖⟫^8] = ‖w‖^8 * E[x0^8]`.
    have hcoord : sphereAvg24 (fun x : ℝ²⁴ => (⟪wunit, x⟫ : ℝ) ^ 8) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) := by
      -- use `sphereAvg24_coord0_pow_eq_inner_pow` for the unit vector `wunit`
      have := sphereAvg24_coord0_pow_eq_inner_pow (u := wunit) hunit 8
      simpa [real_inner_comm] using! this.symm
    have hcoord' : sphereAvg24 (fun x : ℝ²⁴ => (⟪x, wunit⟫ : ℝ) ^ 8) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) := by
      simpa [real_inner_comm] using! hcoord
    have hscale :
        (fun x : ℝ²⁴ => (⟪x, w⟫ : ℝ) ^ 8) =
          (fun x : ℝ²⁴ => (‖w‖ ^ 8) * (⟪x, wunit⟫ : ℝ) ^ 8) := by
      funext x
      have : (⟪x, w⟫ : ℝ) = ‖w‖ * (⟪x, wunit⟫ : ℝ) := by
        -- `w = ‖w‖ • wunit`
        have : (‖w‖ : ℝ) • wunit = w := by
          simp [wunit, smul_smul, hwne]
        calc
          (⟪x, w⟫ : ℝ) = ⟪x, (‖w‖ : ℝ) • wunit⟫ := by simp [this]
          _ = ‖w‖ * (⟪x, wunit⟫ : ℝ) := by
              simp [inner_smul_right]
      simp [this, mul_pow]
    calc
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, w⟫ : ℝ) ^ 8)
          = sphereAvg24 (fun x : ℝ²⁴ => (‖w‖ ^ 8) * (⟪x, wunit⟫ : ℝ) ^ 8) := by
              simp [hscale]
      _ = (‖w‖ ^ 8) * sphereAvg24 (fun x : ℝ²⁴ => (⟪x, wunit⟫ : ℝ) ^ 8) := by
              simpa using!
                (sphereAvg24_smul (a := (‖w‖ ^ 8)) (f := fun x : ℝ²⁴ => (⟪x, wunit⟫ : ℝ) ^ 8))
      _ = (‖w‖ ^ 8) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) := by
              rw [hcoord']
  have hEw' :
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 8) =
        (16 : ℝ) * (1 / 4992 : ℝ) := by
    have : (fun x : ℝ²⁴ => (⟪x, w⟫ : ℝ) ^ 8) =
        fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 8 := by
      funext x
      have hinner : (⟪x, w⟫ : ℝ) = x (0 : Fin 24) + x (1 : Fin 24) := by
        simp [w, inner_add_right, EuclideanSpace.inner_single_right]
      simp [hinner]
    -- substitute `hA8` and `hwNorm`
    simpa [this, hwNorm, hA8, mul_assoc] using! hEw
  -- Binomial expansion; odd terms vanish by reflection in coordinate `0`.
  have hodd (k : ℕ) (hk : Odd k) :
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k)) = 0 := by
    have huv :
        (⟪EuclideanSpace.single (0 : Fin 24) (1 : ℝ),
            EuclideanSpace.single (1 : Fin 24) (1 : ℝ)⟫ : ℝ) = 0 := by
      simp [EuclideanSpace.inner_single_left]
    have := CommonNeighbors44Aux.sphereAvg24_inner_pow_mul_inner_pow_eq_zero_of_odd_left
      (u := EuclideanSpace.single (0 : Fin 24) (1 : ℝ))
      (v := EuclideanSpace.single (1 : Fin 24) (1 : ℝ))
      (huv := huv) (i := k) (j := (8 - k)) hk
    simpa [EuclideanSpace.inner_single_right, mul_assoc, mul_left_comm, mul_comm] using! this
  -- Express `E[(x0+x1)^8]` as a finite sum and simplify.
  let F : ℝ :=
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 4)
  have hbinom :
      sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 8) =
        (2 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) +
          (56 : ℝ) *
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) +
            (70 : ℝ) * F := by
    -- use the binomial formula and eliminate odd `k`
    let s : Finset ℕ := Finset.range 9
    have hint :
        ∀ k ∈ s,
          Integrable
            (fun x : S23 =>
              (Nat.choose 8 k : ℝ) * (x.1 (0 : Fin 24) : ℝ) ^ k * (x.1 (1 : Fin 24) : ℝ) ^ (8 - k))
            sphereMeasure24 := by
      intro k hk
      -- bounded monomial
      have :
          Integrable
            (fun x : S23 =>
              (x.1 (0 : Fin 24) : ℝ) ^ k * (x.1 (1 : Fin 24) : ℝ) ^ (8 - k))
            sphereMeasure24 :=
        integrable_coord_pow_mul_coord_pow (0 : Fin 24) (1 : Fin 24) k (8 - k)
      simpa [mul_assoc] using! this.const_mul (Nat.choose 8 k : ℝ)
    have hsum :
        sphereAvg24 (fun x : ℝ²⁴ =>
            s.sum (fun k =>
              (Nat.choose 8 k : ℝ) * (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k))) =
          s.sum (fun k =>
            sphereAvg24 (fun x : ℝ²⁴ =>
              (Nat.choose 8 k : ℝ) * (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k))) := by
      simpa using! (sphereAvg24_finset_sum (s := s)
        (f := fun k : ℕ => fun x : ℝ²⁴ =>
          (Nat.choose 8 k : ℝ) * (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k)) hint)
    have hpow :
        (fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 8) =
          (fun x : ℝ²⁴ =>
            s.sum (fun k =>
              (Nat.choose 8 k : ℝ) * (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k))) := by
      funext x
      -- `add_pow` gives the binomial expansion
      simpa [s, mul_assoc, mul_left_comm, mul_comm] using!
        add_pow (x (0 : Fin 24)) (x (1 : Fin 24)) 8
    have hsum' :
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 8) =
          s.sum (fun k =>
            sphereAvg24 (fun x : ℝ²⁴ =>
              (Nat.choose 8 k : ℝ) * (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k))) := by
      simpa [hpow] using! hsum
    -- Evaluate each `k` term.
    have hterm_even :
        ∀ k : ℕ, k ∈ s → Even k →
          sphereAvg24 (fun x : ℝ²⁴ =>
            (Nat.choose 8 k : ℝ) * (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k)) =
            (Nat.choose 8 k : ℝ) *
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k)) := by
      intro k hk he
      simpa [mul_assoc] using! (sphereAvg24_smul (a := (Nat.choose 8 k : ℝ))
        (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k)))
    have hterm_odd :
        ∀ k : ℕ, k ∈ s → Odd k →
          sphereAvg24 (fun x : ℝ²⁴ =>
            (Nat.choose 8 k : ℝ) * (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k)) = 0 := by
      intro k hk hkodd
      have : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k)) = 0 :=
        hodd k hkodd
      -- pull out the scalar
      simpa [mul_assoc, this] using! (sphereAvg24_smul (a := (Nat.choose 8 k : ℝ))
        (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k)))
    -- Reduce the sum to `k=0,2,4,6,8`.
    have hswap :
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 6) =
          sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
      have := sphereAvg24_comp_linearIsometryEquiv
        (e := LinearIsometryEquiv.piLpCongrLeft (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (E := ℝ)
          (Equiv.swap (0 : Fin 24) (1 : Fin 24)))
        (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2)
      simpa [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', mul_assoc, mul_left_comm,
        mul_comm] using! this
    have h8symm :
        sphereAvg24 (fun x : ℝ²⁴ => (x (1 : Fin 24)) ^ 8) =
          sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) := by
      simpa using! (sphereAvg24_coord_pow_eq 8 (1 : Fin 24) (0 : Fin 24))
    -- Now compute by simp on the finite range sum.
    -- `simp` will expand the 9-term sum; we then use `hterm_odd` and rewrite the even terms.
    -- Finally, collect coefficients with `ring`.
    have :
        (s.sum fun k =>
            sphereAvg24 (fun x : ℝ²⁴ =>
              (Nat.choose 8 k : ℝ) * (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k)))
          =
          (2 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) +
            (56 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) +
              (70 : ℝ) * F := by
      -- Expand `range 9` and simplify term-by-term:
      -- odd indices vanish, and even indices reduce to the three moments `A8, A62, F`.
      let f : ℕ → ℝ :=
        fun k =>
          sphereAvg24 (fun x : ℝ²⁴ =>
            (Nat.choose 8 k : ℝ) * (x (0 : Fin 24)) ^ k * (x (1 : Fin 24)) ^ (8 - k))
      have hsum_expand :
          s.sum f =
            f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
        simp [s, f, Finset.sum_range_succ]
      have hchoose0 : (Nat.choose 8 0 : ℝ) = (1 : ℝ) := by
        exact_mod_cast (show Nat.choose 8 0 = 1 by decide)
      have hchoose2 : (Nat.choose 8 2 : ℝ) = (28 : ℝ) := by
        exact_mod_cast (show Nat.choose 8 2 = 28 by decide)
      have hchoose4 : (Nat.choose 8 4 : ℝ) = (70 : ℝ) := by
        exact_mod_cast (show Nat.choose 8 4 = 70 by decide)
      have hchoose6 : (Nat.choose 8 6 : ℝ) = (28 : ℝ) := by
        exact_mod_cast (show Nat.choose 8 6 = 28 by decide)
      have hchoose8 : (Nat.choose 8 8 : ℝ) = (1 : ℝ) := by
        exact_mod_cast (show Nat.choose 8 8 = 1 by decide)
      have hf1 : f 1 = 0 := by
        have := hterm_odd 1 (by simp [s]) (by decide : Odd 1)
        simpa [f] using! this
      have hf3 : f 3 = 0 := by
        have := hterm_odd 3 (by simp [s]) (by decide : Odd 3)
        simpa [f] using! this
      have hf5 : f 5 = 0 := by
        have := hterm_odd 5 (by simp [s]) (by decide : Odd 5)
        simpa [f] using! this
      have hf7 : f 7 = 0 := by
        have := hterm_odd 7 (by simp [s]) (by decide : Odd 7)
        simpa [f] using! this
      have hf0 :
          f 0 = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) := by
        have h0 := hterm_even 0 (by simp [s]) (by decide : Even 0)
        -- `k=0` term is `E[x1^8]`, then use coordinate symmetry.
        calc
            f 0
                = (Nat.choose 8 0 : ℝ) *
                    sphereAvg24 (fun x : ℝ²⁴ =>
                      (x (0 : Fin 24)) ^ 0 * (x (1 : Fin 24)) ^ (8 - 0)) := by
                      dsimp [f]
                      exact h0
          _ = sphereAvg24 (fun x : ℝ²⁴ => (x (1 : Fin 24)) ^ 8) := by
                simp
          _ = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) := by
                simpa using! h8symm
      have hf8 :
          f 8 = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) := by
        have h8 := hterm_even 8 (by simp [s]) (by decide : Even 8)
        calc
            f 8
                = (Nat.choose 8 8 : ℝ) *
                    sphereAvg24 (fun x : ℝ²⁴ =>
                      (x (0 : Fin 24)) ^ 8 * (x (1 : Fin 24)) ^ (8 - 8)) := by
                      dsimp [f]
                      exact h8
          _ = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) := by
                simp
      have hf2 :
          f 2 =
            (28 : ℝ) *
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
        have h2 := hterm_even 2 (by simp [s]) (by decide : Even 2)
        calc
          f 2
              = (Nat.choose 8 2 : ℝ) *
                  sphereAvg24 (fun x : ℝ²⁴ =>
                    (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ (8 - 2)) := by
                    simpa [f, mul_assoc] using! h2
          _ = (Nat.choose 8 2 : ℝ) *
                  sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 6) := by
                simp
          _ = (Nat.choose 8 2 : ℝ) *
                  sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
                simp [hswap]
          _ =
              (28 : ℝ) *
                sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
                simp [hchoose2]
      have hf6 :
          f 6 =
            (28 : ℝ) *
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) := by
        have h6 := hterm_even 6 (by simp [s]) (by decide : Even 6)
        assumption
      have hf4 :
          f 4 = (70 : ℝ) * F := by
        have h4 := hterm_even 4 (by simp [s]) (by decide : Even 4)
        assumption
      -- Combine the nine terms.
      calc
        s.sum f
            = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := hsum_expand
        _ =
            (2 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 8) +
              (56 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 6 * (x (1 : Fin 24)) ^ 2) +
                (70 : ℝ) * F := by
              -- use the computed `hf*` identities and collect coefficients
              simp [hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8]
              ring
    simpa [hsum'] using! this
  -- Solve for `F` using the explicit value `E[(x0+x1)^8] = 16 * E[x0^8]`.
  have hE :
      (16 : ℝ) * (1 / 4992 : ℝ) =
        (2 : ℝ) * (1 / 4992 : ℝ) + (56 : ℝ) * (1 / 34944 : ℝ) + (70 : ℝ) * F := by
    -- replace each moment by its known value and use `hbinom`.
    simpa [F, hA8, hA62, hbinom] using! hEw'.symm
  -- compute
  have hF : F = (1 / 58240 : ℝ) := by nlinarith [hE]
  simpa [F] using! hF

/-!
## Mixed moments for an orthogonal unit pair

We transport the coordinate computations to any orthogonal unit pair using an orthonormal basis.
-/

lemma exists_orthonormalBasis_uv {u v : ℝ²⁴} (hu1 : ‖u‖ = (1 : ℝ)) (hv1 : ‖v‖ = (1 : ℝ))
    (huv : (⟪u, v⟫ : ℝ) = 0) :
    ∃ b : OrthonormalBasis (Fin 24) ℝ ℝ²⁴, b (0 : Fin 24) = u ∧ b (1 : Fin 24) = v := by
  let s : Set (Fin 24) := Set.insert (0 : Fin 24) ({(1 : Fin 24)} : Set (Fin 24))
  let vf : Fin 24 → ℝ²⁴ :=
    fun i => if i = (0 : Fin 24) then u else if i = (1 : Fin 24) then v else 0
  have hon : Orthonormal ℝ (s.restrict vf) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = (0 : Fin 24) ∨ i = (1 : Fin 24) := by
      simpa (config := { contextual := false })
        [s, Set.mem_insert_iff, Set.mem_singleton_iff] using! hi
    have hj' : j = (0 : Fin 24) ∨ j = (1 : Fin 24) := by
      simpa (config := { contextual := false })
        [s, Set.mem_insert_iff, Set.mem_singleton_iff] using! hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · simp [Set.restrict, vf, hu1]
    · simp [Set.restrict, vf, huv]
    · have : (⟪v, u⟫ : ℝ) = 0 := by simpa [real_inner_comm] using! huv
      simp [Set.restrict, vf, this]
    · simp [Set.restrict, vf, hv1]
  have hcard : Module.finrank ℝ ℝ²⁴ = Fintype.card (Fin 24) := by
    exact finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 24)
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq (E := ℝ²⁴) (𝕜 := ℝ) (ι := Fin 24)
      hcard (v := vf) (s := s) hon
  have hs0 : (0 : Fin 24) ∈ s := by
    dsimp [s]
    exact (Set.mem_insert_iff).2 (Or.inl rfl)
  have hs1 : (1 : Fin 24) ∈ s := by
    dsimp [s]
    exact (Set.mem_insert_iff).2 (Or.inr ((Set.mem_singleton_iff).2 rfl))
  refine ⟨b, ?_, ?_⟩
  · simpa [s, vf] using! hb (0 : Fin 24) hs0
  · simpa [s, vf] using! hb (1 : Fin 24) hs1

/-- Mixed moment `sphereAvg24 ((⟪x,u⟫)^2 * (⟪x,v⟫)^2)` for an orthogonal pair `u ⟂ v`. -/
public theorem sphereAvg24_inner_sq_mul_inner_sq_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ C)
    (huv : (⟪u, v⟫ : ℝ) = 0) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 2 * (⟪x, v⟫ : ℝ) ^ 2) = (1 / 624 : ℝ) := by
  have hu1 : ‖u‖ = (1 : ℝ) := h.code.norm_one hu
  have hv1 : ‖v‖ = (1 : ℝ) := h.code.norm_one hv
  obtain ⟨b, hb0, hb1⟩ := exists_orthonormalBasis_uv (u := u) (v := v) hu1 hv1 huv
  let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := b.repr
  have hcoord0 : ∀ x : ℝ²⁴, (e x) (0 : Fin 24) = (⟪u, x⟫ : ℝ) := by
    intro x
    simpa [e, hb0] using! (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := (0 : Fin 24)))
  have hcoord1 : ∀ x : ℝ²⁴, (e x) (1 : Fin 24) = (⟪v, x⟫ : ℝ) := by
    intro x
    simpa [e, hb1] using! (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := (1 : Fin 24)))
  have hinv :=
    sphereAvg24_comp_linearIsometryEquiv (e := e)
      (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2)
  have hcoord :
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 2 * (⟪x, v⟫ : ℝ) ^ 2) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) := by
    -- rewrite the LHS as `f ∘ e`
    have : sphereAvg24 (fun x : ℝ²⁴ => ((e x) (0 : Fin 24)) ^ 2 * ((e x) (1 : Fin 24)) ^ 2) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) := by
      simp [hinv]
    -- now rewrite the integrand
    simpa [hcoord0, hcoord1, real_inner_comm] using! this
  have hB :=
    sphereAvg24_coord_sq_mul_coord_sq_eq (h := h) (u := u) hu
  simpa [hcoord] using! hB

/-- Mixed moment `sphereAvg24 ((⟪x,u⟫)^4 * (⟪x,v⟫)^2)` for an orthogonal pair `u ⟂ v`. -/
public theorem sphereAvg24_inner_pow_four_mul_inner_sq_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ C)
    (huv : (⟪u, v⟫ : ℝ) = 0) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4 * (⟪x, v⟫ : ℝ) ^ 2) = (1 / 5824 : ℝ) := by
  have hu1 : ‖u‖ = (1 : ℝ) := h.code.norm_one hu
  have hv1 : ‖v‖ = (1 : ℝ) := h.code.norm_one hv
  obtain ⟨b, hb0, hb1⟩ := exists_orthonormalBasis_uv (u := u) (v := v) hu1 hv1 huv
  let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := b.repr
  have hcoord0 : ∀ x : ℝ²⁴, (e x) (0 : Fin 24) = (⟪u, x⟫ : ℝ) := by
    intro x
    simpa [e, hb0] using! (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := (0 : Fin 24)))
  have hcoord1 : ∀ x : ℝ²⁴, (e x) (1 : Fin 24) = (⟪v, x⟫ : ℝ) := by
    intro x
    simpa [e, hb1] using! (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := (1 : Fin 24)))
  have hinv :=
    sphereAvg24_comp_linearIsometryEquiv (e := e)
      (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2)
  have hcoord :
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4 * (⟪x, v⟫ : ℝ) ^ 2) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2) := by
    have : sphereAvg24 (fun x : ℝ²⁴ => ((e x) (0 : Fin 24)) ^ 4 * ((e x) (1 : Fin 24)) ^ 2) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 2) := by
      simp [hinv]
    simpa [hcoord0, hcoord1, real_inner_comm] using! this
  have hD :=
    sphereAvg24_coord0_pow_four_mul_coord1_sq_eq (h := h) (u := u) hu
  simpa [hcoord] using! hD

/-- Mixed moment `sphereAvg24 ((⟪x,u⟫)^4 * (⟪x,v⟫)^4)` for an orthogonal pair `u ⟂ v`. -/
public theorem sphereAvg24_inner_pow_four_mul_inner_pow_four_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ C)
    (huv : (⟪u, v⟫ : ℝ) = 0) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4 * (⟪x, v⟫ : ℝ) ^ 4) = (1 / 58240 : ℝ) := by
  have hu1 : ‖u‖ = (1 : ℝ) := h.code.norm_one hu
  have hv1 : ‖v‖ = (1 : ℝ) := h.code.norm_one hv
  obtain ⟨b, hb0, hb1⟩ := exists_orthonormalBasis_uv (u := u) (v := v) hu1 hv1 huv
  let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := b.repr
  have hcoord0 : ∀ x : ℝ²⁴, (e x) (0 : Fin 24) = (⟪u, x⟫ : ℝ) := by
    intro x
    simpa [e, hb0] using! (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := (0 : Fin 24)))
  have hcoord1 : ∀ x : ℝ²⁴, (e x) (1 : Fin 24) = (⟪v, x⟫ : ℝ) := by
    intro x
    simpa [e, hb1] using! (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := (1 : Fin 24)))
  have hinv :=
    sphereAvg24_comp_linearIsometryEquiv (e := e)
      (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 4)
  have hcoord :
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4 * (⟪x, v⟫ : ℝ) ^ 4) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 4) := by
    have : sphereAvg24 (fun x : ℝ²⁴ => ((e x) (0 : Fin 24)) ^ 4 * ((e x) (1 : Fin 24)) ^ 4) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4 * (x (1 : Fin 24)) ^ 4) := by
      simp [hinv]
    simpa [hcoord0, hcoord1, real_inner_comm] using! this
  have hF :=
    sphereAvg24_coord0_pow_four_mul_coord1_pow_four_eq (h := h) (u := u) hu
  simpa [hcoord] using! hF

/-!
## The spherical average `11/49140`
-/

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44MomentsFinal
