-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.IndPoly
import SpherePacking.Dim24.Uniqueness.BS81.EqCase24Support
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.InnerMvPoly24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Auxiliary lemmas for 44 common neighbors

This file provides supporting lemmas for the "44 common neighbors" count in BS81 Lemma 18(ii),
following the note `paper/Notes/SphericalLP/bs81_common_neighbors_44.tex`.

We keep the final statement in `CommonNeighbors44.lean`; this file supplies:
* the indicator polynomial `indPoly`,
* rewriting averages as double sums,
* spherical mixed-moment computations in dimension `24`,
* evaluation of the final spherical average (equal to `11 / 49140`).
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44Aux

noncomputable section

open scoped RealInnerProductSpace BigOperators

open MeasureTheory Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Design reduction for inner-product monomials
-/

/-- Design reduction for mixed inner-product monomials of total degree at most `11`. -/
public lemma finsetAvg_inner_pow_mul_inner_pow_eq_sphereAvg
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u v : ℝ²⁴} (i j : ℕ) (hij : i + j ≤ 11) :
    finsetAvg h.code.finite.toFinset (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ i * (⟪v, x⟫ : ℝ) ^ j) =
      sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ i * (⟪v, x⟫ : ℝ) ^ j) := by
  have hD : IsBS81SphericalDesign24 11 h.code.finite.toFinset := h.design11
  have hEq := hD.2
  have hhom : (((innerMvPoly24 u) ^ i) * ((innerMvPoly24 v) ^ j)).IsHomogeneous (i + j) :=
    innerMvPoly24_pow_mul_pow_isHomogeneous (u := u) (v := v) i j
  have := hEq (i + j) (((innerMvPoly24 u) ^ i) * ((innerMvPoly24 v) ^ j)) hij hhom
  have hfun :
      mvPolyEval24 (((innerMvPoly24 u) ^ i) * ((innerMvPoly24 v) ^ j)) =
        (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ i * (⟪v, x⟫ : ℝ) ^ j) := by
    funext x
    simpa using!
      (mvPolyEval24_innerMvPoly24_pow_mul_pow (u := u) (v := v) (x := x) (i := i) (j := j))
  simpa [hfun] using! this

/-- Design reduction for `indPolyTerm`: `finsetAvg = sphereAvg24` on each term in the double sum. -/
public lemma finsetAvg_indPolyTerm_eq_sphereAvg {C : Set ℝ²⁴} (h : EqCase24Pkg C) (u v : ℝ²⁴)
    (i j : ℕ) (hi : i ∈ indPolyIdx) (hj : j ∈ indPolyIdx) :
    finsetAvg h.code.finite.toFinset (indPolyTerm u v i j) = sphereAvg24 (indPolyTerm u v i j) := by
  have hi' : i ≤ 5 := Nat.lt_succ_iff.mp (by simpa [indPolyIdx] using! (Finset.mem_range.mp hi))
  have hj' : j ≤ 5 := Nat.lt_succ_iff.mp (by simpa [indPolyIdx] using! (Finset.mem_range.mp hj))
  have hij : i + j ≤ 11 := by
    lia
  have hindPolyMon :
      indPolyMon u v i j = fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ i * (⟪v, x⟫ : ℝ) ^ j := by
    funext x
    simp [indPolyMon, real_inner_comm]
  have hmonEq :
      finsetAvg h.code.finite.toFinset (indPolyMon u v i j) =
        sphereAvg24 (indPolyMon u v i j) := by
    simpa [hindPolyMon] using!
      (finsetAvg_inner_pow_mul_inner_pow_eq_sphereAvg (h := h) (u := u) (v := v) (i := i) (j := j)
        hij)
  have hfin :
      finsetAvg h.code.finite.toFinset (indPolyTerm u v i j) =
        (indPolyCoeff i * indPolyCoeff j) *
          finsetAvg h.code.finite.toFinset (indPolyMon u v i j) := by
    simpa [indPolyTerm] using!
      (AdditionTheorem.Bridge24.finsetAvg_smul (C := h.code.finite.toFinset)
        (a := (indPolyCoeff i * indPolyCoeff j)) (f := indPolyMon u v i j))
  have hsphere :
      sphereAvg24 (indPolyTerm u v i j) =
        (indPolyCoeff i * indPolyCoeff j) * sphereAvg24 (indPolyMon u v i j) := by
    simpa [indPolyTerm] using!
      (sphereAvg24_smul (a := (indPolyCoeff i * indPolyCoeff j)) (f := indPolyMon u v i j))
  calc
    finsetAvg h.code.finite.toFinset (indPolyTerm u v i j) =
        (indPolyCoeff i * indPolyCoeff j) *
          finsetAvg h.code.finite.toFinset (indPolyMon u v i j) := hfin
    _ = (indPolyCoeff i * indPolyCoeff j) * sphereAvg24 (indPolyMon u v i j) := by
          simp [hmonEq]
    _ = sphereAvg24 (indPolyTerm u v i j) := hsphere.symm

public theorem finsetAvg_indPoly_mul_indPoly_eq_sphereAvg_of_pkg
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ C) :
    finsetAvg h.code.finite.toFinset
        (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) =
      sphereAvg24 (fun x : ℝ²⁴ => indPoly (⟪x, u⟫ : ℝ) * indPoly (⟪x, v⟫ : ℝ)) := by
  have hu1 : ‖u‖ = (1 : ℝ) := h.code.norm_one hu
  have hv1 : ‖v‖ = (1 : ℝ) := h.code.norm_one hv
  refine finsetAvg_indPoly_mul_indPoly_eq_sphereAvg_of_termwise (Cfin := h.code.finite.toFinset)
    (u := u) (v := v) hu1 hv1 ?_
  exact fun i a j a_1 => finsetAvg_indPolyTerm_eq_sphereAvg h u v i j a a_1

/-!
## Averages of single inner-product powers (design reduction)
-/

/-- Design reduction for a single inner-product power of degree at most `11`. -/
public lemma finsetAvg_inner_pow_eq_sphereAvg
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (m : ℕ) (hm : m ≤ 11) :
    finsetAvg h.code.finite.toFinset (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ m) =
      sphereAvg24 (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ m) := by
  have hD : IsBS81SphericalDesign24 11 h.code.finite.toFinset := h.design11
  have hEq := hD.2
  have hhom : ((innerMvPoly24 u) ^ m).IsHomogeneous m :=
    innerMvPoly24_pow_isHomogeneous (u := u) (m := m)
  have := hEq m ((innerMvPoly24 u) ^ m) hm hhom
  have hfun : mvPolyEval24 ((innerMvPoly24 u) ^ m) = (fun x : ℝ²⁴ => (⟪u, x⟫ : ℝ) ^ m) := by
    funext x
    simpa using! (mvPolyEval24_innerMvPoly24_pow (u := u) (x := x) (m := m))
  simpa [hfun] using! this

/-!
## Odd moments vanish (for orthogonal pairs)

If `⟪u,v⟫ = 0`, we can reflect in the hyperplane orthogonal to `u`; this negates `u` and fixes `v`.
-/

/-- If `u ⟂ v`, then odd moments in `⟪x,u⟫` vanish under `sphereAvg24`. -/
public lemma sphereAvg24_inner_pow_mul_inner_pow_eq_zero_of_odd_left
    {u v : ℝ²⁴} (huv : (⟪u, v⟫ : ℝ) = 0) {i j : ℕ} (hi : Odd i) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ) ^ j) = 0 := by
  let K : Submodule ℝ ℝ²⁴ := (ℝ ∙ u)ᗮ
  let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := K.reflection
  have hvK : v ∈ K := by
    -- `v ⟂ u` means `v ∈ (ℝ ∙ u)ᗮ`.
    simpa [K] using! (Submodule.mem_orthogonal_singleton_iff_inner_right.2 huv)
  have he_v : e v = v := by
    simpa [e] using! (Submodule.reflection_mem_subspace_eq_self (K := K) hvK)
  have he_u : e u = -u := by
    -- reflection in `(ℝ∙u)ᗮ` sends `u` to `-u`.
    simpa [e, K] using! (Submodule.reflection_orthogonalComplement_singleton_eq_neg (𝕜 := ℝ) u)
  have hinv :=
    (sphereAvg24_comp_linearIsometryEquiv (e := e)
      (f := fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ) ^ j)).symm
  have hflip :
      (fun x : ℝ²⁴ => (⟪e x, u⟫ : ℝ) ^ i * (⟪e x, v⟫ : ℝ) ^ j) =
    fun x : ℝ²⁴ => -((⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ) ^ j) := by
    funext x
    have hu' : (⟪e x, u⟫ : ℝ) = -(⟪x, u⟫ : ℝ) := by
      -- `u = e (-u)` and `e` preserves inner products.
      have : e (-u) = u := by
        calc
          e (-u) = -e u := by simp
          _ = u := by simp [he_u]
      have hinner : (⟪e x, u⟫ : ℝ) = ⟪x, -u⟫ := by
        -- `⟪e x, e (-u)⟫ = ⟪x, -u⟫`.
        simpa [this] using! (LinearIsometryEquiv.inner_map_map e x (-u))
      simpa [inner_neg_right] using! hinner
    have hv' : (⟪e x, v⟫ : ℝ) = (⟪x, v⟫ : ℝ) := by
      have hinner : (⟪e x, v⟫ : ℝ) = ⟪x, v⟫ := by
        simpa [he_v] using! (LinearIsometryEquiv.inner_map_map e x v)
      simpa using! hinner
    -- Use oddness to simplify `(-a)^i`.
    simp [hu', hv', hi.neg_pow]
  have : sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ) ^ j) =
      -sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ) ^ j) := by
    -- Invariance plus flip.
    have := congrArg id (show
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ) ^ j) =
        sphereAvg24 (fun x : ℝ²⁴ => (⟪e x, u⟫ : ℝ) ^ i * (⟪e x, v⟫ : ℝ) ^ j) from hinv)
    -- rewrite RHS as `sphereAvg24 (-f)`.
    simpa [hflip, sphereAvg24_neg] using! this
  linarith

/-- If `u ⟂ v`, then odd moments in `⟪x,v⟫` vanish under `sphereAvg24`. -/
public lemma sphereAvg24_inner_pow_mul_inner_pow_eq_zero_of_odd_right
    {u v : ℝ²⁴} (huv : (⟪u, v⟫ : ℝ) = 0) {i j : ℕ} (hj : Odd j) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ i * (⟪x, v⟫ : ℝ) ^ j) = 0 := by
  have :=
    sphereAvg24_inner_pow_mul_inner_pow_eq_zero_of_odd_left (u := v) (v := u)
      (huv := by simpa [real_inner_comm] using! huv) (i := j) (j := i) hj
  simpa [mul_comm, mul_left_comm, mul_assoc] using! this

/-!
## Moment computations from the distance distribution (powers 6 and 8)

We compute the *finite* averages of `w ↦ ⟪u,w⟫^6` and `w ↦ ⟪u,w⟫^8` using `h.distCount_eq`.
By the design axiom, these match the corresponding spherical averages.
-/

lemma card_filter_inner_eq_distCount
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (t : ℝ) :
    ((h.code.finite.toFinset.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = t).card : ℝ) =
      (Uniqueness.BS81.distCount (n := 24) C u t : ℝ) := by
  let Cfin : Finset ℝ²⁴ := h.code.finite.toFinset
  let S : Set ℝ²⁴ := {w : ℝ²⁴ | w ∈ C ∧ (⟪u, w⟫ : ℝ) = t}
  have hfinite : S.Finite := h.code.finite.subset (by intro w hw; exact hw.1)
  have hto : hfinite.toFinset = Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = t := by
    ext w
    simp [S, Cfin, Set.Finite.mem_toFinset, and_comm]
  have hncard : (Uniqueness.BS81.distCount (n := 24) C u t : ℝ) =
      (hfinite.toFinset.card : ℝ) := by
    -- `distCount` is `Set.ncard S`.
    simp [Uniqueness.BS81.distCount, S, Set.ncard_eq_toFinset_card, hfinite]
  simpa [Cfin, hto] using! hncard.symm

lemma sum_indicator_eq_filter_card (Cfin : Finset ℝ²⁴) (p : ℝ²⁴ → Prop) [DecidablePred p] :
    Cfin.sum (fun w : ℝ²⁴ => if p w then (1 : ℝ) else 0) = (Cfin.filter p).card :=
  Finset.sum_boole p Cfin

lemma finsetSum_inner_pow_six_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    (h.code.finite.toFinset.sum fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 6) = (675 / 4 : ℝ) := by
  let Cfin : Finset ℝ²⁴ := h.code.finite.toFinset
  have hEqCase : Uniqueness.BS81.EqCase24 C :=
    EqCase24Pkg.toEqCase24 (C := C) h
  have hmemCfin : ∀ {w : ℝ²⁴}, w ∈ Cfin ↔ w ∈ C := by
    intro w
    simp [Cfin]
  have hsup : ∀ w : ℝ²⁴, w ∈ Cfin →
      (⟪u, w⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, w⟫ : ℝ) = (-1 : ℝ) ∨
        (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) ∨ (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) ∨
          (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) ∨ (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) ∨
            (⟪u, w⟫ : ℝ) = (0 : ℝ) := by
    intro w hw
    exact
     inner_eq_one_or_eq_neg_one_or_eq_half_or_eq_neg_half_or_eq_quarter_or_eq_neg_quarter_or_eq_zero
       (C := C) hEqCase (hu := hu) (hv := hmemCfin.mp hw)
  -- Pointwise: express `⟪u,w⟫^6` as a linear combination of indicator functions of the fibers.
  have hpoint : ∀ w : ℝ²⁴, w ∈ Cfin →
      (⟪u, w⟫ : ℝ) ^ 6 =
        (if (⟪u, w⟫ : ℝ) = (1 : ℝ) then (1 : ℝ) else 0) +
          (if (⟪u, w⟫ : ℝ) = (-1 : ℝ) then (1 : ℝ) else 0) +
            (1 / 64 : ℝ) *
              ((if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
                (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) +
              (1 / 4096 : ℝ) *
                ((if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0)) := by
    intro w hw
    rcases hsup w hw with h' | h' | h' | h' | h' | h' | h'
    · simp [h']; norm_num
    · simp [h']; norm_num
    · simp [h']; norm_num
    · simp [h']; norm_num
    · simp [h']; norm_num
    · simp [h']; norm_num
    · simp [h']; norm_num
  have hsum_point :
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 6) =
        Cfin.sum (fun w : ℝ²⁴ =>
          (if (⟪u, w⟫ : ℝ) = (1 : ℝ) then (1 : ℝ) else 0) +
            (if (⟪u, w⟫ : ℝ) = (-1 : ℝ) then (1 : ℝ) else 0) +
              (1 / 64 : ℝ) *
                ((if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) +
                (1 / 4096 : ℝ) *
                  ((if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
                    (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0))) := by
    refine Finset.sum_congr rfl (fun w hw => hpoint w hw)
  -- Use the distance-distribution field to evaluate the fiber-cardinalities.
  rcases h.distCount_eq (u := u) hu with ⟨h1, hneg1, hhalf, hneghalf, hquart, hnegquart, -⟩
  have hcard_filter (t : ℝ) :
      ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = t).card : ℝ) =
        (Uniqueness.BS81.distCount (n := 24) C u t : ℝ) :=
    card_filter_inner_eq_distCount (h := h) (u := u) (t := t)
  have h1' : (Uniqueness.BS81.distCount (n := 24) C u (1 : ℝ) : ℝ) = 1 := by
    exact_mod_cast h1
  have hneg1' : (Uniqueness.BS81.distCount (n := 24) C u (-1 : ℝ) : ℝ) = 1 := by
    exact_mod_cast hneg1
  have hhalf' :
      (Uniqueness.BS81.distCount (n := 24) C u (1 / 2 : ℝ) : ℝ) = 4600 := by
    exact_mod_cast hhalf
  have hneghalf' :
      (Uniqueness.BS81.distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ) = 4600 := by
    exact_mod_cast hneghalf
  have hquart' :
      (Uniqueness.BS81.distCount (n := 24) C u (1 / 4 : ℝ) : ℝ) = 47104 := by
    exact_mod_cast hquart
  have hnegquart' :
      (Uniqueness.BS81.distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ) = 47104 := by
    exact_mod_cast hnegquart
  -- Finish by straightforward algebra, keeping the rewrite steps small.
  let f1 : ℝ²⁴ → ℝ := fun w => if (⟪u, w⟫ : ℝ) = (1 : ℝ) then (1 : ℝ) else 0
  let f2 : ℝ²⁴ → ℝ := fun w => if (⟪u, w⟫ : ℝ) = (-1 : ℝ) then (1 : ℝ) else 0
  let f3 : ℝ²⁴ → ℝ := fun w =>
    (1 / 64 : ℝ) *
      ((if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
        (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0))
  let f4 : ℝ²⁴ → ℝ := fun w =>
    (1 / 4096 : ℝ) *
      ((if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
        (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0))
  let f12 : ℝ²⁴ → ℝ := fun w => f1 w + f2 w
  let f34 : ℝ²⁴ → ℝ := fun w => f3 w + f4 w
  have hsum_split :
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 6) = Cfin.sum f12 + Cfin.sum f34 := by
    have hpoint' : ∀ w : ℝ²⁴, w ∈ Cfin → (⟪u, w⟫ : ℝ) ^ 6 = f12 w + f34 w := by
      intro w hw
      refine (hpoint w hw).trans ?_
      dsimp [f1, f2, f3, f4, f12, f34]
      ring_nf
    calc
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 6)
          = Cfin.sum (fun w : ℝ²⁴ => f12 w + f34 w) := by
              refine Finset.sum_congr rfl (fun w hw => hpoint' w hw)
      _ = Cfin.sum f12 + Cfin.sum f34 := by
            simpa [f12, f34] using! (Finset.sum_add_distrib (f := f12) (g := f34) (s := Cfin))
  have hsum_f12 : Cfin.sum f12 = Cfin.sum f1 + Cfin.sum f2 := by
    simpa [f12] using! (Finset.sum_add_distrib (f := f1) (g := f2) (s := Cfin))
  have hsum_f34 : Cfin.sum f34 = Cfin.sum f3 + Cfin.sum f4 := by
    simpa [f34] using! (Finset.sum_add_distrib (f := f3) (g := f4) (s := Cfin))
  have hsum_f1 : Cfin.sum f1 = (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 : ℝ)).card :=
    sum_indicator_eq_filter_card Cfin fun w => ⟪u, w⟫ = 1
  have hsum_f2 : Cfin.sum f2 = (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 : ℝ)).card :=
    sum_indicator_eq_filter_card Cfin fun w => ⟪u, w⟫ = -1
  have hsum_f3 :
      Cfin.sum f3 =
        (1 / 64 : ℝ) *
          ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card +
            (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card) := by
    calc
      Cfin.sum f3
          = (1 / 64 : ℝ) *
              Cfin.sum (fun w : ℝ²⁴ =>
                (if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) := by
              -- Pull out the scalar.
              simp [f3, Finset.mul_sum]
      _ = (1 / 64 : ℝ) *
            (Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
              Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) := by
              simp [Finset.sum_add_distrib, mul_add]
      _ = (1 / 64 : ℝ) *
            ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card +
              (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card) := by
              simp
  have hsum_f4 :
      Cfin.sum f4 =
        (1 / 4096 : ℝ) *
          ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card +
            (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card) := by
    calc
      Cfin.sum f4
          = (1 / 4096 : ℝ) *
              Cfin.sum (fun w : ℝ²⁴ =>
                (if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0)) := by
              simp [f4, Finset.mul_sum]
      _ = (1 / 4096 : ℝ) *
            (Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
              Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0)) := by
              simp [Finset.sum_add_distrib, mul_add]
      _ = (1 / 4096 : ℝ) *
            ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card +
              (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card) := by
              simp
  have hsum_cards :
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 6) =
        ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 : ℝ)).card : ℝ) +
          ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 : ℝ)).card : ℝ) +
            (1 / 64 : ℝ) *
              (((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card : ℝ) +
                ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card : ℝ)) +
              (1 / 4096 : ℝ) *
                (((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card : ℝ) +
                  ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card : ℝ)) := by
    -- Assemble the pieces, keeping reassociation minimal.
    calc
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 6)
          = (Cfin.sum f12 + Cfin.sum f34) := hsum_split
      _ = (Cfin.sum f1 + Cfin.sum f2) + (Cfin.sum f3 + Cfin.sum f4) := by
            rw [hsum_f12, hsum_f34]
      _ = (Cfin.sum f1) + (Cfin.sum f2) + (Cfin.sum f3) + (Cfin.sum f4) := by
            ac_rfl
      _ = (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 : ℝ)).card +
            (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 : ℝ)).card +
              (1 / 64 : ℝ) *
                ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card +
                  (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card) +
                (1 / 4096 : ℝ) *
                  ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card +
                    (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card) := by
            rw [hsum_f1, hsum_f2, hsum_f3, hsum_f4]
            -- At this point the goal is definitional.
      _ = _ := by ring
  -- Substitute the explicit counts.
  -- (Note: `distCount` counts are in `ℕ`; we work in `ℝ`.)
  calc
    (h.code.finite.toFinset.sum fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 6) = _ := by
      simpa [Cfin] using! hsum_cards
    _ = (675 / 4 : ℝ) := by
      -- Rewrite fiber-cardinalities using the explicit distance distribution.
      -- (We keep the `t = -(1/2)` and `t = -(1/4)` cases explicit to avoid rewriting issues.)
      have hhalf'' :
          (Uniqueness.BS81.distCount (n := 24) C u ((2 : ℝ)⁻¹) : ℝ) = 4600 := by
        simpa [one_div] using! hhalf'
      have hquart'' :
          (Uniqueness.BS81.distCount (n := 24) C u ((4 : ℝ)⁻¹) : ℝ) = 47104 := by
        simpa [one_div] using! hquart'
      -- Replace the `Finset` cards by `distCount` and then by the explicit numerals.
      rw [hcard_filter (t := (1 : ℝ)), hcard_filter (t := (-1 : ℝ)),
        hcard_filter (t := ((2 : ℝ)⁻¹)), hcard_filter (t := (-1 / 2 : ℝ)),
        hcard_filter (t := ((4 : ℝ)⁻¹)), hcard_filter (t := (-1 / 4 : ℝ))]
      simp [h1', hneg1', hhalf'', hneghalf', hquart'', hnegquart']
      norm_num

/-- Sixth moment in the BS81 equality case: the finite average of `⟪u,w⟫^6` equals `5 / 5824`. -/
public theorem finsetAvg_inner_pow_six_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    finsetAvg h.code.finite.toFinset (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 6) = (5 / 5824 : ℝ) := by
  -- Convert sum to average using `|C| = 196560`.
  have hncard : Set.ncard C = h.code.finite.toFinset.card := by
    simpa using! (Set.ncard_eq_toFinset_card (s := C) h.code.finite)
  have hcardNat : h.code.finite.toFinset.card = 196560 := by
    simpa [hncard] using! h.card_eq
  have hcardR : (h.code.finite.toFinset.card : ℝ) = (196560 : ℝ) := by exact_mod_cast hcardNat
  have hsum := finsetSum_inner_pow_six_eq (h := h) (hu := hu)
  unfold finsetAvg
  have : (h.code.finite.toFinset.card : ℝ)⁻¹ * (675 / 4 : ℝ) = (5 / 5824 : ℝ) := by
    norm_num [hcardR]
  simp [hsum, this]

/-!
### Moment computations for powers 4 and 8

These are derived exactly as for the sixth moment, using the explicit distance distribution.
-/

lemma finsetSum_inner_pow_four_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    (h.code.finite.toFinset.sum fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 4) = (945 : ℝ) := by
  let Cfin : Finset ℝ²⁴ := h.code.finite.toFinset
  have hEqCase : Uniqueness.BS81.EqCase24 C :=
    EqCase24Pkg.toEqCase24 (C := C) h
  have hmemCfin : ∀ {w : ℝ²⁴}, w ∈ Cfin ↔ w ∈ C := by
    intro w
    simp [Cfin]
  have hsup : ∀ w : ℝ²⁴, w ∈ Cfin →
      (⟪u, w⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, w⟫ : ℝ) = (-1 : ℝ) ∨
        (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) ∨ (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) ∨
          (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) ∨ (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) ∨
            (⟪u, w⟫ : ℝ) = (0 : ℝ) := by
    intro w hw
    exact
     inner_eq_one_or_eq_neg_one_or_eq_half_or_eq_neg_half_or_eq_quarter_or_eq_neg_quarter_or_eq_zero
       (C := C) hEqCase (hu := hu) (hv := hmemCfin.mp hw)
  have hpoint : ∀ w : ℝ²⁴, w ∈ Cfin →
      (⟪u, w⟫ : ℝ) ^ 4 =
        (if (⟪u, w⟫ : ℝ) = (1 : ℝ) then (1 : ℝ) else 0) +
          (if (⟪u, w⟫ : ℝ) = (-1 : ℝ) then (1 : ℝ) else 0) +
            (1 / 16 : ℝ) *
              ((if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
                (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) +
              (1 / 256 : ℝ) *
                ((if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0)) := by
    intro w hw
    rcases hsup w hw with h' | h' | h' | h' | h' | h' | h'
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
  have hsum_point :
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 4) =
        Cfin.sum (fun w : ℝ²⁴ =>
          (if (⟪u, w⟫ : ℝ) = (1 : ℝ) then (1 : ℝ) else 0) +
            (if (⟪u, w⟫ : ℝ) = (-1 : ℝ) then (1 : ℝ) else 0) +
              (1 / 16 : ℝ) *
                ((if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) +
                (1 / 256 : ℝ) *
                  ((if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
                    (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0))) := by
    refine Finset.sum_congr rfl (fun w hw => hpoint w hw)
  rcases h.distCount_eq (u := u) hu with ⟨h1, hneg1, hhalf, hneghalf, hquart, hnegquart, -⟩
  have hcard_filter (t : ℝ) :
      ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = t).card : ℝ) =
        (Uniqueness.BS81.distCount (n := 24) C u t : ℝ) :=
    card_filter_inner_eq_distCount (h := h) (u := u) (t := t)
  have h1' : (Uniqueness.BS81.distCount (n := 24) C u (1 : ℝ) : ℝ) = 1 := by
    exact_mod_cast h1
  have hneg1' : (Uniqueness.BS81.distCount (n := 24) C u (-1 : ℝ) : ℝ) = 1 := by
    exact_mod_cast hneg1
  have hhalf' :
      (Uniqueness.BS81.distCount (n := 24) C u (1 / 2 : ℝ) : ℝ) = 4600 := by
    exact_mod_cast hhalf
  have hneghalf' :
      (Uniqueness.BS81.distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ) = 4600 := by
    exact_mod_cast hneghalf
  have hquart' :
      (Uniqueness.BS81.distCount (n := 24) C u (1 / 4 : ℝ) : ℝ) = 47104 := by
    exact_mod_cast hquart
  have hnegquart' :
      (Uniqueness.BS81.distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ) = 47104 := by
    exact_mod_cast hnegquart
  -- Summation: split into four indicator sums as in the sixth-moment computation.
  let f1 : ℝ²⁴ → ℝ := fun w => if (⟪u, w⟫ : ℝ) = (1 : ℝ) then (1 : ℝ) else 0
  let f2 : ℝ²⁴ → ℝ := fun w => if (⟪u, w⟫ : ℝ) = (-1 : ℝ) then (1 : ℝ) else 0
  let f3 : ℝ²⁴ → ℝ := fun w =>
    (1 / 16 : ℝ) *
      ((if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
        (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0))
  let f4 : ℝ²⁴ → ℝ := fun w =>
    (1 / 256 : ℝ) *
      ((if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
        (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0))
  let f12 : ℝ²⁴ → ℝ := fun w => f1 w + f2 w
  let f34 : ℝ²⁴ → ℝ := fun w => f3 w + f4 w
  have hsum_split :
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 4) = Cfin.sum f12 + Cfin.sum f34 := by
    have hpoint' : ∀ w : ℝ²⁴, w ∈ Cfin → (⟪u, w⟫ : ℝ) ^ 4 = f12 w + f34 w := by
      intro w hw
      simpa [f1, f2, f3, f4, f12, f34, add_assoc, add_left_comm, add_comm, mul_assoc] using!
        hpoint w hw
    calc
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 4)
          = Cfin.sum (fun w : ℝ²⁴ => f12 w + f34 w) := by
              refine Finset.sum_congr rfl (fun w hw => hpoint' w hw)
      _ = Cfin.sum f12 + Cfin.sum f34 := by
            simpa [f12, f34] using! (Finset.sum_add_distrib (f := f12) (g := f34) (s := Cfin))
  have hsum_f12 : Cfin.sum f12 = Cfin.sum f1 + Cfin.sum f2 := by
    simpa [f12] using! (Finset.sum_add_distrib (f := f1) (g := f2) (s := Cfin))
  have hsum_f34 : Cfin.sum f34 = Cfin.sum f3 + Cfin.sum f4 := by
    simpa [f34] using! (Finset.sum_add_distrib (f := f3) (g := f4) (s := Cfin))
  have hsum_f1 : Cfin.sum f1 = (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 : ℝ)).card :=
    sum_indicator_eq_filter_card Cfin fun w => ⟪u, w⟫ = 1
  have hsum_f2 : Cfin.sum f2 = (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 : ℝ)).card :=
    sum_indicator_eq_filter_card Cfin fun w => ⟪u, w⟫ = -1
  have hsum_f3 :
      Cfin.sum f3 =
        (1 / 16 : ℝ) *
          ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card +
            (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card) := by
    calc
      Cfin.sum f3
          = (1 / 16 : ℝ) *
              Cfin.sum (fun w : ℝ²⁴ =>
                (if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) := by
              simp [f3, Finset.mul_sum]
      _ = (1 / 16 : ℝ) *
            (Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
              Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) := by
              simp [Finset.sum_add_distrib, mul_add]
      _ = (1 / 16 : ℝ) *
            ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card +
              (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card) := by
              simp
  have hsum_f4 :
      Cfin.sum f4 =
        (1 / 256 : ℝ) *
          ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card +
            (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card) := by
    calc
      Cfin.sum f4
          = (1 / 256 : ℝ) *
              Cfin.sum (fun w : ℝ²⁴ =>
                (if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0)) := by
              simp [f4, Finset.mul_sum]
      _ = (1 / 256 : ℝ) *
            (Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
              Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0)) := by
              simp [Finset.sum_add_distrib, mul_add]
      _ = (1 / 256 : ℝ) *
            ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card +
              (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card) := by
              simp
  have hsum_cards :
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 4) =
        ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 : ℝ)).card : ℝ) +
          ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 : ℝ)).card : ℝ) +
            (1 / 16 : ℝ) *
              (((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card : ℝ) +
                ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card : ℝ)) +
              (1 / 256 : ℝ) *
                (((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card : ℝ) +
                  ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card : ℝ)) := by
    calc
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 4)
          = (Cfin.sum f12 + Cfin.sum f34) := hsum_split
      _ = (Cfin.sum f1 + Cfin.sum f2) + (Cfin.sum f3 + Cfin.sum f4) := by
            rw [hsum_f12, hsum_f34]
      _ = (Cfin.sum f1) + (Cfin.sum f2) + (Cfin.sum f3) + (Cfin.sum f4) := by
            ac_rfl
      _ = (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 : ℝ)).card +
            (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 : ℝ)).card +
              (1 / 16 : ℝ) *
                ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card +
                  (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card) +
                (1 / 256 : ℝ) *
                  ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card +
                    (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card) := by
            rw [hsum_f1, hsum_f2, hsum_f3, hsum_f4]
      _ = _ := by ring
  calc
    (h.code.finite.toFinset.sum fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 4) = _ := by
      simpa [Cfin] using! hsum_cards
    _ = (945 : ℝ) := by
      have hhalf'' :
          (Uniqueness.BS81.distCount (n := 24) C u ((2 : ℝ)⁻¹) : ℝ) = 4600 := by
        simpa [one_div] using! hhalf'
      have hquart'' :
          (Uniqueness.BS81.distCount (n := 24) C u ((4 : ℝ)⁻¹) : ℝ) = 47104 := by
        simpa [one_div] using! hquart'
      rw [hcard_filter (t := (1 : ℝ)), hcard_filter (t := (-1 : ℝ)),
        hcard_filter (t := ((2 : ℝ)⁻¹)), hcard_filter (t := (-1 / 2 : ℝ)),
        hcard_filter (t := ((4 : ℝ)⁻¹)), hcard_filter (t := (-1 / 4 : ℝ))]
      simp [h1', hneg1', hhalf'', hneghalf', hquart'', hnegquart']
      norm_num

/-- Fourth moment in the BS81 equality case: the finite average of `⟪u,w⟫^4` equals `1 / 208`. -/
public theorem finsetAvg_inner_pow_four_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    finsetAvg h.code.finite.toFinset (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 4) = (1 / 208 : ℝ) := by
  have hncard : Set.ncard C = h.code.finite.toFinset.card := by
    simpa using! (Set.ncard_eq_toFinset_card (s := C) h.code.finite)
  have hcardNat : h.code.finite.toFinset.card = 196560 := by
    simpa [hncard] using! h.card_eq
  have hcardR : (h.code.finite.toFinset.card : ℝ) = (196560 : ℝ) := by exact_mod_cast hcardNat
  have hsum := finsetSum_inner_pow_four_eq (h := h) (hu := hu)
  unfold finsetAvg
  have : (h.code.finite.toFinset.card : ℝ)⁻¹ * (945 : ℝ) = (1 / 208 : ℝ) := by
    norm_num [hcardR]
  simp [hsum, this]

lemma finsetSum_inner_pow_eight_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    (h.code.finite.toFinset.sum fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 8) = (315 / 8 : ℝ) := by
  let Cfin : Finset ℝ²⁴ := h.code.finite.toFinset
  have hEqCase : Uniqueness.BS81.EqCase24 C :=
    EqCase24Pkg.toEqCase24 (C := C) h
  have hmemCfin : ∀ {w : ℝ²⁴}, w ∈ Cfin ↔ w ∈ C := by
    intro w
    simp [Cfin]
  have hsup : ∀ w : ℝ²⁴, w ∈ Cfin →
      (⟪u, w⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, w⟫ : ℝ) = (-1 : ℝ) ∨
        (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) ∨ (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) ∨
          (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) ∨ (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) ∨
            (⟪u, w⟫ : ℝ) = (0 : ℝ) := by
    intro w hw
    exact
     inner_eq_one_or_eq_neg_one_or_eq_half_or_eq_neg_half_or_eq_quarter_or_eq_neg_quarter_or_eq_zero
       (C := C) hEqCase (hu := hu) (hv := hmemCfin.mp hw)
  have hpoint : ∀ w : ℝ²⁴, w ∈ Cfin →
      (⟪u, w⟫ : ℝ) ^ 8 =
        (if (⟪u, w⟫ : ℝ) = (1 : ℝ) then (1 : ℝ) else 0) +
          (if (⟪u, w⟫ : ℝ) = (-1 : ℝ) then (1 : ℝ) else 0) +
            (1 / 256 : ℝ) *
              ((if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
                (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) +
              (1 / 65536 : ℝ) *
                ((if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0)) := by
    intro w hw
    rcases hsup w hw with h' | h' | h' | h' | h' | h' | h'
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
    · simp [h'] ; norm_num
  have hsum_point :
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 8) =
        Cfin.sum (fun w : ℝ²⁴ =>
          (if (⟪u, w⟫ : ℝ) = (1 : ℝ) then (1 : ℝ) else 0) +
            (if (⟪u, w⟫ : ℝ) = (-1 : ℝ) then (1 : ℝ) else 0) +
              (1 / 256 : ℝ) *
                ((if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) +
                (1 / 65536 : ℝ) *
                  ((if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
                    (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0))) := by
    refine Finset.sum_congr rfl (fun w hw => hpoint w hw)
  rcases h.distCount_eq (u := u) hu with ⟨h1, hneg1, hhalf, hneghalf, hquart, hnegquart, -⟩
  have hcard_filter (t : ℝ) :
      ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = t).card : ℝ) =
        (Uniqueness.BS81.distCount (n := 24) C u t : ℝ) :=
    card_filter_inner_eq_distCount (h := h) (u := u) (t := t)
  have h1' : (Uniqueness.BS81.distCount (n := 24) C u (1 : ℝ) : ℝ) = 1 := by
    exact_mod_cast h1
  have hneg1' : (Uniqueness.BS81.distCount (n := 24) C u (-1 : ℝ) : ℝ) = 1 := by
    exact_mod_cast hneg1
  have hhalf' :
      (Uniqueness.BS81.distCount (n := 24) C u (1 / 2 : ℝ) : ℝ) = 4600 := by
    exact_mod_cast hhalf
  have hneghalf' :
      (Uniqueness.BS81.distCount (n := 24) C u (-1 / 2 : ℝ) : ℝ) = 4600 := by
    exact_mod_cast hneghalf
  have hquart' :
      (Uniqueness.BS81.distCount (n := 24) C u (1 / 4 : ℝ) : ℝ) = 47104 := by
    exact_mod_cast hquart
  have hnegquart' :
      (Uniqueness.BS81.distCount (n := 24) C u (-1 / 4 : ℝ) : ℝ) = 47104 := by
    exact_mod_cast hnegquart
  let f1 : ℝ²⁴ → ℝ := fun w => if (⟪u, w⟫ : ℝ) = (1 : ℝ) then (1 : ℝ) else 0
  let f2 : ℝ²⁴ → ℝ := fun w => if (⟪u, w⟫ : ℝ) = (-1 : ℝ) then (1 : ℝ) else 0
  let f3 : ℝ²⁴ → ℝ := fun w =>
    (1 / 256 : ℝ) *
      ((if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
        (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0))
  let f4 : ℝ²⁴ → ℝ := fun w =>
    (1 / 65536 : ℝ) *
      ((if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
        (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0))
  let f12 : ℝ²⁴ → ℝ := fun w => f1 w + f2 w
  let f34 : ℝ²⁴ → ℝ := fun w => f3 w + f4 w
  have hsum_split :
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 8) = Cfin.sum f12 + Cfin.sum f34 := by
    have hpoint' : ∀ w : ℝ²⁴, w ∈ Cfin → (⟪u, w⟫ : ℝ) ^ 8 = f12 w + f34 w := by
      intro w hw
      simpa [f1, f2, f3, f4, f12, f34, add_assoc, add_left_comm, add_comm, mul_assoc] using!
        hpoint w hw
    calc
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 8)
          = Cfin.sum (fun w : ℝ²⁴ => f12 w + f34 w) := by
              refine Finset.sum_congr rfl (fun w hw => hpoint' w hw)
      _ = Cfin.sum f12 + Cfin.sum f34 := by
            simpa [f12, f34] using! (Finset.sum_add_distrib (f := f12) (g := f34) (s := Cfin))
  have hsum_f12 : Cfin.sum f12 = Cfin.sum f1 + Cfin.sum f2 := by
    simpa [f12] using! (Finset.sum_add_distrib (f := f1) (g := f2) (s := Cfin))
  have hsum_f34 : Cfin.sum f34 = Cfin.sum f3 + Cfin.sum f4 := by
    simpa [f34] using! (Finset.sum_add_distrib (f := f3) (g := f4) (s := Cfin))
  have hsum_f1 : Cfin.sum f1 = (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 : ℝ)).card :=
    sum_indicator_eq_filter_card Cfin fun w => ⟪u, w⟫ = 1
  have hsum_f2 : Cfin.sum f2 = (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 : ℝ)).card :=
    sum_indicator_eq_filter_card Cfin fun w => ⟪u, w⟫ = -1
  have hsum_f3 :
      Cfin.sum f3 =
        (1 / 256 : ℝ) *
          ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card +
            (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card) := by
    calc
      Cfin.sum f3
          = (1 / 256 : ℝ) *
              Cfin.sum (fun w : ℝ²⁴ =>
                (if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) := by
              simp [f3, Finset.mul_sum]
      _ = (1 / 256 : ℝ) *
            (Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) then (1 : ℝ) else 0) +
              Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ) then (1 : ℝ) else 0)) := by
              simp [Finset.sum_add_distrib, mul_add]
      _ = (1 / 256 : ℝ) *
            ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card +
              (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card) := by
              simp
  have hsum_f4 :
      Cfin.sum f4 =
        (1 / 65536 : ℝ) *
          ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card +
            (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card) := by
    calc
      Cfin.sum f4
          = (1 / 65536 : ℝ) *
              Cfin.sum (fun w : ℝ²⁴ =>
                (if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
                  (if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0)) := by
              simp [f4, Finset.mul_sum]
      _ = (1 / 65536 : ℝ) *
            (Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ) then (1 : ℝ) else 0) +
              Cfin.sum (fun w : ℝ²⁴ => if (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ) then (1 : ℝ) else 0)) := by
              simp [Finset.sum_add_distrib, mul_add]
      _ = (1 / 65536 : ℝ) *
            ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card +
              (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card) := by
              simp
  have hsum_cards :
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 8) =
        ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 : ℝ)).card : ℝ) +
          ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 : ℝ)).card : ℝ) +
            (1 / 256 : ℝ) *
              (((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card : ℝ) +
                ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card : ℝ)) +
              (1 / 65536 : ℝ) *
                (((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card : ℝ) +
                  ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card : ℝ)) := by
    calc
      Cfin.sum (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 8)
          = (Cfin.sum f12 + Cfin.sum f34) := hsum_split
      _ = (Cfin.sum f1 + Cfin.sum f2) + (Cfin.sum f3 + Cfin.sum f4) := by
            rw [hsum_f12, hsum_f34]
      _ = (Cfin.sum f1) + (Cfin.sum f2) + (Cfin.sum f3) + (Cfin.sum f4) := by
            ac_rfl
      _ = (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 : ℝ)).card +
            (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 : ℝ)).card +
              (1 / 256 : ℝ) *
                ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)).card +
                  (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 2 : ℝ)).card) +
                (1 / 65536 : ℝ) *
                  ((Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 4 : ℝ)).card +
                    (Cfin.filter fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (-1 / 4 : ℝ)).card) := by
            rw [hsum_f1, hsum_f2, hsum_f3, hsum_f4]
      _ = _ := by ring
  calc
    (h.code.finite.toFinset.sum fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 8) = _ := by
      simpa [Cfin] using! hsum_cards
    _ = (315 / 8 : ℝ) := by
      have hhalf'' :
          (Uniqueness.BS81.distCount (n := 24) C u ((2 : ℝ)⁻¹) : ℝ) = 4600 := by
        simpa [one_div] using! hhalf'
      have hquart'' :
          (Uniqueness.BS81.distCount (n := 24) C u ((4 : ℝ)⁻¹) : ℝ) = 47104 := by
        simpa [one_div] using! hquart'
      rw [hcard_filter (t := (1 : ℝ)), hcard_filter (t := (-1 : ℝ)),
        hcard_filter (t := ((2 : ℝ)⁻¹)), hcard_filter (t := (-1 / 2 : ℝ)),
        hcard_filter (t := ((4 : ℝ)⁻¹)), hcard_filter (t := (-1 / 4 : ℝ))]
      simp [h1', hneg1', hhalf'', hneghalf', hquart'', hnegquart']
      norm_num

/-- Eighth moment in the BS81 equality case: the finite average of `⟪u,w⟫^8` equals `1 / 4992`. -/
public theorem finsetAvg_inner_pow_eight_eq
    {C : Set ℝ²⁴} (h : EqCase24Pkg C) {u : ℝ²⁴} (hu : u ∈ C) :
    finsetAvg h.code.finite.toFinset (fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) ^ 8) = (1 / 4992 : ℝ) := by
  have hncard : Set.ncard C = h.code.finite.toFinset.card := by
    simpa using! (Set.ncard_eq_toFinset_card (s := C) h.code.finite)
  have hcardNat : h.code.finite.toFinset.card = 196560 := by
    simpa [hncard] using! h.card_eq
  have hcardR : (h.code.finite.toFinset.card : ℝ) = (196560 : ℝ) := by exact_mod_cast hcardNat
  have hsum := finsetSum_inner_pow_eight_eq (h := h) (hu := hu)
  unfold finsetAvg
  have : (h.code.finite.toFinset.card : ℝ)⁻¹ * (315 / 8 : ℝ) = (1 / 4992 : ℝ) := by
    norm_num [hcardR]
  simp [hsum, this]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44Aux
