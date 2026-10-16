-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.DodecadExists
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.DotSupportLite
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.LinearCode
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Puncturing by zeroing coordinates

This file implements the "puncture away a dodecad" step in the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex` (Lemmas `puncture_even` and
`lifts_pinned`).

We work in length `24` throughout: puncturing a set `S` of coordinates is modeled by the map
`eraseCoords S`, which zeroes out coordinates in `S`. The resulting image code `eraseCode S C` and
the embedded even-weight code `evenWeightCode S` are used in the later extraction arguments.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open Set
open scoped BigOperators
open scoped symmDiff

namespace GolayUniquenessSteps.WittDesignUniqueTheory

/-- `eraseCoords S w` is obtained from `w` by zeroing out all coordinates in `S`. -/
@[expose] public def eraseCoords (S : Finset (Fin 24)) (w : BinWord 24) : BinWord 24 :=
  fun i => if i ∈ S then 0 else w i

/-- The image of a code under `eraseCoords S` (an embedded version of puncturing). -/
@[expose] public def eraseCode (S : Finset (Fin 24)) (C : Code 24) : Code 24 :=
  (eraseCoords S) '' C

/-- Predicate asserting that a word is identically `0` on a set of coordinates. -/
@[expose] public def IsZeroOn (S : Finset (Fin 24)) (w : BinWord 24) : Prop :=
  ∀ i : Fin 24, i ∈ S → w i = 0

/-- Words that are zero on `S` and have even weight. -/
@[expose] public def evenWeightCode (S : Finset (Fin 24)) : Code 24 :=
  {w : BinWord 24 | IsZeroOn S w ∧ Even (weight w)}

namespace PunctureEven

open GolayBounds

/-- The linear map corresponding to `eraseCoords S`. -/
@[expose] public def eraseLinear (S : Finset (Fin 24)) : BinWord 24 →ₗ[ZMod 2] BinWord 24 where
  toFun := eraseCoords S
  map_add' := by
    intro x y
    funext i
    by_cases hi : i ∈ S <;> simp [eraseCoords, hi]
  map_smul' := by
    intro a x
    funext i
    by_cases hi : i ∈ S <;> simp [eraseCoords, hi]

@[simp] lemma eraseCoords_apply_mem (S : Finset (Fin 24)) (w : BinWord 24) {i : Fin 24}
    (hi : i ∈ S) : eraseCoords S w i = 0 := by
  simp [eraseCoords, hi]

attribute [grind =] eraseCoords_apply_mem

@[simp] lemma eraseCoords_apply_notMem (S : Finset (Fin 24)) (w : BinWord 24) {i : Fin 24}
    (hi : i ∉ S) : eraseCoords S w i = w i := by
  simp [eraseCoords, hi]

attribute [grind =] eraseCoords_apply_notMem

/-- `eraseCoords S` is additive. -/
public lemma eraseCoords_add (S : Finset (Fin 24)) (x y : BinWord 24) :
    eraseCoords S (x + y) = eraseCoords S x + eraseCoords S y := by
  funext i
  by_cases hi : i ∈ S <;> simp [eraseCoords, hi, Pi.add_apply]

attribute [grind =] eraseCoords_add

lemma isZeroOn_eraseCoords (S : Finset (Fin 24)) (w : BinWord 24) :
    IsZeroOn S (eraseCoords S w) := by
  intro i hi
  simpa using! eraseCoords_apply_mem (S := S) (w := w) hi

/-- The support of `eraseCoords S w` is `support w \\ S`. -/
public lemma support_eraseCoords (S : Finset (Fin 24)) (w : BinWord 24) :
    support (eraseCoords S w) = (support w) \ S := by
  ext i
  by_cases hiS : i ∈ S <;> simp [eraseCoords, hiS, GolayBounds.mem_support]

attribute [grind =] support_eraseCoords

lemma weight_eraseCoords (S : Finset (Fin 24)) (w : BinWord 24) :
    weight (eraseCoords S w) = ((support w) \ S).card := by
  simp [GolayBounds.weight_eq_card_support, support_eraseCoords (S := S) (w := w)]

/-- `eraseCoords S w = 0` if and only if `support w ⊆ S`. -/
public lemma eraseCoords_eq_zero_iff_support_subset (S : Finset (Fin 24)) (w : BinWord 24) :
    eraseCoords S w = 0 ↔ support w ⊆ S := by
  constructor
  · intro h i hi
    by_cases hiS : i ∈ S
    · exact hiS
    · exfalso
      have h0 : w i = 0 := by
        have := congrArg (fun f : BinWord 24 => f i) h
        simpa [eraseCoords, hiS] using! this
      have h1 : w i = 1 := (GolayBounds.mem_support (w := w) i).1 hi
      rw [h0] at h1
      exact zero_ne_one h1
  · intro h
    funext i
    by_cases hiS : i ∈ S
    · simp [eraseCoords, hiS]
    · have hi : i ∉ support w := by
        intro hi'
        exact hiS (h hi')
      have hwi : w i = 0 := GolayBounds.eq_zero_of_not_mem_support (w := w) (i := i) hi
      simp [eraseCoords, hiS, hwi]

attribute [grind =] eraseCoords_eq_zero_iff_support_subset

/-- Erasing on the support of a word produces the zero word. -/
public lemma eraseCoords_support_eq_zero (u : BinWord 24) :
    eraseCoords (support u) u = 0 :=
  (eraseCoords_eq_zero_iff_support_subset (S := support u) (w := u)).2 (by simp)

attribute [grind =] eraseCoords_support_eq_zero

lemma isLinearCode_eraseCode (S : Finset (Fin 24)) (C : Code 24) (hlin : IsLinearCode C) :
    IsLinearCode (eraseCode S C) := by
  constructor
  · refine ⟨0, hlin.1, ?_⟩
    simpa [eraseLinear] using! (eraseLinear (S := S)).map_zero
  · intro x y hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    refine ⟨x' + y', hlin.2 x' y' hx' hy', ?_⟩
    simpa using! (eraseCoords_add (S := S) x' y')

lemma even_weight_eraseCoords_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C) {u c : BinWord 24}
    (huC : u ∈ C) (hcC : c ∈ C) :
    Even (weight (eraseCoords (support u) c)) := by
  have hEven_c : Even (weight c) := by
    have h4 : 4 ∣ weight c := hC.doublyEven hcC
    have h2 : 2 ∣ weight c := dvd_trans (by decide : 2 ∣ 4) h4
    exact (Nat.even_iff).2 (Nat.mod_eq_zero_of_dvd h2)
  have hEven_inter : Even (support c ∩ support u).card := by
    have hdot : dot (n := 24) c u = 0 := hC.selfOrth hcC huC
    exact (DotSupportLite.dot_eq_zero_iff_even_card_support_inter (w₁ := c) (w₂ := u)).1 hdot
  have hle : (support c ∩ support u).card ≤ (support c).card :=
    Finset.card_le_card (Finset.inter_subset_left (s₁ := support c) (s₂ := support u))
  have hdiff :
      Even ((support c).card - (support c ∩ support u).card) := by
    have hm : Even (support c).card := by
      simpa [GolayBounds.weight_eq_card_support] using! hEven_c
    have hn : Even (support c ∩ support u).card := hEven_inter
    have : Even (support c).card ↔ Even (support c ∩ support u).card :=
      ⟨fun _ => hn, fun _ => hm⟩
    exact (Nat.even_sub hle).2 this
  have : weight (eraseCoords (support u) c) = (support c \ support u).card := by
    simp [weight_eraseCoords]
  -- `card (supp c \\ supp u) = card(supp c) - card(supp c ∩ supp u)`
  simpa [this, Finset.card_sdiff, Finset.inter_comm] using! hdiff

lemma nonzero_of_weight_eq {w : BinWord 24} (hw : weight w = 12) : w ≠ 0 := by
  intro h0
  have hw0 : weight w = 0 := by simp [h0, weight]
  have : (12 : Nat) = 0 := hw.symm.trans hw0
  exact (by decide : (12 : Nat) ≠ 0) this

lemma hammingDist_zero_right {w : BinWord 24} : hammingDist (0 : BinWord 24) w = weight w := by
  simp [hammingDist, zero_add]

attribute [grind =] hammingDist_zero_right

/-- In a code with `minDist ≥ 8`, any nonzero word has weight at least `8`. -/
public lemma weight_ge_minDist_of_mem
    (C : Code 24) (hmin : 8 ≤ minDist C) {w : BinWord 24}
    (h0C : (0 : BinWord 24) ∈ C) (hwC : w ∈ C) (hw0 : w ≠ 0) :
    8 ≤ weight w := by
  have hdist_ge :=
    GolayBounds.hammingDist_ge_of_minDist_ge (C := C) (d := 8) hmin h0C hwC (by
      intro hEq
      exact hw0 hEq.symm)
  simpa [hammingDist_zero_right] using! hdist_ge

lemma support_symmDiff_eq_sdiff_of_subset
    {s t : Finset (Fin 24)} (h : t ⊆ s) : s ∆ t = s \ t := by
  ext i
  grind (splits := 1) only [Finset.mem_symmDiff, Finset.mem_sdiff, = Finset.subset_iff]

attribute [grind =] support_symmDiff_eq_sdiff_of_subset

lemma support_add_eq_sdiff_of_support_subset
    (u x : BinWord 24) (h : support x ⊆ support u) :
    support (fun i => u i + x i) = support u \ support x := by
  have hsupp : support (fun i => u i + x i) = support u ∆ support x := by
    change support (u + x) = support u ∆ support x
    simpa using! (GolayBounds.support_add_eq_symmDiff (w₁ := u) (w₂ := x))
  have hsdiff : support u ∆ support x = support u \ support x := by
    simpa using! (support_symmDiff_eq_sdiff_of_subset (s := support u) (t := support x) h)
  exact hsupp.trans hsdiff

/--
If `support x ⊆ support u`, with `weight u = 12` and `weight x ≥ 8`, then
`weight (u + x) ≤ 4`.
-/
public lemma weight_add_le_four_of_support_subset
    (u x : BinWord 24) (hsupp : support x ⊆ support u)
    (hu : weight u = 12) (hx : 8 ≤ weight x) :
    weight (u + x) ≤ 4 := by
  have hsupp' : support (u + x) = support u \ support x := by
    simpa [Pi.add_apply] using! (support_add_eq_sdiff_of_support_subset u x hsupp)
  have hwt : weight (u + x) = (support u \ support x).card := by
    simp [GolayBounds.weight_eq_card_support, hsupp']
  have hu_card : (support u).card = 12 := by
    simpa [GolayBounds.weight_eq_card_support] using! hu
  have hx_card_ge : 8 ≤ (support x).card := by
    simpa [GolayBounds.weight_eq_card_support] using! hx
  have hsdiff : (support u \ support x).card = (support u).card - (support x).card := by
    simpa using! Finset.card_sdiff_of_subset (s := support x) (t := support u) hsupp
  have hsub :
      (support u).card - (support x).card ≤ (support u).card - 8 :=
    Nat.sub_le_sub_left hx_card_ge (support u).card
  simp_all

theorem ncard_eraseCode_support_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C)
    {u : BinWord 24} (huC : u ∈ C) (hwt : weight u = 12) :
    (eraseCode (support u) C).ncard = 2 ^ 11 := by
  let U : Submodule (ZMod 2) (BinWord 24) := LinearCode.submodule (n := 24) C hC.linear
  let f : BinWord 24 →ₗ[ZMod 2] BinWord 24 := eraseLinear (support u)
  let g : U →ₗ[ZMod 2] BinWord 24 := f.domRestrict U
  have hUcard : Nat.card U = 2 ^ 12 := by
    calc
      Nat.card U = Nat.card (C : Set (BinWord 24)) := rfl
      _ = (C : Set (BinWord 24)).ncard := (Nat.card_coe_set_eq (C : Set (BinWord 24)))
      _ = 2 ^ 12 := hC.card_eq
  -- kernel of `g` is `{0,u}`
  have hker :
      ((LinearMap.ker g : Submodule (ZMod 2) U) : Set U) = {0, (⟨u, huC⟩ : U)} := by
    ext x
    constructor
    · intro hx
      have hx0 : eraseCoords (support u) (x : BinWord 24) = 0 := by
        simpa [g, f, eraseLinear] using! (show g x = 0 from hx)
      have hsupp : support (x : BinWord 24) ⊆ support u :=
        (eraseCoords_eq_zero_iff_support_subset (S := support u) (x : BinWord 24)).1 hx0
      by_cases hxz : (x : BinWord 24) = 0
      · left
        apply Subtype.ext
        simpa using! hxz
      · right
        -- `x` is supported in `supp u`; show `x = u` using `d(C)=8`.
        have hmin : 8 ≤ minDist C := hC.minDist_ge
        have hxwt_ge : 8 ≤ weight (x : BinWord 24) :=
          weight_ge_minDist_of_mem (C := C) hmin hC.linear.1 x.2 hxz
        -- weight of `u + x` is `12 - weight x`, hence ≤ 4
        let y : BinWord 24 := fun i => u i + (x : BinWord 24) i
        have hyC : y ∈ C := hC.linear.2 u (x : BinWord 24) huC x.2
        have hywt_le4 : weight y ≤ 4 := by
          have : weight (u + (x : BinWord 24)) ≤ 4 :=
            weight_add_le_four_of_support_subset u (x : BinWord 24) hsupp hwt hxwt_ge
          simpa [y, Pi.add_apply] using! this
        by_cases hy0 : y = 0
        · -- then `x = u`
          have hx_eq_u : (x : BinWord 24) = u := by
            have : u + (x : BinWord 24) = 0 := by
              simpa [y, Pi.add_apply] using! hy0
            exact ((binWord_add_eq_zero_iff_eq (u := u) (v := (x : BinWord 24))).1 this).symm
          exact Subtype.ext hx_eq_u
        · -- contradiction with `minDist ≥ 8`
          have hywt_ge : 8 ≤ weight y :=
            weight_ge_minDist_of_mem (C := C) hmin hC.linear.1 hyC hy0
          exact False.elim ((not_lt_of_ge hywt_ge) (lt_of_le_of_lt hywt_le4 (by decide)))
    · intro hx
      rcases hx with hx | hx
      · subst hx
        simp [g]
      · -- `x = u`
        have hx' : x = (⟨u, huC⟩ : U) := by simpa using! hx
        subst hx'
        simpa [g, f, eraseLinear] using! (eraseCoords_support_eq_zero (u := u))
  have hker_card : Nat.card (LinearMap.ker g) = 2 := by
    have hne : (0 : U) ≠ (⟨u, huC⟩ : U) := by
      intro hEq
      have : (u : BinWord 24) = 0 := by
        simpa using! congrArg (fun z : U => (z : BinWord 24)) hEq.symm
      exact nonzero_of_weight_eq hwt this
    have hker_ncard : ((LinearMap.ker g : Submodule (ZMod 2) U) : Set U).ncard = 2 := by
      simpa [hker] using! (Set.ncard_pair hne)
    -- convert `ncard` to `Nat.card`
    assumption
  -- card of the quotient is `2^11`
  have hquot_card : Nat.card (U ⧸ LinearMap.ker g) = 2 ^ 11 := by
    open scoped Classical in
    have hmulF :
        Fintype.card U =
          Fintype.card { x : U // g x = 0 } * Fintype.card (U ⧸ LinearMap.ker g) := by
      simpa [Nat.card_eq_fintype_card] using!
        (Submodule.card_eq_card_quotient_mul_card (S := LinearMap.ker g) (M := U))
    have hUcardF : Fintype.card U = 2 ^ 12 := by simpa [Nat.card_eq_fintype_card] using! hUcard
    have hkerF : Fintype.card { x : U // g x = 0 } = 2 := by
      simpa [Nat.card_eq_fintype_card] using! hker_card
    have hmul' : Fintype.card (U ⧸ LinearMap.ker g) * 2 = 2 ^ 12 := by
      have hmul0 :
          2 ^ 12 =
            Fintype.card { x : U // g x = 0 } * Fintype.card (U ⧸ LinearMap.ker g) := by
        simpa [hUcardF] using! hmulF
      have hmul1 : 2 ^ 12 = 2 * Fintype.card (U ⧸ LinearMap.ker g) := by
        simpa [hkerF] using! hmul0
      have : 2 * Fintype.card (U ⧸ LinearMap.ker g) = 2 ^ 12 := by simpa using! hmul1.symm
      simpa [Nat.mul_comm] using! this
    have hpow : 2 ^ 11 * 2 = 2 ^ 12 := by simp [pow_succ]
    have : Fintype.card (U ⧸ LinearMap.ker g) * 2 = 2 ^ 11 * 2 := by
      simpa [hpow] using! hmul'
    have : Fintype.card (U ⧸ LinearMap.ker g) = 2 ^ 11 :=
      Nat.mul_right_cancel (by decide : 0 < 2) this
    simpa [Nat.card_eq_fintype_card] using! this
  have hrange_card : Nat.card (LinearMap.range g) = 2 ^ 11 := by
    have hEq :
        Nat.card (LinearMap.range g) = Nat.card (U ⧸ LinearMap.ker g) :=
      (Nat.card_congr (g.quotKerEquivRange.toEquiv)).symm
    exact hEq.trans hquot_card
  have hrange_set : (LinearMap.range g : Set (BinWord 24)) = eraseCode (support u) C := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : BinWord 24), x.2, rfl⟩
    · rintro ⟨c, hcC, rfl⟩
      exact ⟨⟨c, hcC⟩, rfl⟩
  -- finish by rewriting `ncard` as `Nat.card` of the corresponding subtype
  calc
    (eraseCode (support u) C).ncard = Nat.card (eraseCode (support u) C : Set (BinWord 24)) :=
      (Nat.card_coe_set_eq (eraseCode (support u) C : Set (BinWord 24))).symm
    _ = Nat.card (LinearMap.range g : Set (BinWord 24)) := by simp [hrange_set]
    _ = Nat.card (LinearMap.range g) := rfl
    _ = 2 ^ 11 := hrange_card

def onesWord : BinWord 24 := fun _ => 1

lemma support_onesWord : support onesWord = (Finset.univ : Finset (Fin 24)) := by
  ext i
  simp [onesWord, support]

lemma even_weight_iff_dot_onesWord_eq_zero (w : BinWord 24) :
    Even (weight w) ↔ dot (n := 24) w onesWord = 0 := by
  -- `dot w ones = 0` ↔ `Even |supp w ∩ supp ones|` ↔ `Even |supp w|`
  have hdot :
      dot (n := 24) w onesWord = 0 ↔ Even (support w).card := by
    have : dot (n := 24) w onesWord = 0 ↔ Even (support w ∩ support onesWord).card :=
      (DotSupportLite.dot_eq_zero_iff_even_card_support_inter (w₁ := w) (w₂ := onesWord))
    simpa [support_onesWord, Finset.inter_univ] using! this
  -- rewrite `weight` as `card support`
  simpa [GolayBounds.weight_eq_card_support] using! hdot.symm

theorem ncard_evenWeightCode_of_card12 (S : Finset (Fin 24)) (hS : S.card = 12) :
    (evenWeightCode S).ncard = 2 ^ 11 := by
  let Z : Set (BinWord 24) := {w : BinWord 24 | IsZeroOn S w}
  let E : Set (BinWord 24) := {w : BinWord 24 | IsZeroOn S w ∧ dot (n := 24) w onesWord = 0}
  let O : Set (BinWord 24) := {w : BinWord 24 | IsZeroOn S w ∧ dot (n := 24) w onesWord = 1}
  have hE : (evenWeightCode S) = E := by
    ext w
    simp [evenWeightCode, E, even_weight_iff_dot_onesWord_eq_zero]
  have hZ_union : Z = E ∪ O := by
    ext w
    simp [Z, E, O]
    have hd : dot (n := 24) w onesWord = 0 ∨ dot (n := 24) w onesWord = 1 :=
      GolayBounds.zmod2_eq_zero_or_eq_one (dot (n := 24) w onesWord)
    grind (splits := 2)
  have hdisj : Disjoint E O := by
    refine Set.disjoint_left.2 ?_
    intro w hwE hwO
    have : (0 : ZMod 2) = 1 := by simpa [hwE.2] using! hwO.2
    exact (zero_ne_one (α := ZMod 2)) this
  -- count `Z` by identifying it with functions on the complement of `S`
  let T : Type := {i : Fin 24 // i ∉ S}
  have hT : Fintype.card T = 12 := by
    have hcomp :
        Fintype.card T =
          Fintype.card (Fin 24) - Fintype.card {i : Fin 24 // i ∈ S} := by
      simp [T, Fintype.card_subtype_compl]
    have hmem : Fintype.card {i : Fin 24 // i ∈ S} = S.card := by
      -- the type `{i // i ∈ S}` is definitional equal to the finset-as-type `S`
      exact Fintype.card_coe S
    simp [hcomp, hmem, hS]
  let equivZ : Z ≃ (T → ZMod 2) :=
    { toFun := fun w i => (w : BinWord 24) i
      invFun := fun f =>
        ⟨fun i => if hi : i ∈ S then 0 else f ⟨i, hi⟩, by
          intro i hi
          simp [hi]⟩
      left_inv := by
        intro w
        ext i
        by_cases hi : i ∈ S
        · have := w.2 i hi
          simp [hi, this]
        · simp [hi]
      right_inv := by
        intro f
        funext i
        cases i with
        | mk i hi =>
          simp [hi] }
  have hZcard : Z.ncard = 2 ^ 12 := by
    have hcard : Nat.card Z = Nat.card (T → ZMod 2) := Nat.card_congr equivZ
    calc
      Z.ncard = Nat.card Z :=
        (Nat.card_coe_set_eq Z).symm
      _ = Nat.card (T → ZMod 2) := hcard
      _ = 2 ^ 12 := by
            simp [Nat.card_eq_fintype_card, hT]
  -- toggle map: add the basis vector at some `q ∉ S`
  have hTpos : 0 < Fintype.card T := by
    simp [hT]
  let q : T := Classical.choice (Fintype.card_pos_iff.1 hTpos)
  let basis : BinWord 24 := fun i => if i = q.1 then 1 else 0
  let toggle : BinWord 24 → BinWord 24 := fun w i => w i + basis i
  have htoggle_invol : Function.Involutive toggle := by
    intro w
    funext i
    simp [toggle, add_assoc, GolayBounds.zmod2_add_self]
  have htoggle_inj : Function.Injective toggle := htoggle_invol.injective
  have htoggle_zeroOn : ∀ {w}, IsZeroOn S w → IsZeroOn S (toggle w) := by
    intro w hw0 i hi
    have : i ≠ q.1 := by
      intro hEq
      exact q.2 (hEq ▸ hi)
    simp [toggle, basis, hw0 i hi, this]
  have hbasis_dot : dot (n := 24) basis onesWord = 1 := by
    have hb : support basis = {q.1} := by
      ext i
      by_cases hiq : i = q.1 <;> simp [basis, GolayBounds.mem_support, hiq]
    -- `dot w ones = card(support w)` for `w= basis`, and `support basis = {q.1}`.
    simpa [hb, support_onesWord] using!
      (DotSupportLite.dot_eq_card_support_inter (w₁ := basis) (w₂ := onesWord))
  have htoggle_maps_EO : toggle '' E ⊆ O := by
    rintro w ⟨x, hxE, rfl⟩
    refine ⟨htoggle_zeroOn hxE.1, ?_⟩
    have : dot (n := 24) (toggle x) onesWord =
        dot (n := 24) x onesWord + dot (n := 24) basis onesWord := by
      simpa [toggle] using! (dot_add_left (n := 24) (x₁ := x) (x₂ := basis) (y := onesWord))
    simp [this, hxE.2, hbasis_dot]
  have htoggle_maps_OE : toggle '' O ⊆ E := by
    rintro w ⟨x, hxO, rfl⟩
    refine ⟨htoggle_zeroOn hxO.1, ?_⟩
    have : dot (n := 24) (toggle x) onesWord =
        dot (n := 24) x onesWord + dot (n := 24) basis onesWord := by
      simpa [toggle] using! (dot_add_left (n := 24) (x₁ := x) (x₂ := basis) (y := onesWord))
    simp [this, hxO.2, hbasis_dot]
  have hEcard_eq : E.ncard = O.ncard := by
    have hE_le : E.ncard ≤ O.ncard := by
      simpa [Set.ncard_image_of_injective (s := E) htoggle_inj] using!
        (Set.ncard_le_ncard htoggle_maps_EO (by toFinite_tac))
    have hO_le : O.ncard ≤ E.ncard := by
      simpa [Set.ncard_image_of_injective (s := O) htoggle_inj] using!
        (Set.ncard_le_ncard htoggle_maps_OE (by toFinite_tac))
    exact le_antisymm hE_le hO_le
  have hZ_ncard : Z.ncard = E.ncard + O.ncard := by
    simpa [hZ_union] using! (Set.ncard_union_eq hdisj (by toFinite_tac) (by toFinite_tac))
  -- solve for `E.ncard`
  have hmul : E.ncard * 2 = 2 ^ 12 := by
    have : 2 * E.ncard = 2 ^ 12 := by
      -- `Z.ncard = E.ncard + O.ncard = 2 * E.ncard`
      calc
        2 * E.ncard = E.ncard + E.ncard := by simp [two_mul]
        _ = E.ncard + O.ncard := by simp [hEcard_eq]
        _ = Z.ncard := by simp [hZ_ncard]
        _ = 2 ^ 12 := hZcard
    simpa [Nat.mul_comm] using! this
  have hpow : 2 ^ 11 * 2 = 2 ^ 12 := by simp [pow_succ]
  have : E.ncard * 2 = 2 ^ 11 * 2 := by simpa [hpow] using! hmul
  have hEfinal : E.ncard = 2 ^ 11 := Nat.mul_right_cancel (by decide : 0 < 2) this
  -- translate back to `evenWeightCode`
  simp [hE, E, hEfinal]

end PunctureEven

/-- For a sharp code, erasing on a dodecad support produces an even-weight codeword. -/
public theorem eraseCode_subset_evenWeightCode_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C)
    {u : BinWord 24} (huC : u ∈ C) :
    eraseCode (support u) C ⊆ evenWeightCode (support u) := by
  intro w hw
  rcases hw with ⟨c, hcC, rfl⟩
  refine ⟨PunctureEven.isZeroOn_eraseCoords (S := support u) c, ?_⟩
  exact PunctureEven.even_weight_eraseCoords_of_sharp (C := C) hC (u := u) (c := c) huC hcC

/--
For a sharp code, erasing on a dodecad support produces exactly the embedded even-weight
code.
-/
public theorem eraseCode_eq_evenWeightCode_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C)
    {u : BinWord 24} (huC : u ∈ C) (hwt : weight u = 12) :
    eraseCode (support u) C = evenWeightCode (support u) := by
  refine Set.eq_of_subset_of_ncard_le (eraseCode_subset_evenWeightCode_of_sharp (C := C) hC huC)
    ?_
  have hsupp : (support u).card = 12 := by
    simpa [GolayBounds.weight_eq_card_support] using! hwt
  have hcardErase : (eraseCode (support u) C).ncard = 2 ^ 11 :=
    PunctureEven.ncard_eraseCode_support_of_sharp (C := C) hC huC hwt
  have hcardEven : (evenWeightCode (support u)).ncard = 2 ^ 11 :=
    PunctureEven.ncard_evenWeightCode_of_card12 (S := support u) hsupp
  simp [hcardErase, hcardEven]

def pinnedHyperplaneSubmodule (C : Code 24) (hlin : IsLinearCode C) (p : Fin 24) :
    Submodule (ZMod 2) (BinWord 24) :=
  (LinearCode.submodule (n := 24) C hlin) ⊓ LinearMap.ker (LinearMap.proj p)

theorem pinnedHyperplane_eraseCoords_isEquiv_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C)
    {u : BinWord 24} (huC : u ∈ C) (hwt : weight u = 12)
    {p : Fin 24} (hp : p ∈ support u) :
    Nonempty
      ((pinnedHyperplaneSubmodule (C := C) hC.linear p) ≃ₗ[ZMod 2]
        (LinearCode.submodule (n := 24) (eraseCode (support u) C)
          (PunctureEven.isLinearCode_eraseCode (S := support u) (C := C) hC.linear))) := by
  let S : Finset (Fin 24) := support u
  let Hp : Submodule (ZMod 2) (BinWord 24) := pinnedHyperplaneSubmodule (C := C) hC.linear p
  let V : Submodule (ZMod 2) (BinWord 24) :=
    LinearCode.submodule (n := 24) (eraseCode S C)
      (PunctureEven.isLinearCode_eraseCode (S := S) (C := C) hC.linear)
  let f : BinWord 24 →ₗ[ZMod 2] BinWord 24 := PunctureEven.eraseLinear S
  let g : Hp →ₗ[ZMod 2] V :=
    (f.domRestrict Hp).codRestrict V (by
      intro x
      refine ⟨(x : BinWord 24), ?_, rfl⟩
      simpa using! x.2.1)
  have hu_p : u p = 1 := (GolayBounds.mem_support (w := u) p).1 hp
  have hfu : f u = 0 := by
    -- `f` is `eraseCoords S` and `S = supp u`.
    simpa [f, S, PunctureEven.eraseLinear] using! (PunctureEven.eraseCoords_support_eq_zero (u := u))
  have hker : ∀ d : Hp, g d = 0 → d = 0 := by
    intro d hd
    have hd0 : f d.1 = 0 := by
      -- `g` is a `codRestrict` of `f` so we can compare values in `BinWord 24`.
      exact congrArg (fun z : V => (z : BinWord 24)) hd
    have hdz0 : eraseCoords S d.1 = 0 := by
      simpa [f, PunctureEven.eraseLinear] using! hd0
    have hsupp : support d.1 ⊆ support u := by
      -- `S = supp u`
      simpa [S] using!
        (PunctureEven.eraseCoords_eq_zero_iff_support_subset (S := support u) d.1).1 hdz0
    have hdC : d.1 ∈ C := by
      simpa using! d.2.1
    have hdp0 : d.1 p = 0 := by
      have : (LinearMap.proj p : BinWord 24 →ₗ[ZMod 2] ZMod 2) d.1 = 0 := d.2.2
      simpa using! this
    by_cases hdword0 : d.1 = 0
    · apply Subtype.ext
      simp [hdword0]
    · -- otherwise, contradict `d(C)=8` as in BS81 Lemma `lifts_pinned`
      have hmin : 8 ≤ minDist C := hC.minDist_ge
      have hdwt_ge : 8 ≤ weight d.1 :=
        PunctureEven.weight_ge_minDist_of_mem (C := C) hmin hC.linear.1 hdC hdword0
      let z : BinWord 24 := u + d.1
      have hzC : z ∈ C := hC.linear.2 u d.1 huC hdC
      have hzwt_le4 : weight z ≤ 4 :=
        PunctureEven.weight_add_le_four_of_support_subset u (↑d) hsupp hwt hdwt_ge
      have hFalse : False := by
        by_cases hz0 : z = 0
        · have hd_eq_u : d.1 = u := by
            have : u + d.1 = 0 := by simpa [z] using! hz0
            have hd' := (GolayBounds.binWord_add_eq_zero_iff_eq (u := u) (v := d.1)).1 this
            simpa using! hd'.symm
          have hup0 : u p = 0 := by simpa [hd_eq_u] using! hdp0
          simp [hu_p] at hup0
        · have hzwt_ge : 8 ≤ weight z :=
            PunctureEven.weight_ge_minDist_of_mem (C := C) hmin hC.linear.1 hzC hz0
          exact (not_lt_of_ge hzwt_ge (lt_of_le_of_lt hzwt_le4 (by decide)))
      exact False.elim hFalse
  have hinj : Function.Injective g :=
    (injective_iff_map_eq_zero g).mpr hker
  have hsurj : Function.Surjective g := by
    intro y
    rcases (show (y : BinWord 24) ∈ eraseCode S C from y.2) with ⟨c, hcC, hcy⟩
    rcases GolayBounds.zmod2_eq_zero_or_eq_one (c p) with hcp0 | hcp1
    · refine ⟨⟨c, ?_⟩, ?_⟩
      · refine ⟨hcC, ?_⟩
        -- `c ∈ ker(proj p)` because `c p = 0`.
        change (LinearMap.proj p : BinWord 24 →ₗ[ZMod 2] ZMod 2) c = 0
        simpa using! hcp0
      · apply Subtype.ext
        -- `g c = eraseCoords S c = y`
        simpa [g, f, PunctureEven.eraseLinear] using! hcy
    · -- flip by adding `u` to pin the coordinate
      let c' : BinWord 24 := c + u
      have hc'C : c' ∈ C := hC.linear.2 c u hcC huC
      refine ⟨⟨c', ?_⟩, ?_⟩
      · refine ⟨hc'C, ?_⟩
        change (LinearMap.proj p : BinWord 24 →ₗ[ZMod 2] ZMod 2) c' = 0
        -- pointwise: `c' p = c p + u p = 1 + 1 = 0`
        simp [c', hcp1, hu_p, LinearMap.proj, GolayBounds.zmod2_add_self]
      · apply Subtype.ext
        have hErU : eraseCoords S u = 0 := by
          simpa [f, PunctureEven.eraseLinear] using! hfu
        have hadd : eraseCoords S (c + u) = eraseCoords S c + eraseCoords S u := by
          simpa using! PunctureEven.eraseCoords_add (S := S) c u
        have : eraseCoords S c' = eraseCoords S c := by
          calc
            eraseCoords S c' = eraseCoords S (c + u) := by simp [c']
            _ = eraseCoords S c + eraseCoords S u := hadd
            _ = eraseCoords S c := by simp [hErU]
        -- `g c' = eraseCoords S c' = eraseCoords S c = y`
        have hcy' : eraseCoords S c' = (y : BinWord 24) := by simpa [this] using! hcy
        simpa [g, f, PunctureEven.eraseLinear] using! hcy'
  refine ⟨LinearEquiv.ofBijective g ⟨hinj, hsurj⟩⟩

end GolayUniquenessSteps.WittDesignUniqueTheory
end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
