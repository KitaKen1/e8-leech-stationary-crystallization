-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeFromLattice
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeBounds.WeightLowerBound
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeMinDist
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeCardBound
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4Constraints
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.Shell4
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16.MinNorm
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionA
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Isometry.Types
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.BasepointInjection
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.ScaledCoord
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Set.Card

/-!
# Counting forces the Golay parameters

This file formalizes the counting step in BS81 Lemma 21: the shell size `|L₄| = 196560` forces the
extracted code `codeFromLattice` to have the Golay parameters.

We prove the forcing inequality
`|L₄| ≤ 1104 + 2^7 * N₈ + 24 * |𝒞|`,
and combine it with the bounds `N₈ ≤ 759` and `|𝒞| ≤ 2^12` to deduce the equalities
`N₈ = 759`, `|𝒞| = 2^12`, and `minDist 𝒞 = 8`.

## Main statement
* `CodeIsGolayCountFinal.forcing_parameters_codeFromLattice`

## References
`paper/Notes/CodingTheory/bs81_lemma21_golay_inputs.tex`, Theorem `thm:count_forces_parameters`.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Set
open Finset

open Uniqueness.BS81
open Uniqueness.BS81.CodingTheory
open Uniqueness.BS81.Thm15.Lemma21

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace CodeIsGolayCountFinal

local notation "shell4" => Uniqueness.BS81.latticeShell4
local notation "code" => CodeFromLattice.codeFromLattice

lemma zmod2_intCast_neg_one : ((-1 : ℤ) : ZMod 2) = (1 : ZMod 2) := by
  decide

attribute [simp] zmod2_intCast_neg_one

lemma zmod2_int_div2_eq_zero_of_eq_zero {z : ℤ} (hz : z = 0) :
    ((z / 2 : ℤ) : ZMod 2) = 0 := by
  subst hz
  simp

lemma zmod2_int_div2_eq_one_of_eq_two {z : ℤ} (hz : z = 2) :
    ((z / 2 : ℤ) : ZMod 2) = 1 := by
  subst hz
  simp

lemma zmod2_int_div2_eq_one_of_eq_neg_two {z : ℤ} (hz : z = -2) :
    ((z / 2 : ℤ) : ZMod 2) = 1 := by
  subst hz
  simp

lemma fintypeCard_subtype_eq_card_univ_filter {α : Type} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    Fintype.card {a : α // p a} = (Finset.univ.filter p).card :=
  Fintype.card_subtype p

/-!
## `scaledCoord` determines a vector
-/

/-!
## Shell-4 size
-/

/-- In the equality case, the shell `shell4 C` has cardinality `196560`. -/
public lemma ncard_shell4_eq_196560
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    Set.ncard (shell4 C) = 196560 := by
  have hshell : shell4 C = Uniqueness.BS81.twoCodeVectors C :=
    Uniqueness.BS81.Thm15.Lemma17.shell4_eq_twoCodeVectors (C := C) hEq
  calc
    Set.ncard (shell4 C) = Set.ncard (Uniqueness.BS81.twoCodeVectors C) := by
      simp [hshell]
    _ = Set.ncard C := Uniqueness.BS81.ncard_twoCodeVectors_eq C
    _ = 196560 := hEq.card_eq

lemma shell4_finite (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    (shell4 C).Finite := by
  have hshell' : shell4 C = Uniqueness.BS81.twoCodeVectors C :=
    Uniqueness.BS81.Thm15.Lemma17.shell4_eq_twoCodeVectors (C := C) hEq
  have hfin : (Uniqueness.BS81.twoCodeVectors C).Finite :=
    Uniqueness.BS81.twoCodeVectors_finite (C := C) hEq.code.finite
  simpa [hshell'] using! hfin

lemma shell4_nonempty
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    (shell4 C).Nonempty := by
  have hpos : 0 < Set.ncard (shell4 C) := by
    rw [ncard_shell4_eq_196560 (C := C) hEq]
    decide
  exact (Set.ncard_pos (s := shell4 C) (shell4_finite (C := C) hEq)).1 hpos

/-!
## Pattern subclasses of the shell
-/

lemma card_filter_eq_zero_of_isPattern1 {z : Fin 24 → ℤ} (hz : isPattern1 z) :
    (Finset.univ.filter fun i : Fin 24 => z i = 0).card = 16 := by
  have hzerosCard : Fintype.card {i : Fin 24 // z i = 0} = 16 := by
    calc
      Fintype.card {i : Fin 24 // z i = 0} = #{i : Fin 24 | z i = 0} := by
        simpa using! (Fintype.card_subtype (α := Fin 24) (p := fun i : Fin 24 => z i = 0))
      _ = 16 := hz.1
  exact
    (fintypeCard_subtype_eq_card_univ_filter (p := fun i : Fin 24 => z i = 0)).symm.trans
      hzerosCard

lemma card_filter_ne_zero_of_isPattern1 {z : Fin 24 → ℤ} (hz : isPattern1 z) :
    (Finset.univ.filter fun i : Fin 24 => z i ≠ 0).card = 8 := by
  have hzeros' : (Finset.univ.filter fun i : Fin 24 => z i = 0).card = 16 :=
    card_filter_eq_zero_of_isPattern1 hz
  have hsplit :
      (Finset.univ.filter fun i : Fin 24 => z i = 0).card +
          (Finset.univ.filter fun i : Fin 24 => z i ≠ 0).card = 24 := by
    simpa using!
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 24)))
        (p := fun i : Fin 24 => z i = 0))
  have := Nat.eq_sub_of_add_eq' hsplit
  simpa [hzeros'] using! this

private lemma weight_intDiv2_of_isPattern1 {z : Fin 24 → ℤ} (hz : isPattern1 z) :
    weight (fun i : Fin 24 => ((z i / 2 : ℤ) : ZMod 2)) = 8 := by
  let c : BinWord 24 := fun i : Fin 24 => ((z i / 2 : ℤ) : ZMod 2)
  have hci : ∀ i : Fin 24, c i = 1 ↔ z i ≠ 0 := by
    intro i
    rcases hz.2 i with h0 | h2 | hN2
    · simp [c, h0]
    · simp [c, h2]
    · simp [c, hN2]
  have :
      (Finset.univ.filter fun i : Fin 24 => c i = 1) =
        (Finset.univ.filter fun i : Fin 24 => z i ≠ 0) := by
    ext i
    simp [hci i]
  simpa [CodingTheory.weight, c, this] using! (card_filter_ne_zero_of_isPattern1 hz)

lemma card_filter_eq_zero_of_isPattern2 {z : Fin 24 → ℤ} (hz : isPattern2 z) :
    (Finset.univ.filter fun i : Fin 24 => z i = 0).card = 22 := by
  have hzerosCard : Fintype.card {i : Fin 24 // z i = 0} = 22 := by
    calc
      Fintype.card {i : Fin 24 // z i = 0} = #{i : Fin 24 | z i = 0} := by
        simpa using! (Fintype.card_subtype (α := Fin 24) (p := fun i : Fin 24 => z i = 0))
      _ = 22 := hz.1
  exact
    (fintypeCard_subtype_eq_card_univ_filter (p := fun i : Fin 24 => z i = 0)).symm.trans
      hzerosCard

lemma card_filter_ne_zero_of_isPattern2 {z : Fin 24 → ℤ} (hz : isPattern2 z) :
    (Finset.univ.filter fun i : Fin 24 => z i ≠ 0).card = 2 := by
  have hzeros' : (Finset.univ.filter fun i : Fin 24 => z i = 0).card = 22 :=
    card_filter_eq_zero_of_isPattern2 hz
  have hsplit :
      (Finset.univ.filter fun i : Fin 24 => z i = 0).card +
          (Finset.univ.filter fun i : Fin 24 => z i ≠ 0).card = 24 := by
    simpa using!
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 24)))
        (p := fun i : Fin 24 => z i = 0))
  have := Nat.eq_sub_of_add_eq' hsplit
  simpa [hzeros'] using! this

/-- Every shell vector is of type I, II, or III, according to its integer-coordinate pattern. -/
public lemma shell4_subset_TypeI_union_TypeII_union_TypeIII
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    shell4 C ⊆ TypeI (C := C) hDn ∪ TypeII (C := C) hDn ∪ TypeIII (C := C) hDn := by
  intro u hu
  rcases shell4_patterns (C := C) (hEq := hEq) (hDn := hDn) hu with
    ⟨z, hzCoord, _hpar, _hsumsq, hpat⟩
  rcases hpat with h1 | h2 | h3
  · -- `TypeII`
    exact Or.inl (Or.inr ⟨hu, z, hzCoord, h1⟩)
  · -- `TypeI`
    exact Or.inl (Or.inl ⟨hu, z, hzCoord, h2⟩)
  · -- `TypeIII`
    exact Or.inr ⟨hu, z, hzCoord, h3⟩

/-!
## Type I bound: `|TypeI| ≤ 1104`
-/

def pairLT : Finset (Fin 24 × Fin 24) :=
  ((Finset.univ : Finset (Fin 24)).product Finset.univ).filter fun p => p.1 < p.2

lemma card_pairLT : pairLT.card = 276 := by
  let t : Fin 24 → Finset (Fin 24 × Fin 24) := fun i =>
    (Finset.Ioi i).image fun j => (i, j)
  have hpairLT : pairLT = (Finset.univ : Finset (Fin 24)).biUnion t := by
    ext p
    rcases p with ⟨i, j⟩
    constructor
    · intro hp
      have hij : i < j := by
        simpa [pairLT] using! (Finset.mem_filter.1 hp).2
      refine Finset.mem_biUnion.2 ?_
      refine ⟨i, by simp, ?_⟩
      refine Finset.mem_image.2 ?_
      refine ⟨j, ?_, rfl⟩
      simpa [Finset.mem_Ioi] using! hij
    · intro hp
      rcases Finset.mem_biUnion.1 hp with ⟨i, _hi, hp⟩
      rcases Finset.mem_image.1 hp with ⟨j, hj, hpEq⟩
      cases hpEq
      have hij : i < j := by
        simpa [Finset.mem_Ioi] using! hj
      simp [pairLT, hij]
  have hdisj : ((Finset.univ : Finset (Fin 24)) : Set (Fin 24)).PairwiseDisjoint t := by
    intro i _hi j _hj hij
    refine Finset.disjoint_left.2 ?_
    intro x hxi hxj
    rcases Finset.mem_image.1 hxi with ⟨a, _ha, rfl⟩
    rcases Finset.mem_image.1 hxj with ⟨b, _hb, hEq⟩
    have : i = j :=
      (congrArg Prod.fst hEq).symm
    exact hij this
  have ht_card : ∀ i : Fin 24, (t i).card = (Finset.Ioi i).card := by
    intro i
    have hinj : Function.Injective (fun j : Fin 24 => (i, j)) := by
      intro a b hab
      exact congrArg Prod.snd hab
    simpa [t] using!
      (Finset.card_image_of_injective (s := Finset.Ioi i) (f := fun j => (i, j)) hinj)
  calc
    pairLT.card = ((Finset.univ : Finset (Fin 24)).biUnion t).card := by simp [hpairLT]
    _ = ∑ i ∈ (Finset.univ : Finset (Fin 24)), (t i).card := by
      simpa using!
        (Finset.card_biUnion (s := (Finset.univ : Finset (Fin 24))) (t := t) hdisj)
    _ = ∑ i : Fin 24, (Finset.Ioi i).card := by
      simp [ht_card]
    _ = 276 := by
      -- sum over `i : Fin 24` of the tail-length `|(i,24)| = 24 - 1 - i`
      decide

lemma card_TypeIParam : Nat.card (pairLT × Bool × Bool) = 1104 := by
  simp [Nat.card_eq_fintype_card, card_pairLT]

open scoped Classical in
section

/-- Type I bound: `|TypeI| ≤ 1104`. -/
public lemma ncard_TypeI_le_1104
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    Set.ncard (TypeI (C := C) hDn) ≤ 1104 := by
  -- Encode a type-I vector by its two nonzero coordinates and their signs.
  let f : ℝ²⁴ → pairLT × Bool × Bool := fun u =>
    if hu : u ∈ TypeI (C := C) hDn then
      let z : Fin 24 → ℤ := Classical.choose hu.2
      let hpat : isPattern2 z := (Classical.choose_spec hu.2).2
      let supp : Finset (Fin 24) := Finset.univ.filter fun i : Fin 24 => z i ≠ 0
      have hsupp_card : supp.card = 2 := by
        simpa [supp] using! card_filter_ne_zero_of_isPattern2 hpat
      have hsupp_ne : supp.Nonempty := Finset.card_pos.mp (by simp [hsupp_card])
      let i0 : Fin 24 := supp.min' hsupp_ne
      let j0 : Fin 24 := supp.max' hsupp_ne
      have hij : i0 < j0 := by
        have : 1 < supp.card := by simp [hsupp_card]
        simpa [i0, j0, hsupp_ne] using! (Finset.min'_lt_max'_of_card supp this)
      have hp : (i0, j0) ∈ pairLT := by
        simp [pairLT, hij]
      (⟨(i0, j0), hp⟩, decide (z i0 = (-4 : ℤ)), decide (z j0 = (-4 : ℤ)))
    else
      (⟨(0, 1), by simp [pairLT]⟩, false, false)
  have hf_maps :
      ∀ u ∈ TypeI (C := C) hDn, f u ∈ (Set.univ : Set (pairLT × Bool × Bool)) := by
    intro u hu
    simp [f, hu]
  have hf_inj : Set.InjOn f (TypeI (C := C) hDn) := by
    intro u hu v hv huv
    have hu' : u ∈ TypeI (C := C) hDn := hu
    have hv' : v ∈ TypeI (C := C) hDn := hv
    -- Recover the chosen integer-coordinate witnesses.
    have huShell : u ∈ shell4 C := hu'.1
    set zu : Fin 24 → ℤ := Classical.choose hu'.2 with hzu_def
    have hzu : ∀ i, scaledCoord hDn.e i u = (zu i : ℝ) := by
      simpa [hzu_def] using! (Classical.choose_spec hu'.2).1
    have hpu : isPattern2 zu := by
      simpa [hzu_def] using! (Classical.choose_spec hu'.2).2
    have hvShell : v ∈ shell4 C := hv'.1
    set zv : Fin 24 → ℤ := Classical.choose hv'.2 with hzv_def
    have hzv : ∀ i, scaledCoord hDn.e i v = (zv i : ℝ) := by
      simpa [hzv_def] using! (Classical.choose_spec hv'.2).1
    have hpv : isPattern2 zv := by
      simpa [hzv_def] using! (Classical.choose_spec hv'.2).2
    let suppu : Finset (Fin 24) := Finset.univ.filter fun i : Fin 24 => zu i ≠ 0
    have hsuppu_card : suppu.card = 2 := by
      simpa [suppu] using! card_filter_ne_zero_of_isPattern2 hpu
    have hsuppu_ne : suppu.Nonempty := Finset.card_pos.mp (by simp [hsuppu_card])
    let i0u : Fin 24 := suppu.min' hsuppu_ne
    let j0u : Fin 24 := suppu.max' hsuppu_ne
    have hiju : i0u < j0u := by
      have : 1 < suppu.card := by simp [hsuppu_card]
      simpa [i0u, j0u, hsuppu_ne] using! (Finset.min'_lt_max'_of_card suppu this)
    have hpairu : (i0u, j0u) ∈ pairLT := by simp [pairLT, hiju]
    let suppv : Finset (Fin 24) := Finset.univ.filter fun i : Fin 24 => zv i ≠ 0
    have hsuppv_card : suppv.card = 2 := by
      simpa [suppv] using! card_filter_ne_zero_of_isPattern2 hpv
    have hsuppv_ne : suppv.Nonempty := Finset.card_pos.mp (by simp [hsuppv_card])
    let i0v : Fin 24 := suppv.min' hsuppv_ne
    let j0v : Fin 24 := suppv.max' hsuppv_ne
    have hijv : i0v < j0v := by
      have : 1 < suppv.card := by simp [hsuppv_card]
      simpa [i0v, j0v, hsuppv_ne] using! (Finset.min'_lt_max'_of_card suppv this)
    have hpairv : (i0v, j0v) ∈ pairLT := by simp [pairLT, hijv]
    -- Unfold `f` in the equality and extract the three component equalities.
    have huv' :
        (i0u = i0v ∧ j0u = j0v) ∧
          (zu i0u = (-4 : ℤ) ↔ zv i0v = (-4 : ℤ)) ∧ (zu j0u = (-4 : ℤ) ↔ zv j0v = (-4 : ℤ)) := by
      simpa [f, hu', hv', hzu_def, hzv_def, suppu, suppv, i0u, j0u, i0v, j0v, hpairu,
        hpairv] using! huv
    rcases huv' with ⟨hij, hb0, hb1⟩
    rcases hij with ⟨hi0, hj0⟩
    have hi0u_mem : i0u ∈ suppu := Finset.min'_mem suppu hsuppu_ne
    have hj0u_mem : j0u ∈ suppu := Finset.max'_mem suppu hsuppu_ne
    have hi0v_mem : i0v ∈ suppv := Finset.min'_mem suppv hsuppv_ne
    have hj0v_mem : j0v ∈ suppv := Finset.max'_mem suppv hsuppv_ne
    have supp_eq_pair_of_card2 (supp : Finset (Fin 24)) (hsupp_card : supp.card = 2)
        (hsupp_ne : supp.Nonempty) :
        supp = ({supp.min' hsupp_ne, supp.max' hsupp_ne} : Finset (Fin 24)) := by
      have hsub : ({supp.min' hsupp_ne, supp.max' hsupp_ne} : Finset (Fin 24)) ⊆ supp := by
        intro i hi
        rcases (by simpa using! hi) with rfl | rfl
        · exact Finset.min'_mem supp hsupp_ne
        · exact Finset.max'_mem supp hsupp_ne
      have hne : supp.min' hsupp_ne ≠ supp.max' hsupp_ne := by
        have : 1 < supp.card := by simp [hsupp_card]
        have hlt : supp.min' hsupp_ne < supp.max' hsupp_ne := by
          simpa [hsupp_ne] using! (Finset.min'_lt_max'_of_card supp this)
        exact ne_of_lt hlt
      have hle : supp.card ≤ ({supp.min' hsupp_ne, supp.max' hsupp_ne} : Finset (Fin 24)).card := by
        simp [hsupp_card, hne]
      exact (Finset.eq_of_subset_of_card_le hsub hle).symm
    have hsuppu_eq : suppu = {i0u, j0u} := by
      simpa [i0u, j0u] using! (supp_eq_pair_of_card2 suppu hsuppu_card hsuppu_ne)
    have hsuppv_eq : suppv = {i0v, j0v} := by
      simpa [i0v, j0v] using! (supp_eq_pair_of_card2 suppv hsuppv_card hsuppv_ne)
    have hpm4_of_mem_suppu {i : Fin 24} (hi : i ∈ suppu) : zu i = 4 ∨ zu i = -4 := by
      have hne : zu i ≠ 0 := (Finset.mem_filter.1 hi).2
      rcases hpu.2 i with h0 | h4 | hN4
      · exact (hne h0).elim
      · exact Or.inl h4
      · exact Or.inr hN4
    have hpm4_of_mem_suppv {i : Fin 24} (hi : i ∈ suppv) : zv i = 4 ∨ zv i = -4 := by
      have hne : zv i ≠ 0 := (Finset.mem_filter.1 hi).2
      rcases hpv.2 i with h0 | h4 | hN4
      · exact (hne h0).elim
      · exact Or.inl h4
      · exact Or.inr hN4
    have eq_of_pm4_of_iff_neg4 {a b : ℤ} (ha : a = 4 ∨ a = -4) (hb : b = 4 ∨ b = -4)
        (h : a = -4 ↔ b = -4) : a = b := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exfalso
        exact (show (4 : ℤ) ≠ -4 by decide) (h.2 rfl)
      · exfalso
        exact (show (4 : ℤ) ≠ -4 by decide) (h.1 rfl)
      · rfl
    have hzu_i0 : zu i0u = zv i0u := by
      have ha : zu i0u = 4 ∨ zu i0u = -4 := hpm4_of_mem_suppu hi0u_mem
      have hb : zv i0v = 4 ∨ zv i0v = -4 := hpm4_of_mem_suppv hi0v_mem
      have : zu i0u = zv i0v := eq_of_pm4_of_iff_neg4 ha hb hb0
      simpa [hi0] using! this
    have hzu_j0 : zu j0u = zv j0u := by
      have ha : zu j0u = 4 ∨ zu j0u = -4 := hpm4_of_mem_suppu hj0u_mem
      have hb : zv j0v = 4 ∨ zv j0v = -4 := hpm4_of_mem_suppv hj0v_mem
      have : zu j0u = zv j0v := eq_of_pm4_of_iff_neg4 ha hb hb1
      simpa [hj0] using! this
    have hzu_zero : ∀ i : Fin 24, i ∉ suppu → zu i = 0 := by
      intro i hi
      have : ¬ zu i ≠ 0 := by simpa [suppu] using! hi
      exact (not_ne_iff.1 this)
    have hzv_zero : ∀ i : Fin 24, i ∉ suppv → zv i = 0 := by
      intro i hi
      have : ¬ zv i ≠ 0 := by simpa [suppv] using! hi
      exact (not_ne_iff.1 this)
    have hzu_eq_zv : ∀ i : Fin 24, zu i = zv i := by
      intro i
      by_cases hi0u' : i = i0u
      · subst hi0u'
        simpa using! hzu_i0
      by_cases hj0u' : i = j0u
      · subst hj0u'
        simpa using! hzu_j0
      have hi_suppu : i ∉ suppu := by
        have : i ∉ ({i0u, j0u} : Finset (Fin 24)) := by
          simp [Finset.mem_insert, Finset.mem_singleton, hi0u', hj0u']
        simpa [hsuppu_eq] using! this
      have hi0v' : i ≠ i0v := by simpa [hi0] using! hi0u'
      have hj0v' : i ≠ j0v := by simpa [hj0] using! hj0u'
      have hi_suppv : i ∉ suppv := by
        have : i ∉ ({i0v, j0v} : Finset (Fin 24)) := by
          simp [Finset.mem_insert, Finset.mem_singleton, hi0v', hj0v']
        simpa [hsuppv_eq] using! this
      simp [hzu_zero i hi_suppu, hzv_zero i hi_suppv]
    have hscaled : ∀ i : Fin 24, scaledCoord hDn.e i u = scaledCoord hDn.e i v := by
      intro i
      have : zu i = zv i := hzu_eq_zv i
      simp [hzu i, hzv i, this]
    exact eq_of_scaledCoord_eq (e := hDn.e) hDn.ortho hscaled
  have hle :
      Set.ncard (TypeI (C := C) hDn) ≤ Set.ncard (Set.univ : Set (pairLT × Bool × Bool)) :=
    Set.ncard_le_ncard_of_injOn f hf_maps hf_inj
  have huniv : Set.ncard (Set.univ : Set (pairLT × Bool × Bool)) = 1104 := by
    calc
      Set.ncard (Set.univ : Set (pairLT × Bool × Bool)) = Nat.card (pairLT × Bool × Bool) := by
        simp
      _ = 1104 := card_TypeIParam
  exact le_trans hle (le_of_eq huniv)

end

/-!
## A nonzero codeword exists (so `minDist` is meaningful)
-/

lemma exists_nonzero_mem_codeFromLattice
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    ∃ c ∈ code (C := C) hDn, c ≠ (0 : BinWord 24) := by
  -- Pick a shell vector not of type I (type I has at most 1104 elements).
  have hshellCard : Set.ncard (shell4 C) = 196560 := ncard_shell4_eq_196560 (C := C) hEq
  have hTypeI : Set.ncard (TypeI (C := C) hDn) ≤ 1104 := ncard_TypeI_le_1104 (C := C) hDn
  have hnot_all : ¬ shell4 C ⊆ TypeI (C := C) hDn := by
    intro hsub
    have hshell_ne0 : Set.ncard (shell4 C) ≠ 0 := by
      simp [hshellCard]
    have hshell_finite : (shell4 C).Finite := Set.finite_of_ncard_ne_zero hshell_ne0
    have hTypeI_finite : (TypeI (C := C) hDn).Finite :=
      hshell_finite.subset (by intro u hu; exact hu.1)
    have : Set.ncard (shell4 C) ≤ Set.ncard (TypeI (C := C) hDn) :=
      Set.ncard_le_ncard hsub hTypeI_finite
    have : (196560 : ℕ) ≤ 1104 :=
      le_trans (by simpa [hshellCard] using! this) hTypeI
    have hcontra : ¬ (196560 : ℕ) ≤ 1104 := by decide
    exact hcontra this
  rcases (Set.not_subset.1 hnot_all) with ⟨u, huShell, huNotI⟩
  -- Classify `u` and build a nonzero codeword.
  rcases shell4_patterns (C := C) (hEq := hEq) (hDn := hDn) huShell with
    ⟨z, hzCoord, _hpar, _hsumsq, hpat⟩
  rcases hpat with h1 | h2 | h3
  · -- pattern 1: use the support indicator (a weight-8 codeword).
    let c : BinWord 24 := fun i => ((z i / 2 : ℤ) : ZMod 2)
    have hc_mem : c ∈ code (C := C) hDn := by
      refine ⟨u, huShell.1, z, hzCoord, ?_, ?_⟩
      · intro i
        exact even_of_isPattern1 h1 i
      · intro i
        rfl
    have hc_ne0 : c ≠ (0 : BinWord 24) := by
      intro h0
      have hwt0 : weight c = 0 := by simp [CodingTheory.weight, h0]
      have hwt8 : weight c = 8 := by simpa [c] using! weight_intDiv2_of_isPattern1 h1
      have : (8 : ℕ) = 0 := by simpa [hwt8] using! hwt0.symm
      exact (by decide : (8 : ℕ) ≠ 0) this
    exact ⟨c, hc_mem, hc_ne0⟩
  · -- pattern 2: contradiction with `huNotI`
    exfalso
    exact huNotI ⟨huShell, z, hzCoord, h2⟩
  · -- pattern 3: use the codeword coming from the even vector `2•u`
    let x : ℝ²⁴ := (2 : ℝ) • u
    let z2 : Fin 24 → ℤ := fun i => 2 * z i
    let c : BinWord 24 := fun i => ((z2 i / 2 : ℤ) : ZMod 2)
    have hxL : x ∈ (latticeL C : Set ℝ²⁴) := by
      -- `shell4 ⊆ latticeL` and lattices are closed under addition.
      have huL : u ∈ (latticeL C : Set ℝ²⁴) := huShell.1
      have : u + u ∈ (latticeL C : Set ℝ²⁴) := (latticeL C).add_mem huL huL
      simpa [x, two_smul] using! this
    have hz2Coord : ∀ i : Fin 24, scaledCoord hDn.e i x = (z2 i : ℝ) := by
      intro i
      have : scaledCoord hDn.e i x = (2 : ℝ) * scaledCoord hDn.e i u := by
        simp [x, scaledCoord, coord, real_inner_smul_right, mul_left_comm]
      -- rewrite using `hzCoord`
      simpa [z2, hzCoord i, Int.cast_mul, two_mul, mul_add, mul_assoc] using! this
    have hc_mem : c ∈ code (C := C) hDn := by
      refine ⟨x, hxL, z2, hz2Coord, ?_, ?_⟩
      · intro i
        refine ⟨z i, by simp [z2, two_mul]⟩
      · intro i
        -- `(2*z)/2 = z`
        simp [c, z2, two_mul]
    have hc_ne0 : c ≠ (0 : BinWord 24) := by
      intro h0
      -- In pattern 3 all `z i` are odd, so `c i = 1` for all `i`, hence `c ≠ 0`.
      have : c 0 = 1 := by
        -- `z 0` is `±1` or `±3`
        rcases h3.2 (0 : Fin 24) with hz1 | hrest
        · simp [c, z2, hz1]
        rcases hrest with hzN1 | hrest
        · simp [c, z2, hzN1]
        rcases hrest with hz3 | hzN3
        · simp only [c, z2, hz3]; decide
        · simp only [c, z2, hzN3]; decide
      -- contradiction with `h0`
      have h0eq := this
      simp [h0] at h0eq
    exact ⟨c, hc_mem, hc_ne0⟩

/-!
## Minimum distance and standard bounds for the extracted code
-/

lemma minDist_ge_eight_codeFromLattice
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    8 ≤ minDist (code (C := C) hDn) := by
  have hlin : IsLinearCode (code (C := C) hDn) :=
    CodeFromLattice.codeFromLattice_linear (C := C) hDn
  have hne : ∃ c ∈ code (C := C) hDn, c ≠ (0 : BinWord 24) :=
    exists_nonzero_mem_codeFromLattice (C := C) hEq hDn
  have hwt :
      ∀ c : BinWord 24, c ∈ code (C := C) hDn → c ≠ 0 → 8 ≤ weight c := by
    intro c hc hc0
    exact
      CodeFromLattice.weight_ge_eight_of_mem_codeFromLattice (C := C) (h := hEq) hDn hc hc0
  exact CodingTheory.le_minDist_of_linear_of_weight_ge (code C hDn) hlin 8 hwt hne

lemma ncard_code_le_two_pow12
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    Set.ncard (code (C := C) hDn) ≤ 2 ^ 12 :=
  CodeCardBound.ncard_code_le_two_pow12_of_minDist_ge (C := code (C := C) hDn)
      (minDist_ge_eight_codeFromLattice (C := C) hEq hDn)

lemma ncard_weight8Words_le_759
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    Set.ncard (weight8Words (code (C := C) hDn)) ≤ 759 :=
  Uniqueness.BS81.CodingTheory.weight8_codewords_le_759_of_minDist_ge
      (C := code (C := C) hDn)
      (minDist_ge_eight_codeFromLattice (C := C) hEq hDn)

/-!
## Type II bound: `|TypeII| ≤ 2^7 * N₈`
-/

def SignRep : Type := {s : Fin 8 → Bool // s 0 = false}

instance : Fintype SignRep := by
  unfold SignRep
  infer_instance

lemma card_SignRep : Nat.card SignRep = 2 ^ 7 := by
  -- `SignRep` is equivalent to `Fin 7 → Bool`: coordinate `0` is fixed to `false`.
  let fwd : (Fin 7 → Bool) → SignRep := fun g => ⟨Fin.cons false g, by simp⟩
  let bwd : SignRep → (Fin 7 → Bool) := fun s i => s.1 i.succ
  have hEquiv : SignRep ≃ (Fin 7 → Bool) :=
    { toFun := bwd
      invFun := fun g => fwd g
      left_inv := by
        intro s
        apply Subtype.ext
        funext k
        refine Fin.cases ?_ (fun i => ?_) k
        · simpa [fwd, bwd] using! s.2.symm
        · simp [fwd, bwd]
      right_inv := by
        intro g
        funext i
        simp [fwd, bwd] }
  have hcard : Fintype.card SignRep = 2 ^ 7 := by
    calc
      Fintype.card SignRep = Fintype.card (Fin 7 → Bool) := Fintype.card_congr hEquiv
      _ = 2 ^ 7 := by simp
  simpa [Nat.card_eq_fintype_card] using! hcard

/-!
Canonical representative of a sign pattern: force bit `0` to be `false`.

This is the usual `2^7` bound for an independent set in the `8`-cube: if two realizable sign
patterns agreed on bits `1..7` but differed on bit `0`, their difference would be a lattice vector
of squared norm `2`, contradicting BS81 Lemma 16 (`minNorm_sq_ge_four`).
-/

def mkSignRep (b : Fin 8 → Bool) : SignRep :=
  if h0 : b 0 then
    ⟨fun k => if k = 0 then false else b k, by simp⟩
  else
    ⟨b, by simp [h0]⟩

lemma mkSignRep_apply_ne_zero {b : Fin 8 → Bool} {k : Fin 8} (hk : k ≠ 0) :
    (mkSignRep b).1 k = b k := by
  by_cases h0 : b 0 <;> simp [mkSignRep, h0, hk]

lemma mkSignRep_apply_zero (b : Fin 8 → Bool) : (mkSignRep b).1 0 = false := by
  by_cases h0 : b 0 <;> simp [mkSignRep, h0]

/-!
`TypeII` → `weight8Words code` map, forgetting signs.
-/

lemma typeII_to_weight8Words
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    {u : ℝ²⁴} (hu : u ∈ TypeII (C := C) hDn) :
    ∃ c : BinWord 24, c ∈ weight8Words (code (C := C) hDn) := by
  rcases hu with ⟨huShell, z, hzCoord, hzPat⟩
  let c : BinWord 24 := fun i => ((z i / 2 : ℤ) : ZMod 2)
  have hc_mem : c ∈ code (C := C) hDn := by
    refine ⟨u, huShell.1, z, hzCoord, ?_, ?_⟩
    · intro i
      exact even_of_isPattern1 hzPat i
    · intro i
      rfl
  have hwt : weight c = 8 := by simpa [c] using! weight_intDiv2_of_isPattern1 hzPat
  exact ⟨c, hc_mem, hwt⟩

open scoped Classical in
section

/-- Type II bound: `TypeII` is controlled by the weight-`8` words in the extracted code. -/
public lemma ncard_TypeII_le
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    Set.ncard (TypeII (C := C) hDn) ≤ (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) := by
  -- If there are no weight-8 words, then there are no type-II vectors.
  by_cases hW8 : (weight8Words (code (C := C) hDn)).Nonempty
  · -- Encode a type-II vector by (its underlying weight-8 word, 7 sign bits).
    let Weight8 : Type := Set.Elem (weight8Words (code (C := C) hDn))
    let cod : Type := Weight8 × SignRep
    have hcod_nonempty : Nonempty cod := by
      rcases hW8 with ⟨w, hw⟩
      exact ⟨(⟨w, hw⟩, ⟨fun _ => false, by simp⟩)⟩
    let enc : {u : ℝ²⁴ // u ∈ TypeII (C := C) hDn} → cod := fun uu =>
      let u : ℝ²⁴ := uu.1
      have hu : u ∈ TypeII (C := C) hDn := uu.2
      let z : Fin 24 → ℤ := Classical.choose hu.2
      let hz : ∀ i, scaledCoord hDn.e i u = (z i : ℝ) := (Classical.choose_spec hu.2).1
      let hzPat : isPattern1 z := (Classical.choose_spec hu.2).2
      let cw : BinWord 24 := fun i : Fin 24 => ((z i / 2 : ℤ) : ZMod 2)
      have hcw_mem : cw ∈ weight8Words (code (C := C) hDn) := by
        -- membership in the extracted code
        have hcw_code : cw ∈ code (C := C) hDn := by
          refine ⟨u, hu.1.1, z, hz, ?_, ?_⟩
          · intro i
            exact even_of_isPattern1 hzPat i
          · intro i
            rfl
        -- weight is `8` because exactly 8 coordinates are nonzero
        have hwt : weight cw = 8 := by simpa [cw] using! weight_intDiv2_of_isPattern1 hzPat
        exact ⟨hcw_code, hwt⟩
      let w8 : Weight8 := ⟨cw, hcw_mem⟩
      -- order the support of the weight-8 word and record 7 sign bits (drop `k=0`)
      let B : Finset (Fin 24) := support w8.1
      have hB8 : B.card = 8 := by
        have : weight w8.1 = 8 := w8.2.2
        simpa [CodingTheory.GolayBounds.weight_eq_card_support, B] using! this
      let iso : Fin 8 ≃o B := B.orderIsoOfFin hB8
      let signRep : SignRep :=
        ⟨fun k => if k = 0 then false else decide (z (iso k).1 = (-2 : ℤ)), by simp⟩
      (w8, signRep)
    let f : ℝ²⁴ → cod := fun u =>
      if hu : u ∈ TypeII (C := C) hDn then enc ⟨u, hu⟩ else Classical.choice hcod_nonempty
    have hf_maps : ∀ u ∈ TypeII (C := C) hDn, f u ∈ (Set.univ : Set cod) := by
      intro u hu
      simp [f, hu]
    have hf_inj : Set.InjOn f (TypeII (C := C) hDn) := by
      intro u hu v hv huv
      have hu' : u ∈ TypeII (C := C) hDn := hu
      have hv' : v ∈ TypeII (C := C) hDn := hv
      -- unfold `f` on both points
      simp only [f, hu', hv', dif_pos] at huv
      -- extract witnesses
      set zu : Fin 24 → ℤ := Classical.choose hu'.2 with hzu_def
      have hzu : ∀ i, scaledCoord hDn.e i u = (zu i : ℝ) := by
        simpa [hzu_def] using! (Classical.choose_spec hu'.2).1
      have hzuPat : isPattern1 zu := by
        simpa [hzu_def] using! (Classical.choose_spec hu'.2).2
      set zv : Fin 24 → ℤ := Classical.choose hv'.2 with hzv_def
      have hzv : ∀ i, scaledCoord hDn.e i v = (zv i : ℝ) := by
        simpa [hzv_def] using! (Classical.choose_spec hv'.2).1
      have hzvPat : isPattern1 zv := by
        simpa [hzv_def] using! (Classical.choose_spec hv'.2).2
      -- split the pair equality from `enc`
      have hw8 :
          (enc ⟨u, hu'⟩).1 = (enc ⟨v, hv'⟩).1 := congrArg Prod.fst huv
      have hsign :
          (enc ⟨u, hu'⟩).2 = (enc ⟨v, hv'⟩).2 := congrArg Prod.snd huv
      -- abbreviate the common weight-8 word and its ordered support
      set w8u : Weight8 := (enc ⟨u, hu'⟩).1
      set w8v : Weight8 := (enc ⟨v, hv'⟩).1
      have hw : w8u = w8v := by simpa [w8u, w8v] using! hw8
      have hwval : w8u.1 = w8v.1 := by
        simpa using! congrArg Subtype.val hw
      have hw8u_apply : ∀ i : Fin 24, w8u.1 i = ((zu i / 2 : ℤ) : ZMod 2) := by
        intro i
        simp [w8u, enc, zu]
      have hw8v_apply : ∀ i : Fin 24, w8v.1 i = ((zv i / 2 : ℤ) : ZMod 2) := by
        intro i
        simp [w8v, enc, zv]
      set B : Finset (Fin 24) := support w8u.1
      have hB8 : B.card = 8 := by
        have : weight w8u.1 = 8 := w8u.2.2
        simpa [CodingTheory.GolayBounds.weight_eq_card_support, B] using! this
      have hEmb_eq : ∀ h : B.card = 8, B.orderEmbOfFin h = B.orderEmbOfFin hB8 :=
        fun h => orderEmbOfFin.congr_simp B B rfl h
      have hSupport_zv : support (fun i : Fin 24 => ((zv i / 2 : ℤ) : ZMod 2)) = B :=
        eq_of_veq (congrArg val (congrArg support (id (Eq.symm hwval))))
      let iso : Fin 8 ≃o B := B.orderIsoOfFin hB8
      let i0 : Fin 24 := (iso 0).1
      have hi0B : i0 ∈ B := by
        simp [i0]
      have hsignBits :
          ∀ k : Fin 8, k ≠ 0 →
            decide (zu (iso k).1 = (-2 : ℤ)) = decide (zv (iso k).1 = (-2 : ℤ)) := by
        intro k hk0
        have := congrArg (fun s : SignRep => s.1 k) hsign
        simpa [enc, hk0, hzu_def.symm, hzv_def.symm, w8u, w8v, hw, hwval, B, hB8, hEmb_eq,
          hSupport_zv, i0, iso] using! this
      have hz_eq_on :
          ∀ k : Fin 8, k ≠ 0 → zu (iso k).1 = zv (iso k).1 := by
        intro k hk0
        have hdec :
            decide (zu (iso k).1 = (-2 : ℤ)) = decide (zv (iso k).1 = (-2 : ℤ)) :=
          hsignBits k hk0
        -- possible values are `±2` on the support
        have hu2 : zu (iso k).1 = 2 ∨ zu (iso k).1 = -2 := by
          rcases hzuPat.2 (iso k).1 with hz0 | hz2 | hzm2
          · exfalso
            have : (iso k).1 ∈ B := (iso k).2
            have hone : w8u.1 (iso k).1 = 1 :=
              (CodingTheory.GolayBounds.mem_support w8u.1 (iso k).1).1 (by simp [B])
            -- but `zu=0` forces the codeword value `0`
            have hzero : w8u.1 (iso k).1 = 0 :=
              zmod2_int_div2_eq_zero_of_eq_zero hz0
            have hcontra := hone
            simp [hzero] at hcontra
          · exact Or.inl hz2
          · exact Or.inr hzm2
        have hv2 : zv (iso k).1 = 2 ∨ zv (iso k).1 = -2 := by
          rcases hzvPat.2 (iso k).1 with hz0 | hz2 | hzm2
          · exfalso
            have : (iso k).1 ∈ B := (iso k).2
            have hone : w8u.1 (iso k).1 = 1 :=
              (CodingTheory.GolayBounds.mem_support w8u.1 (iso k).1).1 (by simp [B])
            -- `zv=0` forces the codeword value `0`
            have hzero : w8u.1 (iso k).1 = 0 := by
              calc
                w8u.1 (iso k).1 = w8v.1 (iso k).1 := by simp [hw]
                _ = ((zv (iso k).1 / 2 : ℤ) : ZMod 2) := hw8v_apply (iso k).1
                _ = 0 := zmod2_int_div2_eq_zero_of_eq_zero hz0
            have hcontra := hone
            simp [hzero] at hcontra
          · exact Or.inl hz2
          · exact Or.inr hzm2
        rcases hu2 with hz2 | hzm2 <;> rcases hv2 with hz2' | hzm2'
        · simp [hz2, hz2']
        · -- rule out `2 / -2` using the sign-bit decision equality
          have : (false : Bool) = true := by
            have h := hdec
            simp [hz2, hzm2'] at h
          cases this
        · -- rule out `-2 / 2`
          have : (true : Bool) = false := by
            have h := hdec
            simp [hzm2, hz2'] at h
          cases this
        · simp [hzm2, hzm2']
      -- show the coordinate `i0` is also equal: otherwise `‖u-v‖^2 = 2`
      have hz0_eq : zu i0 = zv i0 := by
        by_contra hne
        have hu2 : zu i0 = 2 ∨ zu i0 = -2 := by
          rcases hzuPat.2 i0 with hz0 | hz2 | hzm2
          · exfalso
            have hone : w8u.1 i0 = 1 :=
              (CodingTheory.GolayBounds.mem_support w8u.1 i0).1 (by simpa [B] using! hi0B)
            have hzero : w8u.1 i0 = 0 :=
              zmod2_int_div2_eq_zero_of_eq_zero hz0
            have hcontra := hone
            simp [hzero] at hcontra
          · exact Or.inl hz2
          · exact Or.inr hzm2
        have hv2 : zv i0 = 2 ∨ zv i0 = -2 := by
          rcases hzvPat.2 i0 with hz0 | hz2 | hzm2
          · exfalso
            have hone : w8u.1 i0 = 1 :=
              (CodingTheory.GolayBounds.mem_support w8u.1 i0).1 (by simpa [B] using! hi0B)
            have hzero : w8u.1 i0 = 0 := by
              calc
                w8u.1 i0 = w8v.1 i0 := by simp [hw]
                _ = ((zv i0 / 2 : ℤ) : ZMod 2) := hw8v_apply i0
                _ = 0 := zmod2_int_div2_eq_zero_of_eq_zero hz0
            have hcontra := hone
            simp [hzero] at hcontra
          · exact Or.inl hz2
          · exact Or.inr hzm2
        have hdiff_i0 : scaledCoord hDn.e i0 (u - v) = (zu i0 - zv i0 : ℝ) := by
          have := scaledCoord_sub (e := hDn.e) i0 u v
          simp [this, hzu i0, hzv i0]
        have hdiff_other :
            ∀ i : Fin 24, i ≠ i0 → scaledCoord hDn.e i (u - v) = 0 := by
          intro i hii0
          by_cases hiB : i ∈ B
          · rcases iso.surjective ⟨i, hiB⟩ with ⟨k, hk⟩
            have hk0 : k ≠ 0 := by
              intro hk0
              have : (iso 0).1 = i := by simpa [hk0] using! congrArg Subtype.val hk
              exact hii0 (this.symm.trans rfl)
            have hzEq : zu i = zv i := by
              have := hz_eq_on k hk0
              simpa [hk] using! this
            have := scaledCoord_sub (e := hDn.e) i u v
            simp [this, hzu i, hzv i, hzEq]
          · -- outside the support: both are `0` by pattern1
            rcases hzuPat.2 i with hz0 | hz2 | hzm2
            · have : zv i = 0 := by
                rcases hzvPat.2 i with hz0' | hz2' | hzm2'
                · exact hz0'
                · exfalso
                  have hvone : w8v.1 i = 1 :=
                    zmod2_int_div2_eq_one_of_eq_two hz2'
                  have huone : w8u.1 i = 1 := by simpa [hw] using! hvone
                  have : i ∈ B := (CodingTheory.GolayBounds.mem_support w8u.1 i).2 huone
                  exact hiB this
                · exfalso
                  have hvone : w8v.1 i = 1 := by
                    exact zmod2_int_div2_eq_one_of_eq_neg_two hzm2'
                  have huone : w8u.1 i = 1 := by simpa [hw] using! hvone
                  have : i ∈ B := (CodingTheory.GolayBounds.mem_support w8u.1 i).2 huone
                  exact hiB this
              have hzv0 : zv i = 0 := this
              have hsub := scaledCoord_sub (e := hDn.e) i u v
              simp [hsub, hzu i, hzv i, hz0, hzv0]
            · exfalso
              have huone : w8u.1 i = 1 :=
                zmod2_int_div2_eq_one_of_eq_two hz2
              have : i ∈ B := (CodingTheory.GolayBounds.mem_support w8u.1 i).2 huone
              exact hiB this
            · exfalso
              have huone : w8u.1 i = 1 :=
                zmod2_int_div2_eq_one_of_eq_neg_two hzm2
              have : i ∈ B := (CodingTheory.GolayBounds.mem_support w8u.1 i).2 huone
              exact hiB this
        have hsum_sq : (∑ i : Fin 24, (scaledCoord hDn.e i (u - v)) ^ 2) = (16 : ℝ) := by
          have hzero :
              ∀ i : Fin 24, i ≠ i0 → (scaledCoord hDn.e i (u - v)) ^ 2 = 0 := by
            intro i hii0
            simp [hdiff_other i hii0]
          have hmem : i0 ∈ (Finset.univ : Finset (Fin 24)) := by simp
          have hsingle :
              (∑ i : Fin 24, (scaledCoord hDn.e i (u - v)) ^ 2) =
                (scaledCoord hDn.e i0 (u - v)) ^ 2 :=
            Fintype.sum_eq_single i0 hzero
          have hdiff_abs : (scaledCoord hDn.e i0 (u - v)) ^ 2 = (16 : ℝ) := by
            rcases hu2 with hu2 | hu2 <;> rcases hv2 with hv2 | hv2
            · exfalso
              exact hne (by simp [hu2, hv2])
            · -- `2 - (-2) = 4`
              simp [hdiff_i0, hu2, hv2]
              norm_num
            · -- `(-2) - 2 = -4`
              simp [hdiff_i0, hu2, hv2]
              norm_num
            · exfalso
              exact hne (by simp [hu2, hv2])
          simp [hsingle, hdiff_abs]
        have hnorm_sq : ‖u - v‖ ^ 2 = (2 : ℝ) := by
          have hnorm :=
            Uniqueness.BS81.Thm15.Lemma21.CodeFromLattice.norm_sq_eq_sum_scaledCoord_sq_div8
              (e := hDn.e) hDn.ortho (u - v)
          have hmul : ((8 : ℝ)⁻¹) * (16 : ℝ) = (2 : ℝ) := by
            norm_num
          simpa [hsum_sq, hmul] using! hnorm
        have hmemL : (u - v) ∈ (latticeL C : Set ℝ²⁴) := (latticeL C).sub_mem hu'.1.1 hv'.1.1
        exact
          (Uniqueness.BS81.Thm15.Lemma16.no_norm_sq_two_vector_in_latticeL
            (C := C) hEq) ⟨u - v, hmemL, hnorm_sq⟩
      have hz_eq : zu = zv := by
        funext i
        by_cases hi : i = i0
        · subst hi; exact hz0_eq
        · by_cases hiB : i ∈ B
          · rcases iso.surjective ⟨i, hiB⟩ with ⟨k, hk⟩
            have hk0 : k ≠ 0 := by
              intro hk0
              have : (iso 0).1 = i := by simpa [hk0] using! congrArg Subtype.val hk
              exact hi (this.symm.trans rfl)
            have := hz_eq_on k hk0
            simpa [hk] using! this
          · rcases hzuPat.2 i with hz0 | hz2 | hzm2
            · have : zv i = 0 := by
                rcases hzvPat.2 i with hz0' | hz2' | hzm2'
                · exact hz0'
                · exfalso
                  have hvone : w8v.1 i = 1 :=
                    zmod2_int_div2_eq_one_of_eq_two hz2'
                  have huone : w8u.1 i = 1 := by simpa [hw] using! hvone
                  have : i ∈ B := (CodingTheory.GolayBounds.mem_support w8u.1 i).2 huone
                  exact hiB this
                · exfalso
                  have hvone : w8v.1 i = 1 := by
                    exact zmod2_int_div2_eq_one_of_eq_neg_two hzm2'
                  have huone : w8u.1 i = 1 := by simpa [hw] using! hvone
                  have : i ∈ B := (CodingTheory.GolayBounds.mem_support w8u.1 i).2 huone
                  exact hiB this
              simp [hz0, this]
            · exfalso
              have huone : w8u.1 i = 1 :=
                zmod2_int_div2_eq_one_of_eq_two hz2
              have : i ∈ B := (CodingTheory.GolayBounds.mem_support w8u.1 i).2 huone
              exact hiB this
            · exfalso
              have huone : w8u.1 i = 1 :=
                zmod2_int_div2_eq_one_of_eq_neg_two hzm2
              have : i ∈ B := (CodingTheory.GolayBounds.mem_support w8u.1 i).2 huone
              exact hiB this
      have hscaled : ∀ i, scaledCoord hDn.e i u = scaledCoord hDn.e i v := by
        intro i
        simp [hzu i, hz_eq, hzv i]
      exact eq_of_scaledCoord_eq (e := hDn.e) hDn.ortho hscaled
    -- `Set.ncard_le_ncard_of_injOn` needs finiteness of the codomain set `univ`.
    haveI : Finite Weight8 := by infer_instance
    letI : Fintype Weight8 := Fintype.ofFinite Weight8
    have hle : Set.ncard (TypeII (C := C) hDn) ≤ Set.ncard (Set.univ : Set cod) :=
      Set.ncard_le_ncard_of_injOn (s := TypeII (C := C) hDn) (t := (Set.univ : Set cod)) f
        hf_maps hf_inj
        (ht := (Set.finite_univ : (Set.univ : Set cod).Finite))
    have hWeight8 : Nat.card Weight8 = Set.ncard (weight8Words (code (C := C) hDn)) := by
      -- `Weight8` is the subtype of `weight8Words`.
      rfl
    have hWeight8_card : Fintype.card Weight8 = Set.ncard (weight8Words (code (C := C) hDn)) := by
      simpa [Nat.card_eq_fintype_card] using! hWeight8
    have hSignRep_card : Fintype.card SignRep = 2 ^ 7 := by
      simpa [Nat.card_eq_fintype_card] using! card_SignRep
    have hcardCod :
        Set.ncard (Set.univ : Set cod) =
          (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) := by
      have hcard_univ : Set.ncard (Set.univ : Set cod) = Nat.card cod :=
        Set.ncard_univ (α := cod)
      have hcard_univ' : Set.ncard (Set.univ : Set cod) = Fintype.card cod :=
        hcard_univ.trans (Nat.card_eq_fintype_card (α := cod))
      calc
        Set.ncard (Set.univ : Set cod) = Fintype.card cod := hcard_univ'
        _ = Fintype.card Weight8 * Fintype.card SignRep := by
          dsimp [cod]
          exact Fintype.card_prod Weight8 SignRep
        _ = Set.ncard (weight8Words (code (C := C) hDn)) * (2 ^ 7) := by
          rw [hWeight8_card, hSignRep_card]
        _ = (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) :=
          Nat.mul_comm _ _
    exact le_trans hle (le_of_eq hcardCod)
  · -- `weight8Words` empty implies `TypeII` empty.
    have hW8_empty : weight8Words (code (C := C) hDn) = ∅ :=
      (Set.not_nonempty_iff_eq_empty.1 hW8)
    have hTypeII_empty : TypeII (C := C) hDn = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro u hu
      rcases typeII_to_weight8Words (C := C) (hDn := hDn) (u := u) hu with ⟨c, hc⟩
      exact hW8 ( ⟨c, hc⟩)
    simp [hW8_empty, hTypeII_empty]

end

/-!
## Type III bound: `|TypeIII| ≤ 24 * |code|`
-/

open scoped Classical in
section

/-- Type III bound: `|TypeIII| ≤ 24 * |code|`. -/
public lemma ncard_TypeIII_le
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    Set.ncard (TypeIII (C := C) hDn) ≤ 24 * Set.ncard (code (C := C) hDn) := by
  -- BS81 Lemma 21, type III bound (Lemma `typeIII_bound`).
  -- fix a type-III vector `u₀`, then map `u` to the pair `(j(u), ρ(√8 (u-u₀)))`.
  -- Equality of the `ρ`-words gives coordinate congruence mod `4`, which forces equality of the
  -- original odd coordinates once `j(u)` is fixed.

  -- Extract the unique "±3 coordinate index" from `isPattern3`.
  by_cases hne : (TypeIII (C := C) hDn).Nonempty
  · rcases hne with ⟨u0, hu0⟩
    rcases hu0.2 with ⟨z0, hz0, hpat0⟩
    let g : ℝ²⁴ → Fin 24 × BinWord 24 := Shell4IsometryBasepoint.injMap (C := C) hDn z0
    have hg_maps :
        ∀ u ∈ TypeIII (C := C) hDn,
          g u ∈ (Set.univ : Set (Fin 24)) ×ˢ (code (C := C) hDn) :=
      Shell4IsometryBasepoint.injMap_mapsTo (C := C) hDn (u0 := u0) (hu0 := hu0)
        (z0 := z0) (hz0 := hz0) (hz0Pat := hpat0)
    have hg_inj : Set.InjOn g (TypeIII (C := C) hDn) :=
      Shell4IsometryBasepoint.injMap_injOn (C := C) hDn (z0 := z0) (hz0Pat := hpat0)
    -- `TypeIII` injects into `Fin 24 × code`.
    have hcodeFinite : (code (C := C) hDn).Finite :=
      (Set.finite_univ.subset (Set.subset_univ _))
    have hprodFinite : ((Set.univ : Set (Fin 24)) ×ˢ (code (C := C) hDn)).Finite :=
      (Set.finite_univ.prod hcodeFinite)
    have hle :=
      Set.ncard_le_ncard_of_injOn (f := g) (t := (Set.univ : Set (Fin 24)) ×ˢ (code (C := C) hDn))
        hg_maps hg_inj hprodFinite
    have hcard_prod :
        Set.ncard ((Set.univ : Set (Fin 24)) ×ˢ (code (C := C) hDn)) =
          24 * Set.ncard (code (C := C) hDn) := by
      -- `ncard univ = 24` for `Fin 24`
      simp [Set.ncard_prod]
    simpa [hcard_prod] using! hle
  · -- empty
    simp [Set.not_nonempty_iff_eq_empty.1 hne]

end

/-!
## Forcing inequality and parameter extraction
-/

/-- Parameter forcing: the extracted code has `|code| = 2^12`, `N₈ = 759`, and `minDist = 8`. -/
public theorem forcing_parameters_codeFromLattice
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    Set.ncard (code (C := C) hDn) = 2 ^ 12 ∧
      Set.ncard (weight8Words (code (C := C) hDn)) = 759 ∧
      minDist (code (C := C) hDn) = 8 := by
  -- Combine shell subset and type bounds.
  have hshell : Set.ncard (shell4 C) = 196560 := ncard_shell4_eq_196560 (C := C) hEq
  have hI : Set.ncard (TypeI (C := C) hDn) ≤ 1104 := ncard_TypeI_le_1104 (C := C) hDn
  have hII :
      Set.ncard (TypeII (C := C) hDn) ≤ (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) :=
    ncard_TypeII_le (C := C) (hEq := hEq) (hDn := hDn)
  have hIII : Set.ncard (TypeIII (C := C) hDn) ≤ 24 * Set.ncard (code (C := C) hDn) :=
    ncard_TypeIII_le (C := C) (hDn := hDn)
  have hsub : shell4 C ⊆ TypeI (C := C) hDn ∪ TypeII (C := C) hDn ∪ TypeIII (C := C) hDn :=
    shell4_subset_TypeI_union_TypeII_union_TypeIII (C := C) (hEq := hEq) (hDn := hDn)
  have hshell_finite : (shell4 C).Finite := shell4_finite (C := C) hEq
  have hunion_finite :
      (TypeI (C := C) hDn ∪ TypeII (C := C) hDn ∪ TypeIII (C := C) hDn).Finite := by
    -- each type is a subset of `shell4`, so the union is a subset of `shell4`.
    refine hshell_finite.subset ?_
    intro u hu
    -- unions are left-associated: `(TypeI ∪ TypeII) ∪ TypeIII`
    rcases hu with hu12 | huIII
    · rcases hu12 with huI | huII
      · exact huI.1
      · exact huII.1
    · exact huIII.1
  have hshell_le :
      Set.ncard (shell4 C) ≤
        Set.ncard (TypeI (C := C) hDn ∪ TypeII (C := C) hDn ∪ TypeIII (C := C) hDn) :=
    Set.ncard_le_ncard hsub hunion_finite
  have hunion_le :
      Set.ncard (TypeI (C := C) hDn ∪ TypeII (C := C) hDn ∪ TypeIII (C := C) hDn) ≤
        Set.ncard (TypeI (C := C) hDn) + Set.ncard (TypeII (C := C) hDn) +
          Set.ncard (TypeIII (C := C) hDn) := by
    have h12 :
        Set.ncard (TypeI (C := C) hDn ∪ TypeII (C := C) hDn) ≤
          Set.ncard (TypeI (C := C) hDn) + Set.ncard (TypeII (C := C) hDn) :=
      Set.ncard_union_le (TypeI (C := C) hDn) (TypeII (C := C) hDn)
    have h123 :
        Set.ncard ((TypeI (C := C) hDn ∪ TypeII (C := C) hDn) ∪ TypeIII (C := C) hDn) ≤
          Set.ncard (TypeI (C := C) hDn ∪ TypeII (C := C) hDn) +
            Set.ncard (TypeIII (C := C) hDn) :=
      Set.ncard_union_le (TypeI (C := C) hDn ∪ TypeII (C := C) hDn) (TypeIII (C := C) hDn)
    exact le_add_of_le_add_right h123 h12
  have hforce :
      196560 ≤ 1104 + (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) +
        24 * Set.ncard (code (C := C) hDn) := by
    have hshell_bound :
        Set.ncard (shell4 C) ≤
          1104 + (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) +
            24 * Set.ncard (code (C := C) hDn) := by
      refine le_trans (le_trans hshell_le hunion_le) ?_
      -- add the three bounds
      nlinarith [hI, hII, hIII]
    simpa [hshell] using! hshell_bound
  -- Apply the global upper bounds and force equality.
  have hcode_le : Set.ncard (code (C := C) hDn) ≤ 2 ^ 12 :=
    ncard_code_le_two_pow12 (C := C) hEq hDn
  have hN8_le : Set.ncard (weight8Words (code (C := C) hDn)) ≤ 759 :=
    ncard_weight8Words_le_759 (C := C) hEq hDn
  have hmax :
      1104 + (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) +
          24 * Set.ncard (code (C := C) hDn) ≤
        196560 := by
    -- monotonicity in both factors
    have hle :
        1104 + (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) +
            24 * Set.ncard (code (C := C) hDn) ≤
        1104 + (2 ^ 7) * 759 + 24 * (2 ^ 12) := by
      nlinarith [hN8_le, hcode_le]
    -- compute the RHS
    have heq : 1104 + (2 ^ 7) * 759 + 24 * (2 ^ 12) = 196560 := by decide
    simpa [heq] using! hle
  have hEqAll :
      1104 + (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) +
          24 * Set.ncard (code (C := C) hDn) =
        196560 :=
    le_antisymm hmax hforce
  -- deduce `N8 = 759` and `|code| = 2^12` by a strictness argument
  have hN8_eq : Set.ncard (weight8Words (code (C := C) hDn)) = 759 := by
    by_contra hne
    have hlt : Set.ncard (weight8Words (code (C := C) hDn)) ≤ 758 := by
      have hlt' : Set.ncard (weight8Words (code (C := C) hDn)) < 759 :=
        lt_of_le_of_ne hN8_le hne
      -- `759 = 758 + 1`
      exact Nat.le_of_lt_succ (by simpa using! hlt')
    have hcontra :
        1104 + (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) +
            24 * Set.ncard (code (C := C) hDn) ≤
          196432 := by
      nlinarith [hlt, hcode_le]
    have hbad : (196560 : ℕ) ≤ 196432 := (le_of_eq hEqAll.symm).trans hcontra
    exact (by decide : ¬ ((196560 : ℕ) ≤ 196432)) hbad
  have hcode_eq : Set.ncard (code (C := C) hDn) = 2 ^ 12 := by
    by_contra hne
    have hlt : Set.ncard (code (C := C) hDn) ≤ 2 ^ 12 - 1 := by
      have hlt' : Set.ncard (code (C := C) hDn) < 2 ^ 12 := lt_of_le_of_ne hcode_le hne
      exact Nat.le_pred_of_lt hlt'
    have hcontra :
        1104 + (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) +
            24 * Set.ncard (code (C := C) hDn) ≤
          196536 := by
      -- Here we already know `N8 = 759`.
      have hmul : 24 * Set.ncard (code (C := C) hDn) ≤ 24 * (2 ^ 12 - 1) :=
        Nat.mul_le_mul_left 24 hlt
      have htmp :
          1104 + (2 ^ 7) * 759 + 24 * Set.ncard (code (C := C) hDn) ≤
            1104 + (2 ^ 7) * 759 + 24 * (2 ^ 12 - 1) :=
        Nat.add_le_add_left hmul (1104 + (2 ^ 7) * 759)
      have hle :
          1104 + (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) +
              24 * Set.ncard (code (C := C) hDn) ≤
            1104 + (2 ^ 7) * 759 + 24 * (2 ^ 12 - 1) := by
        -- rewrite `N8` to `759`, then use monotonicity in the `24 * |code|` term
        rw [hN8_eq]
        exact htmp
      have hcalc : 1104 + (2 ^ 7) * 759 + 24 * (2 ^ 12 - 1) = 196536 := by decide
      exact le_trans hle (le_of_eq hcalc)
    have hbad : (196560 : ℕ) ≤ 196536 := (le_of_eq hEqAll.symm).trans hcontra
    exact (by decide : ¬ ((196560 : ℕ) ≤ 196536)) hbad
  -- Now `minDist = 8` via existence of a weight-8 word.
  have hmin_ge : 8 ≤ minDist (code (C := C) hDn) :=
    minDist_ge_eight_codeFromLattice (C := C) hEq hDn
  have hN8_pos : 0 < Set.ncard (weight8Words (code (C := C) hDn)) := by
    have h759 : (0 : ℕ) < 759 := by decide
    rw [hN8_eq]
    exact h759
  have hfiniteW8 : (weight8Words (code (C := C) hDn)).Finite :=
    (Set.finite_univ.subset (Set.subset_univ _))
  have hnonempty : (weight8Words (code (C := C) hDn)).Nonempty :=
    (Set.ncard_pos (s := weight8Words (code (C := C) hDn)) hfiniteW8).1 hN8_pos
  rcases hnonempty with ⟨w, hw⟩
  have hwC : w ∈ code (C := C) hDn := hw.1
  have hw0 : w ≠ (0 : BinWord 24) := by
    intro h0
    have : weight w = 0 := by
      simp [h0, CodingTheory.weight]
    simpa [this] using! hw.2
  have hmin_le : minDist (code (C := C) hDn) ≤ 8 := by
    have h :=
      Uniqueness.BS81.Thm15.Lemma21.CodingTheory.minDist_le_weight_of_nonzero_mem
        (C := code (C := C) hDn) (CodeFromLattice.codeFromLattice_linear (C := C) hDn)
        (w := w) hwC hw0
    exact h.trans_eq (by simp [hw.2])
  have hmin_eq : minDist (code (C := C) hDn) = 8 := le_antisymm ( hmin_le) hmin_ge
  exact ⟨hcode_eq, hN8_eq, hmin_eq⟩

/-!
## Existence of a Type-III basepoint

The `196560` shell count forces the existence of at least one Type-III vector. We record this as a
standalone lemma.
-/

/-- In the equality case, `TypeIII` is nonempty, so we can choose a basepoint of type III. -/
public theorem exists_typeIII_basepoint
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    ∃ u : ℝ²⁴,
      u ∈ TypeIII (C := C) hDn ∧
        ∃ z : Fin 24 → ℤ,
          (∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ)) ∧ isPattern3 z := by
  -- If `TypeIII` were empty, the crude `TypeI` and `TypeII` bounds would give
  -- `|shell4| ≤ 1104 + 2^7 * 759`, contradicting `|shell4| = 196560`.
  by_cases hIII : (TypeIII (C := C) hDn).Nonempty
  · rcases hIII with ⟨u, hu⟩
    refine ⟨u, hu, ?_⟩
    rcases hu.2 with ⟨z, hz, hpat⟩
    exact ⟨z, hz, hpat⟩
  · have hshell : Set.ncard (shell4 C) = 196560 := ncard_shell4_eq_196560 (C := C) hEq
    have hsub123 : shell4 C ⊆ TypeI (C := C) hDn ∪ TypeII (C := C) hDn ∪ TypeIII (C := C) hDn :=
      shell4_subset_TypeI_union_TypeII_union_TypeIII (C := C) (hEq := hEq) (hDn := hDn)
    have hshell_finite : (shell4 C).Finite := shell4_finite (C := C) hEq
    have hIII_empty : TypeIII (C := C) hDn = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 (fun u hu => hIII ⟨u, hu⟩)
    have hsub12 : shell4 C ⊆ TypeI (C := C) hDn ∪ TypeII (C := C) hDn := by
      simpa [hIII_empty, union_assoc] using! hsub123
    have h12_finite : (TypeI (C := C) hDn ∪ TypeII (C := C) hDn).Finite := by
      -- each type is a subset of `shell4`, so the union is a subset of `shell4`.
      refine hshell_finite.subset ?_
      intro u hu
      rcases hu with huI | huII
      · exact huI.1
      · exact huII.1
    have hshell_le : Set.ncard (shell4 C) ≤ Set.ncard (TypeI (C := C) hDn ∪ TypeII (C := C) hDn) :=
      Set.ncard_le_ncard hsub12 h12_finite
    have hI : Set.ncard (TypeI (C := C) hDn) ≤ 1104 := ncard_TypeI_le_1104 (C := C) hDn
    have hII :
        Set.ncard (TypeII (C := C) hDn) ≤ (2 ^ 7) * 759 := by
      have hII' :
          Set.ncard (TypeII (C := C) hDn) ≤
            (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) :=
        ncard_TypeII_le (C := C) (hEq := hEq) (hDn := hDn)
      have hW8 : Set.ncard (weight8Words (code (C := C) hDn)) ≤ 759 :=
        ncard_weight8Words_le_759 (C := C) (hEq := hEq) (hDn := hDn)
      exact le_trans hII' (Nat.mul_le_mul_left (2 ^ 7) hW8)
    have hcontra : Set.ncard (shell4 C) ≤ 1104 + (2 ^ 7) * 759 := by
      have h12_le :
          Set.ncard (TypeI (C := C) hDn ∪ TypeII (C := C) hDn) ≤
            Set.ncard (TypeI (C := C) hDn) + Set.ncard (TypeII (C := C) hDn) :=
        Set.ncard_union_le (TypeI (C := C) hDn) (TypeII (C := C) hDn)
      have h12_le' :
          Set.ncard (TypeI (C := C) hDn ∪ TypeII (C := C) hDn) ≤ 1104 + (2 ^ 7) * 759 := by
        exact le_trans h12_le (Nat.add_le_add hI hII)
      exact le_trans hshell_le (by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using! h12_le')
    have : ¬ ((196560 : ℕ) ≤ 1104 + (2 ^ 7) * 759) := by decide
    exact (this ((le_of_eq hshell.symm).trans hcontra)).elim

end CodeIsGolayCountFinal

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
