-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Design23632Unique
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneUniqueness.Extract
import Mathlib.Data.Fintype.EquivFin

/-!
# Relabelling the extracted `2-(6,3,2)` design

Starting from the extracted triple system on the complement `U₀ = univ \ B₀` of a block in a
biplane, we transport it to the canonical point type of the `2-(6,3,2)` design (`Design23632`).
The main result is `tripleSystem6_is23632`, which packages the axioms as
`Design23632.Is23632 (tripleSystem6 ...)`, so that one can apply `Design23632.unique_up_to_relabel`.

This corresponds to Step 3 in the proof of Theorem `thm:biplane_unique` in the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`, using Lemma `lem:23632_unique`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Step3

noncomputable section

variable (D : Biplane.Structure) {B0 : Biplane.Block}

/-- The complement of the distinguished block `B0`, as a finset of points. -/
public abbrev U0 : Finset Biplane.Point :=
  Aux.U0 (B0 := B0)

/-- The point type of the complement `U0 = univ \\ B0`. -/
public abbrev UPoint : Type :=
  {x : Biplane.Point // x ∈ U0 (B0 := B0)}

/-- The outside part, but reinterpreted as a finset of points in the subtype `UPoint`. -/
@[expose] public noncomputable def outsideU (B : Biplane.Block) : Finset (UPoint (B0 := B0)) :=
  ((Aux.outside (B0 := B0) B).attach).map
    { toFun := fun x => ⟨x.1, (Aux.outside_subset_U0 (B0 := B0) (B := B)) x.2⟩
      inj' := by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun u : UPoint (B0 := B0) => u.1) h }

/-- The extracted triple system, viewed as blocks on the subtype `UPoint`. -/
@[expose] public noncomputable def tripleSystemU (D : Biplane.Structure) (B0 : Biplane.Block) :
    Finset (Finset (UPoint (B0 := B0))) :=
  (D.blocks.erase B0).image (fun B => outsideU (B0 := B0) B)

/-- Transport the extracted triple system to `Design23632.Point` along an equivalence. -/
@[expose] public noncomputable def tripleSystem6 (D : Biplane.Structure) (B0 : Biplane.Block)
    (e : Equiv (UPoint (B0 := B0)) Design23632.Point) :
    Finset Design23632.Block :=
  (tripleSystemU (D := D) (B0 := B0)).image (fun t => t.map e.toEmbedding)

namespace Aux

open scoped BigOperators

/-- A point of `UPoint` is not a member of the distinguished block `B0`. -/
public lemma not_mem_B0 (u : UPoint (B0 := B0)) : u.1 ∉ B0 := by
  simpa using! (BiplaneUniqueness.Aux.mem_U0_iff (B0 := B0) (x := u.1)).1 u.2

lemma card_UPoint (hB0 : B0 ∈ D.blocks) : Fintype.card (UPoint (B0 := B0)) = 6 := by
 calc
    Fintype.card (UPoint (B0 := B0))
        = (U0 (B0 := B0)).card := by
            -- `UPoint` is definitionally `{x // x ∈ U0}`.
            simp [UPoint]
    _ = 6 := by
          simpa using! (BiplaneUniqueness.Aux.U0_card (D := D) (B0 := B0) hB0)

noncomputable def chooseEquiv6 (hB0 : B0 ∈ D.blocks) :
    Equiv (UPoint (B0 := B0)) Design23632.Point :=
  Fintype.equivFinOfCardEq (card_UPoint (D := D) (B0 := B0) hB0)

lemma mem_outsideU_iff {u : UPoint (B0 := B0)} {B : Biplane.Block} :
    u ∈ outsideU (B0 := B0) B ↔ u.1 ∈ Aux.outside (B0 := B0) B := by
  constructor
  · intro hu
    rcases Finset.mem_map.1 hu with ⟨x, _hx, hxEq⟩
    have : u.1 = x.1 := congrArg Subtype.val hxEq.symm
    exact this.symm ▸ x.2
  · intro hu
    refine Finset.mem_map.2 ⟨⟨u.1, hu⟩, by simp, ?_⟩
    exact Subtype.ext rfl

attribute [grind =] mem_outsideU_iff

/-- Membership in `outsideU B` is equivalent to membership of the underlying point in `B`. -/
public lemma mem_outsideU_iff_mem_block {u : UPoint (B0 := B0)} {B : Biplane.Block} :
    u ∈ outsideU (B0 := B0) B ↔ u.1 ∈ B := by
  have huB0 : u.1 ∉ B0 := not_mem_B0 (B0 := B0) u
  grind (splits := 0) only [mem_outsideU_iff, Aux.mem_outside_iff, Finset.mem_sdiff]

attribute [grind =] mem_outsideU_iff_mem_block

lemma injOn_outsideU_erase (hB0 : B0 ∈ D.blocks) :
    Set.InjOn (fun B : Biplane.Block => outsideU (B0 := B0) B) (D.blocks.erase B0) := by
  intro B hB B' hB' hEq
  by_cases hne : B = B'
  · exact hne
  · exfalso
    -- Reduce to a contradiction from `B ≠ B'`.
    -- (Working in `False` avoids needing `by_contra`/`Classical`.)
    have hBmem : B ∈ D.blocks := (Finset.mem_erase.1 hB).2
    have hB'mem : B' ∈ D.blocks := (Finset.mem_erase.1 hB').2
    have hBne0 : B ≠ B0 := (Finset.mem_erase.1 hB).1
    have hOutsideB : (Aux.outside (B0 := B0) B).card = 3 :=
      Aux.outside_card_eq_three (D := D) (B0 := B0) (hB0 := hB0) (hB := hBmem) (hne := hBne0)
    have hsub : Aux.outside (B0 := B0) B ⊆ B ∩ B' := by
      intro x hx
      refine Finset.mem_inter.2 ⟨(Finset.mem_sdiff.1 hx).1, ?_⟩
      have hxB0 : x ∉ B0 := (Finset.mem_sdiff.1 hx).2
      let u : UPoint (B0 := B0) :=
        ⟨x, (BiplaneUniqueness.Aux.mem_U0_iff (B0 := B0) (x := x)).2 hxB0⟩
      have huB : u ∈ outsideU (B0 := B0) B :=
        (mem_outsideU_iff (B0 := B0) (u := u) (B := B)).2 hx
      have huB' : u ∈ outsideU (B0 := B0) B' := by simpa [hEq] using! huB
      exact (mem_outsideU_iff_mem_block (B0 := B0) (u := u) (B := B')).1 huB'
    have hcard_le : 3 ≤ (B ∩ B').card := by
      simpa [hOutsideB] using! (Finset.card_le_card hsub)
    have hinter : (B ∩ B').card = 2 := D.inter_card (B := B) (B' := B') hBmem hB'mem hne
    have : 3 ≤ 2 := by
      exact le_of_le_of_eq hcard_le hinter
    exact (by decide : ¬ (3 ≤ 2)) this

lemma tripleSystemU_card (hB0 : B0 ∈ D.blocks) :
    (tripleSystemU (D := D) (B0 := B0)).card = 10 := by
  have hErase : (D.blocks.erase B0).card = 10 := by
    simpa [D.blocks_card] using! (Finset.card_erase_of_mem hB0)
  -- `outsideU` is injective on `blocks.erase B0`, so `card (image outsideU ...) = card ...`.
  have hInj : Set.InjOn (fun B : Biplane.Block => outsideU (B0 := B0) B) (D.blocks.erase B0) :=
    injOn_outsideU_erase (D := D) (B0 := B0) hB0
  simpa [tripleSystemU, hErase] using! (Finset.card_image_of_injOn (s := D.blocks.erase B0) hInj)

lemma tripleSystemU_block_card (hB0 : B0 ∈ D.blocks)
    (t : Finset (UPoint (B0 := B0))) (ht : t ∈ tripleSystemU (D := D) (B0 := B0)) :
    t.card = 3 := by
  rcases Finset.mem_image.1 ht with ⟨B, hB, rfl⟩
  have hBmem : B ∈ D.blocks := (Finset.mem_erase.1 hB).2
  have hBne0 : B ≠ B0 := (Finset.mem_erase.1 hB).1
  have hOutside : (Aux.outside (B0 := B0) B).card = 3 :=
    Aux.outside_card_eq_three (D := D) (B0 := B0) (hB0 := hB0) (hB := hBmem) (hne := hBne0)
  -- `outsideU` is a `Finset.map` of `outside.attach`, hence preserves card.
  have hcard : (outsideU (B0 := B0) B).card = (Aux.outside (B0 := B0) B).card := by
    simp [outsideU]
  simpa [hOutside] using! hcard

lemma tripleSystemU_pairCount (hB0 : B0 ∈ D.blocks)
    (u v : UPoint (B0 := B0)) (huv : u ≠ v) :
    ((tripleSystemU (D := D) (B0 := B0)).filter fun t => u ∈ t ∧ v ∈ t).card = 2 := by
  let f : Biplane.Block → Finset (UPoint (B0 := B0)) := fun B => outsideU (B0 := B0) B
  have hInj : Set.InjOn f (D.blocks.erase B0) := injOn_outsideU_erase (D := D) (B0 := B0) hB0
  have hfilter :
      (tripleSystemU (D := D) (B0 := B0)).filter (fun t => u ∈ t ∧ v ∈ t) =
        ((D.blocks.erase B0).filter fun B => u ∈ f B ∧ v ∈ f B).image f := by
    simpa [tripleSystemU, f] using!
      (Finset.filter_image (s := D.blocks.erase B0) (f := f) (p := fun t => u ∈ t ∧ v ∈ t))
  have hInj' : Set.InjOn f ((D.blocks.erase B0).filter fun B => u ∈ f B ∧ v ∈ f B) := by
    intro B hB B' hB' hEq
    exact hInj (x₁ := B) (Finset.mem_filter.1 hB).1 (x₂ := B') (Finset.mem_filter.1 hB').1 hEq
  have hcard :
      ((tripleSystemU (D := D) (B0 := B0)).filter fun t => u ∈ t ∧ v ∈ t).card =
        ((D.blocks.erase B0).filter fun B => u ∈ f B ∧ v ∈ f B).card := by
    simpa [hfilter] using!
      (Finset.card_image_of_injOn hInj')
  have huB0 : u.1 ∉ B0 := not_mem_B0 (B0 := B0) u
  have hnotmem : B0 ∉ D.blocks.filter (fun B => u.1 ∈ B ∧ v.1 ∈ B) := by
    intro hmem
    exact huB0 (Finset.mem_filter.1 hmem).2.1
  have hEraseEq :
      ((D.blocks.erase B0).filter fun B => u.1 ∈ B ∧ v.1 ∈ B) =
        D.blocks.filter fun B => u.1 ∈ B ∧ v.1 ∈ B := by
    simpa [Finset.erase_eq_of_notMem hnotmem] using!
      (Finset.filter_erase (s := D.blocks) (p := fun B => u.1 ∈ B ∧ v.1 ∈ B) B0)
  have huv' : u.1 ≠ v.1 :=
    Subtype.coe_ne_coe.mpr huv
  calc
    ((tripleSystemU (D := D) (B0 := B0)).filter fun t => u ∈ t ∧ v ∈ t).card
        = ((D.blocks.erase B0).filter fun B => u ∈ f B ∧ v ∈ f B).card := hcard
    _ = ((D.blocks.erase B0).filter fun B => u.1 ∈ B ∧ v.1 ∈ B).card := by
          refine congrArg Finset.card ?_
          ext B
          simp [f, mem_outsideU_iff_mem_block (B0 := B0)]
    _ = (D.blocks.filter fun B => u.1 ∈ B ∧ v.1 ∈ B).card := by
          simp [hEraseEq]
    _ = 2 := by
          simpa [Biplane.Structure.lam] using!
            (Biplane.Structure.lam_eq_two (D := D) (x := u.1) (y := v.1) huv')

lemma inj_map_equiv (e : Equiv (UPoint (B0 := B0)) Design23632.Point) :
    Function.Injective (fun t : Finset (UPoint (B0 := B0)) => t.map e.toEmbedding) := by
  simpa using! (Finset.map_injective e.toEmbedding)

attribute [grind inj] inj_map_equiv

lemma mem_map_equiv
    (e : Equiv (UPoint (B0 := B0)) Design23632.Point)
    (t : Finset (UPoint (B0 := B0))) (a : Design23632.Point) :
    a ∈ t.map e.toEmbedding ↔ e.symm a ∈ t := by
  simp

attribute [grind =] mem_map_equiv

end Aux

/-- The transported triple system on `Design23632.Point` satisfies the `2-(6,3,2)` axioms. -/
public theorem tripleSystem6_is23632 :
    ∀ {B0 : Biplane.Block}, B0 ∈ D.blocks →
      ∃ e : Equiv (UPoint (B0 := B0)) Design23632.Point,
        Design23632.Is23632 (tripleSystem6 (D := D) (B0 := B0) e) := by
  intro B0 hB0
  let e : Equiv (UPoint (B0 := B0)) Design23632.Point := Aux.chooseEquiv6 (D := D) (B0 := B0) hB0
  refine ⟨e, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- card = 10
    have hT : (tripleSystemU (D := D) (B0 := B0)).card = 10 :=
      Aux.tripleSystemU_card (D := D) (B0 := B0) hB0
    have hInj : Set.InjOn (fun t : Finset (UPoint (B0 := B0)) => t.map e.toEmbedding)
        (tripleSystemU (D := D) (B0 := B0)) := by
      intro t _ht t' _ht' hEq
      exact (Aux.inj_map_equiv (B0 := B0) (e := e)) hEq
    have hcardImage :
        (tripleSystem6 (D := D) (B0 := B0) e).card = (tripleSystemU (D := D) (B0 := B0)).card := by
      simpa [tripleSystem6] using! (Finset.card_image_of_injOn hInj)
    simpa [hT] using! congrArg id hcardImage
  · -- every block has card 3
    intro B hB
    rcases Finset.mem_image.1 hB with ⟨t, ht, rfl⟩
    have htCard : t.card = 3 := Aux.tripleSystemU_block_card (D := D) (B0 := B0) hB0 t ht
    simpa
  · -- each pair appears exactly twice
    intro a b hab
    have hab' : (e.symm a) ≠ (e.symm b) := by
      simpa
    -- express `pairCount` as a subtype-level count via `filter_image` and injectivity of `map e`.
    let f : Finset (UPoint (B0 := B0)) → Design23632.Block := fun t => t.map e.toEmbedding
    let S := tripleSystemU (D := D) (B0 := B0)
    let P : Finset (UPoint (B0 := B0)) → Prop := fun t => (e.symm a) ∈ t ∧ (e.symm b) ∈ t
    have hfilter :
        (tripleSystem6 (D := D) (B0 := B0) e).filter (fun B => a ∈ B ∧ b ∈ B) =
          (S.filter P).image f := by
      simpa [S, P, tripleSystem6, f, Aux.mem_map_equiv, and_left_comm, and_assoc, and_comm] using!
        (Finset.filter_image (s := S) (f := f) (p := fun B => a ∈ B ∧ b ∈ B))
    have hInj : Set.InjOn f
        (S.filter P) := by
      intro t _ht t' _ht' hEq
      exact (Aux.inj_map_equiv (B0 := B0) (e := e)) hEq
    have hcardImage :
        ((tripleSystem6 (D := D) (B0 := B0) e).filter (fun B => a ∈ B ∧ b ∈ B)).card =
          (S.filter P).card := by
      simpa [hfilter] using! (Finset.card_image_of_injOn hInj)
    have h2 : (S.filter P).card = 2 := by
      simpa [S, P] using!
        Aux.tripleSystemU_pairCount (D := D) (B0 := B0) hB0 (e.symm a) (e.symm b) hab'
    -- unfold `pairCount` and conclude
    simpa [Design23632.pairCount, hcardImage] using! h2

/-- Relabel `tripleSystem6` to the canonical list of blocks for the `2-(6,3,2)` design. -/
public theorem exists_relabel_to_canonicalBlocks
    {B0 : Biplane.Block}
    {e : Equiv (UPoint (B0 := B0)) Design23632.Point}
    (hT : Design23632.Is23632 (tripleSystem6 (D := D) (B0 := B0) e)) :
    ∃ σ : Equiv Design23632.Point Design23632.Point,
      Design23632.mapDesign σ (tripleSystem6 (D := D) (B0 := B0) e) =
        Design23632.canonicalBlocks := by
  simpa using! Design23632.unique_up_to_relabel
    (T := tripleSystem6 (D := D) (B0 := B0) e) hT

end

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Step3

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
