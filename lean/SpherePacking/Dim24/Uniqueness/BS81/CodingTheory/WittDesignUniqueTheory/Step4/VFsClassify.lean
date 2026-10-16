-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneUniqueness.PairIdx
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.Step4.Auxiliary
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.Step4.Step4VertexFamilies
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.Step4.VertexFamilyClassify
import Mathlib.Tactic.ByContra

/-!
# Step 4: certifying and classifying recovered vertex families

Assume Step 3 identifies the extracted triple system with the canonical `2-(6,3,2)` design.
For `x ∈ B0`, the finset `famIdx x` is defined as the set of canonical block indices coming from
the four blocks through `x` other than `B0`.

This file proves:
* `famIdx x` satisfies the vertex-family conditions, and
* therefore `famIdx x` is one of the five canonical families `famA'` through `famE'`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace Design23632

/-- Build `List.Pairwise R` from a `Nodup` list and a membership-based hypothesis. -/
public lemma pairwise_of_nodup_of_forall_mem
    {R : BlockIdx → BlockIdx → Prop} {L : List BlockIdx} (hN : L.Nodup)
    (hR : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → R i j) :
    L.Pairwise R :=
  List.Nodup.pairwise_of_forall_ne hN hR

end Design23632

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Step4.Aux4

variable (D : Biplane.Structure) {B0 : Biplane.Block}

lemma exists_block_through_pair
    {x u : Biplane.Point} (hxu : x ≠ u) :
    ∃ B : Biplane.Block, B ∈ D.blocks ∧ x ∈ B ∧ u ∈ B := by
  have hlam : D.lam x u = 2 := Biplane.Structure.lam_eq_two (D := D) (x := x) (y := u) hxu
  have hcard :
      (D.blocks.filter fun B : Biplane.Block => x ∈ B ∧ u ∈ B).card = 2 := by
    simpa [Biplane.Structure.lam] using! hlam
  have hpos : 0 < (D.blocks.filter fun B : Biplane.Block => x ∈ B ∧ u ∈ B).card := by
    simp [hcard]
  rcases Finset.card_pos.1 hpos with ⟨B, hB⟩
  grind only [= Finset.mem_filter]

/-- If `B` and `B'` are distinct blocks through `x` (other than `B0`), then the associated triples
`tripleOfBlock e B` and `tripleOfBlock e B'` intersect in exactly one point. -/
public lemma tripleOfBlock_inter_card_one
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    {x : Biplane.Point} (hx : x ∈ B0)
    {B B' : Biplane.Block} (hB : B ∈ blocksThroughB0 (D := D) (B0 := B0) x)
    (hB' : B' ∈ blocksThroughB0 (D := D) (B0 := B0) x) (hne : B ≠ B') :
    (tripleOfBlock (B0 := B0) e B ∩ tripleOfBlock (B0 := B0) e B').card = 1 := by
  have hBerase : B ∈ D.blocks.erase B0 := (Finset.mem_filter.1 hB).1
  have hB'erase : B' ∈ D.blocks.erase B0 := (Finset.mem_filter.1 hB').1
  have hBmem : B ∈ D.blocks := (Finset.mem_erase.1 hBerase).2
  have hB'mem : B' ∈ D.blocks := (Finset.mem_erase.1 hB'erase).2
  have hBne0 : B ≠ B0 := (Finset.mem_erase.1 hBerase).1
  have hB'ne0 : B' ≠ B0 := (Finset.mem_erase.1 hB'erase).1
  have hxB : x ∈ B := (Finset.mem_filter.1 hB).2
  have hxB' : x ∈ B' := (Finset.mem_filter.1 hB').2
  have hinter : (B ∩ B').card = 2 := D.inter_card (B := B) (B' := B') hBmem hB'mem hne
  have hinterB0 : (B ∩ B' ∩ B0) = ({x} : Finset Biplane.Point) := by
    have hxInt : x ∈ B ∩ B' ∩ B0 := by
      simp [hxB, hxB', hx]
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨hxInt, ?_⟩
    intro y hy
    have hyB : y ∈ B := (Finset.mem_inter.1 (Finset.mem_inter.1 hy).1).1
    have hyB' : y ∈ B' := (Finset.mem_inter.1 (Finset.mem_inter.1 hy).1).2
    have hyB0 : y ∈ B0 := (Finset.mem_inter.1 hy).2
    by_contra hyx
    have hBspec : B ∈ D.blocks ∧ x ∈ B ∧ y ∈ B ∧ B ≠ B0 := ⟨hBmem, hxB, hyB, hBne0⟩
    have hB'spec : B' ∈ D.blocks ∧ x ∈ B' ∧ y ∈ B' ∧ B' ≠ B0 := ⟨hB'mem, hxB', hyB', hB'ne0⟩
    have huniq := BiplaneUniqueness.Aux.exists_unique_other_block_through_pair
      (D := D) (B0 := B0) hB0 (x := x) (y := y) hx hyB0 (Ne.symm hyx)
    have : B = B' := ExistsUnique.unique huniq hBspec hB'spec
    exact hne this
  have hOutsideCard : ((B \ B0) ∩ (B' \ B0)).card = 1 := by
    have hEq : ((B \ B0) ∩ (B' \ B0)) = ((B ∩ B') \ B0) := by
      ext y
      simp [and_left_comm, and_assoc, and_comm]
    grind only [= Finset.card_sdiff, usr Finset.card_sdiff_add_card_inter, = Finset.card_singleton]
  let outsideU := Step3.outsideU (B0 := B0)
  have hOutsideUCard : ((outsideU B) ∩ (outsideU B')).card = 1 := by
    have hmap :
        (((outsideU B) ∩ (outsideU B')).map (valEmb (B0 := B0))) = ((B \ B0) ∩ (B' \ B0)) := by
      simp [outsideU, Finset.map_inter, outsideU_map_val (B0 := B0) (B := B),
        outsideU_map_val (B0 := B0) (B := B')]
    have hcardMap :
        ((outsideU B) ∩ (outsideU B')).card =
          (((outsideU B) ∩ (outsideU B')).map (valEmb (B0 := B0))).card :=
      Eq.symm (Finset.card_map (valEmb B0))
    have : (((outsideU B) ∩ (outsideU B')).map (valEmb (B0 := B0))).card = 1 := by
      simpa [hmap] using! hOutsideCard
    exact hcardMap.trans this
  have hmap_inter :
      ((outsideU B) ∩ (outsideU B')).map e.toEmbedding =
        (tripleOfBlock (B0 := B0) e B ∩ tripleOfBlock (B0 := B0) e B') := by
    simp [outsideU, tripleOfBlock, Finset.map_inter]
  -- combine using `card_map` and `hmap_inter`
  calc
    (tripleOfBlock (B0 := B0) e B ∩ tripleOfBlock (B0 := B0) e B').card
        = (((outsideU B) ∩ (outsideU B')).map e.toEmbedding).card := by
            exact (congrArg Finset.card hmap_inter).symm
    _ = ((outsideU B) ∩ (outsideU B')).card := by
            simp
    _ = 1 := hOutsideUCard

/-- Any two distinct canonical blocks in `famIdx x` intersect in exactly one point. -/
public lemma blk_inter_card_one_of_mem_famIdx
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    {x : Biplane.Point} (hx : x ∈ B0)
    {i j : Design23632.BlockIdx} (hi : i ∈ famIdx (D := D) (B0 := B0) e x)
    (hj : j ∈ famIdx (D := D) (B0 := B0) e x) (hij : i ≠ j) :
    (Design23632.blk i ∩ Design23632.blk j).card = 1 := by
  have hi' : Design23632.blk i ∈ famBlocks (D := D) (B0 := B0) e x := (Finset.mem_filter.1 hi).2
  have hj' : Design23632.blk j ∈ famBlocks (D := D) (B0 := B0) e x := (Finset.mem_filter.1 hj).2
  rcases Finset.mem_image.1 hi' with ⟨B, hB, hBi⟩
  rcases Finset.mem_image.1 hj' with ⟨B', hB', hB'j⟩
  have hneBB' : B ≠ B' := by
    intro hEq
    apply hij
    have : Design23632.blk i = Design23632.blk j := by
      calc
        Design23632.blk i = tripleOfBlock (B0 := B0) e B := hBi.symm
        _ = tripleOfBlock (B0 := B0) e B' := by subst hEq; rfl
        _ = Design23632.blk j := hB'j
    exact blk_injective this
  simpa [hBi, hB'j] using!
    tripleOfBlock_inter_card_one (D := D) (B0 := B0) hB0 (e := e) (x := x) hx hB hB' hneBB'

/-- The union of canonical blocks in `famIdx x` is all of `Fin 6`. -/
public lemma famIdx_sup_blk_eq_univ
    {B0 : Biplane.Block}
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    {x : Biplane.Point} (hx : x ∈ B0)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    (famIdx (D := D) (B0 := B0) e x).sup Design23632.blk = Finset.univ := by
  ext p
  constructor
  · intro _
    simp
  · intro _
    refine (Finset.mem_sup.2 ?_)
    let u : Step3.UPoint (B0 := B0) := e.symm p
    have hxu : x ≠ u.1 := by
      intro hEq
      have hxB0' : u.1 ∈ B0 := by simpa [hEq] using! hx
      have huB0 : u.1 ∉ B0 := Step3.Aux.not_mem_B0 (B0 := B0) u
      exact huB0 hxB0'
    rcases exists_block_through_pair (D := D) (x := x) (u := u.1) hxu with ⟨B, hBmem, hxB, huB⟩
    have hBne0 : B ≠ B0 := by
      intro hEq
      have huNot : u.1 ∉ B0 := Step3.Aux.not_mem_B0 (B0 := B0) u
      have : u.1 ∈ B0 := by simpa [hEq] using! huB
      exact huNot this
    have hBerase : B ∈ D.blocks.erase B0 := by
      simp [hBmem, hBne0]
    have htriple_mem : tripleOfBlock (B0 := B0) e B ∈ Design23632.canonicalBlocks := by
      have : tripleOfBlock (B0 := B0) e B ∈ Step3.tripleSystem6 (D := D) (B0 := B0) e :=
        tripleOfBlock_mem_tripleSystem6 (D := D) (B0 := B0) (B := B) hBerase e
      simpa [hT] using! this
    have htriple_img :
        tripleOfBlock (B0 := B0) e B ∈ Finset.univ.image Design23632.blk := by
      simpa [canonicalBlocks_eq_image_blk] using! htriple_mem
    rcases Finset.mem_image.1 htriple_img with ⟨i, hi, hEq⟩
    have hiFam : i ∈ famIdx (D := D) (B0 := B0) e x := by
      refine Finset.mem_filter.2 ?_
      refine ⟨by simp, ?_⟩
      have : Design23632.blk i ∈ famBlocks (D := D) (B0 := B0) e x := by
        refine Finset.mem_image.2 ?_
        have hBx : B ∈ blocksThroughB0 (D := D) (B0 := B0) x := by
          simp [blocksThroughB0, hBerase, hxB]
        refine ⟨B, hBx, ?_⟩
        exact hEq.symm
      exact this
    have hpblk : p ∈ Design23632.blk i := by
      have huOutside : u ∈ Step3.outsideU (B0 := B0) B :=
        (mem_outsideU_iff_mem_block (B0 := B0) (u := u) (B := B)).2 huB
      have : p ∈ tripleOfBlock (B0 := B0) e B :=
        (mem_tripleOfBlock_iff (B0 := B0) (e := e) (B := B) (p := p)).2
          (by simpa [u] using! huOutside)
      simpa [hEq, tripleOfBlock] using! this
    exact ⟨i, hiFam, hpblk⟩

/-- `famIdx x` satisfies the boolean vertex-family predicate `isVertexFamilyIdxB₄`. -/
public lemma famIdx_isVertexFamilyIdxB₄
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    {x : Biplane.Point} (hx : x ∈ B0)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    Design23632.isVertexFamilyIdxB₄
        (Design23632.listOfFam (famIdx (D := D) (B0 := B0) e x)) = true := by
  let L := Design23632.listOfFam (famIdx (D := D) (B0 := B0) e x)
  have hlen : L.length = 4 := by
    have := Design23632.listOfFam_length (F := famIdx (D := D) (B0 := B0) e x)
    simpa [L, famIdx_card (D := D) (B0 := B0) hB0 (e := e) (x := x) hx hT] using! this
  have hnodup : L.Nodup := by
    simpa [L] using! Design23632.listOfFam_nodup (F := famIdx (D := D) (B0 := B0) e x)
  have hpairs : Design23632.allPairsInterOneB L = true := by
    have hPairwise :
        Design23632.PairwiseInterOne L := by
      refine (Design23632.pairwise_of_nodup_of_forall_mem
        (R := fun i j => (Design23632.blk i ∩ Design23632.blk j).card = 1)
        (L := L) hnodup ?_)
      intro i hi j hj hij
      have hi' : i ∈ famIdx (D := D) (B0 := B0) e x := by
        simpa [Design23632.mem_listOfFam_iff, L] using! hi
      have hj' : j ∈ famIdx (D := D) (B0 := B0) e x := by
        simpa [Design23632.mem_listOfFam_iff, L] using! hj
      exact blk_inter_card_one_of_mem_famIdx (D := D) (B0 := B0) hB0 (e := e) hx hi' hj' hij
    exact (Design23632.allPairsInterOneB_eq_true_iff L).2 hPairwise
  have hunion : ((L.toFinset.image Design23632.blk).sup id) = Finset.univ := by
    -- rewrite the image-`sup` to indices, then apply `famIdx_sup_blk_eq_univ`.
    have hto : L.toFinset = famIdx (D := D) (B0 := B0) e x := by
      simpa [L] using! (Design23632.listOfFam_toFinset (F := famIdx (D := D) (B0 := B0) e x))
    -- move to `Finset.sup` over indices
    simpa [hto, Finset.sup_image] using!
      (famIdx_sup_blk_eq_univ (D := D) (B0 := B0) (e := e) (x := x) hx hT)
  -- conclude by unfolding the boolean predicate
  simp [Design23632.isVertexFamilyIdxB₄, L, hlen, hnodup, hpairs, hunion]

/-- Classify `famIdx x` as one of the five canonical vertex families. -/
public lemma classify_famIdx
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    {x : Biplane.Point} (hx : x ∈ B0)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    famIdx (D := D) (B0 := B0) e x =
        Design23632.famA' ∨ famIdx (D := D) (B0 := B0) e x = Design23632.famB' ∨
        famIdx (D := D) (B0 := B0) e x = Design23632.famC' ∨
        famIdx (D := D) (B0 := B0) e x = Design23632.famD' ∨
        famIdx (D := D) (B0 := B0) e x = Design23632.famE' := by
  exact Design23632.classify_vertexFamilyIdxB₄_toFinset
    (F := famIdx (D := D) (B0 := B0) e x)
    (hF := famIdx_isVertexFamilyIdxB₄ (D := D) (B0 := B0) hB0 (e := e) (x := x) hx hT)

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Step4.Aux4
end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
