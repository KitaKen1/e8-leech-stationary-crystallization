-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneUniqueness.PairIdx
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneUniqueness.Relabel
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.Step4.Auxiliary
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.Step4.VertexFamilyClassify
import Mathlib.Tactic.ByContra

/-!
# Step 4: vertex families coming from `B0`

Assume Step 3 identifies the extracted triple system with the canonical `2-(6,3,2)` blocks. For a
point `x ∈ B0`, we consider the four blocks through `x` other than `B0`, map them to triples in
`U0`, and transport them to `Design23632`. The resulting `4`-subset of block indices is the vertex
family associated to `x`.

This file packages the basic constructions (`blocksThroughB0`, `tripleOfBlock`, `famIdx`) and the
cardinality and injectivity lemmas needed in the Step 4 reconstruction.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Step4.Aux4

noncomputable section

variable (D : Biplane.Structure) {B0 : Biplane.Block}

/-- Compose the Step 3 equivalence `e` with a relabeling `σ` of `Design23632.Point`. -/
public abbrev e₁
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (σ : Equiv Design23632.Point Design23632.Point) :
    Equiv (Step3.UPoint (B0 := B0)) Design23632.Point :=
  e.trans σ

/-- Mapping `tripleSystem6` by `σ` is the same as replacing `e` by `e₁`. -/
public lemma tripleSystem6_mapDesign
    {e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point}
    {σ : Equiv Design23632.Point Design23632.Point} :
    Design23632.mapDesign σ (Step3.tripleSystem6 (D := D) (B0 := B0) e) =
      Step3.tripleSystem6 (D := D) (B0 := B0) (e₁ (B0 := B0) e σ) := by
  ext B
  constructor <;> intro hB
  · rcases (Design23632.mem_mapDesign (σ := σ)
        (T := Step3.tripleSystem6 (D := D) (B0 := B0) e) (B := B)).1 hB with ⟨B0', hB0', rfl⟩
    rcases Finset.mem_image.1 hB0' with ⟨t, ht, rfl⟩
    refine Finset.mem_image.2 ⟨t, ht, ?_⟩
    simp [e₁, Finset.map_map]
  · rcases Finset.mem_image.1 hB with ⟨t, ht, rfl⟩
    refine (Design23632.mem_mapDesign (σ := σ)
        (T := Step3.tripleSystem6 (D := D) (B0 := B0) e)
        (B := (t.map (e₁ (B0 := B0) e σ).toEmbedding))).2 ?_
    refine ⟨t.map e.toEmbedding, Finset.mem_image.2 ⟨t, ht, rfl⟩, ?_⟩
    simp [e₁, Finset.map_map]

/-- A `mapDesign` hypothesis can be rewritten as an equality for `tripleSystem6` with `e₁`. -/
public lemma tripleSystem6_eq_canonical
    {e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point}
    {σ : Equiv Design23632.Point Design23632.Point}
    (hσ :
      Design23632.mapDesign σ (Step3.tripleSystem6 (D := D) (B0 := B0) e) =
        Design23632.canonicalBlocks) :
    Step3.tripleSystem6 (D := D) (B0 := B0) (e₁ (B0 := B0) e σ) =
      Design23632.canonicalBlocks := by
  simpa [tripleSystem6_mapDesign (D := D) (B0 := B0) (e := e) (σ := σ)] using! hσ

/-- The blocks through `x`, excluding the distinguished block `B0`. -/
public abbrev blocksThroughB0 (B0 : Biplane.Block) (x : Biplane.Point) : Finset Biplane.Block :=
  (D.blocks.erase B0).filter fun B => x ∈ B

/-- The triple in `U0` obtained from a block `B` by taking `outsideU` and transporting along `e`. -/
public abbrev tripleOfBlock (B0 : Biplane.Block)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point) (B : Biplane.Block) :
    Design23632.Block :=
  (Step3.outsideU (B0 := B0) B).map e.toEmbedding

/-- Membership in `tripleOfBlock` can be expressed using `e.symm` and `outsideU`. -/
public lemma mem_tripleOfBlock_iff
    (B0 : Biplane.Block)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (B : Biplane.Block) (p : Design23632.Point) :
    p ∈ tripleOfBlock (B0 := B0) e B ↔ e.symm p ∈ Step3.outsideU (B0 := B0) B := by
  simp [tripleOfBlock]

attribute [grind =_] mem_tripleOfBlock_iff

/-- The family of triples obtained from blocks through `x`, transported to `Design23632`. -/
public abbrev famBlocks (B0 : Biplane.Block)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point) (x : Biplane.Point) :
    Finset Design23632.Block :=
  (blocksThroughB0 (D := D) (B0 := B0) x).image (fun B => tripleOfBlock (B0 := B0) e B)

/-- The set of canonical block indices appearing in the vertex family at `x`. -/
public abbrev famIdx (B0 : Biplane.Block)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point) (x : Biplane.Point) :
    Finset Design23632.BlockIdx :=
  (Finset.univ : Finset Design23632.BlockIdx).filter fun i =>
    Design23632.blk i ∈ famBlocks (D := D) (B0 := B0) e x

/-- A rewrite of `blocksThroughB0` using `filter` on `D.blocks` and `erase B0`. -/
public lemma blocksThroughB0_eq_erase_filter (B0 : Biplane.Block) (x : Biplane.Point) :
    blocksThroughB0 (D := D) (B0 := B0) x = (D.blocks.filter fun B => x ∈ B).erase B0 := by
  ext B
  simp [blocksThroughB0, and_left_comm, and_comm]

/-- If `x ∈ B0`, then exactly `4` blocks other than `B0` pass through `x`. -/
public lemma blocksThroughB0_card
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks) {x : Biplane.Point} (hx : x ∈ B0) :
    (blocksThroughB0 (D := D) (B0 := B0) x).card = 4 := by
  have hr : D.r x = 5 := Biplane.Structure.r_eq_five (D := D) x
  have hmem : B0 ∈ D.blocks.filter (fun B => x ∈ B) := by
    simp [hB0, hx]
  have hcard_filter : (D.blocks.filter fun B => x ∈ B).card = 5 := by
    simpa [Biplane.Structure.r] using! hr
  have hcard_erase :
      ((D.blocks.filter fun B => x ∈ B).erase B0).card = 4 := by
    simp [Finset.card_erase_of_mem hmem, hcard_filter]
  simpa [blocksThroughB0_eq_erase_filter (D := D) (B0 := B0) (x := x)] using! hcard_erase

/-- The embedding `UPoint ↪ Point` given by the subtype coercion. -/
public abbrev valEmb (B0 : Biplane.Block) : Step3.UPoint (B0 := B0) ↪ Biplane.Point :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Mapping `outsideU` by `Subtype.val` recovers the finset difference `B \\ B0`. -/
public lemma outsideU_map_val (B0 : Biplane.Block) (B : Biplane.Block) :
    (Step3.outsideU (B0 := B0) B).map (valEmb (B0 := B0)) = (B \ B0) := by
  ext x
  -- expand `outsideU`; the two `Finset.map` membership characterizations reduce to `x ∈ B \\ B0`.
  simp [Step3.outsideU, valEmb, BiplaneUniqueness.Aux.outside, BiplaneUniqueness.Aux.mem_U0_iff]

/-- Membership in `outsideU` is equivalent to membership in the underlying block. -/
public lemma mem_outsideU_iff_mem_block
    (B0 : Biplane.Block) (u : Step3.UPoint (B0 := B0)) (B : Biplane.Block) :
    u ∈ Step3.outsideU (B0 := B0) B ↔ u.1 ∈ B := by
  simpa using! (Step3.Aux.mem_outsideU_iff_mem_block (B0 := B0) (u := u) (B := B))

/-- The map `outsideU` is injective on `D.blocks.erase B0`. -/
public lemma outsideU_inj
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    {B B' : Biplane.Block} (hB : B ∈ D.blocks.erase B0) (hB' : B' ∈ D.blocks.erase B0)
    (hne : B ≠ B') :
    Step3.outsideU (B0 := B0) B ≠ Step3.outsideU (B0 := B0) B' := by
  intro hEq
  have hEqPts : (B \ B0) = (B' \ B0) := by
    have := congrArg (fun t => t.map (valEmb (B0 := B0))) hEq
    simpa [outsideU_map_val (B0 := B0) (B := B), outsideU_map_val (B0 := B0) (B := B')] using! this
  have hBmem : B ∈ D.blocks := (Finset.mem_erase.1 hB).2
  have hB'mem : B' ∈ D.blocks := (Finset.mem_erase.1 hB').2
  have hinter : (B ∩ B').card = 2 := D.inter_card (B := B) (B' := B') hBmem hB'mem hne
  have houtcard : (B \ B0).card = 3 := by
    have hne0 : B ≠ B0 := (Finset.mem_erase.1 hB).1
    simpa [BiplaneUniqueness.Aux.outside] using!
      (BiplaneUniqueness.Aux.outside_card_eq_three (D := D) (B0 := B0) (B := B) hB0 hBmem hne0)
  have hsubset : (B \ B0) ⊆ (B ∩ B') := by
    intro x hx
    refine Finset.mem_inter.2 ⟨(Finset.mem_sdiff.1 hx).1, ?_⟩
    exact (Finset.mem_sdiff.1 (by simpa [hEqPts] using! hx)).1
  have hle : (3 : Nat) ≤ 2 := by
    simpa [houtcard, hinter] using! (Finset.card_le_card hsubset)
  exact Nat.not_succ_le_self 2 hle

/-- The map `tripleOfBlock` is injective on `blocksThroughB0`. -/
public lemma tripleOfBlock_injOn
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point) (x : Biplane.Point) :
    Set.InjOn (tripleOfBlock (B0 := B0) e) (blocksThroughB0 (D := D) (B0 := B0) x) := by
  intro B hB B' hB' hEq
  -- reduce to equality of `outsideU`
  have hEqU : Step3.outsideU (B0 := B0) B = Step3.outsideU (B0 := B0) B' := by
    have := congrArg (fun t => t.map e.symm.toEmbedding) hEq
    simpa [tripleOfBlock, Finset.map_map] using! this
  by_contra hne
  have hBerase : B ∈ D.blocks.erase B0 := (Finset.mem_filter.1 hB).1
  have hB'erase : B' ∈ D.blocks.erase B0 := (Finset.mem_filter.1 hB').1
  exact (outsideU_inj (D := D) (B0 := B0) hB0 (B := B) (B' := B') hBerase hB'erase hne) hEqU

/-- The family `famBlocks` has cardinality `4` for `x ∈ B0`. -/
public lemma famBlocks_card
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    {x : Biplane.Point} (hx : x ∈ B0) :
    (famBlocks (D := D) (B0 := B0) e x).card = 4 := by
  have hBlocks : (blocksThroughB0 (D := D) (B0 := B0) x).card = 4 :=
    blocksThroughB0_card (D := D) (B0 := B0) hB0 hx
  have hinj :
      Set.InjOn (tripleOfBlock (B0 := B0) e) (blocksThroughB0 (D := D) (B0 := B0) x) :=
    tripleOfBlock_injOn (D := D) (B0 := B0) hB0 e x
  have hImg :
      (famBlocks (D := D) (B0 := B0) e x).card = (blocksThroughB0 (D := D) (B0 := B0) x).card := by
    simpa [famBlocks] using! (Finset.card_image_of_injOn hinj)
  simpa [hBlocks] using! hImg

/-- Each `tripleOfBlock` lies in the global triple system `tripleSystem6`. -/
public lemma tripleOfBlock_mem_tripleSystem6
    {B0 : Biplane.Block} {B : Biplane.Block} (hB : B ∈ D.blocks.erase B0)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point) :
    tripleOfBlock (B0 := B0) e B ∈ Step3.tripleSystem6 (D := D) (B0 := B0) e := by
  unfold Step3.tripleSystem6
  refine Finset.mem_image.2 ?_
  refine ⟨Step3.outsideU (B0 := B0) B, ?_, rfl⟩
  unfold Step3.tripleSystemU
  refine Finset.mem_image.2 ?_
  exact ⟨B, hB, rfl⟩

/-- The family `famBlocks` is contained in `tripleSystem6`. -/
public lemma famBlocks_subset_tripleSystem6
    (B0 : Biplane.Block)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point) (x : Biplane.Point) :
    famBlocks (D := D) (B0 := B0) e x ⊆ Step3.tripleSystem6 (D := D) (B0 := B0) e := by
  intro t ht
  rcases Finset.mem_image.1 ht with ⟨B, hB, rfl⟩
  have hBerase : B ∈ D.blocks.erase B0 := (Finset.mem_filter.1 hB).1
  exact tripleOfBlock_mem_tripleSystem6 (D := D) (B0 := B0) (B := B) hBerase e

/-- The map `Design23632.blk : BlockIdx → Block` is injective. -/
public lemma blk_injective : Function.Injective (Design23632.blk) := by
  decide

/-- The canonical blocks are the image of `blk` over all block indices. -/
public lemma canonicalBlocks_eq_image_blk :
    Design23632.canonicalBlocks =
      (Finset.univ : Finset Design23632.BlockIdx).image Design23632.blk := by
  decide

/-- The image of `famIdx` under `blk` is exactly the corresponding `famBlocks`. -/
public lemma famIdx_image_blk
    {B0 : Biplane.Block}
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (x : Biplane.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    (famIdx (D := D) (B0 := B0) e x).image Design23632.blk =
      famBlocks (D := D) (B0 := B0) e x := by
  ext t
  constructor
  · intro ht
    rcases Finset.mem_image.1 ht with ⟨i, hi, rfl⟩
    exact (Finset.mem_filter.1 hi).2
  · intro ht
    -- `t` lies in the canonical blocks, hence equals `blk i` for some index.
    have htcanon : t ∈ Design23632.canonicalBlocks := by
      have ht' : t ∈ Step3.tripleSystem6 (D := D) (B0 := B0) e :=
        famBlocks_subset_tripleSystem6 (D := D) (B0 := B0) (e := e) x ht
      simpa [hT] using! ht'
    have htimg : t ∈ (Finset.univ : Finset Design23632.BlockIdx).image Design23632.blk := by
      simpa [canonicalBlocks_eq_image_blk] using! htcanon
    rcases Finset.mem_image.1 htimg with ⟨i, hi, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨i, ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨by simp, by grind only⟩

/-- The vertex-family finset `famIdx` has cardinality `4` for `x ∈ B0`. -/
public lemma famIdx_card
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    {x : Biplane.Point} (hx : x ∈ B0)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    (famIdx (D := D) (B0 := B0) e x).card = 4 := by
  have hImg :
      (famIdx (D := D) (B0 := B0) e x).image Design23632.blk =
        famBlocks (D := D) (B0 := B0) e x :=
    famIdx_image_blk (D := D) (B0 := B0) (e := e) x hT
  have hcardFam : (famBlocks (D := D) (B0 := B0) e x).card = 4 :=
    famBlocks_card (D := D) (B0 := B0) hB0 (e := e) (x := x) hx
  have hcardImg :
      ((famIdx (D := D) (B0 := B0) e x).image Design23632.blk).card =
        (famIdx (D := D) (B0 := B0) e x).card := by
    simpa using! (Finset.card_image_of_injective (s := famIdx (D := D) (B0 := B0) e x)
      (f := Design23632.blk) blk_injective)
  simp_all

end

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Step4.Aux4

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
