-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.Step4.VFsClassify
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.Step4.Auxiliary
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneIso
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.ReconstructedCanonBiplane
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases

/-!
# Step 4: reconstructing an isomorphism to the canonical biplane

Assume the Step 3 relabeling identifies the extracted `2-(6,3,2)` triple system with
`Design23632.canonicalBlocks`. This file reconstructs an explicit point permutation
`τ : Biplane.Point ≃ Biplane.Point` sending a biplane structure `D` to the fixed canonical biplane
`ReconstructedCanonicalBiplane.canonicalStructure`. The construction uses the classification of
the five vertex families coming from points of the distinguished block `B0`.

The main result is
`reconstruct_iso_to_canonical_of_tripleSystem6_eq_canonicalBlocks`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Step4

noncomputable section

open Biplane
open Step3
open scoped BigOperators
open Finset

namespace Aux4Iso
variable (D : Biplane.Structure) {B0 : Biplane.Block}

def complEquivUPoint (B0 : Biplane.Block) :
    {x : Biplane.Point // x ∉ B0} ≃ Step3.UPoint (B0 := B0) where
  toFun := fun x =>
    ⟨x.1, (BiplaneUniqueness.Aux.mem_U0_iff (B0 := B0) (x := x.1)).2 x.2⟩
  invFun := fun u =>
    ⟨u.1, (BiplaneUniqueness.Aux.mem_U0_iff (B0 := B0) (x := u.1)).1 u.2⟩
  left_inv := by intro x; ext; rfl
  right_inv := by intro u; ext; rfl

def famByLabel : Fin 5 → Finset Design23632.BlockIdx
  | ⟨0, _⟩ => Design23632.famA'
  | ⟨1, _⟩ => Design23632.famB'
  | ⟨2, _⟩ => Design23632.famC'
  | ⟨3, _⟩ => Design23632.famD'
  | ⟨4, _⟩ => Design23632.famE'

lemma famByLabel_injective : Function.Injective famByLabel := by
  decide

/-- If Step 3 identifies `tripleSystem6` with the canonical blocks, then this also holds for
`e₁`. -/
public lemma tripleSystem6_e1_eq_canonical
    {e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point}
    {σ : Equiv Design23632.Point Design23632.Point}
    (hσ :
      Design23632.mapDesign σ (Step3.tripleSystem6 (D := D) (B0 := B0) e) =
        Design23632.canonicalBlocks) :
    Step3.tripleSystem6 (D := D) (B0 := B0) (Step4.Aux4.e₁ (B0 := B0) e σ) =
      Design23632.canonicalBlocks :=
  Step4.Aux4.tripleSystem6_eq_canonical (D := D) (B0 := B0) (e := e) (σ := σ) hσ

abbrev famOfPoint
    {e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point}
    (x : {x : Biplane.Point // x ∈ B0}) :
    Finset Design23632.BlockIdx :=
  Step4.Aux4.famIdx (D := D) (B0 := B0) e x.1

noncomputable def labelOfPoint (F : Finset Design23632.BlockIdx) : Fin 5 :=
  if _ : F = Design23632.famA' then 0
  else if _ : F = Design23632.famB' then 1
  else if _ : F = Design23632.famC' then 2
  else if _ : F = Design23632.famD' then 3
  else 4

lemma labelOfPoint_spec
    {F : Finset Design23632.BlockIdx}
    (hF :
      F = Design23632.famA' ∨ F = Design23632.famB' ∨ F = Design23632.famC' ∨
        F = Design23632.famD' ∨ F = Design23632.famE') :
    Aux4Iso.famByLabel (labelOfPoint F) = F := by
  rcases hF with rfl | rfl | rfl | rfl | rfl <;> decide

lemma famOfPoint_eq_famByLabel_labelOfPoint
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    {e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point}
    {x : Biplane.Point} (hx : x ∈ B0)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    Aux4Iso.famByLabel
        (labelOfPoint (Step4.Aux4.famIdx (D := D) (B0 := B0) e x)) =
      Step4.Aux4.famIdx (D := D) (B0 := B0) e x := by
  -- use the classification lemma for `famIdx`, then apply `labelOfPoint_spec`
  have hF :=
    Step4.Aux4.classify_famIdx (D := D) (B0 := B0) hB0 (e := e) (x := x) hx hT
  simpa using! (labelOfPoint_spec (F := Step4.Aux4.famIdx (D := D) (B0 := B0) e x) hF)

end Aux4Iso

namespace Aux4IsoProof

open Aux4

variable (D : Biplane.Structure) {B0 : Biplane.Block}

abbrev label (F : Finset Design23632.BlockIdx) : Fin 5 :=
  Aux4Iso.labelOfPoint F

abbrev labelPt
    {B0 : Biplane.Block} {e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point}
    (x : {x : Biplane.Point // x ∈ B0}) : Fin 5 :=
  label (Step4.Aux4.famIdx (D := D) (B0 := B0) e x.1)

lemma labelPt_spec
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    {e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point}
    {x : {x : Biplane.Point // x ∈ B0}}
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    Aux4Iso.famByLabel (labelPt (D := D) (B0 := B0) (e := e) x) =
      Step4.Aux4.famIdx (D := D) (B0 := B0) e x.1 :=
  Aux4Iso.famOfPoint_eq_famByLabel_labelOfPoint (D := D) (B0 := B0) hB0 (x := x.1) x.2 hT

attribute [grind inj] blk_injective

lemma tripleOfBlock_injOn_erase
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point) :
    Set.InjOn (Step4.Aux4.tripleOfBlock (B0 := B0) e) (D.blocks.erase B0) := by
  intro B hB B' hB' hEq
  have hEqU : Step3.outsideU (B0 := B0) B = Step3.outsideU (B0 := B0) B' := by
    have := congrArg (fun t => t.map e.symm.toEmbedding) hEq
    simpa [Step4.Aux4.tripleOfBlock, Finset.map_map] using! this
  by_contra hne
  exact (Step4.Aux4.outsideU_inj (D := D) (B0 := B0) hB0 (B := B) (B' := B') hB hB' hne) hEqU

/-!
## Step 4A: vertex-family intersections recover the triple index for a pair in `B0`
-/

open BiplaneUniqueness.Aux

lemma tripleOfBlock_mem_tripleSystem6
    {B0 : Biplane.Block} {e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point}
    {B : Biplane.Block} (hB : B ∈ D.blocks.erase B0) :
    Step4.Aux4.tripleOfBlock (B0 := B0) e B ∈ Step3.tripleSystem6 (D := D) (B0 := B0) e :=
  Aux4.tripleOfBlock_mem_tripleSystem6 D hB e

lemma exists_idx_of_mem_canonicalBlocks
    {t : Design23632.Block} (ht : t ∈ Design23632.canonicalBlocks) :
    ∃ i : Design23632.BlockIdx, Design23632.blk i = t := by
  have ht' : t ∈ (Finset.univ : Finset Design23632.BlockIdx).image Design23632.blk := by
    simpa [canonicalBlocks_eq_image_blk] using! ht
  rcases Finset.mem_image.1 ht' with ⟨i, _hi, rfl⟩
  exact ⟨i, rfl⟩

lemma mem_famIdx_iff
    {B0 : Biplane.Block} (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (x : Biplane.Point) (i : Design23632.BlockIdx) :
    i ∈ famIdx (D := D) (B0 := B0) e x ↔ Design23632.blk i ∈ famBlocks (D := D) (B0 := B0) e x := by
  simp [famIdx]

lemma exists_block_of_mem_famIdx
    {B0 : Biplane.Block} (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    {x : Biplane.Point} {i : Design23632.BlockIdx}
    (hi : i ∈ famIdx (D := D) (B0 := B0) e x) :
    ∃ B : Biplane.Block, B ∈ D.blocks.erase B0 ∧ x ∈ B ∧
      tripleOfBlock (B0 := B0) e B = Design23632.blk i := by
  have hi' : Design23632.blk i ∈ famBlocks (D := D) (B0 := B0) e x :=
    (mem_famIdx_iff (D := D) (B0 := B0) (e := e) (x := x) (i := i)).1 hi
  rcases Finset.mem_image.1 hi' with ⟨B, hB, hEq⟩
  have hBerase : B ∈ D.blocks.erase B0 := (Finset.mem_filter.1 hB).1
  have hxB : x ∈ B := (Finset.mem_filter.1 hB).2
  exact ⟨B, hBerase, hxB, hEq⟩

lemma famIdx_inter_card_one
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    {x y : Biplane.Point} (hx : x ∈ B0) (hy : y ∈ B0) (hxy : x ≠ y)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    ((famIdx (D := D) (B0 := B0) e x) ∩ (famIdx (D := D) (B0 := B0) e y)).card = 1 := by
  let Bxy : Biplane.Block :=
    otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy
  have hBxy :=
    otherBlockThroughPair_spec (D := D) (B0 := B0) hB0 hx hy hxy
  have hBxy_mem : Bxy ∈ D.blocks := hBxy.1
  have hxBxy : x ∈ Bxy := hBxy.2.1
  have hyBxy : y ∈ Bxy := hBxy.2.2.1
  have hBxy_ne0 : Bxy ≠ B0 := hBxy.2.2.2
  have hBxy_erase : Bxy ∈ D.blocks.erase B0 := by
    simp [Bxy, hBxy_mem, hBxy_ne0]
  have ht_triple : tripleOfBlock (B0 := B0) e Bxy ∈ Design23632.canonicalBlocks := by
    have ht' :
        tripleOfBlock (B0 := B0) e Bxy ∈ Step3.tripleSystem6 (D := D) (B0 := B0) e := by
      exact tripleOfBlock_mem_tripleSystem6 (D := D) (B0 := B0) (e := e) hBxy_erase
    simpa [hT] using! ht'
  rcases exists_idx_of_mem_canonicalBlocks (t := tripleOfBlock (B0 := B0) e Bxy) ht_triple with
    ⟨i0, hi0⟩
  have hi0_memX : i0 ∈ famIdx (D := D) (B0 := B0) e x := by
    refine (mem_famIdx_iff (D := D) (B0 := B0) (e := e) (x := x) (i := i0)).2 ?_
    refine Finset.mem_image.2 ⟨Bxy, ?_, by simpa [Bxy] using! hi0.symm⟩
    simp [blocksThroughB0, hBxy_erase, hxBxy]
  have hi0_memY : i0 ∈ famIdx (D := D) (B0 := B0) e y := by
    refine (mem_famIdx_iff (D := D) (B0 := B0) (e := e) (x := y) (i := i0)).2 ?_
    refine Finset.mem_image.2 ⟨Bxy, ?_, by simpa [Bxy] using! hi0.symm⟩
    simp [blocksThroughB0, hBxy_erase, hyBxy]
  have hi0_mem :
      i0 ∈ (famIdx (D := D) (B0 := B0) e x) ∩ (famIdx (D := D) (B0 := B0) e y) :=
    Finset.mem_inter.2 ⟨hi0_memX, hi0_memY⟩
  refine (Finset.card_eq_one).2 ⟨i0, ?_⟩
  ext j
  constructor
  · intro hj
    have hjX : j ∈ famIdx (D := D) (B0 := B0) e x := (Finset.mem_inter.1 hj).1
    have hjY : j ∈ famIdx (D := D) (B0 := B0) e y := (Finset.mem_inter.1 hj).2
    rcases exists_block_of_mem_famIdx (D := D) (B0 := B0) e hjX with ⟨Bx, hBx_erase, hxBx, hBxEq⟩
    rcases exists_block_of_mem_famIdx (D := D) (B0 := B0) e hjY with ⟨By, hBy_erase, hyBy, hByEq⟩
    have hEqTrip :
        tripleOfBlock (B0 := B0) e Bx = tripleOfBlock (B0 := B0) e By := by
      simp [hBxEq, hByEq]
    have hBxBy : Bx = By :=
      tripleOfBlock_injOn_erase (D := D) (B0 := B0) hB0 e hBx_erase hBy_erase hEqTrip
    have hyBx : y ∈ Bx := by simpa [hBxBy] using! hyBy
    have hBx_ne0 : Bx ≠ B0 := (Finset.mem_erase.1 hBx_erase).1
    have hBx_prop : Bx ∈ D.blocks ∧ x ∈ Bx ∧ y ∈ Bx ∧ Bx ≠ B0 := by
      refine ⟨(Finset.mem_erase.1 hBx_erase).2, hxBx, hyBx, hBx_ne0⟩
    have hBxy_prop : Bxy ∈ D.blocks ∧ x ∈ Bxy ∧ y ∈ Bxy ∧ Bxy ≠ B0 := by
      refine ⟨hBxy_mem, hxBxy, hyBxy, hBxy_ne0⟩
    have huniq := exists_unique_other_block_through_pair (D := D) (B0 := B0) hB0 hx hy hxy
    have hBx_eq : Bx = Bxy := huniq.unique hBx_prop hBxy_prop
    have hblkEq : Design23632.blk j = Design23632.blk i0 := by
      calc
        Design23632.blk j = Step4.Aux4.tripleOfBlock (B0 := B0) e Bx := by simpa using! hBxEq.symm
        _ = Step4.Aux4.tripleOfBlock (B0 := B0) e Bxy := by simp [hBx_eq]
        _ = Design23632.blk i0 := by simp [Bxy, hi0]
    have hji0 : j = i0 := blk_injective hblkEq
    simp [hji0]
  · intro hj
    have : j = i0 := by simpa using! (Finset.mem_singleton.1 hj)
    subst this
    exact hi0_mem

/-!
## Step 4B: label the five points of `B0` by canonical vertex families
-/

lemma labelPt_injective
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    Function.Injective (labelPt (D := D) (B0 := B0) (e := e)) := by
  intro x y hxy
  by_contra hne
  have hxy' : x.1 ≠ y.1 := fun hEq => hne (Subtype.ext hEq)
  have hEqFam :
      Step4.Aux4.famIdx (D := D) (B0 := B0) e x.1 =
        Step4.Aux4.famIdx (D := D) (B0 := B0) e y.1 := by
    simpa [labelPt_spec (D := D) (B0 := B0) hB0 (e := e) (x := x) hT,
      labelPt_spec (D := D) (B0 := B0) hB0 (e := e) (x := y) hT] using!
      congrArg Aux4Iso.famByLabel hxy
  have hcard_inter :
      ((Step4.Aux4.famIdx (D := D) (B0 := B0) e x.1) ∩
          (Step4.Aux4.famIdx (D := D) (B0 := B0) e y.1)).card = 1 := by
    simpa using!
      famIdx_inter_card_one (D := D) (B0 := B0) hB0 (e := e)
        (x := x.1) (y := y.1) x.2 y.2 hxy' hT
  have hcard_eq4 :
      ((Step4.Aux4.famIdx (D := D) (B0 := B0) e x.1) ∩
          (Step4.Aux4.famIdx (D := D) (B0 := B0) e y.1)).card = 4 := by
    simpa [hEqFam] using!
      Step4.Aux4.famIdx_card (D := D) (B0 := B0) hB0 (e := e) (x := x.1) x.2 hT
  grind only

lemma labelPt_ne
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks)
    {x y : Biplane.Point} (hx : x ∈ B0) (hy : y ∈ B0) (hxy : x ≠ y) :
    labelPt (D := D) (e := e) ⟨x, hx⟩ ≠ labelPt (D := D) (e := e) ⟨y, hy⟩ := by
  intro hEq
  apply hxy
  simpa using! congrArg Subtype.val ((labelPt_injective (D := D) (B0 := B0) hB0 e hT) hEq)

lemma card_B0Point
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks) :
    Fintype.card {x : Biplane.Point // x ∈ B0} = 5 := by
  have hcard : Fintype.card {x : Biplane.Point // x ∈ B0} = B0.card := by
    simp
  simp [hcard, D.block_card B0 hB0]

lemma labelPt_bijective
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    Function.Bijective (labelPt (D := D) (B0 := B0) (e := e)) := by
  have hinj : Function.Injective (labelPt (D := D) (B0 := B0) (e := e)) :=
    labelPt_injective (D := D) (B0 := B0) hB0 e hT
  refine ⟨hinj, ?_⟩
  -- surjectivity from injectivity + cardinality
  by_contra hnsurj
  have hlt := Fintype.card_lt_of_injective_not_surjective
    (f := labelPt (D := D) (B0 := B0) (e := e)) hinj hnsurj
  have hcardDom :
      Fintype.card {x : Biplane.Point // x ∈ B0} = 5 :=
    card_B0Point (D := D) (B0 := B0) hB0
  have hcardCod : Fintype.card (Fin 5) = 5 := by simp
  grind only

noncomputable def eB0
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    {x : Biplane.Point // x ∈ B0} ≃ Fin 5 :=
  Equiv.ofBijective (labelPt (D := D) (B0 := B0) (e := e))
    (labelPt_bijective (D := D) (B0 := B0) hB0 e hT)

noncomputable def eU0
    (B0 : Biplane.Block)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point) :
    {x : Biplane.Point // x ∉ B0} ≃ Fin 6 :=
  (Aux4Iso.complEquivUPoint B0).trans e

noncomputable def pointPerm
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    Biplane.Point ≃ Biplane.Point :=
  ((Equiv.sumCompl (fun p : Biplane.Point => p ∈ B0)).symm.trans
      (Equiv.sumCongr (eB0 (D := D) (B0 := B0) hB0 e hT) (eU0 B0 e))).trans
    (finSumFinEquiv : Fin 5 ⊕ Fin 6 ≃ Fin 11)

@[simp] lemma pointPerm_apply_of_mem
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks)
    {x : Biplane.Point} (hx : x ∈ B0) :
    pointPerm (D := D) (B0 := B0) hB0 e hT x =
      Fin.castAdd 6 (eB0 (D := D) (B0 := B0) hB0 e hT ⟨x, hx⟩) := by
  unfold pointPerm
  simp [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos, hx]
  rfl

@[simp] lemma pointPerm_apply_of_not_mem
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks)
    {x : Biplane.Point} (hx : x ∉ B0) :
    pointPerm (D := D) (B0 := B0) hB0 e hT x =
      Fin.natAdd 5 (eU0 B0 e ⟨x, hx⟩) := by
  unfold pointPerm
  simp [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg, hx]
  rfl

@[simp] lemma eB0_apply
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks)
    (x : {x : Biplane.Point // x ∈ B0}) :
    eB0 (D := D) (B0 := B0) hB0 e hT x = labelPt (D := D) (B0 := B0) (e := e) x := by
  rfl

/-!
## Step 4C: a concrete dictionary from pairs of labels to canonical blocks
-/

def idxFromLabels (i j : Fin 5) : Design23632.BlockIdx :=
  match i.1, j.1 with
  | 0, 1 => ⟨0, by decide⟩
  | 1, 0 => ⟨0, by decide⟩
  | 0, 2 => ⟨9, by decide⟩
  | 2, 0 => ⟨9, by decide⟩
  | 0, 3 => ⟨3, by decide⟩
  | 3, 0 => ⟨3, by decide⟩
  | 0, 4 => ⟨6, by decide⟩
  | 4, 0 => ⟨6, by decide⟩
  | 1, 2 => ⟨7, by decide⟩
  | 2, 1 => ⟨7, by decide⟩
  | 1, 3 => ⟨8, by decide⟩
  | 3, 1 => ⟨8, by decide⟩
  | 1, 4 => ⟨4, by decide⟩
  | 4, 1 => ⟨4, by decide⟩
  | 2, 3 => ⟨1, by decide⟩
  | 3, 2 => ⟨1, by decide⟩
  | 2, 4 => ⟨2, by decide⟩
  | 4, 2 => ⟨2, by decide⟩
  | 3, 4 => ⟨5, by decide⟩
  | 4, 3 => ⟨5, by decide⟩
  | _, _ => ⟨0, by decide⟩

lemma famByLabel_inter_eq_singleton (i j : Fin 5) (hij : i ≠ j) :
    Aux4Iso.famByLabel i ∩ Aux4Iso.famByLabel j = {idxFromLabels i j} := by
  fin_cases i <;> fin_cases j <;> try cases hij rfl
  all_goals
    simp [Aux4Iso.famByLabel, idxFromLabels, Finset.inter_comm,
      Design23632.famA'_inter_famB', Design23632.famA'_inter_famC', Design23632.famA'_inter_famD',
      Design23632.famA'_inter_famE', Design23632.famB'_inter_famC', Design23632.famB'_inter_famD',
      Design23632.famB'_inter_famE', Design23632.famC'_inter_famD', Design23632.famC'_inter_famE',
      Design23632.famD'_inter_famE']

def canonBlockOfLabels (i j : Fin 5) : Biplane.Block :=
  match i.1, j.1 with
  | 0, 1 => ({(0 : Biplane.Point), 1, 5, 6, 7} : Biplane.Block)
  | 1, 0 => ({(0 : Biplane.Point), 1, 5, 6, 7} : Biplane.Block)
  | 0, 2 => ({(0 : Biplane.Point), 2, 7, 9, 10} : Biplane.Block)
  | 2, 0 => ({(0 : Biplane.Point), 2, 7, 9, 10} : Biplane.Block)
  | 0, 3 => ({(0 : Biplane.Point), 3, 5, 8, 10} : Biplane.Block)
  | 3, 0 => ({(0 : Biplane.Point), 3, 5, 8, 10} : Biplane.Block)
  | 0, 4 => ({(0 : Biplane.Point), 4, 6, 8, 9} : Biplane.Block)
  | 4, 0 => ({(0 : Biplane.Point), 4, 6, 8, 9} : Biplane.Block)
  | 1, 2 => ({(1 : Biplane.Point), 2, 6, 8, 10} : Biplane.Block)
  | 2, 1 => ({(1 : Biplane.Point), 2, 6, 8, 10} : Biplane.Block)
  | 1, 3 => ({(1 : Biplane.Point), 3, 7, 8, 9} : Biplane.Block)
  | 3, 1 => ({(1 : Biplane.Point), 3, 7, 8, 9} : Biplane.Block)
  | 1, 4 => ({(1 : Biplane.Point), 4, 5, 9, 10} : Biplane.Block)
  | 4, 1 => ({(1 : Biplane.Point), 4, 5, 9, 10} : Biplane.Block)
  | 2, 3 => ({(2 : Biplane.Point), 3, 5, 6, 9} : Biplane.Block)
  | 3, 2 => ({(2 : Biplane.Point), 3, 5, 6, 9} : Biplane.Block)
  | 2, 4 => ({(2 : Biplane.Point), 4, 5, 7, 8} : Biplane.Block)
  | 4, 2 => ({(2 : Biplane.Point), 4, 5, 7, 8} : Biplane.Block)
  | 3, 4 => ({(3 : Biplane.Point), 4, 6, 7, 10} : Biplane.Block)
  | 4, 3 => ({(3 : Biplane.Point), 4, 6, 7, 10} : Biplane.Block)
  | _, _ => ({(0 : Biplane.Point), 1, 2, 3, 4} : Biplane.Block)

open ReconstructedCanonicalBiplane

lemma canonBlockOfLabels_mem (i j : Fin 5) (hij : i ≠ j) :
    canonBlockOfLabels i j ∈ ReconstructedCanonicalBiplane.canonBlocks := by
  fin_cases i <;> fin_cases j <;> try cases hij rfl
  all_goals
    simp [canonBlockOfLabels, canonBlocks, B0, B01, B02, B03, B04, B12, B13, B14, B23, B24, B34]

def canonBlockUnion (i j : Fin 5) : Biplane.Block :=
  ({(Fin.castAdd 6 i : Biplane.Point), Fin.castAdd 6 j} : Biplane.Block) ∪
    (Design23632.blk (idxFromLabels i j)).image (Fin.natAdd 5)

lemma canonBlockOfLabels_eq_union (i j : Fin 5) (hij : i ≠ j) :
    canonBlockOfLabels i j = canonBlockUnion i j := by
  fin_cases i <;> fin_cases j <;> try cases hij rfl
  all_goals
    simp only [canonBlockOfLabels, canonBlockUnion, idxFromLabels, Design23632.blk]
    decide

/-!
## Step 4D: triple index for a pair in `B0`, and images of blocks under `pointPerm`
-/

lemma tripleOf_otherBlock_eq_blk_idxFromLabels
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    {x y : Biplane.Point} (hx : x ∈ B0) (hy : y ∈ B0) (hxy : x ≠ y)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    tripleOfBlock (B0 := B0) e
        (otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy) =
      Design23632.blk
        (idxFromLabels
          (labelPt (D := D) (e := e) ⟨x, hx⟩)
          (labelPt (D := D) (e := e) ⟨y, hy⟩)) := by
  let Bxy : Biplane.Block :=
    otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy
  have hBxy :=
    otherBlockThroughPair_spec (D := D) (B0 := B0) hB0 hx hy hxy
  have hBxy_mem : Bxy ∈ D.blocks := hBxy.1
  have hxBxy : x ∈ Bxy := hBxy.2.1
  have hyBxy : y ∈ Bxy := hBxy.2.2.1
  have hBxy_ne0 : Bxy ≠ B0 := hBxy.2.2.2
  have hBxy_erase : Bxy ∈ D.blocks.erase B0 := by
    simp [Bxy, hBxy_mem, hBxy_ne0]
  have ht_triple : tripleOfBlock (B0 := B0) e Bxy ∈ Design23632.canonicalBlocks := by
    have ht' :
        tripleOfBlock (B0 := B0) e Bxy ∈ Step3.tripleSystem6 (D := D) (B0 := B0) e := by
      exact tripleOfBlock_mem_tripleSystem6 (D := D) (B0 := B0) (e := e) hBxy_erase
    simpa [hT] using! ht'
  rcases exists_idx_of_mem_canonicalBlocks (t := tripleOfBlock (B0 := B0) e Bxy) ht_triple with
    ⟨i0, hi0⟩
  have hi0_memX : i0 ∈ famIdx (D := D) (B0 := B0) e x := by
    refine (mem_famIdx_iff (D := D) (B0 := B0) (e := e) (x := x) (i := i0)).2 ?_
    refine Finset.mem_image.2 ⟨Bxy, ?_, by simpa [Bxy] using! hi0.symm⟩
    simp [blocksThroughB0, hBxy_erase, hxBxy]
  have hi0_memY : i0 ∈ famIdx (D := D) (B0 := B0) e y := by
    refine (mem_famIdx_iff (D := D) (B0 := B0) (e := e) (x := y) (i := i0)).2 ?_
    refine Finset.mem_image.2 ⟨Bxy, ?_, by simpa [Bxy] using! hi0.symm⟩
    simp [blocksThroughB0, hBxy_erase, hyBxy]
  have hi0_mem :
      i0 ∈ (famIdx (D := D) (B0 := B0) e x) ∩ (famIdx (D := D) (B0 := B0) e y) :=
    Finset.mem_inter.2 ⟨hi0_memX, hi0_memY⟩
  let lx : Fin 5 := labelPt (D := D) (B0 := B0) (e := e) ⟨x, hx⟩
  let ly : Fin 5 := labelPt (D := D) (B0 := B0) (e := e) ⟨y, hy⟩
  have hlxy : lx ≠ ly := by
    simpa [lx, ly] using! labelPt_ne (D := D) hB0 (e := e) hT hx hy hxy
  have hxSpec :
      Aux4Iso.famByLabel lx = famIdx (D := D) (B0 := B0) e x :=
    (labelPt_spec (D := D) (B0 := B0) hB0 (e := e) (x := ⟨x, hx⟩) hT)
  have hySpec :
      Aux4Iso.famByLabel ly = famIdx (D := D) (B0 := B0) e y :=
    (labelPt_spec (D := D) (B0 := B0) hB0 (e := e) (x := ⟨y, hy⟩) hT)
  have hinter :
      famIdx (D := D) (B0 := B0) e x ∩ famIdx (D := D) (B0 := B0) e y = {idxFromLabels lx ly} := by
    -- rewrite to canonical families and use the precomputed intersections
    simpa [hxSpec, hySpec] using! (famByLabel_inter_eq_singleton (i := lx) (j := ly) hlxy)
  have : i0 = idxFromLabels lx ly := by
    have : i0 ∈ ({idxFromLabels lx ly} : Finset _) := by simpa [hinter] using! hi0_mem
    simpa using! (Finset.mem_singleton.1 this)
  -- finish
  subst this
  simpa [Bxy] using! hi0.symm

lemma otherBlock_inter_eq_pair
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    {x y : Biplane.Point} (hx : x ∈ B0) (hy : y ∈ B0) (hxy : x ≠ y) :
    otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy ∩ B0 = {x, y} := by
  let Bxy : Biplane.Block :=
    otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy
  have hBxy :=
    otherBlockThroughPair_spec (D := D) (B0 := B0) hB0 hx hy hxy
  have hBxy_mem : Bxy ∈ D.blocks := hBxy.1
  have hBxy_ne0 : Bxy ≠ B0 := hBxy.2.2.2
  have hxBxy : x ∈ Bxy := hBxy.2.1
  have hyBxy : y ∈ Bxy := hBxy.2.2.1
  have hsubset : ({x, y} : Finset Biplane.Point) ⊆ (Bxy ∩ B0) := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact Finset.mem_inter.2 ⟨hxBxy, hx⟩
    · rcases Finset.mem_singleton.1 hz with rfl
      exact Finset.mem_inter.2 ⟨hyBxy, hy⟩
  have hcard : (Bxy ∩ B0).card = 2 := by
    -- intersection size in a biplane
    exact D.inter_card (B := Bxy) (B' := B0) hBxy_mem hB0 (by simpa [Bxy] using! hBxy_ne0)
  have hcard' : ({x, y} : Finset Biplane.Point).card = 2 := by
    simpa using! (Finset.card_pair hxy)
  have hle : (Bxy ∩ B0).card ≤ ({x, y} : Finset Biplane.Point).card := by
    simp [hcard, hcard']
  -- subset + card equality
  have hEq : ({x, y} : Finset Biplane.Point) = (Bxy ∩ B0) :=
    Finset.eq_of_subset_of_card_le hsubset hle
  simpa [Bxy] using! hEq.symm

lemma otherBlock_map_pointPerm_eq_union
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks)
    {x y : Biplane.Point} (hx : x ∈ B0) (hy : y ∈ B0) (hxy : x ≠ y) :
    let τ := pointPerm (D := D) (B0 := B0) hB0 e hT
    let lx := labelPt (D := D) (B0 := B0) (e := e) ⟨x, hx⟩
    let ly := labelPt (D := D) (B0 := B0) (e := e) ⟨y, hy⟩
    (otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy).map τ.toEmbedding =
      ({(Fin.castAdd 6 lx : Biplane.Point), Fin.castAdd 6 ly} : Biplane.Block) ∪
        (Design23632.blk (idxFromLabels lx ly)).image (Fin.natAdd 5) := by
  intro τ lx ly
  let Bxy : Biplane.Block :=
    otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy
  have hBxy :=
    otherBlockThroughPair_spec (D := D) (B0 := B0) hB0 hx hy hxy
  have hBxy_mem : Bxy ∈ D.blocks := hBxy.1
  have hBxy_ne0 : Bxy ≠ B0 := hBxy.2.2.2
  have hBxy_erase : Bxy ∈ D.blocks.erase B0 := by
    simp [Bxy, hBxy_mem, hBxy_ne0]
  have hxBxy : x ∈ Bxy := hBxy.2.1
  have hyBxy : y ∈ Bxy := hBxy.2.2.1
  have hInter : Bxy ∩ B0 = {x, y} :=
    otherBlock_inter_eq_pair (D := D) (B0 := B0) hB0 hx hy hxy
  have hlx : τ x = Fin.castAdd 6 lx := by
    -- unfold `τ` and use simp
    subst τ lx ly
    simpa [Aux4IsoProof.eB0_apply] using!
      (pointPerm_apply_of_mem (D := D) (B0 := B0) hB0 e hT (x := x) hx)
  have hly : τ y = Fin.castAdd 6 ly := by
    subst τ lx ly
    simpa [Aux4IsoProof.eB0_apply] using!
      (pointPerm_apply_of_mem (D := D) (B0 := B0) hB0 e hT (x := y) hy)
  have hTriple :
      Step4.Aux4.tripleOfBlock (B0 := B0) e Bxy = Design23632.blk (idxFromLabels lx ly) := by
    exact tripleOf_otherBlock_eq_blk_idxFromLabels D hB0 e hx hy hxy hT
  -- prove equality by ext on membership and splitting whether the preimage lies in `B0`
  ext z
  constructor
  · intro hz
    rcases Finset.mem_map.1 hz with ⟨p, hp, rfl⟩
    by_cases hp0 : p ∈ B0
    · have hpPair : p = x ∨ p = y := by
        have : p ∈ ({x, y} : Finset Biplane.Point) := by
          have : p ∈ (Bxy ∩ B0) := Finset.mem_inter.2 ⟨hp, hp0⟩
          simpa [hInter] using! this
        simpa [Finset.mem_insert, Finset.mem_singleton] using! this
      rcases hpPair with rfl | rfl <;>
        exact Finset.mem_union.2 (Or.inl (by simp [hlx, hly]))
    · -- outside point: show it lands in the `natAdd` image of the triple block
      have hz' : τ p = Fin.natAdd 5 (eU0 B0 e ⟨p, hp0⟩) := by
        subst τ
        simpa using! (pointPerm_apply_of_not_mem (D := D) (B0 := B0) hB0 e hT (x := p) hp0)
      have hu0 : (Aux4Iso.complEquivUPoint B0 ⟨p, hp0⟩) ∈ Step3.outsideU (B0 := B0) Bxy :=
        (Step4.Aux4.mem_outsideU_iff_mem_block (B0 := B0)
            (u := Aux4Iso.complEquivUPoint B0 ⟨p, hp0⟩) (B := Bxy)).2
          (by simpa using! hp)
      have hmemTriple : eU0 B0 e ⟨p, hp0⟩ ∈ Step4.Aux4.tripleOfBlock (B0 := B0) e Bxy :=
        Finset.mem_map.2 ⟨Aux4Iso.complEquivUPoint B0 ⟨p, hp0⟩, hu0, rfl⟩
      refine Finset.mem_union.2 (Or.inr ?_)
      have :
          Fin.natAdd 5 (eU0 B0 e ⟨p, hp0⟩) ∈
            (Design23632.blk (idxFromLabels lx ly)).image (Fin.natAdd 5) := by
        refine Finset.mem_image.2 ⟨eU0 B0 e ⟨p, hp0⟩, ?_, rfl⟩
        grind only
      simpa [hz'] using! this
  · intro hz
    rcases Finset.mem_union.1 hz with hz | hz
    · -- in the pair part: `z` is one of the two images of `x,y`
      have hz' : z = Fin.castAdd 6 lx ∨ z = Fin.castAdd 6 ly := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using! hz
      rcases hz' with rfl | rfl
      · refine Finset.mem_map.2 ?_
        exact ⟨x, hxBxy, by simp [hlx]⟩
      · refine Finset.mem_map.2 ?_
        exact ⟨y, hyBxy, by simp [hly]⟩
    · -- in the triple part: peel off `image` and then `map` in `tripleOfBlock`
      rcases Finset.mem_image.1 hz with ⟨q, hq, rfl⟩
      have hq' : q ∈ Step4.Aux4.tripleOfBlock (B0 := B0) e Bxy := by
        grind only
      rcases Finset.mem_map.1 hq' with ⟨u, hu, rfl⟩
      have huBxy : u.1 ∈ Bxy :=
        (Step4.Aux4.mem_outsideU_iff_mem_block (B0 := B0) (u := u) (B := Bxy)).1 hu
      have huNot : u.1 ∉ B0 := Step3.Aux.not_mem_B0 (B0 := B0) u
      refine Finset.mem_map.2 ⟨u.1, huBxy, ?_⟩
      subst τ
      have hucompl : Aux4Iso.complEquivUPoint B0 ⟨u.1, huNot⟩ = u := by
        apply Subtype.ext
        rfl
      have : eU0 B0 e ⟨u.1, huNot⟩ = e u := by
        simp [eU0, hucompl]
      simpa [this] using!
        (pointPerm_apply_of_not_mem (D := D) (B0 := B0) hB0 e hT (x := u.1) huNot)

lemma otherBlock_map_pointPerm_eq_canonBlockOfLabels
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks)
    {x y : Biplane.Point} (hx : x ∈ B0) (hy : y ∈ B0) (hxy : x ≠ y) :
    let τ := pointPerm (D := D) (B0 := B0) hB0 e hT
    let lx := labelPt (D := D) (B0 := B0) (e := e) ⟨x, hx⟩
    let ly := labelPt (D := D) (B0 := B0) (e := e) ⟨y, hy⟩
    (otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy).map τ.toEmbedding =
      canonBlockOfLabels lx ly := by
  intro τ lx ly
  have hlxy : lx ≠ ly := by
    simpa [lx, ly] using! labelPt_ne (D := D) hB0 (e := e) hT hx hy hxy
  have hUnion :
      (otherBlockThroughPair (D := D) (B0 := B0) hB0 hx hy hxy).map τ.toEmbedding =
        canonBlockUnion lx ly := by
    -- use the union description, then rewrite the triple block via `idxFromLabels`
    have h := otherBlock_map_pointPerm_eq_union (D := D) (B0 := B0) hB0 e hT hx hy hxy
    simpa [canonBlockUnion, τ, lx, ly] using! h
  -- rewrite `canonBlockUnion` to the explicit canonical block
  have hEq : canonBlockUnion lx ly = canonBlockOfLabels lx ly :=
    (canonBlockOfLabels_eq_union (i := lx) (j := ly) hlxy).symm
  simpa [hEq] using! hUnion

/-- Reconstruct an isomorphism from `D` to the fixed canonical biplane from a canonical Step 3
relabeling. -/
public theorem reconstruct_iso_to_canonical_of_tripleSystem6_eq_canonicalBlocks
    {B0 : Biplane.Block} (hB0 : B0 ∈ D.blocks)
    (e : Equiv (Step3.UPoint (B0 := B0)) Design23632.Point)
    (hT : Step3.tripleSystem6 (D := D) (B0 := B0) e = Design23632.canonicalBlocks) :
    Biplane.IsIso D ReconstructedCanonicalBiplane.canonicalStructure := by
  let τ : Biplane.Point ≃ Biplane.Point := pointPerm (D := D) (B0 := B0) hB0 e hT
  refine ⟨τ, ?_⟩
  -- show `mapBlocks τ D.blocks = canonBlocks`, then rewrite to `canonicalStructure.blocks`.
  have hsubset :
      Biplane.mapBlocks τ D.blocks ⊆ ReconstructedCanonicalBiplane.canonBlocks := by
    intro B hB
    rcases (Biplane.mem_mapBlocks (σ := τ) (T := D.blocks) (B := B)).1 hB with ⟨B', hB', rfl⟩
    by_cases hEq0 : B' = B0
    · subst B'
      -- `B0` maps to `{0,1,2,3,4}`
      let base : Biplane.Block :=
        (Finset.univ : Finset (Fin 5)).image (fun i : Fin 5 => (Fin.castAdd 6 i : Biplane.Point))
      have hmap : (B0.map τ.toEmbedding) = base := by
        ext z
        constructor
        · intro hz
          rcases Finset.mem_map.1 hz with ⟨p, hp, rfl⟩
          have : τ p = Fin.castAdd 6 (eB0 (D := D) (B0 := B0) hB0 e hT ⟨p, hp⟩) := by
            subst τ
            simpa using! (pointPerm_apply_of_mem (D := D) (B0 := B0) hB0 e hT (x := p) hp)
          refine Finset.mem_image.2 ?_
          refine ⟨eB0 (D := D) (B0 := B0) hB0 e hT ⟨p, hp⟩, by simp, ?_⟩
          simp [this]
        · intro hz
          rcases Finset.mem_image.1 hz with ⟨i, _hi, rfl⟩
          -- pick a preimage point of `i` in `B0`
          rcases (eB0 (D := D) (B0 := B0) hB0 e hT).surjective i with ⟨b, hb⟩
          refine Finset.mem_map.2 ?_
          refine ⟨b.1, b.2, ?_⟩
          subst τ
          -- compute `τ` on a `B0`-point
          have : pointPerm (D := D) (B0 := B0) hB0 e hT b.1 =
              Fin.castAdd 6 (eB0 (D := D) (B0 := B0) hB0 e hT b) := by
            exact pointPerm_apply_of_mem (D := D) (B0 := B0) hB0 e hT (x := b.1) b.2
          simp [hb, this]
      have hbase : base = ({(0 : Biplane.Point), 1, 2, 3, 4} : Biplane.Block) := by decide
      -- membership in `canonBlocks`
      have : (B0.map τ.toEmbedding) ∈ ReconstructedCanonicalBiplane.canonBlocks := by
        have hmem :
            ({(0 : Biplane.Point), 1, 2, 3, 4} : Biplane.Block) ∈
              ReconstructedCanonicalBiplane.canonBlocks := by
          decide
        simpa [hmap, hbase] using! hmem
      simpa using! this
    · -- `B' ≠ B0`: pick the two points of `B' ∩ B0` and use the pair-indexed description
      have hcardInt : (B' ∩ B0).card = 2 :=
        D.inter_card (B := B') (B' := B0) hB' hB0 (by simpa [eq_comm] using! hEq0)
      rcases Finset.card_eq_two.1 hcardInt with ⟨x, y, hxy, hInt⟩
      have hx0 : x ∈ B0 := by
        have : x ∈ (B' ∩ B0) := by simp [hInt]
        exact (Finset.mem_inter.1 this).2
      have hy0 : y ∈ B0 := by
        have : y ∈ (B' ∩ B0) := by simp [hInt]
        exact (Finset.mem_inter.1 this).2
      have hxB' : x ∈ B' := by
        have : x ∈ (B' ∩ B0) := by simp [hInt]
        exact (Finset.mem_inter.1 this).1
      have hyB' : y ∈ B' := by
        have : y ∈ (B' ∩ B0) := by simp [hInt]
        exact (Finset.mem_inter.1 this).1
      -- identify `B'` with the unique non-`B0` block through `{x,y}`
      have huniq := exists_unique_other_block_through_pair (D := D) (B0 := B0) hB0 hx0 hy0 hxy
      have hB'prop : B' ∈ D.blocks ∧ x ∈ B' ∧ y ∈ B' ∧ B' ≠ B0 := ⟨hB', hxB', hyB', hEq0⟩
      have hOtherprop :=
        otherBlockThroughPair_spec (D := D) (B0 := B0) hB0 hx0 hy0 hxy
      have hB'eq :
          B' = otherBlockThroughPair (D := D) (B0 := B0) hB0 hx0 hy0 hxy :=
        huniq.unique hB'prop hOtherprop
      -- use the Step4 image computation for the other block
      let lx : Fin 5 := labelPt (D := D) (e := e) ⟨x, hx0⟩
      let ly : Fin 5 := labelPt (D := D) (e := e) ⟨y, hy0⟩
      have hlxy : lx ≠ ly := by
        simpa [lx, ly] using! labelPt_ne (D := D) hB0 (e := e) hT hx0 hy0 hxy
      have hImg :
          (B'.map τ.toEmbedding) = canonBlockOfLabels lx ly := by
        subst τ
        simpa [hB'eq, lx, ly] using!
          (otherBlock_map_pointPerm_eq_canonBlockOfLabels (D := D) (B0 := B0) hB0 (e := e) hT
            (x := x) (y := y) hx0 hy0 hxy)
      have hmem : canonBlockOfLabels lx ly ∈ ReconstructedCanonicalBiplane.canonBlocks :=
        canonBlockOfLabels_mem (i := lx) (j := ly) hlxy
      simpa [hImg] using! hmem
  -- conclude by card comparison
  have hcard :
      (ReconstructedCanonicalBiplane.canonBlocks).card ≤ (Biplane.mapBlocks τ D.blocks).card := by
    -- both cards are `11`
    have h1 : (Biplane.mapBlocks τ D.blocks).card = 11 := by
      simp [Biplane.card_mapBlocks, D.blocks_card]
    have h2 : (ReconstructedCanonicalBiplane.canonBlocks).card = 11 :=
      ReconstructedCanonicalBiplane.canonBlocks_card
    simp [h1, h2]
  have hEq : Biplane.mapBlocks τ D.blocks = ReconstructedCanonicalBiplane.canonBlocks :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  -- transport to the actual `canonicalStructure.blocks`
  simpa [ReconstructedCanonicalBiplane.canonBlocks_eq_blocks] using! hEq


end Aux4IsoProof

end

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneUniqueness.Step4

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
