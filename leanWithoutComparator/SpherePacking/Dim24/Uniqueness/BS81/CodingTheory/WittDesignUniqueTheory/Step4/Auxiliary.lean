-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Design23632VertexFamilies
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.ReconstructedCanonBiplane
import Mathlib.Data.List.Sublists

/-!
# Auxiliary decidable facts for Step 4

This file is intentionally computational:
- it records explicit singleton-intersection facts for the five canonical vertex families
  `famA'` through `famE'` of the canonical `2-(6,3,2)` design (as finsets of block indices), and
- it exposes an explicit `canonBlocks` finset equal to
  `ReconstructedCanonicalBiplane.canonicalStructure.blocks`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

namespace Design23632

/-!
### Small decidable facts about canonical vertex families

We work with the index-level representation from `Design23632VertexFamilies.lean`:
vertex families are `List BlockIdx`, where `BlockIdx := Fin 10` indexes the ten canonical blocks.
-/

/-- The canonical vertex family `famA` as a finset. The prime indicates the finset version. -/
@[expose] public def famA' : Finset BlockIdx := famA.toFinset
/-- The canonical vertex family `famB` as a finset. The prime indicates the finset version. -/
@[expose] public def famB' : Finset BlockIdx := famB.toFinset
/-- The canonical vertex family `famC` as a finset. The prime indicates the finset version. -/
@[expose] public def famC' : Finset BlockIdx := famC.toFinset
/-- The canonical vertex family `famD` as a finset. The prime indicates the finset version. -/
@[expose] public def famD' : Finset BlockIdx := famD.toFinset
/-- The canonical vertex family `famE` as a finset. The prime indicates the finset version. -/
@[expose] public def famE' : Finset BlockIdx := famE.toFinset

/-- List the elements of a finset `F` in increasing order, using `List.finRange 10`. -/
@[expose] public def listOfFam (F : Finset BlockIdx) : List BlockIdx :=
  (List.finRange 10).filter (fun i => decide (i ∈ F))

/-- Membership in `listOfFam F` is equivalent to membership in `F`. -/
public lemma mem_listOfFam_iff (F : Finset BlockIdx) (i : BlockIdx) : i ∈ listOfFam F ↔ i ∈ F := by
  simp [listOfFam, decide_eq_true_eq]

/-!
### Classifying vertex families (index level)
-/

/-!
We use the boolean predicate `Design23632.isVertexFamilyIdxB` from
`Design23632VertexFamilies.lean`, applied to `listOfFam`.

This keeps the classification computational (`decide` works) without needing global decidability
instances for nested `∀`-quantifiers.
-/

def IsVertexFamilyIdxB (F : Finset BlockIdx) : Bool :=
  Design23632.isVertexFamilyIdxB (listOfFam F)

def IsVertexFamilyIdx (F : Finset BlockIdx) : Prop :=
  IsVertexFamilyIdxB F = true

/-- `listOfFam F` is a sublist of `List.finRange 10`. -/
public lemma listOfFam_sublist (F : Finset BlockIdx) :
    List.Sublist (listOfFam F) (List.finRange 10) :=
  List.filter_sublist

/-- Converting `listOfFam F` back to a finset gives `F`. -/
public lemma listOfFam_toFinset (F : Finset BlockIdx) : (listOfFam F).toFinset = F := by
  ext i; simp [listOfFam]

attribute [grind =] listOfFam_toFinset

/-- The list `listOfFam F` has no duplicates. -/
public lemma listOfFam_nodup (F : Finset BlockIdx) : (listOfFam F).Nodup := by
  -- `finRange` has no duplicates and `filter` preserves `Nodup`.
  simpa [listOfFam] using! (List.Nodup.filter (fun i => decide (i ∈ F)) (List.nodup_finRange 10))

/-- The length of `listOfFam F` equals `F.card`. -/
public lemma listOfFam_length (F : Finset BlockIdx) : (listOfFam F).length = F.card := by
  simpa [listOfFam_toFinset (F := F)] using!
    (List.toFinset_card_of_nodup (listOfFam_nodup F)).symm

def vertexFamilyFams : List (Finset BlockIdx) :=
  vertexFamilies.map List.toFinset

lemma vertexFamilyFams_eq :
    vertexFamilyFams = [famE', famD', famC', famB', famA'] := by
  -- Reuse the precomputed list-level classification `vertexFamilies_eq`.
  simpa [vertexFamilyFams, famA', famB', famC', famD', famE'] using!
    congrArg (fun L => L.map List.toFinset) vertexFamilies_eq

lemma classify_isVertexFamilyIdx
    (F : Finset BlockIdx) (hF : IsVertexFamilyIdx F) :
    F = famA' ∨ F = famB' ∨ F = famC' ∨ F = famD' ∨ F = famE' := by
  -- First show `listOfFam F` appears in `vertexFamilies`.
  have hlen : (listOfFam F).length = 4 := by
    -- extract the `length = 4` check from the boolean predicate
    have hbool : Design23632.isVertexFamilyIdxB (listOfFam F) = true := by
      simpa [IsVertexFamilyIdx, IsVertexFamilyIdxB] using! hF
    have hbool' :
        (((listOfFam F).length = 4 ∧ Design23632.nodupB (listOfFam F) = true) ∧
            Design23632.allPairsInterOne (listOfFam F) = true) ∧
          Design23632.unionPoints (listOfFam F) = (Finset.univ : Finset Point) := by
      simpa [Design23632.isVertexFamilyIdxB, Bool.and_eq_true_iff, decide_eq_true_eq] using! hbool
    exact hbool'.1.1.1
  have hmem_sublists : listOfFam F ∈ List.sublistsLen 4 (List.finRange 10) := by
    have hsub : List.Sublist (listOfFam F) (List.finRange 10) := listOfFam_sublist F
    exact (List.mem_sublistsLen.2 ⟨hsub, hlen⟩)
  have hpred : Design23632.isVertexFamilyIdxB (listOfFam F) = true := by
    simpa [IsVertexFamilyIdx, IsVertexFamilyIdxB] using! hF
  have hmem_vertexFamilies : listOfFam F ∈ vertexFamilies := by
    refine List.mem_filter.2 ?_
    exact ⟨hmem_sublists, by simp [hpred]⟩
  have hmem_vf : F ∈ vertexFamilyFams := by
    refine List.mem_map.2 ?_
    refine ⟨listOfFam F, hmem_vertexFamilies, ?_⟩
    simp [listOfFam_toFinset (F := F)]
  -- now use the explicit computation of `vertexFamilyFams`
  have : F = famE' ∨ F = famD' ∨ F = famC' ∨ F = famB' ∨ F = famA' := by
    simpa [vertexFamilyFams_eq] using! hmem_vf
  -- reorder to `A`-`E`
  grind only

/-!
### Singleton intersections of canonical vertex families
-/

/-- `famA'` and `famB'` intersect in the singleton `{0}`. -/
public lemma famA'_inter_famB' : (famA' ∩ famB' : Finset BlockIdx) = {0} := by decide
/-- `famA'` and `famC'` intersect in the singleton `{9}`. -/
public lemma famA'_inter_famC' : (famA' ∩ famC' : Finset BlockIdx) = {9} := by decide
/-- `famA'` and `famD'` intersect in the singleton `{3}`. -/
public lemma famA'_inter_famD' : (famA' ∩ famD' : Finset BlockIdx) = {3} := by decide
/-- `famA'` and `famE'` intersect in the singleton `{6}`. -/
public lemma famA'_inter_famE' : (famA' ∩ famE' : Finset BlockIdx) = {6} := by decide

/-- `famB'` and `famC'` intersect in the singleton `{7}`. -/
public lemma famB'_inter_famC' : (famB' ∩ famC' : Finset BlockIdx) = {7} := by decide
/-- `famB'` and `famD'` intersect in the singleton `{8}`. -/
public lemma famB'_inter_famD' : (famB' ∩ famD' : Finset BlockIdx) = {8} := by decide
/-- `famB'` and `famE'` intersect in the singleton `{4}`. -/
public lemma famB'_inter_famE' : (famB' ∩ famE' : Finset BlockIdx) = {4} := by decide

/-- `famC'` and `famD'` intersect in the singleton `{1}`. -/
public lemma famC'_inter_famD' : (famC' ∩ famD' : Finset BlockIdx) = {1} := by decide
/-- `famC'` and `famE'` intersect in the singleton `{2}`. -/
public lemma famC'_inter_famE' : (famC' ∩ famE' : Finset BlockIdx) = {2} := by decide

/-- `famD'` and `famE'` intersect in the singleton `{5}`. -/
public lemma famD'_inter_famE' : (famD' ∩ famE' : Finset BlockIdx) = {5} := by decide

end Design23632

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
