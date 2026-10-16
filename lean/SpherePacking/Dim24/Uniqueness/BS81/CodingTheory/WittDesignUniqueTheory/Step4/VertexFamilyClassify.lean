-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.Step4.Auxiliary
import Mathlib.Data.List.Sublists

/-!
# Classifying vertex families (computational)

This file provides a computational classification of vertex families for the canonical `2-(6,3,2)`
design, in a form convenient for Step 4.

We introduce a lightweight boolean predicate on `List BlockIdx` that checks the paper conditions:
`length = 4`, no duplicates, pairwise block intersections have card `1`, and the union of points is
all of `Fin 6`. We then enumerate all `4`-sublists of `finRange 10` and certify by `decide` that
there are exactly five such families, matching `famA`-`famE`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace Design23632

/-- Boolean check that all pairs of blocks in the list intersect in `1` point. -/
@[expose] public def allPairsInterOneB : List BlockIdx → Bool
  | [] => true
  | i :: is =>
      (is.all (fun j => decide ((blk i ∩ blk j).card = 1))) && allPairsInterOneB is

/-- The propositional version of `allPairsInterOneB`. -/
@[expose] public def PairwiseInterOne (L : List BlockIdx) : Prop :=
  L.Pairwise fun i j => (blk i ∩ blk j).card = 1

/-- `allPairsInterOneB` returns `true` exactly when `PairwiseInterOne` holds. -/
public lemma allPairsInterOneB_eq_true_iff (L : List BlockIdx) :
    allPairsInterOneB L = true ↔ PairwiseInterOne L := by
  induction L with
  | nil =>
      simp [allPairsInterOneB, PairwiseInterOne]
  | cons i is ih =>
      simp [allPairsInterOneB, PairwiseInterOne, ih, List.pairwise_cons, List.all_eq_true,
        decide_eq_true_eq]

/-- Boolean predicate for being a vertex family (length `4`). -/
@[expose] public def isVertexFamilyIdxB₄ (L : List BlockIdx) : Bool :=
  decide (L.length = 4) &&
  decide L.Nodup &&
  allPairsInterOneB L &&
  decide ((L.toFinset.image blk).sup id = (Finset.univ : Finset Point))

/-- All vertex families, found by filtering `4`-sublists of `finRange 10`. -/
public def vertexFamilies₄ : List (List BlockIdx) :=
  (List.sublistsLen 4 (List.finRange 10)).filter isVertexFamilyIdxB₄

/-- The precomputed list of vertex families agrees with `[famE, famD, famC, famB, famA]`. -/
public lemma vertexFamilies₄_eq : vertexFamilies₄ = [famE, famD, famC, famB, famA] := by decide

/-- Classify a vertex family given as a finset of indices, via `listOfFam`. -/
public lemma classify_vertexFamilyIdxB₄_toFinset
    (F : Finset BlockIdx) (hF : isVertexFamilyIdxB₄ (listOfFam F) = true) :
    F = famA' ∨ F = famB' ∨ F = famC' ∨ F = famD' ∨ F = famE' := by
  have hF' :
      (((listOfFam F).length = 4 ∧ (listOfFam F).Nodup) ∧ allPairsInterOneB (listOfFam F) = true) ∧
        (listOfFam F).toFinset.sup blk = (Finset.univ : Finset Point) := by
    simpa [isVertexFamilyIdxB₄, Bool.and_eq_true_iff] using! hF
  have hlen : (listOfFam F).length = 4 := hF'.1.1.1
  have hmem_sublists : listOfFam F ∈ List.sublistsLen 4 (List.finRange 10) :=
    (List.mem_sublistsLen.2 ⟨listOfFam_sublist F, hlen⟩)
  have hmem : listOfFam F ∈ vertexFamilies₄ := by
    simp [vertexFamilies₄, hmem_sublists, hF]
  have hmem' :
      listOfFam F = famE ∨ listOfFam F = famD ∨ listOfFam F = famC ∨ listOfFam F = famB ∨
        listOfFam F = famA := by
    simpa [vertexFamilies₄_eq] using! hmem
  rcases hmem' with h | h | h | h | h
  · have : F = famE' := by
      simpa [listOfFam_toFinset (F := F), famE'] using! congrArg List.toFinset h
    grind
  · have : F = famD' := by
      simpa [listOfFam_toFinset (F := F), famD'] using! congrArg List.toFinset h
    grind
  · have : F = famC' := by
      simpa [listOfFam_toFinset (F := F), famC'] using! congrArg List.toFinset h
    grind
  · have : F = famB' := by
      simpa [listOfFam_toFinset (F := F), famB'] using! congrArg List.toFinset h
    grind
  · have : F = famA' := by
      simpa [listOfFam_toFinset (F := F), famA'] using! congrArg List.toFinset h
    grind

end Design23632

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
