module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Biplane23632
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Sublists

/-!
# Vertex families in the canonical `2-(6,3,2)` design

We follow Lemma `23632_vertex_families` from the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.

To keep the proof robust and computational (and to avoid `Finset (Finset _)` equality issues),
we enumerate all `4`-element sublists of the ten canonical blocks and filter those satisfying the
vertex-family predicate. The resulting list is certified by `decide`.

## Main definitions
* `Design23632.vertexFamilies`
* `Design23632.famA`
* `Design23632.famB`
* `Design23632.famC`
* `Design23632.famD`
* `Design23632.famE`

## Main statements
* `Design23632.vertexFamilies_eq`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

namespace Design23632

/-- Indices for the ten canonical blocks, used to avoid `Finset (Finset _)` equality issues. -/
public abbrev BlockIdx := Fin 10

-- Canonical blocks, indexed by `Fin 10` in the order used in `canonicalBlocks`.
/-- The `i`-th canonical block, indexed by `BlockIdx`. -/
@[expose] public def blk : BlockIdx → Block
  | ⟨0, _⟩ => ({0, 1, 2} : Block)
  | ⟨1, _⟩ => ({0, 1, 4} : Block)
  | ⟨2, _⟩ => ({0, 2, 3} : Block)
  | ⟨3, _⟩ => ({0, 3, 5} : Block)
  | ⟨4, _⟩ => ({0, 4, 5} : Block)
  | ⟨5, _⟩ => ({1, 2, 5} : Block)
  | ⟨6, _⟩ => ({1, 3, 4} : Block)
  | ⟨7, _⟩ => ({1, 3, 5} : Block)
  | ⟨8, _⟩ => ({2, 3, 4} : Block)
  | ⟨9, _⟩ => ({2, 4, 5} : Block)

/-- Intersection cardinality of two canonical blocks (via their indices). -/
public def interCard (i j : BlockIdx) : Nat :=
  (blk i ∩ blk j).card

/-- Union of the point sets of a list of block indices. -/
public def unionPoints (L : List BlockIdx) : Finset Point :=
  (L.foldr (fun i acc => blk i ∪ acc) ∅)

/-- Boolean predicate asserting that all pairwise intersections have cardinality `1`. -/
public def allPairsInterOne : List BlockIdx → Bool
  | [] => true
  | i :: is =>
      (is.all (fun j => decide (interCard i j = 1))) && allPairsInterOne is

/-- Boolean `nodup` check for `BlockIdx` lists, implemented by a quadratic scan. -/
public def nodupB (L : List BlockIdx) : Bool :=
  -- quadratic `nodup` is fine at this tiny size
  L.all (fun i => (L.erase i).all (fun j => decide (i ≠ j)))

/-- Boolean predicate for being a vertex family, stated in terms of block indices. -/
@[expose] public def isVertexFamilyIdxB (L : List BlockIdx) : Bool :=
  decide (L.length = 4) &&
  nodupB L &&
  allPairsInterOne L &&
  decide (unionPoints L = (Finset.univ : Finset Point))

/-- The list of all vertex families in the canonical design, enumerated by brute force. -/
@[expose] public def vertexFamilies : List (List BlockIdx) :=
  (List.sublistsLen 4 (List.finRange 10)).filter isVertexFamilyIdxB

/-- A concrete vertex family (list of block indices). -/
@[expose] public def famA : List BlockIdx := [0, 3, 6, 9]
/-- A concrete vertex family (list of block indices). -/
@[expose] public def famB : List BlockIdx := [0, 4, 7, 8]
/-- A concrete vertex family (list of block indices). -/
@[expose] public def famC : List BlockIdx := [1, 2, 7, 9]
/-- A concrete vertex family (list of block indices). -/
@[expose] public def famD : List BlockIdx := [1, 3, 5, 8]
/-- A concrete vertex family (list of block indices). -/
@[expose] public def famE : List BlockIdx := [2, 4, 5, 6]

lemma famA_isVertex : isVertexFamilyIdxB famA = true := by decide
lemma famB_isVertex : isVertexFamilyIdxB famB = true := by decide
lemma famC_isVertex : isVertexFamilyIdxB famC = true := by decide
lemma famD_isVertex : isVertexFamilyIdxB famD = true := by decide
lemma famE_isVertex : isVertexFamilyIdxB famE = true := by decide

/-- The exhaustive list of vertex families in the canonical design. -/
public lemma vertexFamilies_eq : vertexFamilies = [famE, famD, famC, famB, famA] := by
  decide

end Design23632

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
