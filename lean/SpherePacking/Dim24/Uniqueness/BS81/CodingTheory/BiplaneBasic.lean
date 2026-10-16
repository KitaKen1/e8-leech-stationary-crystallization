-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Basic facts about the `2-(11,5,2)` biplane

We use a convenient axiomatisation matching the construction in
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`:
we start from a family of `11` subsets of an `11`-set, each of size `5`, with constant pairwise
intersection size `2`. From this we derive the usual biplane parameters:
each point lies in exactly `5` blocks, and each pair of points lies in exactly `2` blocks.

## Main definitions
* `Biplane.Structure`
* `Biplane.Structure.r`
* `Biplane.Structure.lam`

## Main statements
* `Biplane.Structure.sum_r_eq_55`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open scoped BigOperators

namespace Biplane

/-- The point type for the `2-(11,5,2)` biplane. -/
public abbrev Point := Fin 11
/-- A block is a finite set of points. In a `Biplane.Structure`, blocks have cardinality `5`. -/
public abbrev Block := Finset Point

/-- An axiomatisation of a `2-(11,5,2)` biplane by constant block intersections. -/
public structure Structure where
  blocks : Finset Block
  blocks_card : blocks.card = 11
  block_card : ∀ B ∈ blocks, B.card = 5
  inter_card : ∀ ⦃B B'⦄, B ∈ blocks → B' ∈ blocks → B ≠ B' → (B ∩ B').card = 2

namespace Structure

variable (D : Structure)

/-- For a point `x`, the number of blocks of the biplane containing `x`. -/
@[expose] public def r (x : Point) : ℕ :=
  (D.blocks.filter fun B => x ∈ B).card

/-- For points `x,y`, the number of blocks of the biplane containing both `x` and `y`. -/
@[expose] public def lam (x y : Point) : ℕ :=
  (D.blocks.filter fun B => x ∈ B ∧ y ∈ B).card

private def incidences (B : Block) : Finset (Point × Block) :=
  B.product {B}

private lemma mem_incidences {B : Block} {p : Point × Block} :
    p ∈ incidences B ↔ p.1 ∈ B ∧ p.2 = B := by
  rcases p with ⟨x, B0⟩
  simp [incidences, eq_comm]

attribute [grind =] mem_incidences

private lemma incidences_disjoint (B B' : Block) (h : B ≠ B') :
    Disjoint (incidences B) (incidences B') := by
  refine Finset.disjoint_left.2 ?_
  intro p hp hp'
  have hB : p.2 = B := (mem_incidences (B := B) (p := p)).1 hp |>.2
  have hB' : p.2 = B' := (mem_incidences (B := B') (p := p)).1 hp' |>.2
  exact h (hB.symm.trans hB')

/-- The sum of the incidence counts `r x` over all points is `55`. -/
public lemma sum_r_eq_55 : (∑ x : Point, D.r x) = 55 := by
  -- Double-count incidences `(x,B)` with `B ∈ blocks` and `x ∈ B`.
  let I : Finset (Point × Block) :=
    D.blocks.biUnion fun B => incidences B
  have hDisj : (↑D.blocks : Set Block).PairwiseDisjoint (fun B => incidences B) := by
    intro B hB B' hB' hne
    exact incidences_disjoint (B := B) (B' := B') hne
  have hIcard_blocks : I.card = ∑ B ∈ D.blocks, B.card := by
    have hIcard : I.card = ∑ B ∈ D.blocks, (incidences B).card := by
      simpa [I] using! (Finset.card_biUnion hDisj)
    -- `card (B × {B}) = card B`.
    have hterm : ∀ B, (incidences B).card = B.card := by
      intro B
      simp [incidences]
    simpa [hterm] using! hIcard
  have hIcard_points : I.card = ∑ x : Point, D.r x := by
    -- fiberwise on the first component
    have hfiber :
        I.card = ∑ x : Point, (I.filter fun p => p.1 = x).card := by
      -- `univ` contains the image of `Prod.fst`
      simpa using!
        (Finset.card_eq_sum_card_fiberwise (s := I) (t := (Finset.univ : Finset Point))
          (f := Prod.fst) (by intro p hp; simp))
    have hfiber' : ∀ x : Point, (I.filter fun p => p.1 = x).card = D.r x := by
      intro x
      -- identify the fiber with the blocks containing `x`
      let Sx : Finset Block := D.blocks.filter fun B => x ∈ B
      have hinj : Function.Injective (fun B : Block => (x, B)) := by
        intro B B' h
        exact congrArg Prod.snd h
      have hEq :
          (I.filter fun p => p.1 = x) = Sx.image (fun B : Block => (x, B)) := by
        ext p
        simp [I, Sx, incidences]
        grind (splits := 3) only
      have : (I.filter fun p => p.1 = x).card = Sx.card := by
        simp [hEq, Finset.card_image_of_injective _ hinj]
      simpa [r, Sx] using! this
    simpa [hfiber'] using! hfiber
  have hsumBlocks : (∑ B ∈ D.blocks, B.card) = 55 := by
    calc
      (∑ B ∈ D.blocks, B.card) = ∑ B ∈ D.blocks, 5 := by
        refine Finset.sum_congr rfl ?_
        intro B hB
        simp [D.block_card B hB]
      _ = D.blocks.card * 5 := by simp
      _ = 55 := by simp [D.blocks_card]
  -- conclude
  have : (∑ x : Point, D.r x) = (∑ B ∈ D.blocks, B.card) := by
    calc
      (∑ x : Point, D.r x) = I.card := by simpa using! hIcard_points.symm
      _ = ∑ B ∈ D.blocks, B.card := hIcard_blocks
  simpa [hsumBlocks] using! this

end Biplane.Structure
end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
