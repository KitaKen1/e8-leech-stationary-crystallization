-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Uniqueness of the `2-(6,3,2)` design

This file follows `paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`,
Lemma `23632_unique`.

## Main definitions
* `Design23632.canonicalBlocks`
* `Design23632.pairCount`
* `Design23632.Is23632`

## Main statements
* `Design23632.canonical_is23632`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

namespace Design23632

/-- The point type for the `2-(6,3,2)` design. -/
public abbrev Point := Fin 6
/-- A block is a finite set of points. In an `Is23632` design, blocks have cardinality `3`. -/
public abbrev Block := Finset Point

/-- The canonical family of ten blocks of the `2-(6,3,2)` design. -/
@[expose] public def canonicalBlocks : Finset Block :=
  { ({0, 1, 2} : Block),
    ({0, 1, 4} : Block),
    ({0, 2, 3} : Block),
    ({0, 3, 5} : Block),
    ({0, 4, 5} : Block),
    ({1, 2, 5} : Block),
    ({1, 3, 4} : Block),
    ({1, 3, 5} : Block),
    ({2, 3, 4} : Block),
    ({2, 4, 5} : Block) }

/-- Count how many blocks in `T` contain both points `a` and `b`. -/
@[expose] public def pairCount (T : Finset Block) (a b : Point) : ℕ :=
  (T.filter fun B => a ∈ B ∧ b ∈ B).card

/-- Predicate asserting that `T` is a `2-(6,3,2)` design. -/
@[expose] public def Is23632 (T : Finset Block) : Prop :=
  T.card = 10 ∧
  (∀ B ∈ T, B.card = 3) ∧
  (∀ a b : Point, a ≠ b → pairCount T a b = 2)

/-- The canonical family of blocks satisfies `Is23632`. -/
public lemma canonical_is23632 : Is23632 canonicalBlocks := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · intro B hB
    rcases (by simpa [canonicalBlocks] using! hB) with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · intro a b hab
    fin_cases a <;> fin_cases b <;> try cases hab rfl
    all_goals decide

end Design23632

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
