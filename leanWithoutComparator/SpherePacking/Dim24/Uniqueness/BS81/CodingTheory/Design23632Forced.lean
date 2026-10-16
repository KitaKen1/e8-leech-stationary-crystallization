-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Biplane23632
import Mathlib.Tactic.FinCases

/-!
# Forcing the canonical `2-(6,3,2)` design

This is the deterministic reconstruction step in
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`, Lemma `23632_unique`.

Assuming `012, 014, 023, 125` are blocks of a `2-(6,3,2)` design, the remaining six blocks are
forced by pair multiplicities.

## Main statement
* `Design23632.forced_of_initial_blocks`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section
namespace Design23632

/-- The set of blocks in `T` containing the given pair of points. -/
public def blocksThroughPair (T : Finset Block) (x y : Point) : Finset Block :=
  T.filter (fun B => x ∈ B ∧ y ∈ B)

/-- Membership characterization for `blocksThroughPair`. -/
@[simp] public lemma mem_blocksThroughPair {T : Finset Block} {x y : Point} {B : Block} :
    B ∈ blocksThroughPair T x y ↔ B ∈ T ∧ x ∈ B ∧ y ∈ B := by
  simp [blocksThroughPair, and_assoc, and_comm]

attribute [grind =_] mem_blocksThroughPair

/-- The cardinality of `blocksThroughPair` is `pairCount`. -/
public lemma blocksThroughPair_card (T : Finset Block) (x y : Point) :
    (blocksThroughPair T x y).card = pairCount T x y := by
  rfl

attribute [grind =_] blocksThroughPair_card

/-- In an `Is23632` design, any block containing a pair `{x,y}` has the form `{x,y,u}`. -/
public lemma shape_of_mem_pair
    (T : Finset Block) (hT : Is23632 T) {x y : Point} (hxy : x ≠ y)
    {B : Block} (hB : B ∈ blocksThroughPair T x y) :
    ∃ u : Point, u ≠ x ∧ u ≠ y ∧ B = ({x, y, u} : Block) := by
  have hBT : B ∈ T := (mem_blocksThroughPair.1 hB).1
  have hcard : B.card = 3 := hT.2.1 B hBT
  have hx : x ∈ B := (mem_blocksThroughPair.1 hB).2.1
  have hy : y ∈ B := (mem_blocksThroughPair.1 hB).2.2
  have hErase : ((B.erase x).erase y).card = 1 := by
    have hy' : y ∈ B.erase x := by
      simp [Finset.mem_erase, hy, hxy.symm]
    have hcard' : (B.erase x).card = 2 := by simp [Finset.card_erase_of_mem hx, hcard]
    simp [Finset.card_erase_of_mem hy', hcard']
  rcases Finset.card_eq_one.1 hErase with ⟨u, hu⟩
  have hu_mem : u ∈ (B.erase x).erase y := by
    simp [hu]
  have huB : u ∈ B := by
    have : u ∈ B.erase x := (Finset.mem_erase.1 hu_mem).2
    exact (Finset.mem_erase.1 this).2
  have hux : u ≠ x := by
    have : u ∈ B.erase x := (Finset.mem_erase.1 hu_mem).2
    exact (Finset.mem_erase.1 this).1
  have huy : u ≠ y := (Finset.mem_erase.1 hu_mem).1
  refine ⟨u, hux, huy, ?_⟩
  -- `({x,y,u} ⊆ B)` and both have card `3`
  have hsubset : ({x, y, u} : Finset Point) ⊆ B := by
    intro t ht
    rcases (by simpa using! ht) with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact huB
  have hcardXYZ : ({x, y, u} : Finset Point).card = 3 := by
    -- use the characterization of card `3`
    have hx_y : x ≠ y := hxy
    have hx_u : x ≠ u := hux.symm
    have hy_u : y ≠ u := huy.symm
    -- `#s = 3` is notation for `s.card = 3`
    simpa using! (Finset.card_eq_three.2 ⟨x, y, u, hx_y, hx_u, hy_u, rfl⟩)
  have hB_le : B.card ≤ ({x, y, u} : Finset Point).card := by
    simp [hcard, hcardXYZ]
  have : ({x, y, u} : Finset Point) = B := Finset.eq_of_subset_of_card_le hsubset hB_le
  exact this.symm

lemma blocksThroughPair_eq_of_two
    {T : Finset Block} {x y : Point} (h : (T.filter (fun B => x ∈ B ∧ y ∈ B)).card = 2) :
    ∃ B₁ B₂ : Block, B₁ ≠ B₂ ∧ (T.filter fun B => x ∈ B ∧ y ∈ B) = {B₁, B₂} := by
  simpa using! Finset.card_eq_two.1 h

/-- If the four blocks `012`, `014`, `023`, `125` are present, then the whole design is
canonical. -/
public theorem forced_of_initial_blocks
    (T : Finset Block) (hT : Is23632 T)
    (h012 : ({0, 1, 2} : Block) ∈ T)
    (h014 : ({0, 1, 4} : Block) ∈ T)
    (h023 : ({0, 2, 3} : Block) ∈ T)
    (h125 : ({1, 2, 5} : Block) ∈ T) :
    T = canonicalBlocks := by
  have h01 : pairCount T 0 1 = 2 := hT.2.2 0 1 (by decide)
  have h02 : pairCount T 0 2 = 2 := hT.2.2 0 2 (by decide)
  have h12 : pairCount T 1 2 = 2 := hT.2.2 1 2 (by decide)
  have h05 : pairCount T 0 5 = 2 := hT.2.2 0 5 (by decide)
  have h13 : pairCount T 1 3 = 2 := hT.2.2 1 3 (by decide)
  have h24 : pairCount T 2 4 = 2 := hT.2.2 2 4 (by decide)
  have h015_not : ({0, 1, 5} : Block) ∉ T := by
    intro h015
    have hge : 3 ≤ pairCount T 0 1 := by
      have hsubset :
          ({ ({0, 1, 2} : Block), ({0, 1, 4} : Block), ({0, 1, 5} : Block) } : Finset Block)
            ⊆ (T.filter fun B => 0 ∈ B ∧ 1 ∈ B) := by
        intro B hB
        rcases (by simpa using! hB) with rfl | rfl | rfl
        · simp [h012]
        · simp [h014]
        · simp [h015]
      have hcard3 :
          ({ ({0, 1, 2} : Block), ({0, 1, 4} : Block), ({0, 1, 5} : Block) } : Finset Block).card =
            3 := by
        decide
      have hle : 3 ≤ (T.filter (fun B => 0 ∈ B ∧ 1 ∈ B)).card := by
        simpa [hcard3] using! (Finset.card_le_card hsubset)
      simpa [blocksThroughPair_card] using! hle
    exact (Nat.not_succ_le_self 2) (Eq.ndrec (motive := fun n => 3 ≤ n) hge h01)
  have h025_not : ({0, 2, 5} : Block) ∉ T := by
    intro h025
    have hge : 3 ≤ pairCount T 0 2 := by
      have hsubset :
          ({ ({0, 1, 2} : Block), ({0, 2, 3} : Block), ({0, 2, 5} : Block) } : Finset Block)
            ⊆ (T.filter fun B => 0 ∈ B ∧ 2 ∈ B) := by
        intro B hB
        rcases (by simpa using! hB) with rfl | rfl | rfl
        · simp [h012]
        · simp [h023]
        · simp [h025]
      have hcard3 :
          ({ ({0, 1, 2} : Block), ({0, 2, 3} : Block), ({0, 2, 5} : Block) } : Finset Block).card =
            3 := by
        decide
      have hle : 3 ≤ (T.filter (fun B => 0 ∈ B ∧ 2 ∈ B)).card := by
        simpa [hcard3] using! (Finset.card_le_card hsubset)
      simpa [blocksThroughPair_card] using! hle
    exact (Nat.not_succ_le_self 2) (Eq.ndrec (motive := fun n => 3 ≤ n) hge h02)
  have h123_not : ({1, 2, 3} : Block) ∉ T := by
    intro h123
    have hge : 3 ≤ pairCount T 1 2 := by
      have hsubset :
          ({ ({0, 1, 2} : Block), ({1, 2, 5} : Block), ({1, 2, 3} : Block) } : Finset Block)
            ⊆ (T.filter fun B => 1 ∈ B ∧ 2 ∈ B) := by
        intro B hB
        rcases (by simpa using! hB) with rfl | rfl | rfl
        · simp [h012]
        · simp [h125]
        · simp [h123]
      have hcard3 :
          ({ ({0, 1, 2} : Block), ({1, 2, 5} : Block), ({1, 2, 3} : Block) } : Finset Block).card =
            3 := by
        decide
      have hle : 3 ≤ (T.filter (fun B => 1 ∈ B ∧ 2 ∈ B)).card := by
        simpa [hcard3] using! (Finset.card_le_card hsubset)
      simpa [blocksThroughPair_card] using! hle
    exact (Nat.not_succ_le_self 2) (Eq.ndrec (motive := fun n => 3 ≤ n) hge h12)
  have h024_not : ({0, 2, 4} : Block) ∉ T := by
    intro h024
    have hge : 3 ≤ pairCount T 0 2 := by
      have hsubset :
          ({ ({0, 1, 2} : Block), ({0, 2, 3} : Block), ({0, 2, 4} : Block) } : Finset Block)
            ⊆ (T.filter fun B => 0 ∈ B ∧ 2 ∈ B) := by
        intro B hB
        rcases (by simpa using! hB) with rfl | rfl | rfl
        · simp [h012]
        · simp [h023]
        · simp [h024]
      have hcard3 :
          ({ ({0, 1, 2} : Block), ({0, 2, 3} : Block), ({0, 2, 4} : Block) } : Finset Block).card =
            3 := by
        decide
      have hle : 3 ≤ (T.filter (fun B => 0 ∈ B ∧ 2 ∈ B)).card := by
        simpa [hcard3] using! (Finset.card_le_card hsubset)
      simpa [blocksThroughPair_card] using! hle
    exact (Nat.not_succ_le_self 2) (Eq.ndrec (motive := fun n => 3 ≤ n) hge h02)
  have h124_not : ({1, 2, 4} : Block) ∉ T := by
    intro h124
    have hge : 3 ≤ pairCount T 1 2 := by
      have hsubset :
          ({ ({0, 1, 2} : Block), ({1, 2, 5} : Block), ({1, 2, 4} : Block) } : Finset Block)
            ⊆ (T.filter fun B => 1 ∈ B ∧ 2 ∈ B) := by
        intro B hB
        rcases (by simpa using! hB) with rfl | rfl | rfl
        · simp [h012]
        · simp [h125]
        · simp [h124]
      have hcard3 :
          ({ ({0, 1, 2} : Block), ({1, 2, 5} : Block), ({1, 2, 4} : Block) } : Finset Block).card =
            3 := by
        decide
      have hle : 3 ≤ (T.filter (fun B => 1 ∈ B ∧ 2 ∈ B)).card := by
        simpa [hcard3] using! (Finset.card_le_card hsubset)
      simpa [blocksThroughPair_card] using! hle
    exact (Nat.not_succ_le_self 2) (Eq.ndrec (motive := fun n => 3 ≤ n) hge h12)
  -- Force `035` and `045` from the two blocks containing `{0,5}`.
  have h05card : (T.filter (fun B => 0 ∈ B ∧ 5 ∈ B)).card = 2 := by
    simpa [blocksThroughPair_card] using! h05
  rcases blocksThroughPair_eq_of_two h05card with ⟨B₁, B₂, hne, hEq⟩
  have hB₁mem : B₁ ∈ (T.filter fun B => 0 ∈ B ∧ 5 ∈ B) := by simp [hEq]
  have hB₂mem : B₂ ∈ (T.filter fun B => 0 ∈ B ∧ 5 ∈ B) := by simp [hEq]
  have hB₁shape : B₁ = ({0, 1, 5} : Block) ∨ B₁ = ({0, 2, 5} : Block) ∨
      B₁ = ({0, 3, 5} : Block) ∨ B₁ = ({0, 4, 5} : Block) := by
    rcases shape_of_mem_pair (T := T) hT (x := 0) (y := 5) (by decide) hB₁mem with
      ⟨u, hu0, hu5, rfl⟩
    fin_cases u <;> (try cases hu0 rfl) <;> (try cases hu5 rfl) <;> decide
  have hB₂shape : B₂ = ({0, 1, 5} : Block) ∨ B₂ = ({0, 2, 5} : Block) ∨
      B₂ = ({0, 3, 5} : Block) ∨ B₂ = ({0, 4, 5} : Block) := by
    rcases shape_of_mem_pair (T := T) hT (x := 0) (y := 5) (by decide) hB₂mem with
      ⟨u, hu0, hu5, rfl⟩
    fin_cases u <;> (try cases hu0 rfl) <;> (try cases hu5 rfl) <;> decide
  have h035_mem : ({0, 3, 5} : Block) ∈ T := by
    have hB₁T : B₁ ∈ T := (mem_blocksThroughPair.1 hB₁mem).1
    have hB₂T : B₂ ∈ T := (mem_blocksThroughPair.1 hB₂mem).1
    -- `B₁` and `B₂` are the two blocks through `{0,5}`; the forbidden options are `015` and `025`,
    -- so one of them is `035`.
    rcases hB₁shape with hB₁eq | hB₁rest
    · subst hB₁eq; exact (h015_not hB₁T).elim
    rcases hB₁rest with hB₁eq | hB₁rest
    · subst hB₁eq; exact (h025_not hB₁T).elim
    rcases hB₁rest with hB₁eq | hB₁eq
    · subst hB₁eq; exact hB₁T
    · -- `B₁ = 045`, so `B₂` must be `035`
      rcases hB₂shape with hB₂eq | hB₂rest
      · subst hB₂eq; exact (h015_not hB₂T).elim
      rcases hB₂rest with hB₂eq | hB₂rest
      · subst hB₂eq; exact (h025_not hB₂T).elim
      rcases hB₂rest with hB₂eq | hB₂eq
      · subst hB₂eq; exact hB₂T
      · subst hB₂eq
        exact (hne (by simp [hB₁eq])).elim
  have h045_mem : ({0, 4, 5} : Block) ∈ T := by
    -- the other block through `{0,5}` is `045`
    have h035f : ({0, 3, 5} : Block) ∈ (T.filter fun B => 0 ∈ B ∧ 5 ∈ B) := by
      simp [h035_mem]
    have hex : ∃ B ∈ (T.filter (fun B => 0 ∈ B ∧ 5 ∈ B)), B ≠ ({0, 3, 5} : Block) := by
      have : 1 < (T.filter (fun B => 0 ∈ B ∧ 5 ∈ B)).card := by
        rw [h05card]
        decide
      exact Finset.exists_mem_ne this {0, 3, 5}
    rcases hex with ⟨B, hB, hneB⟩
    have hBshape : B = ({0, 1, 5} : Block) ∨ B = ({0, 2, 5} : Block) ∨
        B = ({0, 3, 5} : Block) ∨ B = ({0, 4, 5} : Block) := by
      rcases shape_of_mem_pair (T := T) hT (x := 0) (y := 5) (by decide) hB with ⟨u, hu0, hu5, rfl⟩
      fin_cases u <;> (try cases hu0 rfl) <;> (try cases hu5 rfl) <;> decide
    rcases hBshape with hB' | hB' | hB' | hB'
    · subst hB'; exact (h015_not (mem_blocksThroughPair.1 hB).1).elim
    · subst hB'; exact (h025_not (mem_blocksThroughPair.1 hB).1).elim
    · subst hB'; exact (hneB rfl).elim
    · subst hB'; exact (mem_blocksThroughPair.1 hB).1
  -- Force `134` and `135` from the two blocks containing `{1,3}`.
  have h13card : (T.filter (fun B => 1 ∈ B ∧ 3 ∈ B)).card = 2 := by
    simpa [blocksThroughPair_card] using! h13
  rcases blocksThroughPair_eq_of_two h13card with ⟨C₁, C₂, hneC, hEqC⟩
  have hC₁mem : C₁ ∈ (T.filter fun B => 1 ∈ B ∧ 3 ∈ B) := by simp [hEqC]
  have hC₂mem : C₂ ∈ (T.filter fun B => 1 ∈ B ∧ 3 ∈ B) := by simp [hEqC]
  have hC₁shape : C₁ = ({0, 1, 3} : Block) ∨ C₁ = ({1, 2, 3} : Block) ∨
      C₁ = ({1, 3, 4} : Block) ∨ C₁ = ({1, 3, 5} : Block) := by
    rcases shape_of_mem_pair (T := T) hT (x := 1) (y := 3) (by decide) hC₁mem with
      ⟨u, hu1, hu3, rfl⟩
    fin_cases u <;> (try cases hu1 rfl) <;> (try cases hu3 rfl) <;> decide
  have hC₂shape : C₂ = ({0, 1, 3} : Block) ∨ C₂ = ({1, 2, 3} : Block) ∨
      C₂ = ({1, 3, 4} : Block) ∨ C₂ = ({1, 3, 5} : Block) := by
    rcases shape_of_mem_pair (T := T) hT (x := 1) (y := 3) (by decide) hC₂mem with
      ⟨u, hu1, hu3, rfl⟩
    fin_cases u <;> (try cases hu1 rfl) <;> (try cases hu3 rfl) <;> decide
  have h013_not : ({0, 1, 3} : Block) ∉ T := by
    intro h013
    have hge : 3 ≤ pairCount T 0 1 := by
      have hsubset :
          ({ ({0, 1, 2} : Block), ({0, 1, 4} : Block), ({0, 1, 3} : Block) } : Finset Block)
            ⊆ (T.filter fun B => 0 ∈ B ∧ 1 ∈ B) := by
        intro B hB
        rcases (by simpa using! hB) with rfl | rfl | rfl
        · simp [h012]
        · simp [h014]
        · simp [h013]
      have hcard3 :
          ({ ({0, 1, 2} : Block), ({0, 1, 4} : Block), ({0, 1, 3} : Block) } : Finset Block).card =
            3 := by
        decide
      have hle : 3 ≤ (T.filter (fun B => 0 ∈ B ∧ 1 ∈ B)).card := by
        simpa [hcard3] using! (Finset.card_le_card hsubset)
      simpa [blocksThroughPair_card] using! hle
    exact (Nat.not_succ_le_self 2) (Eq.ndrec (motive := fun n => 3 ≤ n) hge h01)
  have h134_mem : ({1, 3, 4} : Block) ∈ T := by
    have hC₁T : C₁ ∈ T := (mem_blocksThroughPair.1 hC₁mem).1
    have hC₂T : C₂ ∈ T := (mem_blocksThroughPair.1 hC₂mem).1
    rcases hC₁shape with hC₁eq | hC₁rest
    · subst hC₁eq; exact (h013_not hC₁T).elim
    rcases hC₁rest with hC₁eq | hC₁rest
    · subst hC₁eq; exact (h123_not hC₁T).elim
    rcases hC₁rest with hC₁eq | hC₁eq
    · subst hC₁eq; exact hC₁T
    · -- `C₁ = 135`, so `C₂` must be `134`
      rcases hC₂shape with hC₂eq | hC₂rest
      · subst hC₂eq; exact (h013_not hC₂T).elim
      rcases hC₂rest with hC₂eq | hC₂rest
      · subst hC₂eq; exact (h123_not hC₂T).elim
      rcases hC₂rest with hC₂eq | hC₂eq
      · subst hC₂eq; exact hC₂T
      · subst hC₂eq
        exact (hneC (by simp [hC₁eq])).elim
  have h135_mem : ({1, 3, 5} : Block) ∈ T := by
    have h134f : ({1, 3, 4} : Block) ∈ (T.filter fun B => 1 ∈ B ∧ 3 ∈ B) := by
      simp [h134_mem]
    have hex : ∃ B ∈ (T.filter (fun B => 1 ∈ B ∧ 3 ∈ B)), B ≠ ({1, 3, 4} : Block) := by
      have : 1 < (T.filter (fun B => 1 ∈ B ∧ 3 ∈ B)).card := by
        rw [h13card]
        decide
      exact Finset.exists_mem_ne this {1, 3, 4}
    rcases hex with ⟨B, hB, hneB⟩
    have hBshape : B = ({0, 1, 3} : Block) ∨ B = ({1, 2, 3} : Block) ∨
        B = ({1, 3, 4} : Block) ∨ B = ({1, 3, 5} : Block) := by
      rcases shape_of_mem_pair (T := T) hT (x := 1) (y := 3) (by decide) hB with ⟨u, hu1, hu3, rfl⟩
      fin_cases u <;> (try cases hu1 rfl) <;> (try cases hu3 rfl) <;> decide
    rcases hBshape with hB' | hB' | hB' | hB'
    · subst hB'; exact (h013_not (mem_blocksThroughPair.1 hB).1).elim
    · subst hB'; exact (h123_not (mem_blocksThroughPair.1 hB).1).elim
    · subst hB'; exact (hneB rfl).elim
    · subst hB'; exact (mem_blocksThroughPair.1 hB).1
  -- Force `234` and `245` from the two blocks containing `{2,4}`.
  have h24card : (T.filter (fun B => 2 ∈ B ∧ 4 ∈ B)).card = 2 := by
    simpa [blocksThroughPair_card] using! h24
  rcases blocksThroughPair_eq_of_two h24card with ⟨D₁, D₂, hneD, hEqD⟩
  have hD₁mem : D₁ ∈ (T.filter fun B => 2 ∈ B ∧ 4 ∈ B) := by simp [hEqD]
  have hD₂mem : D₂ ∈ (T.filter fun B => 2 ∈ B ∧ 4 ∈ B) := by simp [hEqD]
  have hD₁shape : D₁ = ({0, 2, 4} : Block) ∨ D₁ = ({1, 2, 4} : Block) ∨
      D₁ = ({2, 3, 4} : Block) ∨ D₁ = ({2, 4, 5} : Block) := by
    rcases
      shape_of_mem_pair (T := T) hT (x := 2) (y := 4) (by decide) hD₁mem with ⟨u, hu2, hu4, rfl⟩
    fin_cases u <;> (try cases hu2 rfl) <;> (try cases hu4 rfl) <;> decide
  have hD₂shape : D₂ = ({0, 2, 4} : Block) ∨ D₂ = ({1, 2, 4} : Block) ∨
      D₂ = ({2, 3, 4} : Block) ∨ D₂ = ({2, 4, 5} : Block) := by
    rcases
      shape_of_mem_pair (T := T) hT (x := 2) (y := 4) (by decide) hD₂mem with ⟨u, hu2, hu4, rfl⟩
    fin_cases u <;> (try cases hu2 rfl) <;> (try cases hu4 rfl) <;> decide
  have h234_mem : ({2, 3, 4} : Block) ∈ T := by
    have hD₁T : D₁ ∈ T := (mem_blocksThroughPair.1 hD₁mem).1
    have hD₂T : D₂ ∈ T := (mem_blocksThroughPair.1 hD₂mem).1
    rcases hD₁shape with hD₁eq | hD₁rest
    · subst hD₁eq; exact (h024_not hD₁T).elim
    rcases hD₁rest with hD₁eq | hD₁rest
    · subst hD₁eq; exact (h124_not hD₁T).elim
    rcases hD₁rest with hD₁eq | hD₁eq
    · subst hD₁eq; exact hD₁T
    · -- `D₁ = 245`, so `D₂` must be `234`
      rcases hD₂shape with hD₂eq | hD₂rest
      · subst hD₂eq; exact (h024_not hD₂T).elim
      rcases hD₂rest with hD₂eq | hD₂rest
      · subst hD₂eq; exact (h124_not hD₂T).elim
      rcases hD₂rest with hD₂eq | hD₂eq
      · subst hD₂eq; exact hD₂T
      · subst hD₂eq
        exact (hneD (by simp [hD₁eq])).elim
  have h245_mem : ({2, 4, 5} : Block) ∈ T := by
    have h234f : ({2, 3, 4} : Block) ∈ (T.filter fun B => 2 ∈ B ∧ 4 ∈ B) := by
      simp [h234_mem]
    have hex : ∃ B ∈ (T.filter (fun B => 2 ∈ B ∧ 4 ∈ B)), B ≠ ({2, 3, 4} : Block) := by
      have : 1 < (T.filter (fun B => 2 ∈ B ∧ 4 ∈ B)).card := by
        rw [h24card]
        decide
      exact Finset.exists_mem_ne this {2, 3, 4}
    rcases hex with ⟨B, hB, hneB⟩
    have hBshape : B = ({0, 2, 4} : Block) ∨ B = ({1, 2, 4} : Block) ∨
        B = ({2, 3, 4} : Block) ∨ B = ({2, 4, 5} : Block) := by
      rcases shape_of_mem_pair (T := T) hT (x := 2) (y := 4) (by decide) hB with ⟨u, hu2, hu4, rfl⟩
      fin_cases u <;> (try cases hu2 rfl) <;> (try cases hu4 rfl) <;> decide
    rcases hBshape with hB' | hB' | hB' | hB'
    · subst hB'; exact (h024_not (mem_blocksThroughPair.1 hB).1).elim
    · subst hB'; exact (h124_not (mem_blocksThroughPair.1 hB).1).elim
    · subst hB'; exact (hneB rfl).elim
    · subst hB'; exact (mem_blocksThroughPair.1 hB).1
  -- Now `canonicalBlocks ⊆ T`, and both have card `10`.
  have hsubset : canonicalBlocks ⊆ T := by
    intro B hB
    rcases (by simpa [canonicalBlocks] using! hB) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h012
    · exact h014
    · exact h023
    · exact h035_mem
    · exact h045_mem
    · exact h125
    · exact h134_mem
    · exact h135_mem
    · exact h234_mem
    · exact h245_mem
  have hcardCan : canonicalBlocks.card = 10 := by decide
  have hcardT : T.card = 10 := hT.1
  exact (Finset.eq_of_subset_of_card_le hsubset (by simp [hcardT, hcardCan])).symm

end Design23632

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
