-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerParams
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lambda parameters in a Steiner system

We prove the standard double-counting identity

`(# blocks containing T) * choose (k - s) (t - s) = choose (v - s) (t - s)`,

for an `s`-subset `T` with `s ≤ t`.

## Main statement
* `SteinerSystem.card_blocksContaining_mul_choose`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerSystem

noncomputable section

open scoped BigOperators

variable {v k t : ℕ}

/-- Blocks containing a fixed subset `T`, as a finset. -/
@[expose] public def blocksContaining (S : SteinerSystem v k t) (T : Finset (Fin v)) :
    Finset (Finset (Fin v)) :=
  (S.blocksFinset.filter fun B => T ⊆ B)

/-- Membership in `blocksContaining`. -/
@[simp] public lemma mem_blocksContaining (S : SteinerSystem v k t) {T B : Finset (Fin v)} :
    B ∈ S.blocksContaining T ↔ B ∈ S.blocks ∧ T ⊆ B := by
  simp [blocksContaining]

/-- Double-counting: blocks through an `s`-subset. -/
public lemma card_blocksContaining_mul_choose
    (S : SteinerSystem v k t) {T : Finset (Fin v)} {s : ℕ}
    (hT : T.card = s) (hs : s ≤ t) :
    (S.blocksContaining T).card * Nat.choose (k - s) (t - s) =
      Nat.choose (v - s) (t - s) := by
  -- `Uset`: all `t`-subsets containing `T`.
  let Uset : Finset (Finset (Fin v)) := mSubsetsContaining (v := v) T t
  -- For a block `B`, `f B` is the set of `t`-subsets of `B` containing `T`.
  let f : Finset (Fin v) → Finset (Finset (Fin v)) := fun B =>
    (B.powersetCard t).filter fun U => T ⊆ U
  have hf_disj : (↑(S.blocksContaining T) : Set (Finset (Fin v))).PairwiseDisjoint f := by
    intro B hB B' hB' hne
    -- If a `t`-subset is contained in both blocks, the Steiner property forces `B = B'`.
    refine Finset.disjoint_left.2 ?_
    intro U hU hU'
    have hUcard : U.card = t := by
      exact (Finset.mem_powersetCard.1 ((Finset.mem_filter.1 hU).1)).2
    have hBmem : B ∈ S.blocks := (mem_blocksContaining S).1 hB |>.1
    have hB'mem : B' ∈ S.blocks := (mem_blocksContaining S).1 hB' |>.1
    have hUB : U ⊆ B := (Finset.mem_powersetCard.1 ((Finset.mem_filter.1 hU).1)).1
    have hUB' : U ⊆ B' := (Finset.mem_powersetCard.1 ((Finset.mem_filter.1 hU').1)).1
    rcases S.cover_unique U hUcard with ⟨B0, hB0, huniq⟩
    have hBeq : B = B0 := huniq B ⟨hBmem, hUB⟩
    have hB'eq : B' = B0 := huniq B' ⟨hB'mem, hUB'⟩
    exact hne (by simp [hBeq, hB'eq])
  have hsubset : (S.blocksContaining T).biUnion f ⊆ Uset := by
    intro U hU
    rcases Finset.mem_biUnion.1 hU with ⟨B, hB, hUB⟩
    have hU' : U ∈ f B := hUB
    have hUcard : U.card = t := (Finset.mem_powersetCard.1 ((Finset.mem_filter.1 hU').1)).2
    have hTsub : T ⊆ U := (Finset.mem_filter.1 hU').2
    exact (mem_mSubsetsContaining (T := T) (U := U)).2 ⟨hUcard, hTsub⟩
  have hUset_sub : Uset ⊆ (S.blocksContaining T).biUnion f := by
    intro U hU
    have hUcard : U.card = t := (mem_mSubsetsContaining (T := T) (U := U)).1 hU |>.1
    have hTsubU : T ⊆ U := (mem_mSubsetsContaining (T := T) (U := U)).1 hU |>.2
    rcases S.cover_unique U hUcard with ⟨B, hB, huniq⟩
    have hBcont : T ⊆ B := fun x hx => (hB.2) (hTsubU hx)
    have hBmem : B ∈ S.blocksContaining T := (mem_blocksContaining S).2 ⟨hB.1, hBcont⟩
    have hUmem : U ∈ f B := by
      refine Finset.mem_filter.2 ?_
      refine ⟨?_, hTsubU⟩
      refine Finset.mem_powersetCard.2 ?_
      exact ⟨hB.2, hUcard⟩
    exact Finset.mem_biUnion.2 ⟨B, hBmem, hUmem⟩
  have hUnion_eq : (S.blocksContaining T).biUnion f = Uset :=
    Finset.eq_of_subset_of_card_le hsubset (by simpa using! (Finset.card_le_card hUset_sub))
  have hCardUnion :
      ((S.blocksContaining T).biUnion f).card =
        ∑ B ∈ (S.blocksContaining T), (f B).card := by
    simpa using! (Finset.card_biUnion hf_disj)
  -- Each fiber has constant cardinality `choose (k-s) (t-s)`.
  have hFiber : ∀ B ∈ S.blocksContaining T, (f B).card = Nat.choose (k - s) (t - s) := by
    intro B hB
    have hBmem : B ∈ S.blocks := (mem_blocksContaining S).1 hB |>.1
    have hBcard : B.card = k := S.block_card B hBmem
    have hTsubB : T ⊆ B := (mem_blocksContaining S).1 hB |>.2
    -- Use the counting lemma from `SteinerParams`.
    have :
        ((B.powersetCard t).filter fun U => T ⊆ U).card =
          Nat.choose (B.card - s) (t - s) :=
      Finset.card_powersetCard_filter_superset (B := B) (T := T) hTsubB hT hs
    simpa [f, hBcard] using! this
  have hSum :
      (∑ B ∈ (S.blocksContaining T), (f B).card) =
        (S.blocksContaining T).card * Nat.choose (k - s) (t - s) := by
    -- constant sum
    exact Finset.sum_const_nat hFiber
  have hUset_card : Uset.card = Nat.choose (v - s) (t - s) := by
    simpa [Uset] using!
      card_mSubsetsContaining_of_card (v := v) (T := T) (s := s) (m := t) hT hs
  -- Combine.
  calc
    (S.blocksContaining T).card * Nat.choose (k - s) (t - s)
        = ∑ B ∈ (S.blocksContaining T), (f B).card :=
            (Eq.symm hSum)
    _ = ((S.blocksContaining T).biUnion f).card :=
          (Eq.symm hCardUnion)
    _ = Uset.card := by simp [hUnion_eq]
    _ = Nat.choose (v - s) (t - s) := hUset_card

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerSystem
