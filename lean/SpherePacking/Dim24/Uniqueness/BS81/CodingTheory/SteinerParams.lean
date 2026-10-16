-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerDefs
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
-- `grind` is a core Lean tactic; no Mathlib import is needed.

/-!
# Parameter counting for Steiner systems

This file provides small, reusable counting lemmas used in the coding-theory part of the BS81
formalization; it only uses the minimal `SteinerSystem` structure from `SteinerDefs.lean`.

Main tool: for `S : SteinerSystem v k t` and `T` of size `s ≤ t`, #blocks containing `T` is
`choose (v - s) (t - s) / choose (k - s) (t - s)`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open scoped BigOperators

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- Count `m`-subsets of a finset `B` that contain a fixed subset `T` of size `s`. -/
public lemma card_powersetCard_filter_superset (B T : Finset α) {s m : ℕ}
    (hTB : T ⊆ B) (hT : T.card = s) (hsm : s ≤ m) :
    ((B.powersetCard m).filter (fun U => T ⊆ U)).card = Nat.choose (B.card - s) (m - s) := by
  let comp : Finset α := B \ T
  have hcomp : comp.card = B.card - s := by
    have : comp.card = B.card - T.card := by
      simpa [comp, Finset.inter_eq_left.2 hTB] using! (Finset.card_sdiff (s := T) (t := B))
    simpa [hT] using! this
  -- Equivalence between filtered `m`-subsets and `(m-s)`-subsets of `B \\ T`.
  have hEquiv :
      {U // U ∈ (B.powersetCard m).filter (fun U => T ⊆ U)} ≃
        {R // R ∈ comp.powersetCard (m - s)} := by
    refine
      { toFun := fun U => ⟨U.1 \ T, ?_⟩
        invFun := fun R => ⟨T ∪ R.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hU : U.1 ∈ (B.powersetCard m).filter (fun U => T ⊆ U) := U.2
      have hUmem : U.1 ∈ B.powersetCard m := (Finset.mem_filter.1 hU).1
      have hUsubT : T ⊆ U.1 := (Finset.mem_filter.1 hU).2
      have hUsubB : U.1 ⊆ B := (Finset.mem_powersetCard.1 hUmem).1
      have hUcard : U.1.card = m := (Finset.mem_powersetCard.1 hUmem).2
      have hUT : (U.1 \ T).card = m - s := by
        have : (U.1 \ T).card = U.1.card - T.card := by
          simpa [Finset.inter_eq_left.2 hUsubT] using! (Finset.card_sdiff (s := T) (t := U.1))
        simpa [hUcard, hT] using! this
      have hsub : U.1 \ T ⊆ comp := by
        intro x hx
        have hxU : x ∈ U.1 := (Finset.mem_sdiff.1 hx).1
        have hxT : x ∉ T := (Finset.mem_sdiff.1 hx).2
        exact Finset.mem_sdiff.2 ⟨hUsubB hxU, hxT⟩
      exact Finset.mem_powersetCard.2 ⟨hsub, hUT⟩
    · have hR : R.1 ∈ comp.powersetCard (m - s) := R.2
      have hRsub : R.1 ⊆ comp := (Finset.mem_powersetCard.1 hR).1
      have hRcard : R.1.card = m - s := (Finset.mem_powersetCard.1 hR).2
      have hdisj : Disjoint T R.1 := by
        refine Finset.disjoint_left.2 ?_
        intro x hxT hxR
        have hxcomp : x ∈ comp := hRsub hxR
        exact (Finset.mem_sdiff.1 hxcomp).2 hxT
      have hcard : (T ∪ R.1).card = m := by
        have hsum : T.card + R.1.card = m := by
          calc
            T.card + R.1.card = s + (m - s) := by simp [hT, hRcard]
            _ = m := Nat.add_sub_of_le hsm
        have hcard' : (T ∪ R.1).card = T.card + R.1.card :=
          (Finset.card_union_of_disjoint hdisj)
        exact hcard'.trans hsum
      have hsubB : T ∪ R.1 ⊆ B := by
        intro x hx
        rcases Finset.mem_union.1 hx with hxT | hxR
        · exact hTB hxT
        · exact (Finset.mem_sdiff.1 (hRsub hxR)).1
      have hmem : T ∪ R.1 ∈ B.powersetCard m := Finset.mem_powersetCard.2 ⟨hsubB, hcard⟩
      have hsubT : T ⊆ T ∪ R.1 := by intro x hx; simp [hx]
      exact Finset.mem_filter.2 ⟨hmem, hsubT⟩
    · intro U
      apply Subtype.ext
      ext x
      have hU : U.1 ∈ (B.powersetCard m).filter (fun U => T ⊆ U) := U.2
      have hUsubT : T ⊆ U.1 := (Finset.mem_filter.1 hU).2
      have hxU : x ∈ T → x ∈ U.1 := fun hx => hUsubT hx
      grind (splits := 1) only [Finset.mem_union, Finset.mem_sdiff]
    · intro R
      apply Subtype.ext
      ext x
      have hxnotT : x ∈ R.1 → x ∉ T := by
        intro hxR
        have hxcomp : x ∈ comp := (Finset.mem_powersetCard.1 R.2).1 hxR
        exact (Finset.mem_sdiff.1 hxcomp).2
      grind (splits := 1) only [Finset.mem_union, Finset.mem_sdiff]
  have hLeft :
      ((B.powersetCard m).filter (fun U => T ⊆ U)).card =
        Fintype.card {U // U ∈ (B.powersetCard m).filter (fun U => T ⊆ U)} := by
    simp
  have hMid :
      Fintype.card {U // U ∈ (B.powersetCard m).filter (fun U => T ⊆ U)} =
        Fintype.card {R // R ∈ comp.powersetCard (m - s)} := by
    simpa using! (Fintype.card_congr hEquiv)
  have hRight :
      Fintype.card {R // R ∈ comp.powersetCard (m - s)} = (comp.powersetCard (m - s)).card := by
    simp [-Finset.mem_powersetCard]
  have hPow : (comp.powersetCard (m - s)).card = Nat.choose (B.card - s) (m - s) := by
    simp [Finset.card_powersetCard, hcomp]
  calc
    ((B.powersetCard m).filter (fun U => T ⊆ U)).card
        = Fintype.card {U // U ∈ (B.powersetCard m).filter (fun U => T ⊆ U)} := hLeft
    _   = Fintype.card {R // R ∈ comp.powersetCard (m - s)} := hMid
    _   = (comp.powersetCard (m - s)).card := hRight
    _   = Nat.choose (B.card - s) (m - s) := hPow

end Finset

namespace SteinerSystem

variable {v k t : ℕ}

/-- The finset of all blocks of a Steiner system. -/
public def blocksFinset (S : SteinerSystem v k t) : Finset (Finset (Fin v)) :=
  (Set.toFinite S.blocks).toFinset

/-- Membership in `blocksFinset` is membership in `S.blocks`. -/
@[simp] public lemma mem_blocksFinset (S : SteinerSystem v k t) (B : Finset (Fin v)) :
    B ∈ S.blocksFinset ↔ B ∈ S.blocks := by
  simp [blocksFinset]

/-- Cardinality of `blocksFinset` agrees with `Set.ncard` of `S.blocks`. -/
public lemma card_blocksFinset_eq_ncard_blocks (S : SteinerSystem v k t) :
    S.blocksFinset.card = S.blocks.ncard := by
  simpa [blocksFinset] using!
    (S.blocks.ncard_eq_toFinset_card (Set.toFinite S.blocks)).symm

/-- The set of `m`-subsets of `Fin v`, viewed as a finset. -/
public def mSubsets (v : ℕ) (m : ℕ) : Finset (Finset (Fin v)) :=
  (Finset.univ : Finset (Fin v)).powersetCard m

/-- Membership in `mSubsets v m` is the cardinality condition `card = m`. -/
@[simp] public lemma mem_mSubsets {v m : ℕ} {T : Finset (Fin v)} :
    T ∈ mSubsets v m ↔ T.card = m := by
  simp [mSubsets]

/-- `mSubsets v m` has cardinality `Nat.choose v m`. -/
@[simp] public lemma card_mSubsets (v m : ℕ) :
    (mSubsets v m).card = Nat.choose v m := by
  simp [mSubsets, Finset.card_powersetCard]

/-- The finset of `m`-subsets containing a fixed subset `T` of size `s`. -/
public def mSubsetsContaining {v : ℕ} (T : Finset (Fin v)) (m : ℕ) :
    Finset (Finset (Fin v)) :=
  (mSubsets v m).filter fun U => T ⊆ U

/-- Membership in `mSubsetsContaining T m` is `card = m` together with `T ⊆ U`. -/
@[simp] public lemma mem_mSubsetsContaining {v m : ℕ} {T U : Finset (Fin v)} :
    U ∈ mSubsetsContaining T m ↔ U.card = m ∧ T ⊆ U := by
  simp [mSubsetsContaining, mSubsets]

/-- Count `m`-subsets containing `T` by choosing from the complement. -/
public lemma card_mSubsetsContaining_of_card {v : ℕ} {T : Finset (Fin v)} {s m : ℕ}
    (hT : T.card = s) (hsm : s ≤ m) :
    (mSubsetsContaining T m).card = Nat.choose (v - s) (m - s) := by
  simpa [mSubsetsContaining, mSubsets] using!
    (Finset.card_powersetCard_filter_superset
      (B := (Finset.univ : Finset (Fin v))) (T := T) (s := s) (m := m)
      (Finset.subset_univ _) hT hsm)

end SteinerSystem
end
end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
