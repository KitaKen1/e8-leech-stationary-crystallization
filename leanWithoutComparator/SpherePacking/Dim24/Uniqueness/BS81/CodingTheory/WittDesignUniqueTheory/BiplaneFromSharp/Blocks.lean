-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.BiplaneParams
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneFromSharp.Lifts
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.WordFinset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Preimage
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.IntervalCases

/-!
# A biplane from pinned lifts

This file corresponds to Definition `biplane_blocks` and Theorem `biplane_from_code` in
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.

## Main definitions
* `BiplaneFromSharp.K`
* `BiplaneFromSharp.B`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneFromSharp

noncomputable section

open scoped symmDiff
open GolayBounds
open GolayUniquenessSteps.CodeFromOctadsAux
open GolayUniquenessSteps.CodeFromOctads
open PunctureEven

local notation "Word" => BinWord 24

/--
Auxiliary set `K u p v` used in the biplane construction: the part of `support v` inside
`support u \\ {p}`.
-/
@[expose] public def K (u : Word) (p : Fin 24) (v : Word) : Finset (Fin 24) :=
  (support v) ∩ (support u).erase p

/-- The candidate biplane block associated to `u`, a pinned coordinate `p`, and a word `v`. -/
@[expose] public def B (u : Word) (p : Fin 24) (v : Word) : Finset (Fin 24) :=
  (support u).erase p \ K u p v

lemma mem_K_iff {u v : Word} {p x : Fin 24} :
    x ∈ K u p v ↔ x ∈ support v ∧ x ∈ support u ∧ x ≠ p := by
  simp [K, and_assoc, and_comm]

attribute [grind =] mem_K_iff

lemma K_eq_support_inter_of_not_mem_support {u v : Word} {p : Fin 24} (hpv : p ∉ support v) :
    K u p v = support v ∩ support u := by
  ext x
  grind (splits := 2) [K]

attribute [grind =] K_eq_support_inter_of_not_mem_support

/-- Membership characterization for `B u p v` in terms of supports. -/
public lemma mem_B_iff {u v : Word} {p x : Fin 24} :
    x ∈ B u p v ↔ x ∈ support u ∧ x ≠ p ∧ x ∉ support v := by
  simp [B, K, and_assoc, and_left_comm]

attribute [grind =] mem_B_iff

attribute [grind =] card_symmDiff_eq_card_add_card_sub_two_mul_card_inter

lemma eraseCoords_eq_evenBasisWord_iff_support_outside
    {u v : Word} {t0 t1 : Fin 24} (hverase : eraseCoords (support u) v = evenBasisWord t0 t1) :
    (support v) \ (support u) = ({t0, t1} : Finset (Fin 24)) := by
  have hsupp :
      support (eraseCoords (support u) v) = (support v) \ (support u) := by
    simpa using! (PunctureEven.support_eraseCoords (S := support u) (w := v))
  have hsupp' : support (eraseCoords (support u) v) = ({t0, t1} : Finset (Fin 24)) := by
    simpa [evenBasisWord, support_wordOfFinset] using! congrArg support hverase
  exact (by simpa [hsupp] using! hsupp')

lemma nonzero_of_eraseCoords_eq_evenBasisWord
    {u v : Word} {t0 t1 : Fin 24} (ht0 : t0 ∉ support u)
    (hverase : eraseCoords (support u) v = evenBasisWord t0 t1) :
    v ≠ 0 := by
  intro hv0
  have ht0o : eraseCoords (support u) v t0 = 1 := by
    have : t0 ∈ ({t0, t1} : Finset (Fin 24)) := by simp
    simp [hverase, evenBasisWord, wordOfFinset, this]
  have ht0z : eraseCoords (support u) v t0 = 0 := by simp [hv0, eraseCoords, ht0]
  rw [ht0z] at ht0o
  exact (zero_ne_one (α := ZMod 2)) ht0o

lemma weight_eq_two_add_card_K
    {u v : Word} {p : Fin 24} {t0 t1 : Fin 24}
    (hvp0 : v p = 0) (hne : t0 ≠ t1)
    (hverase : eraseCoords (support u) v = evenBasisWord t0 t1) :
    weight v = 2 + (K u p v).card := by
  set S : Finset (Fin 24) := support u
  have hpv : p ∉ support v := (GolayBounds.not_mem_support (w := v) p).2 hvp0
  have hK : K u p v = support v ∩ S := by
    simpa [S] using! (K_eq_support_inter_of_not_mem_support (u := u) (v := v) (p := p) hpv)
  have hout : ((support v) \ S).card = 2 := by
    have hsupp : (support v) \ S = ({t0, t1} : Finset (Fin 24)) :=
      eraseCoords_eq_evenBasisWord_iff_support_outside (u := u) (v := v) (t0 := t0) (t1 := t1)
        hverase
    simpa [hsupp] using! (Finset.card_pair hne)
  have hsplit :
      (support v).card = ((support v) \ S).card + (support v ∩ S).card :=
    (Finset.card_sdiff_add_card_inter (support v) S).symm
  calc
    weight v = (support v).card := by simp [GolayBounds.weight_eq_card_support]
    _ = ((support v) \ S).card + (support v ∩ S).card := hsplit
    _ = 2 + (K u p v).card := by simp [hout, hK]

lemma symmDiff_pair_pair_left {α : Type} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (({a, b} : Finset α) ∆ ({a, c} : Finset α)) = ({b, c} : Finset α) := by
  ext x
  grind (splits := 3) only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]

attribute [grind =] symmDiff_pair_pair_left

lemma evenBasisWord_add_evenBasisWord
    (t0 t1 t2 : Fin 24) (ht01 : t0 ≠ t1) (ht02 : t0 ≠ t2) (ht12 : t1 ≠ t2) :
    evenBasisWord t0 t1 + evenBasisWord t0 t2 = evenBasisWord t1 t2 := by
  have hsymm :
      (({t0, t1} : Finset (Fin 24)) ∆ ({t0, t2} : Finset (Fin 24))) =
        ({t1, t2} : Finset (Fin 24)) :=
    symmDiff_pair_pair_left (a := t0) (b := t1) (c := t2) ht01 ht02 ht12
  funext x
  simpa [evenBasisWord, Pi.add_apply, hsymm] using!
    congrArg (fun f => f x)
      (GolayUniquenessSteps.CodeFromOctads.wordOfFinset_add (n := 24)
        ({t0, t1} : Finset (Fin 24)) ({t0, t2} : Finset (Fin 24)))

attribute [grind =] evenBasisWord_add_evenBasisWord

/--
For a sharp Golay input, the sets `K u p (v i)` obtained from pinned lifts have cardinality `6`.
-/
public theorem K_card_eq_six_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C)
    {u : Word} (huC : u ∈ C) (hwt : weight u = 12)
    {p : Fin 24} (hp : p ∈ support u)
    {t0 : Fin 24} {t : Fin 11 → Fin 24}
    (ht0 : t0 ∉ support u) (hne : ∀ i, t0 ≠ t i)
    {v : Fin 11 → Word}
    (hvC : ∀ i, v i ∈ C) (hvp0 : ∀ i, v i p = 0)
    (hverase : ∀ i, eraseCoords (support u) (v i) = evenBasisFamily t0 t i) :
    ∀ i, (K u p (v i)).card = 6 := by
  intro i
  have hne' : t0 ≠ t i := hne i
  have hv0 : v i ≠ 0 :=
    nonzero_of_eraseCoords_eq_evenBasisWord (u := u) (v := v i) (t0 := t0) (t1 := t i)
      ht0 (by simpa [evenBasisFamily, evenBasisWord] using! hverase i)
  have hwtv : weight (v i) = 2 + (K u p (v i)).card :=
    weight_eq_two_add_card_K (u := u) (v := v i) (p := p) (t0 := t0) (t1 := t i)
      (hvp0 i) hne' (by simpa [evenBasisFamily, evenBasisWord] using! hverase i)
  have hmin : 8 ≤ weight (v i) :=
    PunctureEven.weight_ge_minDist_of_mem (C := C) hC.minDist_ge hC.linear.1 (hvC i) hv0
  have hK_ge6 : 6 ≤ (K u p (v i)).card := by
    have : 8 ≤ 2 + (K u p (v i)).card := by simpa [hwtv] using! hmin
    omega
  have hK_le11 : (K u p (v i)).card ≤ 11 := by
    have hScard : (support u).card = 12 := by
      simpa [GolayBounds.weight_eq_card_support] using! hwt
    have hUcard : ((support u).erase p).card = 11 := by
      simpa [hScard] using! (Finset.card_erase_of_mem hp)
    have hsub : K u p (v i) ⊆ (support u).erase p := by
      intro x hx
      exact (Finset.mem_inter.1 hx).2
    exact le_trans (Finset.card_le_card hsub) (by simp [hUcard])
  have hdiv4 : 4 ∣ weight (v i) := hC.doublyEven (hvC i)
  have hdiv4' : 4 ∣ 2 + (K u p (v i)).card := by simpa [hwtv] using! hdiv4
  rcases hdiv4' with ⟨m, hm⟩
  have hm_ge2 : 2 ≤ m := by
    have h8 : 8 ≤ 2 + (K u p (v i)).card := by simpa [hwtv] using! hmin
    have : 8 ≤ 4 * m := by simpa [hm] using! h8
    have : 4 * 2 ≤ 4 * m := by simpa [Nat.mul_assoc] using! this
    exact Nat.le_of_mul_le_mul_left this (by decide : 0 < 4)
  have hm_le3 : m ≤ 3 := by
    have hk_le13 : 2 + (K u p (v i)).card ≤ 13 := by omega
    have h4m_le13 : 4 * m ≤ 13 := by simpa [hm] using! hk_le13
    have hm_lt4 : m < 4 := by
      have : 4 * m < 16 := lt_of_le_of_lt h4m_le13 (by decide : 13 < 16)
      have : 4 * m < 4 * 4 := by simpa using! this
      exact (Nat.mul_lt_mul_left (by decide : 0 < 4)).1 this
    exact Nat.lt_succ_iff.mp hm_lt4
  have hK_cases : (K u p (v i)).card = 6 ∨ (K u p (v i)).card = 10 := by
    have hk : (K u p (v i)).card = 4 * m - 2 :=
      Nat.eq_sub_of_add_eq' hm
    have hm_lt4 : m < 4 := lt_of_le_of_lt hm_le3 (by decide : 3 < 4)
    interval_cases m using hm_ge2, hm_lt4 <;> simp [hk]
  rcases hK_cases with hK6 | hK10
  · exact hK6
  · -- exclude `10` by looking at `u + v i` of weight `4`
    have hsum_mem : u + v i ∈ C := hC.linear.2 u (v i) huC (hvC i)
    have hsum0 : u + v i ≠ 0 := by
      intro h0
      have hut0 : u t0 = 0 := (GolayBounds.not_mem_support (w := u) t0).1 ht0
      have hvt0 : (v i) t0 = 1 := by
        have hErase : eraseCoords (support u) (v i) t0 = 1 := by
          have ht0_in : t0 ∈ ({t0, t i} : Finset (Fin 24)) := by simp
          simpa [evenBasisFamily, evenBasisWord, wordOfFinset, ht0_in] using!
            congrArg (fun w => w t0) (hverase i)
        -- since `t0 ∉ support u`, erasing leaves the coordinate unchanged
        simpa [eraseCoords, ht0] using! hErase
      grind only [= binWord_add_eq_zero_iff_eq]
    have hmin_sum : 8 ≤ weight (u + v i) :=
      PunctureEven.weight_ge_minDist_of_mem (C := C) hC.minDist_ge hC.linear.1 hsum_mem hsum0
    have hw4 : weight (u + v i) = 4 := by
      -- `support (u+v) = support u ∆ support v`
      have hsupp : support (u + v i) = support u ∆ support (v i) := by
        simpa using! (GolayBounds.support_add_eq_symmDiff (w₁ := u) (w₂ := v i))
      -- `|(supp v) \\ (supp u)| = 2` and `|(supp v) ∩ (supp u)| = 10`.
      have hout : ((support (v i)) \ (support u)).card = 2 := by
        have : (support (v i)) \ (support u) = ({t0, t i} : Finset (Fin 24)) :=
          eraseCoords_eq_evenBasisWord_iff_support_outside (u := u) (v := v i) (t0 := t0)
            (t1 := t i) (by simpa [evenBasisFamily, evenBasisWord] using! hverase i)
        simpa [this] using! (Finset.card_pair (hne i))
      have hin : (support (v i) ∩ support u).card = 10 := by
        -- since `v i p = 0`, `K = support(v) ∩ support(u)`
        have hpv : p ∉ support (v i) := (GolayBounds.not_mem_support (w := v i) p).2 (hvp0 i)
        have hK : K u p (v i) = support (v i) ∩ support u := by
          exact K_eq_support_inter_of_not_mem_support (u := u) (v := v i) (p := p) hpv
        simpa [hK] using! hK10
      have hScard : (support u).card = 12 := by
        simpa [GolayBounds.weight_eq_card_support] using! hwt
      have hsleft : ((support u) \ support (v i)).card = 2 := by
        -- `card_sdiff = card - card(inter)`
        calc
          ((support u) \ support (v i)).card
              = (support u).card - (support (v i) ∩ support u).card := by
                simp [Finset.card_sdiff, Finset.inter_comm]
          _ = 2 := by
                simp [hScard, hin]
      have hdisj : Disjoint ((support u) \ support (v i)) ((support (v i)) \ (support u)) := by
        exact disjoint_sdiff_sdiff
      have hcard : (support u ∆ support (v i)).card = 4 := by
        -- symmDiff is union of disjoint sdiffs
        have : (support u ∆ support (v i)).card =
            ((support u) \ support (v i)).card + ((support (v i)) \ (support u)).card := by
          -- `(s ∆ t)` is definitionally `s \\ t ∪ t \\ s`
          simpa using! (Finset.card_union_of_disjoint hdisj :
            (((support u) \ support (v i)) ∪ ((support (v i)) \ (support u))).card =
              ((support u) \ support (v i)).card + ((support (v i)) \ (support u)).card)
        omega
      simp [GolayBounds.weight_eq_card_support, hsupp, hcard]
    have : (8 : ℕ) ≤ 4 := by
      exact le_of_le_of_eq hmin_sum hw4
    exfalso
    exact (by decide : ¬ ((8 : ℕ) ≤ 4)) this

/--
For a sharp Golay input, distinct pinned lifts produce sets `K u p (v i)` whose pairwise
intersections have cardinality `3`.
-/
public theorem K_inter_card_eq_three_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C)
    {u : Word} (huC : u ∈ C) (hwt : weight u = 12)
    {p : Fin 24} (hp : p ∈ support u)
    {t0 : Fin 24} {t : Fin 11 → Fin 24}
    (ht0 : t0 ∉ support u) (ht : ∀ i, t i ∉ support u) (htinj : Function.Injective t)
    (hne : ∀ i, t0 ≠ t i)
    {v : Fin 11 → Word}
    (hvC : ∀ i, v i ∈ C) (hvp0 : ∀ i, v i p = 0)
    (hverase : ∀ i, eraseCoords (support u) (v i) = evenBasisFamily t0 t i) :
    ∀ i j, i ≠ j → (K u p (v i) ∩ K u p (v j)).card = 3 := by
  intro i j hij
  have htij : t i ≠ t j := fun h => hij (htinj h)
  have hKi : (K u p (v i)).card = 6 :=
    K_card_eq_six_of_sharp (C := C) hC huC hwt hp ht0 hne hvC hvp0 hverase i
  have hKj : (K u p (v j)).card = 6 :=
    K_card_eq_six_of_sharp (C := C) hC huC hwt hp ht0 hne hvC hvp0 hverase j
  -- Notation for the intersection size `s = |Kᵢ ∩ Kⱼ|`.
  set s : ℕ := (K u p (v i) ∩ K u p (v j)).card
  have hcard_symm : ((K u p (v i)) ∆ (K u p (v j))).card = 12 - 2 * s := by
    have := card_symmDiff_eq_card_add_card_sub_two_mul_card_inter
      (s := K u p (v i)) (t := K u p (v j))
    simpa [hKi, hKj, s] using! this
  have hs_le6 : s ≤ 6 := by
    have hsub : (K u p (v i) ∩ K u p (v j)) ⊆ K u p (v i) := Finset.inter_subset_left
    have : (K u p (v i) ∩ K u p (v j)).card ≤ (K u p (v i)).card :=
      Finset.card_le_card hsub
    simpa [s, hKi] using! this
  have hErase :
      eraseCoords (support u) (v i + v j) = evenBasisWord (t i) (t j) := by
    have hEi : eraseCoords (support u) (v i) = evenBasisWord t0 (t i) := by
      simpa [evenBasisFamily] using! hverase i
    have hEj : eraseCoords (support u) (v j) = evenBasisWord t0 (t j) := by
      simpa [evenBasisFamily] using! hverase j
    calc
      eraseCoords (support u) (v i + v j)
          = eraseCoords (support u) (v i) + eraseCoords (support u) (v j) := by
              simp [eraseCoords_add]
      _ = evenBasisWord t0 (t i) + evenBasisWord t0 (t j) := by simp [hEi, hEj]
      _ = evenBasisWord (t i) (t j) := by
        simpa using!
          evenBasisWord_add_evenBasisWord (t0 := t0) (t1 := t i) (t2 := t j) (hne i) (hne j) htij
  have hout : ((support (v i + v j)) \ support u).card = 2 := by
    have hsupp :
        (support (v i + v j)) \ support u = ({t i, t j} : Finset (Fin 24)) :=
      eraseCoords_eq_evenBasisWord_iff_support_outside (u := u) (v := v i + v j) (t0 := t i)
        (t1 := t j) hErase
    simpa [hsupp] using! (Finset.card_pair htij)
  have hin_set :
      support (v i + v j) ∩ support u = (K u p (v i)) ∆ (K u p (v j)) := by
    ext y
    have hsupp_add : support (v i + v j) = support (v i) ∆ support (v j) := by
      simpa using! (GolayBounds.support_add_eq_symmDiff (w₁ := v i) (w₂ := v j))
    by_cases hyP : y = p
    · subst hyP
      have hy_sum : (v i + v j) y = 0 := by simp [Pi.add_apply, hvp0]
      have hy_not : y ∉ support (v i + v j) :=
        (GolayBounds.not_mem_support (w := v i + v j) y).2 hy_sum
      simp [Finset.mem_inter, hy_not, mem_K_iff, Finset.mem_symmDiff]
    · have hyP' : y ≠ p := hyP
      by_cases hyU : y ∈ support u <;>
        grind (splits := 0) only [Finset.mem_inter, Finset.mem_symmDiff, mem_K_iff]
  have hin : (support (v i + v j) ∩ support u).card = ((K u p (v i)) ∆ (K u p (v j))).card := by
    simp [hin_set]
  have hwt_vivj : weight (v i + v j) = 14 - 2 * s := by
    have hsplit :
        (support (v i + v j)).card =
          ((support (v i + v j)) \ support u).card + (support (v i + v j) ∩ support u).card :=
      (Finset.card_sdiff_add_card_inter (support (v i + v j)) (support u)).symm
    have hcard_support :
        (support (v i + v j)).card = 2 + ((K u p (v i)) ∆ (K u p (v j))).card := by
      -- use the split and the computed `outside` / `inside` cards
      calc
        (support (v i + v j)).card =
            ((support (v i + v j)) \ support u).card +
              (support (v i + v j) ∩ support u).card := hsplit
        _ = 2 + ((K u p (v i)) ∆ (K u p (v j))).card := by simp [hout, hin]
    have hcard_symm' : 2 + ((K u p (v i)) ∆ (K u p (v j))).card = 14 - 2 * s := by
      have h2s_le12 : 2 * s ≤ 12 := by
        omega
      calc
        2 + ((K u p (v i)) ∆ (K u p (v j))).card
            = 2 + (12 - 2 * s) := by simp [hcard_symm]
        _ = (2 + 12) - 2 * s := by
            symm
            exact Nat.add_sub_assoc (n := 2) h2s_le12
        _ = 14 - 2 * s := by simp
    -- translate back to `weight`
    simp [GolayBounds.weight_eq_card_support, hcard_support, hcard_symm']
  have hmin_vivj : 8 ≤ weight (v i + v j) := by
    have hmem : v i + v j ∈ C := hC.linear.2 (v i) (v j) (hvC i) (hvC j)
    have hneq : v i + v j ≠ 0 :=
      nonzero_of_eraseCoords_eq_evenBasisWord (ht i) hErase
    exact
      PunctureEven.weight_ge_minDist_of_mem (C := C) hC.minDist_ge hC.linear.1 hmem hneq
  have hs_le : s ≤ 3 := by
    have : 8 ≤ 14 - 2 * s := by simpa [hwt_vivj] using! hmin_vivj
    omega
  have hmin_uivj : 8 ≤ weight (u + v i + v j) := by
    have hmem : u + v i + v j ∈ C := by
      -- close under addition twice
      have h1 : u + v i ∈ C := hC.linear.2 u (v i) huC (hvC i)
      simpa [add_assoc] using! hC.linear.2 (u + v i) (v j) h1 (hvC j)
    have hneq : u + v i + v j ≠ 0 := by
      -- it has a `1` at `t i`
      intro h0
      have hsumti : u (t i) + (v i) (t i) + (v j) (t i) = 0 := by
        have := congrArg (fun w => w (t i)) h0
        simpa [Pi.add_apply, add_assoc] using! this
      have htis : t i ∉ support u := ht i
      have hut : u (t i) = 0 := (GolayBounds.not_mem_support (w := u) (t i)).1 htis
      have hvi : (v i) (t i) = 1 := by
        have hErasei : eraseCoords (support u) (v i) (t i) = 1 := by
          have : t i ∈ ({t0, t i} : Finset (Fin 24)) := by simp
          simpa [evenBasisFamily, evenBasisWord, wordOfFinset, this] using!
            congrArg (fun w => w (t i)) (hverase i)
        simpa [eraseCoords, htis] using! hErasei
      have hvj : (v j) (t i) = 0 := by
        have hErasej : eraseCoords (support u) (v j) (t i) = 0 := by
          have : t i ∉ ({t0, t j} : Finset (Fin 24)) := by
            grind only [Finset.mem_insert, Finset.mem_singleton]
          simpa [evenBasisFamily, evenBasisWord, wordOfFinset, this] using!
            congrArg (fun w => w (t i)) (hverase j)
        simpa [eraseCoords, htis] using! hErasej
      have : (1 : ZMod 2) = 0 := by
        have h := hsumti
        simp [hut, hvi, hvj] at h
      exact one_ne_zero this
    exact
      PunctureEven.weight_ge_minDist_of_mem (C := C) hC.minDist_ge hC.linear.1 hmem hneq
  have hs_ge : 3 ≤ s := by
    have hScard : (support u).card = 12 := by
      simpa [GolayBounds.weight_eq_card_support] using! hwt
    have hinter :
        (support u ∩ support (v i + v j)).card = 12 - 2 * s := by
      -- Use the computed intersection with `support u`.
      have := congrArg Finset.card hin_set
      simpa [Finset.inter_comm, hcard_symm] using! this
    have hcard_sum : (support (v i + v j)).card = 14 - 2 * s := by
      simpa [GolayBounds.weight_eq_card_support] using! hwt_vivj
    have hcard_uivj :
        (support (u + (v i + v j))).card = 2 + 2 * s := by
      have hsymm := card_symmDiff_eq_card_add_card_sub_two_mul_card_inter
        (s := support u) (t := support (v i + v j))
      grind only [=_ support_add_eq_symmDiff]
    have hwt_uivj : weight (u + v i + v j) = 2 + 2 * s := by
      -- `u + v i + v j = u + (v i + v j)`
      have : weight (u + (v i + v j)) = 2 + 2 * s := by
        simp [GolayBounds.weight_eq_card_support, hcard_uivj]
      simpa [add_assoc] using! this
    have hmin_uivj' : 8 ≤ weight (u + (v i + v j)) := by
      simpa [add_assoc] using! hmin_uivj
    have hwt_uivj' : weight (u + (v i + v j)) = 2 + 2 * s := by
      simpa [add_assoc] using! hwt_uivj
    have : 8 ≤ 2 + 2 * s := by simpa [hwt_uivj'] using! hmin_uivj'
    omega
  exact Eq.symm (Nat.le_antisymm hs_ge hs_le)

end

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneFromSharp

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
