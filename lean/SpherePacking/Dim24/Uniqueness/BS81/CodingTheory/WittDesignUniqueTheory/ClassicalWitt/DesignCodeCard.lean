-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.DotSupportLite
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.DotBilin
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittParams
public import
 SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.ClassicalWitt.CodeFromDes
public import
 SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.ClassicalWitt.BlockInter
public import
 SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.WordFinset
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Cardinality of the block-span code

Let `S : SteinerSystem 24 8 5`. We study the binary linear code `codeFromSteinerSystem S` spanned
by the indicator vectors of blocks. The main result `codeFromSteinerSystem_ncard_eq_two_pow_12`
shows this code has cardinality `2 ^ 12`. The argument uses self-orthogonality with respect to the
dot product and a finrank computation.

This supplies the `[24,12]` dimension input needed in the classical Witt design uniqueness proof.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.ClassicalWitt

noncomputable section

open scoped BigOperators symmDiff

open GolayBounds
open CodeFromOctadsAux

local notation "Word" => BinWord 24

def Bdot : LinearMap.BilinForm (ZMod 2) Word :=
  DotBilin.dotBilinForm (n := 24)

/-- A block word lies in the submodule spanned by all block words. -/
public lemma wordOfFinset_mem_blockSubmodule_of_mem_blocks
    (S : SteinerSystem 24 8 5) {B : Finset (Fin 24)} (hB : B ∈ S.blocks) :
    wordOfFinset (n := 24) B ∈ blockSubmodule S.blocks := by
  refine Submodule.subset_span ?_
  exact ⟨B, hB, rfl⟩

lemma dot_wordOfFinset_eq_zero_of_blocks
    (S : SteinerSystem 24 8 5) {B B' : Finset (Fin 24)}
    (hB : B ∈ S.blocks) (hB' : B' ∈ S.blocks) :
    dot (n := 24) (wordOfFinset (n := 24) B) (wordOfFinset (n := 24) B') = 0 := by
  by_cases hEq : B = B'
  · subst hEq
    have hcard : B.card = 8 := S.block_card B hB
    have :
        Even (support (wordOfFinset (n := 24) B) ∩ support (wordOfFinset (n := 24) B)).card := by
      simpa [support_wordOfFinset, Finset.inter_self, hcard] using! (by decide : Even (8 : ℕ))
    exact (DotSupportLite.dot_eq_zero_iff_even_card_support_inter
      (w₁ := wordOfFinset (n := 24) B) (w₂ := wordOfFinset (n := 24) B)).2 this
  · have hEven : Even (B ∩ B').card :=
      BlockIntersections.even_inter_card_of_ne (S := S) (B := B) (B' := B') hB hB' hEq
    have :
        Even (support (wordOfFinset (n := 24) B) ∩ support (wordOfFinset (n := 24) B')).card := by
      simpa [support_wordOfFinset] using! hEven
    exact (DotSupportLite.dot_eq_zero_iff_even_card_support_inter
      (w₁ := wordOfFinset (n := 24) B) (w₂ := wordOfFinset (n := 24) B')).2 this

/-- Any two words in `blockSubmodule S.blocks` are orthogonal for the dot product. -/
public lemma dot_eq_zero_of_mem_blockSubmodule
    (S : SteinerSystem 24 8 5) {x y : Word}
    (hx : x ∈ blockSubmodule S.blocks) (hy : y ∈ blockSubmodule S.blocks) :
    dot (n := 24) x y = 0 := by
  -- Extend `dot_wordOfFinset_eq_zero_of_blocks` to the whole span by bilinearity.
  let s : Set Word := blockWordSet S.blocks
  change x ∈ Submodule.span (ZMod 2) s at hx
  change y ∈ Submodule.span (ZMod 2) s at hy
  refine
    (Submodule.span_induction₂ (R := ZMod 2) (s := s) (t := s)
      (p := fun x y _ _ => dot (n := 24) x y = 0)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy)
  · intro x y hx hy
    rcases hx with ⟨B, hB, rfl⟩
    rcases hy with ⟨B', hB', rfl⟩
    exact dot_wordOfFinset_eq_zero_of_blocks (S := S) (hB := hB) (hB' := hB')
  · intro y _
    simp [dot]
  · intro x _
    simp [dot]
  · intro x₁ x₂ y _ _ _ ih₁ ih₂
    calc
      dot (n := 24) (fun i => x₁ i + x₂ i) y
          = dot (n := 24) x₁ y + dot (n := 24) x₂ y := by
              simpa using! (dot_add_left (n := 24) x₁ x₂ y)
      _ = 0 := by simp [ih₁, ih₂]
  · intro x y₁ y₂ _ _ _ ih₁ ih₂
    calc
      dot (n := 24) x (fun i => y₁ i + y₂ i)
          = dot (n := 24) x y₁ + dot (n := 24) x y₂ := by
              simpa using! (dot_add_right (n := 24) x y₁ y₂)
      _ = 0 := by simp [ih₁, ih₂]
  · intro r x y _ _ ih
    calc
      dot (n := 24) (r • x) y = r * dot (n := 24) x y := by
        simpa using! (DotBilin.dot_smul_left (n := 24) r x y)
      _ = 0 := by simp [ih]
  · intro r x y _ _ ih
    calc
      dot (n := 24) x (r • y) = r * dot (n := 24) x y := by
        simpa using! (DotBilin.dot_smul_right (n := 24) r x y)
      _ = 0 := by simp [ih]

lemma blockSubmodule_le_orthogonal
    (S : SteinerSystem 24 8 5) :
    blockSubmodule S.blocks ≤ (Bdot).orthogonal (blockSubmodule S.blocks) := by
  intro x hx
  -- Membership in the right orthogonal complement is `∀ y ∈ W, Bdot y x = 0`.
  refine
    (LinearMap.BilinForm.mem_orthogonal_iff (B := Bdot) (N := blockSubmodule S.blocks) (m := x)).2
      ?_
  intro y hy
  have hxy : dot (n := 24) x y = 0 := dot_eq_zero_of_mem_blockSubmodule (S := S) hx hy
  -- use symmetry to flip arguments
  have hyx : dot (n := 24) y x = 0 := by simpa [DotBilin.dot_comm] using! hxy
  simpa [LinearMap.BilinForm.IsOrtho, DotBilin.dotBilinForm_apply] using! hyx

def OrthoBlocks (S : SteinerSystem 24 8 5) (w : Word) : Prop :=
  ∀ B : Finset (Fin 24), B ∈ S.blocks → dot (n := 24) (wordOfFinset (n := 24) B) w = 0

lemma orthoBlocks_of_mem_orthogonal
    (S : SteinerSystem 24 8 5) {w : Word}
    (hw : w ∈ (Bdot).orthogonal (blockSubmodule S.blocks)) :
    OrthoBlocks S w := by
  intro B hB
  have hgen : wordOfFinset (n := 24) B ∈ blockSubmodule S.blocks :=
    wordOfFinset_mem_blockSubmodule_of_mem_blocks (S := S) hB
  have hw' :=
    (LinearMap.BilinForm.mem_orthogonal_iff (B := Bdot) (N := blockSubmodule S.blocks) (m := w)).1
      hw
  have : LinearMap.BilinForm.IsOrtho Bdot (wordOfFinset (n := 24) B) w := hw' _ hgen
  simpa [LinearMap.BilinForm.IsOrtho, DotBilin.dotBilinForm_apply] using! this

/-- A `4`-set meets some block in exactly `3` points. -/
public lemma exists_block_inter_card_eq_three
    (S : SteinerSystem 24 8 5) {T : Finset (Fin 24)} (hT : T.card = 4) :
    ∃ B : Finset (Fin 24), B ∈ S.blocks ∧ (T ∩ B).card = 3 := by
  have hTne : T.Nonempty := by
    refine Finset.card_pos.1 ?_
    rw [hT]
    decide
  rcases hTne with ⟨a, haT⟩
  let U : Finset (Fin 24) := T.erase a
  have hUcard : U.card = 3 := by
    simpa [U, hT] using! (Finset.card_erase_of_mem haT)
  have hsub : S.blocksContaining T ⊆ S.blocksContaining U := by
    intro B hB
    have hB' : B ∈ S.blocks ∧ T ⊆ B := (SteinerSystem.mem_blocksContaining S).1 hB
    refine (SteinerSystem.mem_blocksContaining S).2 ?_
    refine ⟨hB'.1, ?_⟩
    intro x hxU
    have hxT : x ∈ T := (Finset.mem_erase.1 hxU).2
    exact hB'.2 hxT
  have hcardT : (S.blocksContaining T).card = 5 := by
    simpa using! WittParams.card_blocksContaining_four (S := S) T hT
  have hcardU : (S.blocksContaining U).card = 21 := by
    simpa [hUcard] using! WittParams.card_blocksContaining_three (S := S) U hUcard
  have hlt : (S.blocksContaining T).card < (S.blocksContaining U).card := by
    rw [hcardT, hcardU]
    decide
  rcases Finset.exists_mem_notMem_of_card_lt_card (s := S.blocksContaining T)
      (t := S.blocksContaining U) hlt with ⟨B, hBU, hBT⟩
  have hBmem : B ∈ S.blocks ∧ U ⊆ B := (SteinerSystem.mem_blocksContaining S).1 hBU
  have hnotT : ¬ T ⊆ B := by
    intro hTB
    exact hBT ((SteinerSystem.mem_blocksContaining S).2 ⟨hBmem.1, hTB⟩)
  have haB : a ∉ B := by
    intro haB
    have hTB : T ⊆ B := by
      intro x hxT
      by_cases hxa : x = a
      · simpa [hxa] using! haB
      · have : x ∈ U := Finset.mem_erase.2 ⟨hxa, hxT⟩
        exact hBmem.2 this
    exact hnotT hTB
  have hinter : T ∩ B = U := by
    ext x
    constructor
    · intro hx
      have hxT : x ∈ T := (Finset.mem_inter.1 hx).1
      have hxB : x ∈ B := (Finset.mem_inter.1 hx).2
      have hxa : x ≠ a := by
        intro hxa
        subst hxa
        exact haB hxB
      exact Finset.mem_erase.2 ⟨hxa, hxT⟩
    · intro hxU
      have hxT : x ∈ T := (Finset.mem_erase.1 hxU).2
      have hxB : x ∈ B := hBmem.2 hxU
      exact Finset.mem_inter.2 ⟨hxT, hxB⟩
  refine ⟨B, hBmem.1, ?_⟩
  simp [hinter, hUcard]

lemma exists_block_contains_left_not_right
    (S : SteinerSystem 24 8 5) {a b : Fin 24} (hab : a ≠ b) :
    ∃ B : Finset (Fin 24), B ∈ S.blocks ∧ a ∈ B ∧ b ∉ B := by
  let Ta : Finset (Fin 24) := {a}
  let Tab : Finset (Fin 24) := {a, b}
  have hsub : S.blocksContaining Tab ⊆ S.blocksContaining Ta := by
    intro B hB
    have hB' : B ∈ S.blocks ∧ Tab ⊆ B := (SteinerSystem.mem_blocksContaining S).1 hB
    refine (SteinerSystem.mem_blocksContaining S).2 ?_
    refine ⟨hB'.1, ?_⟩
    intro x hxTa
    have : x = a := by simpa [Ta] using! hxTa
    subst this
    exact hB'.2 (by simp [Tab])
  have hTa : Ta.card = 1 := by simp [Ta]
  have hTab : Tab.card = 2 := by simp [Tab, hab]
  have hcardTa : (S.blocksContaining Ta).card = 253 := by
    simpa [hTa] using! WittParams.card_blocksContaining_one (S := S) Ta hTa
  have hcardTab : (S.blocksContaining Tab).card = 77 := by
    simpa [hTab] using! WittParams.card_blocksContaining_two (S := S) Tab hTab
  have hlt : (S.blocksContaining Tab).card < (S.blocksContaining Ta).card := by
    rw [hcardTab, hcardTa]
    decide
  rcases Finset.exists_mem_notMem_of_card_lt_card (s := S.blocksContaining Tab)
      (t := S.blocksContaining Ta) hlt with ⟨B, hBmem, hBnot⟩
  have hB' : B ∈ S.blocks ∧ Ta ⊆ B := (SteinerSystem.mem_blocksContaining S).1 hBmem
  have haB : a ∈ B := hB'.2 (by simp [Ta])
  have hbB : b ∉ B := by
    intro hbB
    have hTabsub : Tab ⊆ B := by
      intro x hx
      rcases Finset.mem_insert.1 hx with hxa | hrest
      · subst hxa; exact haB
      rcases Finset.mem_singleton.1 hrest with hxb
      subst hxb; exact hbB
    have : B ∈ S.blocksContaining Tab := by
      exact (SteinerSystem.mem_blocksContaining S).2 ⟨hB'.1, hTabsub⟩
    exact hBnot this
  exact ⟨B, hB'.1, haB, hbB⟩

lemma orthoBlocks_add_blockWord
    (S : SteinerSystem 24 8 5) {w : Word} (hw : OrthoBlocks S w)
    {B : Finset (Fin 24)} (hB : B ∈ S.blocks) :
    OrthoBlocks S (fun i => w i + wordOfFinset (n := 24) B i) := by
  intro B' hB'
  calc
    dot (n := 24) (wordOfFinset (n := 24) B') (fun i => w i + wordOfFinset (n := 24) B i)
        =
          dot (n := 24) (wordOfFinset (n := 24) B') w +
          dot (n := 24) (wordOfFinset (n := 24) B') (wordOfFinset (n := 24) B) := by
            simpa using!
              (dot_add_right (n := 24) (wordOfFinset (n := 24) B') w
                (wordOfFinset (n := 24) B))
      _ = 0 := by
            simp [hw _ hB', dot_wordOfFinset_eq_zero_of_blocks (S := S) (hB := hB') (hB' := hB)]

lemma mem_blockSubmodule_of_orthoBlocks
    (S : SteinerSystem 24 8 5) {w : Word} (hw : OrthoBlocks S w) :
    w ∈ blockSubmodule S.blocks := by
  -- Strong induction on the weight.
  let W : Submodule (ZMod 2) Word := blockSubmodule S.blocks
  let p : ℕ → Prop := fun n => ∀ w : Word, weight w = n → OrthoBlocks S w → w ∈ W
  have hp : ∀ n, (∀ m < n, p m) → p n := by
    intro n ih w hwt hOrtho
    by_cases hn5 : n < 5
    · have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases hn with rfl | rfl | rfl | rfl | rfl
      · -- n = 0
        have hsuppCard : (support w).card = 0 := by
          simpa [GolayBounds.weight_eq_card_support] using! hwt
        have hsupp : support w = (∅ : Finset (Fin 24)) := Finset.card_eq_zero.1 hsuppCard
        have hw0 : w = 0 := by
          funext i
          have hi0 : i ∉ support w := by simp [hsupp]
          have : w i = 0 := (GolayBounds.not_mem_support (w := w) i).1 hi0
          simp [this]
        simp [W, hw0]
      · -- n = 1
        have hsupp : (support w).card = 1 := by
          simpa [GolayBounds.weight_eq_card_support] using! hwt
        have hcardBC : (S.blocksContaining (support w)).card = 253 := by
          simpa using! WittParams.card_blocksContaining_one (S := S) (support w) hsupp
        have hpos : 0 < (S.blocksContaining (support w)).card := by
          rw [hcardBC]
          decide
        rcases Finset.card_pos.1 hpos with ⟨B, hBmem⟩
        have hB : B ∈ S.blocks ∧ support w ⊆ B :=
          (SteinerSystem.mem_blocksContaining S).1 hBmem
        have hdot0 : dot (n := 24) (wordOfFinset (n := 24) B) w = 0 := by
          simpa using! hOrtho B hB.1
        have hEven : Even (support (wordOfFinset (n := 24) B) ∩ support w).card :=
          (DotSupportLite.dot_eq_zero_iff_even_card_support_inter
            (w₁ := wordOfFinset (n := 24) B) (w₂ := w)).1 hdot0
        have hEven' : Even (B ∩ support w).card := by
          simpa [support_wordOfFinset] using! hEven
        have hinter : (B ∩ support w).card = 1 := by
          have : B ∩ support w = support w := Finset.inter_eq_right.2 hB.2
          simp [this, hsupp]
        have : ¬ Even (1 : ℕ) := by decide
        have hEven1 : Even (1 : ℕ) := by
          rw [←hinter]
          exact hEven'
        exact False.elim (this hEven1)
      · -- n = 2
        have hsupp : (support w).card = 2 := by
          simpa [GolayBounds.weight_eq_card_support] using! hwt
        rcases Finset.card_eq_two.1 hsupp with ⟨a, b, hab, hwAB⟩
        have hBex :
            ∃ B : Finset (Fin 24), B ∈ S.blocks ∧ a ∈ B ∧ b ∉ B :=
          exists_block_contains_left_not_right (S := S) (a := a) (b := b) hab
        rcases hBex with ⟨B, hB, haB, hbB⟩
        have hdot0 : dot (n := 24) (wordOfFinset (n := 24) B) w = 0 := by
          simpa using! hOrtho B hB
        have hEven : Even (support (wordOfFinset (n := 24) B) ∩ support w).card :=
          (DotSupportLite.dot_eq_zero_iff_even_card_support_inter
            (w₁ := wordOfFinset (n := 24) B) (w₂ := w)).1 hdot0
        have hEven' : Even (B ∩ support w).card := by
          simpa [support_wordOfFinset] using! hEven
        have hinter : (B ∩ support w).card = 1 := by
          have : B ∩ support w = ({a} : Finset (Fin 24)) := by
            rw [hwAB]
            ext i
            simp [haB, hbB]
          simp [this]
        have : ¬ Even (1 : ℕ) := by decide
        have hEven1 : Even (1 : ℕ) := by
          rw [←hinter]
          exact hEven'
        exact False.elim (this hEven1)
      · -- n = 3
        have hsupp : (support w).card = 3 := by
          simpa [GolayBounds.weight_eq_card_support] using! hwt
        have hcardBC : (S.blocksContaining (support w)).card = 21 := by
          simpa using! WittParams.card_blocksContaining_three (S := S) (support w) hsupp
        have hpos : 0 < (S.blocksContaining (support w)).card := by
          rw [hcardBC]
          decide
        rcases Finset.card_pos.1 hpos with ⟨B, hBmem⟩
        have hB : B ∈ S.blocks ∧ support w ⊆ B :=
          (SteinerSystem.mem_blocksContaining S).1 hBmem
        have hdot0 : dot (n := 24) (wordOfFinset (n := 24) B) w = 0 := by
          simpa using! hOrtho B hB.1
        have hEven : Even (support (wordOfFinset (n := 24) B) ∩ support w).card :=
          (DotSupportLite.dot_eq_zero_iff_even_card_support_inter
            (w₁ := wordOfFinset (n := 24) B) (w₂ := w)).1 hdot0
        have hEven' : Even (B ∩ support w).card := by
          simpa [support_wordOfFinset] using! hEven
        have hinter : (B ∩ support w).card = 3 := by
          have : B ∩ support w = support w := Finset.inter_eq_right.2 hB.2
          simp [this, hsupp]
        have : ¬ Even (3 : ℕ) := by decide
        have hEven3 : Even (3 : ℕ) := by
          rw [←hinter]
          exact hEven'
        exact False.elim (this hEven3)
      · -- n = 4
        have hsupp : (support w).card = 4 := by
          simpa [GolayBounds.weight_eq_card_support] using! hwt
        rcases exists_block_inter_card_eq_three (S := S) (T := support w) hsupp with ⟨B, hB, h3⟩
        have hdot0 : dot (n := 24) (wordOfFinset (n := 24) B) w = 0 := by
          simpa using! hOrtho B hB
        have hEven : Even (support (wordOfFinset (n := 24) B) ∩ support w).card :=
          (DotSupportLite.dot_eq_zero_iff_even_card_support_inter
            (w₁ := wordOfFinset (n := 24) B) (w₂ := w)).1 hdot0
        have hEven' : Even (B ∩ support w).card := by
          simpa [support_wordOfFinset] using! hEven
        have hinter : (B ∩ support w).card = 3 := by
          simpa [Finset.inter_comm] using! h3
        have : ¬ Even (3 : ℕ) := by decide
        have hEven3 : Even (3 : ℕ) := by
          rw [←hinter]
          exact hEven'
        exact False.elim (this hEven3)
    · -- Inductive step: pick a `5`-subset, add the corresponding block, and reduce the weight.
      have hn5' : 5 ≤ n := Nat.le_of_not_gt hn5
      set A : Finset (Fin 24) := support w
      have hAcard : A.card = n := by
        simpa [A, GolayBounds.weight_eq_card_support] using! hwt
      have hAcard_ge : 5 ≤ A.card := by simpa [hAcard] using! hn5'
      rcases (Finset.exists_subset_card_eq (s := A) (n := 5) hAcard_ge) with ⟨T, hTA, hTcard⟩
      have hTcard' : T.card = 5 := hTcard
      rcases S.cover_unique T hTcard' with ⟨B, hB, _⟩
      have hBmem : B ∈ S.blocks := hB.1
      have hTB : T ⊆ B := hB.2
      have hdot0 : dot (n := 24) (wordOfFinset (n := 24) B) w = 0 := by
        simpa using! hOrtho B hBmem
      have hEven : Even (support (wordOfFinset (n := 24) B) ∩ support w).card :=
        (DotSupportLite.dot_eq_zero_iff_even_card_support_inter
          (w₁ := wordOfFinset (n := 24) B) (w₂ := w)).1 hdot0
      have hEvenI : Even (A ∩ B).card := by
        simpa [A, support_wordOfFinset, Finset.inter_comm] using! hEven
      have hIge5 : 5 ≤ (A ∩ B).card := by
        have hsub : T ⊆ A ∩ B :=
          Finset.subset_inter hTA hTB
        simpa [hTcard'] using! (Finset.card_le_card hsub)
      have hIne5 : (A ∩ B).card ≠ 5 := by
        intro hEq
        have hEven5 : Even (5 : ℕ) := by simpa [hEq] using! hEvenI
        have hNot : ¬ Even (5 : ℕ) := by decide
        exact hNot hEven5
      have hIge6 : 6 ≤ (A ∩ B).card :=
        Nat.succ_le_of_lt (lt_of_le_of_ne hIge5 (Ne.symm hIne5))
      let w' : Word := fun i => w i + wordOfFinset (n := 24) B i
      have hOrtho' : OrthoBlocks S w' :=
        orthoBlocks_add_blockWord (S := S) (w := w) hOrtho (B := B) hBmem
      have hBcard : B.card = 8 := S.block_card B hBmem
      have hsupp' : support w' = A ∆ B := by
        simpa [w', A, support_wordOfFinset] using!
          (by
            simpa [Pi.add_apply] using!
              (GolayBounds.support_add_eq_symmDiff (w₁ := w) (w₂ := wordOfFinset (n := 24) B)))
      have hwt' : weight w' = (A ∆ B).card := by
        simp [GolayBounds.weight_eq_card_support, hsupp']
      have hEqCard :
          (A ∆ B).card + 2 * (A ∩ B).card = n + 8 := by
        have := card_symmDiff_add_two_mul_card_inter (A := A) (B := B)
        simpa [hAcard, hBcard] using! this
      have hlt : weight w' < n := by
        omega
      have hw'mem : w' ∈ W := (ih (weight w') hlt) w' rfl hOrtho'
      have hBword : wordOfFinset (n := 24) B ∈ W :=
        wordOfFinset_mem_blockSubmodule_of_mem_blocks (S := S) hBmem
      have hwrec : w = (fun i => w' i + wordOfFinset (n := 24) B i) := by
        grind only
      have : (fun i => w' i + wordOfFinset (n := 24) B i) ∈ W := W.add_mem hw'mem hBword
      simpa [W, hwrec] using! this
  have hres : p (weight w) := Nat.strong_induction_on (p := p) (n := weight w) hp
  simpa [W] using! (hres w rfl hw)

lemma orthogonal_le_blockSubmodule
    (S : SteinerSystem 24 8 5) :
    (Bdot).orthogonal (blockSubmodule S.blocks) ≤ blockSubmodule S.blocks := by
  intro w hw
  exact mem_blockSubmodule_of_orthoBlocks (S := S) (w := w)
    (orthoBlocks_of_mem_orthogonal (S := S) hw)

lemma orthogonal_eq_blockSubmodule
    (S : SteinerSystem 24 8 5) :
    (Bdot).orthogonal (blockSubmodule S.blocks) = blockSubmodule S.blocks := by
  refine le_antisymm (orthogonal_le_blockSubmodule (S := S)) ?_
  intro x hx
  exact (blockSubmodule_le_orthogonal (S := S)) hx

/-- The code spanned by the blocks of a Witt design has cardinality `2 ^ 12`. -/
public theorem codeFromSteinerSystem_ncard_eq_two_pow_12 (S : SteinerSystem 24 8 5) :
    Set.ncard (codeFromSteinerSystem S) = 2 ^ 12 := by
  -- Work with the spanning submodule.
  let W : Submodule (ZMod 2) Word := blockSubmodule S.blocks
  have hW : (Bdot).orthogonal W = W := by
    simpa [W] using! orthogonal_eq_blockSubmodule (S := S)
  have hBnondeg : (Bdot).Nondegenerate := DotBilin.dotBilinForm_nondegenerate (n := 24)
  have hBref : (Bdot).IsRefl :=
    LinearMap.BilinForm.IsSymm.isRefl (H := DotBilin.dotBilinForm_isSymm (n := 24))
  have hV : Module.finrank (ZMod 2) Word = 24 := by
    exact Module.finrank_fin_fun (ZMod 2)
  have hWfin : Module.finrank (ZMod 2) W = 12 := by
    have horth :=
      LinearMap.BilinForm.finrank_orthogonal (B := Bdot) (K := ZMod 2) (V := Word)
        hBnondeg W
    have hle0 : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) Word :=
      Submodule.finrank_le (s := W)
    have hle : Module.finrank (ZMod 2) W ≤ 24 := by simpa [hV] using! hle0
    have hadd :
        Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) W = 24 := by
      -- `a = 24 - a` and `a ≤ 24` imply `a + a = 24`.
      have horth' :
          Module.finrank (ZMod 2) (Bdot.orthogonal W) = 24 - Module.finrank (ZMod 2) W := by
        simpa [hV] using! horth
      have horthEq : Module.finrank (ZMod 2) (Bdot.orthogonal W) = Module.finrank (ZMod 2) W := by
        let e : (Bdot.orthogonal W) ≃ₗ[ZMod 2] W :=
          LinearEquiv.ofEq _ _ hW
        simpa using! (LinearEquiv.finrank_eq e)
      have hEq : Module.finrank (ZMod 2) W = 24 - Module.finrank (ZMod 2) W := by
        calc
          Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) (Bdot.orthogonal W) := by
            simpa using! horthEq.symm
          _ = 24 - Module.finrank (ZMod 2) W := horth'
      have :
          Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) W =
            (24 - Module.finrank (ZMod 2) W) + Module.finrank (ZMod 2) W := by
        simpa using! congrArg (fun t => t + Module.finrank (ZMod 2) W) hEq
      simpa [Nat.sub_add_cancel hle] using! this
    grind only
  open scoped Classical in
  have hCardW : Fintype.card W = 2 ^ 12 := by
    have hCard := (Module.card_eq_pow_finrank (K := ZMod 2) (V := W))
    -- `card (ZMod 2) = 2`.
    simpa [ZMod.card, hWfin] using! hCard
  -- Convert `Fintype.card W` to `Set.ncard` of the carrier.
  have hncardW : Set.ncard (W : Set Word) = 2 ^ 12 := by
    calc
      Set.ncard (W : Set Word) = Nat.card (W : Set Word) := by
        simpa using! (Nat.card_coe_set_eq (s := (W : Set Word))).symm
      _ = Fintype.card W := by
        -- `Nat.card` agrees with `Fintype.card` for finite types.
        exact (Nat.card_eq_fintype_card (α := W))
      _ = 2 ^ 12 := hCardW
  simpa [codeFromSteinerSystem, codeFromBlocks, W] using! hncardW

end

end GolayUniquenessSteps.WittDesignUniqueTheory.ClassicalWitt

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
