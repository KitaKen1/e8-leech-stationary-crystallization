-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Design23632Forced
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

/-!
# Uniqueness of the `2-(6,3,2)` design up to relabeling

This file proves Lemma `23632_unique` (up to relabeling) from the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.

## Main definitions
* `Design23632.mapDesign`

## Main statements
* `Design23632.Is23632.map`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

namespace Design23632

open scoped BigOperators

/-!
## Transporting designs by a point permutation
-/

/-- The embedding of blocks induced by a permutation of points. -/
public def BlockMap (σ : Equiv Point Point) : Block ↪ Block :=
  { toFun := fun B => B.map σ.toEmbedding
    inj' := Finset.map_injective σ.toEmbedding }

/-- Transport a design `T` by a point permutation `σ`. -/
@[expose] public def mapDesign (σ : Equiv Point Point) (T : Finset Block) : Finset Block :=
  T.map (BlockMap σ)

/-- Membership characterization for `mapDesign`. -/
@[simp] public lemma mem_mapDesign {σ : Equiv Point Point} {T : Finset Block} {B : Block} :
    B ∈ mapDesign σ T ↔ ∃ B0 ∈ T, B = B0.map σ.toEmbedding := by
  constructor
  · intro hB
    rcases Finset.mem_map.1 hB with ⟨B0, hB0, rfl⟩
    exact ⟨B0, hB0, rfl⟩
  · rintro ⟨B0, hB0, rfl⟩
    exact Finset.mem_map.2 ⟨B0, hB0, rfl⟩

attribute [grind =] mem_mapDesign

/-- Functoriality of `mapDesign` under composition of permutations. -/
public lemma mapDesign_trans (σ₁ σ₂ : Equiv Point Point) (T : Finset Block) :
    mapDesign (σ₁.trans σ₂) T = mapDesign σ₂ (mapDesign σ₁ T) := by
  ext B
  simp [mapDesign, BlockMap, Finset.map_map]

/-- `mapDesign` preserves cardinality. -/
@[simp] public lemma card_mapDesign (σ : Equiv Point Point) (T : Finset Block) :
    (mapDesign σ T).card = T.card := by
  simp [mapDesign]

@[simp] lemma mem_map_block {σ : Equiv Point Point} {B : Block} {x : Point} :
    x ∈ B.map σ.toEmbedding ↔ σ.symm x ∈ B := by
  simp

attribute [grind =] mem_map_block

/-- Pair multiplicities are preserved under transport by `mapDesign`. -/
public lemma pairCount_mapDesign (σ : Equiv Point Point) (T : Finset Block) (x y : Point) :
    pairCount (mapDesign σ T) x y = pairCount T (σ.symm x) (σ.symm y) := by
  let f : Block ↪ Block := BlockMap σ
  have hEq :
      blocksThroughPair (mapDesign σ T) x y =
        (blocksThroughPair T (σ.symm x) (σ.symm y)).map f := by
    ext B'
    constructor
    · intro hB'
      have hmem : B' ∈ mapDesign σ T := (mem_blocksThroughPair.1 hB').1
      have hx : x ∈ B' := (mem_blocksThroughPair.1 hB').2.1
      have hy : y ∈ B' := (mem_blocksThroughPair.1 hB').2.2
      rcases Finset.mem_map.1 hmem with ⟨B, hB, rfl⟩
      refine Finset.mem_map.2 ?_
      refine ⟨B, ?_, rfl⟩
      refine mem_blocksThroughPair.2 ?_
      refine ⟨hB, ?_⟩
      constructor
      · simpa [BlockMap, mem_map_block] using! hx
      · simpa [BlockMap, mem_map_block] using! hy
    · intro hB'
      rcases Finset.mem_map.1 hB' with ⟨B, hB, rfl⟩
      refine mem_blocksThroughPair.2 ?_
      refine ⟨?_, ?_⟩
      · exact Finset.mem_map.2 ⟨B, (mem_blocksThroughPair.1 hB).1, rfl⟩
      · constructor
        · exact (mem_map_block (σ := σ) (B := B) (x := x)).2 (mem_blocksThroughPair.1 hB).2.1
        · exact (mem_map_block (σ := σ) (B := B) (x := y)).2 (mem_blocksThroughPair.1 hB).2.2
  grind only [=_ blocksThroughPair_card, = Finset.card_map]

/-- Transporting an `Is23632` design by a point permutation preserves `Is23632`. -/
public lemma Is23632.map (T : Finset Block) (hT : Is23632 T) (σ : Equiv Point Point) :
    Is23632 (mapDesign σ T) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [card_mapDesign] using! hT.1
  · intro B hB
    rcases (mem_mapDesign (σ := σ) (T := T) (B := B)).1 hB with ⟨B0, hB0, rfl⟩
    simpa using! hT.2.1 B0 hB0
  · intro x y hxy
    have hxy' : σ.symm x ≠ σ.symm y := by
      intro h
      exact hxy (by simpa using! congrArg σ h)
    simpa [pairCount_mapDesign] using! (hT.2.2 (σ.symm x) (σ.symm y) hxy')

/-!
## Choosing a permutation sending a triple to `012`
-/

lemma exists_perm_send_triple
    {x y z : Point} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ σ : Equiv Point Point, σ x = 0 ∧ σ y = 1 ∧ σ z = 2 := by
  let σ₁ : Equiv Point Point := Equiv.swap x 0
  have hx0 : σ₁ x = 0 := by simp [σ₁]
  have hy₁0 : σ₁ y ≠ 0 := by
    intro hy0
    have : σ₁ x = σ₁ y := by simpa [hx0] using! hy0.symm
    exact hxy (σ₁.injective this)
  let σ₂ : Equiv Point Point := Equiv.swap (σ₁ y) 1
  have hσ₂_fix0 : σ₂ 0 = 0 := by
    have h0ne : (0 : Point) ≠ σ₁ y := by
      intro h
      exact hy₁0 (by simp [h])
    have h0ne1 : (0 : Point) ≠ 1 := by decide
    simpa [σ₂] using! (Equiv.swap_apply_of_ne_of_ne h0ne h0ne1)
  have hy1 : (σ₁.trans σ₂) y = 1 := by
    simp [Equiv.trans_apply, σ₂]
  have hx0' : (σ₁.trans σ₂) x = 0 := by
    simp [Equiv.trans_apply, hx0, hσ₂_fix0]
  let z₂ : Point := (σ₁.trans σ₂) z
  have hz₂_ne0 : z₂ ≠ 0 := by
    intro h
    have : (σ₁.trans σ₂) x = (σ₁.trans σ₂) z := by simpa [z₂, hx0'] using! h.symm
    exact hxz ((σ₁.trans σ₂).injective this)
  have hz₂_ne1 : z₂ ≠ 1 := by
    intro h
    have : (σ₁.trans σ₂) y = (σ₁.trans σ₂) z := by simpa [z₂, hy1] using! h.symm
    exact hyz ((σ₁.trans σ₂).injective this)
  let σ₃ : Equiv Point Point := Equiv.swap z₂ 2
  have hσ₃_fix0 : σ₃ 0 = 0 := by
    have h0ne : (0 : Point) ≠ z₂ := by
      intro h
      exact hz₂_ne0 (by simp [h])
    have h0ne2 : (0 : Point) ≠ 2 := by decide
    simpa [σ₃] using! (Equiv.swap_apply_of_ne_of_ne h0ne h0ne2)
  have hσ₃_fix1 : σ₃ 1 = 1 := by
    have h1ne : (1 : Point) ≠ z₂ := by
      intro h
      exact hz₂_ne1 (by simp [h])
    have h1ne2 : (1 : Point) ≠ 2 := by decide
    simpa [σ₃] using! (Equiv.swap_apply_of_ne_of_ne h1ne h1ne2)
  refine ⟨(σ₁.trans σ₂).trans σ₃, ?_, ?_, ?_⟩
  · simp [Equiv.trans_apply, hx0', hσ₃_fix0]
  · simp [Equiv.trans_apply, hy1, hσ₃_fix1]
  · simp [Equiv.trans_apply, σ₃, z₂]

/-!
## The other block through a pair
-/

lemma exists_other_block_through_pair
    (T : Finset Block) (hT : Is23632 T) {x y z : Point} (hxy : x ≠ y)
    (hB0 : ({x, y, z} : Block) ∈ T) :
    ∃ u : Point, u ≠ z ∧ ({x, y, u} : Block) ∈ T := by
  have hcard : (blocksThroughPair T x y).card = 2 := by
    simpa [blocksThroughPair_card] using! (hT.2.2 x y hxy)
  have hB0_in : ({x, y, z} : Block) ∈ blocksThroughPair T x y := by
    simpa
  rcases Finset.card_eq_two.1 hcard with ⟨B₁, B₂, hne, hEq⟩
  have hmem₁ : B₁ ∈ blocksThroughPair T x y := by simp [hEq]
  have hmem₂ : B₂ ∈ blocksThroughPair T x y := by simp [hEq]
  have hB0_cases : ({x, y, z} : Block) = B₁ ∨ ({x, y, z} : Block) = B₂ := by
    simpa [hEq] using! hB0_in
  refine (hB0_cases.elim (fun h => ?_) (fun h => ?_))
  · subst h
    rcases shape_of_mem_pair T hT (x := x) (y := y) hxy hmem₂ with ⟨u, _, _, hB₂⟩
    have huz : u ≠ z := by
      intro huz
      have : ({x, y, u} : Block) = ({x, y, z} : Block) := by simp [huz]
      exact hne (by simp [hB₂, this])
    refine ⟨u, huz, ?_⟩
    have : B₂ ∈ T := (mem_blocksThroughPair.1 hmem₂).1
    simpa [hB₂] using! this
  · subst h
    rcases shape_of_mem_pair T hT (x := x) (y := y) hxy hmem₁ with ⟨u, _, _, hB₁⟩
    have huz : u ≠ z := by
      intro huz
      have : ({x, y, u} : Block) = ({x, y, z} : Block) := by simp [huz]
      exact hne (by simp [hB₁, this])
    refine ⟨u, huz, ?_⟩
    have : B₁ ∈ T := (mem_blocksThroughPair.1 hmem₁).1
    simpa [hB₁] using! this

lemma third_point_in_345 {u : Point} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hu2 : u ≠ 2) :
    u = 3 ∨ u = 4 ∨ u = 5 := by
  fin_cases u
  · cases hu0 rfl
  · cases hu1 rfl
  · cases hu2 rfl
  · left; rfl
  · right; left; rfl
  · right; right; rfl

lemma block_ne_of_mem_not_mem {B B' : Block} {x : Point} (hx : x ∈ B) (hx' : x ∉ B') :
    B ≠ B' := by
  intro hEq
  exact hx' (hEq ▸ hx)

lemma card_three_blocks {B₁ B₂ B₃ : Block} (h12 : B₁ ≠ B₂) (h13 : B₁ ≠ B₃) (h23 : B₂ ≠ B₃) :
    ({B₁, B₂, B₃} : Finset Block).card = 3 := by
  simpa using! (Finset.card_eq_three.2 ⟨B₁, B₂, B₃, h12, h13, h23, rfl⟩)

lemma three_blocks_through_pair_contra
    (T : Finset Block) (hT : Is23632 T) {x y : Point} (hxy : x ≠ y)
    (B₁ B₂ B₃ : Block)
    (h₁ : B₁ ∈ blocksThroughPair T x y)
    (h₂ : B₂ ∈ blocksThroughPair T x y)
    (h₃ : B₃ ∈ blocksThroughPair T x y)
    (hcard : ({B₁, B₂, B₃} : Finset Block).card = 3) : False := by
  have hsubset :
      ({B₁, B₂, B₃} : Finset Block) ⊆ blocksThroughPair T x y := by
    intro B hB
    rcases (by simpa using! hB) with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  have hge : 3 ≤ (blocksThroughPair T x y).card := by
    simpa [hcard] using! (Finset.card_le_card hsubset)
  have hpair : (blocksThroughPair T x y).card = 2 := by
    simpa [blocksThroughPair_card] using! (hT.2.2 x y hxy)
  have hge' := hge
  rw [hpair] at hge'
  exact (Nat.not_succ_le_self 2) hge'

lemma exists_third_345
    {a b : Point} (ha : a = 3 ∨ a = 4 ∨ a = 5) (hb : b = 3 ∨ b = 4 ∨ b = 5) (hab : a ≠ b) :
    ∃ d : Point,
      (d = 3 ∨ d = 4 ∨ d = 5) ∧ d ≠ a ∧ d ≠ b ∧
        ({a, b, d} : Finset Point) = ({3, 4, 5} : Finset Point) := by
  let S : Finset Point := ({3, 4, 5} : Finset Point)
  have haS : a ∈ S := by
    rcases ha with rfl | rfl | rfl <;> simp [S]
  have hbS : b ∈ S := by
    rcases hb with rfl | rfl | rfl <;> simp [S]
  have hbSa : b ∈ S.erase a := by
    simp [Finset.mem_erase, hbS, hab.symm]
  have hcardEraseA : (S.erase a).card = 2 := by
    simpa [S] using! (Finset.card_erase_of_mem haS)
  have hcardEraseAB : ((S.erase a).erase b).card = 1 := by
    simpa [hcardEraseA] using! (Finset.card_erase_of_mem hbSa)
  rcases Finset.card_eq_one.1 hcardEraseAB with ⟨d, hd⟩
  have hdMem : d ∈ (S.erase a).erase b := by simp [hd]
  have hdS : d ∈ S := (Finset.mem_erase.1 (Finset.mem_erase.1 hdMem).2).2
  have hda : d ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 hdMem).2).1
  have hdb : d ≠ b := (Finset.mem_erase.1 hdMem).1
  have hd345 : d = 3 ∨ d = 4 ∨ d = 5 := by
    simpa [S] using! hdS
  have hsubset : ({a, b, d} : Finset Point) ⊆ S := by
    intro t ht
    rcases (by simpa using! ht) with rfl | rfl | rfl
    · exact haS
    · exact hbS
    · exact hdS
  have hcardABD : ({a, b, d} : Finset Point).card = 3 := by
    simpa using! (Finset.card_eq_three.2 ⟨a, b, d, hab, hda.symm, hdb.symm, rfl⟩)
  have hcardS : S.card = 3 := by decide
  have hEq : ({a, b, d} : Finset Point) = S :=
    Finset.eq_of_subset_of_card_le hsubset (by simp [hcardABD, hcardS])
  exact ⟨d, hd345, hda, hdb, by simpa [S] using! hEq⟩

lemma third_eq_a_or_b_of_mem_blocksThroughPair_0d
    (T : Finset Block) (hT : Is23632 T)
    {a b d : Point}
    (hd345 : d = 3 ∨ d = 4 ∨ d = 5)
    (habd345 : ({a, b, d} : Finset Point) = ({3, 4, 5} : Finset Point))
    (hda : d ≠ a) (hdb : d ≠ b)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ≠ 2)
    (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hb2 : b ≠ 2)
    (h012 : ({0, 1, 2} : Block) ∈ T)
    (h01a : ({0, 1, a} : Block) ∈ T)
    (h02b : ({0, 2, b} : Block) ∈ T)
    {B : Block} (hB : B ∈ blocksThroughPair T 0 d) :
    ∃ u : Point, (u = a ∨ u = b) ∧ B = ({0, d, u} : Block) := by
  have hd0 : d ≠ 0 := by rcases hd345 with rfl | rfl | rfl <;> decide
  have hd1 : d ≠ 1 := by rcases hd345 with rfl | rfl | rfl <;> decide
  have hd2 : d ≠ 2 := by rcases hd345 with rfl | rfl | rfl <;> decide
  have h0d : (0 : Point) ≠ d := by simpa [eq_comm] using! hd0
  rcases shape_of_mem_pair T hT (x := 0) (y := d) h0d hB with ⟨u, hu0, hud, rfl⟩
  have huT : ({0, d, u} : Block) ∈ T := (mem_blocksThroughPair.1 hB).1
  have hu1 : u ≠ 1 := by
    intro hu
    subst hu
    have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T 0 1 := by simp [h012]
    have h01abp : ({0, 1, a} : Block) ∈ blocksThroughPair T 0 1 := by simp [h01a]
    have h01dbp : ({0, d, 1} : Block) ∈ blocksThroughPair T 0 1 := by simp [huT]
    have hcard3 :
        ({({0, 1, 2} : Block), ({0, 1, a} : Block), ({0, d, 1} : Block)} : Finset Block).card =
          3 := by
      refine card_three_blocks ?_ ?_ ?_
      · exact block_ne_of_mem_not_mem (x := 2) (by simp) (by simp [eq_comm, ha2])
      · exact block_ne_of_mem_not_mem (x := 2) (by simp) (by simp [eq_comm, hd2])
      · refine block_ne_of_mem_not_mem (x := a) (by simp) ?_
        simp [ha0, ha1, hda.symm]
    exact (three_blocks_through_pair_contra (T := T) hT (x := 0) (y := 1) (by decide)
      ({0, 1, 2} : Block) ({0, 1, a} : Block) ({0, d, 1} : Block)
      h012bp h01abp h01dbp hcard3)
  have hu2 : u ≠ 2 := by
    intro hu
    subst hu
    have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T 0 2 := by simp [h012]
    have h02bbp : ({0, 2, b} : Block) ∈ blocksThroughPair T 0 2 := by simp [h02b]
    have h02dbp : ({0, d, 2} : Block) ∈ blocksThroughPair T 0 2 := by simp [huT]
    have hcard3 :
        ({({0, 1, 2} : Block), ({0, 2, b} : Block), ({0, d, 2} : Block)} : Finset Block).card =
          3 := by
      refine card_three_blocks ?_ ?_ ?_
      · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, hb1])
      · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, hd1])
      · refine block_ne_of_mem_not_mem (x := b) (by simp) ?_
        simp [hb0, hb2, hdb.symm]
    exact (three_blocks_through_pair_contra (T := T) hT (x := 0) (y := 2) (by decide)
      ({0, 1, 2} : Block) ({0, 2, b} : Block) ({0, d, 2} : Block)
      h012bp h02bbp h02dbp hcard3)
  have hu345 : u = 3 ∨ u = 4 ∨ u = 5 := third_point_in_345 hu0 hu1 hu2
  have huMemS : u ∈ ({3, 4, 5} : Finset Point) := by
    rcases hu345 with rfl | rfl | rfl <;> simp
  have huMemABD : u ∈ ({a, b, d} : Finset Point) := by simpa [habd345] using! huMemS
  have huABD : u = a ∨ u = b ∨ u = d := by simpa using! huMemABD
  refine ⟨u, ?_, rfl⟩
  rcases huABD with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hud h).elim

lemma third_eq_a_or_b_of_mem_blocksThroughPair_2d
    (T : Finset Block) (hT : Is23632 T)
    {a b d : Point}
    (hd345 : d = 3 ∨ d = 4 ∨ d = 5) (habd345 : ({a,b,d} : Finset Point) = ({3,4,5} : Finset Point))
    (hda : d ≠ a) (hdb : d ≠ b)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ≠ 2)
    (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hb2 : b ≠ 2)
    (h012 : ({0,1,2} : Block) ∈ T) (h02b : ({0,2,b} : Block) ∈ T) (h12a : ({1,2,a} : Block) ∈ T)
    {B : Block} (hB : B ∈ blocksThroughPair T 2 d) :
    ∃ u : Point, (u = a ∨ u = b) ∧ B = ({2, d, u} : Block) := by
  have hd0 : d ≠ 0 := by rcases hd345 with rfl | rfl | rfl <;> decide
  have hd1 : d ≠ 1 := by rcases hd345 with rfl | rfl | rfl <;> decide
  have hd2 : d ≠ 2 := by rcases hd345 with rfl | rfl | rfl <;> decide
  have h2d : (2 : Point) ≠ d := by simpa [eq_comm] using! hd2
  rcases shape_of_mem_pair T hT (x := 2) (y := d) h2d hB with ⟨u, hu2, hud, rfl⟩
  have huT : ({2, d, u} : Block) ∈ T := (mem_blocksThroughPair.1 hB).1
  have hu0 : u ≠ 0 := by
    intro hu
    subst hu
    have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T 0 2 := by simp [h012]
    have h02bbp : ({0, 2, b} : Block) ∈ blocksThroughPair T 0 2 := by simp [h02b]
    have h02dbp : ({2, d, 0} : Block) ∈ blocksThroughPair T 0 2 := by simp [huT]
    have hcard3 :
        ({({0,1,2} : Block), ({0,2,b} : Block), ({2,d,0} : Block)} : Finset Block).card = 3 := by
      refine card_three_blocks ?_ ?_ ?_
      · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, hb1])
      · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, hd1])
      · refine block_ne_of_mem_not_mem (x := b) (by simp) ?_
        simp [hb0, hb2, hdb.symm]
    exact (three_blocks_through_pair_contra (T := T) hT (x := 0) (y := 2) (by decide)
      ({0, 1, 2} : Block) ({0, 2, b} : Block) ({2, d, 0} : Block)
      h012bp h02bbp h02dbp hcard3)
  have hu1 : u ≠ 1 := by
    intro hu
    subst hu
    have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T 1 2 := by simp [h012]
    have h12abp : ({1, 2, a} : Block) ∈ blocksThroughPair T 1 2 := by simp [h12a]
    have h12dbp : ({2, d, 1} : Block) ∈ blocksThroughPair T 1 2 := by simp [huT]
    have hcard3 :
        ({({0,1,2} : Block), ({1,2,a} : Block), ({2,d,1} : Block)} : Finset Block).card = 3 := by
      refine card_three_blocks ?_ ?_ ?_
      · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0])
      · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, hd0])
      · refine block_ne_of_mem_not_mem (x := a) (by simp) ?_
        simp [ha2, ha1, hda.symm]
    exact (three_blocks_through_pair_contra (T := T) hT (x := 1) (y := 2) (by decide)
      ({0, 1, 2} : Block) ({1, 2, a} : Block) ({2, d, 1} : Block)
      h012bp h12abp h12dbp hcard3)
  have hu345 : u = 3 ∨ u = 4 ∨ u = 5 := third_point_in_345 hu0 hu1 hu2
  have huMemS : u ∈ ({3, 4, 5} : Finset Point) := by
    rcases hu345 with rfl | rfl | rfl <;> simp
  have huMemABD : u ∈ ({a, b, d} : Finset Point) := by simpa [habd345] using! huMemS
  have huABD : u = a ∨ u = b ∨ u = d := by simpa using! huMemABD
  refine ⟨u, ?_, rfl⟩
  rcases huABD with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hud h).elim

lemma third_eq_a_or_b_of_mem_blocksThroughPair_1d
    (T : Finset Block) (hT : Is23632 T)
    {a b d : Point}
    (hd345 : d = 3 ∨ d = 4 ∨ d = 5) (habd345 : ({a,b,d} : Finset Point) = ({3,4,5} : Finset Point))
    (hda : d ≠ a) (hdb : d ≠ b)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ≠ 2)
    (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hb2 : b ≠ 2)
    (h012 : ({0,1,2} : Block) ∈ T) (h01a : ({0,1,a} : Block) ∈ T) (h12b : ({1,2,b} : Block) ∈ T)
    {B : Block} (hB : B ∈ blocksThroughPair T 1 d) :
    ∃ u : Point, (u = a ∨ u = b) ∧ B = ({1, d, u} : Block) := by
  have hd0 : d ≠ 0 := by rcases hd345 with rfl | rfl | rfl <;> decide
  have hd1 : d ≠ 1 := by rcases hd345 with rfl | rfl | rfl <;> decide
  have hd2 : d ≠ 2 := by rcases hd345 with rfl | rfl | rfl <;> decide
  have h1d : (1 : Point) ≠ d := by simpa [eq_comm] using! hd1
  rcases shape_of_mem_pair T hT (x := 1) (y := d) h1d hB with ⟨u, hu1, hud, rfl⟩
  have huT : ({1, d, u} : Block) ∈ T := (mem_blocksThroughPair.1 hB).1
  have hu0 : u ≠ 0 := by
    intro hu
    subst hu
    have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T 0 1 := by simp [h012]
    have h01abp : ({0, 1, a} : Block) ∈ blocksThroughPair T 0 1 := by simp [h01a]
    have h01dbp : ({1, d, 0} : Block) ∈ blocksThroughPair T 0 1 := by simp [huT]
    have hcard3 :
        ({({0,1,2} : Block), ({0,1,a} : Block), ({1,d,0} : Block)} : Finset Block).card = 3 := by
      refine card_three_blocks ?_ ?_ ?_
      · exact block_ne_of_mem_not_mem (x := 2) (by simp) (by simp [eq_comm, ha2])
      · exact block_ne_of_mem_not_mem (x := 2) (by simp) (by simp [eq_comm, hd2])
      · refine block_ne_of_mem_not_mem (x := a) (by simp) ?_
        simp [ha0, ha1, hda.symm]
    exact (three_blocks_through_pair_contra (T := T) hT (x := 0) (y := 1) (by decide)
      ({0, 1, 2} : Block) ({0, 1, a} : Block) ({1, d, 0} : Block)
      h012bp h01abp h01dbp hcard3)
  have hu2 : u ≠ 2 := by
    intro hu
    subst hu
    have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T 1 2 := by simp [h012]
    have h12bbp : ({1, 2, b} : Block) ∈ blocksThroughPair T 1 2 := by simp [h12b]
    have h12dbp : ({1, d, 2} : Block) ∈ blocksThroughPair T 1 2 := by simp [huT]
    have hcard3 :
        ({({0,1,2} : Block), ({1,2,b} : Block), ({1,d,2} : Block)} : Finset Block).card = 3 := by
      refine card_three_blocks ?_ ?_ ?_
      · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, hb0])
      · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, hd0])
      · refine block_ne_of_mem_not_mem (x := b) (by simp) ?_
        simp [hb1, hb2, hdb.symm]
    exact (three_blocks_through_pair_contra (T := T) hT (x := 1) (y := 2) (by decide)
      ({0, 1, 2} : Block) ({1, 2, b} : Block) ({1, d, 2} : Block)
      h012bp h12bbp h12dbp hcard3)
  have hu345 : u = 3 ∨ u = 4 ∨ u = 5 := third_point_in_345 hu0 hu1 hu2
  have huMemS : u ∈ ({3, 4, 5} : Finset Point) := by
    rcases hu345 with rfl | rfl | rfl <;> simp
  have huMemABD : u ∈ ({a, b, d} : Finset Point) := by simpa [habd345] using! huMemS
  have huABD : u = a ∨ u = b ∨ u = d := by simpa using! huMemABD
  refine ⟨u, ?_, rfl⟩
  rcases huABD with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hud h).elim

lemma exists_perm_fix012_send_abc
    {a b c : Point}
    (ha : a = 3 ∨ a = 4 ∨ a = 5)
    (hb : b = 3 ∨ b = 4 ∨ b = 5)
    (hc : c = 3 ∨ c = 4 ∨ c = 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ τ : Equiv Point Point,
      τ 0 = 0 ∧ τ 1 = 1 ∧ τ 2 = 2 ∧ τ a = 4 ∧ τ b = 3 ∧ τ c = 5 := by
  rcases ha with ha3 | ha4 | ha5
  · subst ha3
    rcases hb with hb3 | hb4 | hb5
    · cases hab (by simp [hb3])
    · subst hb4
      rcases hc with hc3 | hc4 | hc5
      · subst hc3; cases hac rfl
      · subst hc4; cases hbc rfl
      · subst hc5
        refine ⟨Equiv.swap 3 4, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
    · subst hb5
      rcases hc with hc3 | hc4 | hc5
      · subst hc3; cases hac rfl
      · subst hc4
        refine ⟨(Equiv.swap 3 4).trans (Equiv.swap 3 5), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
      · subst hc5; cases hbc rfl
  · subst ha4
    rcases hb with hb3 | hb4 | hb5
    · subst hb3
      rcases hc with hc3 | hc4 | hc5
      · subst hc3; cases hbc rfl
      · subst hc4; cases hac rfl
      · subst hc5
        refine ⟨Equiv.refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
    · cases hab (by simp [hb4])
    · subst hb5
      rcases hc with hc3 | hc4 | hc5
      · subst hc3
        refine ⟨Equiv.swap 3 5, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
      · subst hc4; cases hac rfl
      · subst hc5; cases hbc rfl
  · subst ha5
    rcases hb with hb3 | hb4 | hb5
    · subst hb3
      rcases hc with hc3 | hc4 | hc5
      · subst hc3; cases hbc rfl
      · subst hc4
        refine ⟨Equiv.swap 4 5, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
      · subst hc5; cases hac rfl
    · subst hb4
      rcases hc with hc3 | hc4 | hc5
      · subst hc3
        refine ⟨(Equiv.swap 3 5).trans (Equiv.swap 3 4), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
      · subst hc4; cases hbc rfl
      · subst hc5; cases hac rfl
    · cases hab (by simp [hb5])

/-- Any `Is23632` design is isomorphic to the canonical design via a relabeling of points. -/
public theorem unique_up_to_relabel (T : Finset Block) (hT : Is23632 T) :
    ∃ σ : Equiv Point Point, mapDesign σ T = canonicalBlocks := by
  have hTpos : 0 < T.card := by simp [hT.1]
  rcases Finset.card_pos.1 hTpos with ⟨B0, hB0⟩
  have hB0card : B0.card = 3 := hT.2.1 B0 hB0
  rcases (Finset.card_eq_three.1 hB0card) with ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  rcases exists_perm_send_triple (x := x) (y := y) (z := z) hxy hxz hyz with ⟨σ0, hx0, hy1, hz2⟩
  let T0 : Finset Block := mapDesign σ0 T
  have hT0 : Is23632 T0 := Is23632.map (T := T) hT σ0
  have h012 : ({0, 1, 2} : Block) ∈ T0 := by
    refine (mem_mapDesign (σ := σ0) (T := T) (B := ({0, 1, 2} : Block))).2 ?_
    refine ⟨({x, y, z} : Block), hB0, ?_⟩
    ext t
    fin_cases t <;> simp [hx0, hy1, hz2]
  rcases exists_other_block_through_pair T0 hT0 (x := 0) (y := 1) (by decide) h012 with
    ⟨a, ha2, h01a⟩
  have h012_021 : ({0, 2, 1} : Block) ∈ T0 := by
    simpa [show ({0, 2, 1} : Block) = ({0, 1, 2} : Block) from by decide] using! h012
  rcases exists_other_block_through_pair T0 hT0 (x := 0) (y := 2) (by decide) h012_021 with
    ⟨b, hb1, h02b⟩
  have h012_120 : ({1, 2, 0} : Block) ∈ T0 := by
    simpa [show ({1, 2, 0} : Block) = ({0, 1, 2} : Block) from by decide] using! h012
  rcases exists_other_block_through_pair T0 hT0 (x := 1) (y := 2) (by decide) h012_120 with
    ⟨c, hc0, h12c⟩
  have ha0 : a ≠ 0 := by
    intro h
    simpa [h] using! (hT0.2.1 ({0, 1, a} : Block) h01a)
  have ha1 : a ≠ 1 := by
    intro h
    simpa [h] using! (hT0.2.1 ({0, 1, a} : Block) h01a)
  have hb0 : b ≠ 0 := by
    intro h
    simpa [h] using! (hT0.2.1 ({0, 2, b} : Block) h02b)
  have hb2 : b ≠ 2 := by
    intro h
    simpa [h] using! (hT0.2.1 ({0, 2, b} : Block) h02b)
  have hc1 : c ≠ 1 := by
    intro h
    simpa [h] using! (hT0.2.1 ({1, 2, c} : Block) h12c)
  have hc2 : c ≠ 2 := by
    intro h
    simpa [h] using! (hT0.2.1 ({1, 2, c} : Block) h12c)
  have ha345 : a = 3 ∨ a = 4 ∨ a = 5 := third_point_in_345 ha0 ha1 ha2
  have hb345 : b = 3 ∨ b = 4 ∨ b = 5 := third_point_in_345 hb0 hb1 hb2
  have hc345 : c = 3 ∨ c = 4 ∨ c = 5 := third_point_in_345 hc0 hc1 hc2
  -- prove the third points are distinct (otherwise some pair would lie in ≤ 1 block)
  have hab : a ≠ b := by
    intro hab
    subst hab
    rcases ha345 with rfl | rfl | rfl
    · -- a = b = 3: pair `04` can only occur in `045`
      have h04card : (blocksThroughPair T0 0 4).card = 2 := by
        simpa [blocksThroughPair_card] using! (hT0.2.2 0 4 (by decide))
      have hforced : ∀ B ∈ blocksThroughPair T0 0 4, B = ({0, 4, 5} : Block) := by
        intro B hB
        rcases shape_of_mem_pair T0 hT0 (x := 0) (y := 4) (by decide) hB with ⟨u, hu0, hu4, rfl⟩
        fin_cases u
        · cases hu0 (by decide)
        · -- u = 1: blocks `012,013,014` through `01`
          have h014T : ({0, 1, 4} : Block) ∈ T0 := by
            have hmem : ({0, 4, 1} : Block) ∈ T0 := (mem_blocksThroughPair.1 hB).1
            simpa [show ({0, 4, 1} : Block) = ({0, 1, 4} : Block) from by decide] using! hmem
          have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T0 0 1 := by
            simp [h012]
          have h013bp : ({0, 1, 3} : Block) ∈ blocksThroughPair T0 0 1 := by
            simp [h01a]
          have h014bp : ({0, 1, 4} : Block) ∈ blocksThroughPair T0 0 1 := by
            simp [h014T]
          exact (three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := 1) (by decide)
            ({0, 1, 2} : Block) ({0, 1, 3} : Block) ({0, 1, 4} : Block)
            h012bp h013bp h014bp (by decide)).elim
        · -- u = 2: blocks `012,023,024` through `02`
          have h024T : ({0, 2, 4} : Block) ∈ T0 := by
            have hmem : ({0, 4, 2} : Block) ∈ T0 := (mem_blocksThroughPair.1 hB).1
            simpa [show ({0, 4, 2} : Block) = ({0, 2, 4} : Block) from by decide] using! hmem
          have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T0 0 2 := by simp [h012]
          have h023bp : ({0, 2, 3} : Block) ∈ blocksThroughPair T0 0 2 := by simp [h02b]
          have h024bp : ({0, 2, 4} : Block) ∈ blocksThroughPair T0 0 2 := by simp [h024T]
          exact (three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := 2) (by decide)
            ({0, 1, 2} : Block) ({0, 2, 3} : Block) ({0, 2, 4} : Block)
            h012bp h023bp h024bp (by decide)).elim
        · -- u = 3: blocks `013,023,034` through `03`
          have h034T : ({0, 3, 4} : Block) ∈ T0 := by
            have hmem : ({0, 4, 3} : Block) ∈ T0 := (mem_blocksThroughPair.1 hB).1
            simpa [show ({0, 4, 3} : Block) = ({0, 3, 4} : Block) from by decide] using! hmem
          have h013bp : ({0, 1, 3} : Block) ∈ blocksThroughPair T0 0 3 := by simp [h01a]
          have h023bp : ({0, 2, 3} : Block) ∈ blocksThroughPair T0 0 3 := by simp [h02b]
          have h034bp : ({0, 3, 4} : Block) ∈ blocksThroughPair T0 0 3 := by simp [h034T]
          exact (three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := 3) (by decide)
            ({0, 1, 3} : Block) ({0, 2, 3} : Block) ({0, 3, 4} : Block)
            h013bp h023bp h034bp (by decide)).elim
        · cases hu4 (by decide)
        · decide
      have hsubset : blocksThroughPair T0 0 4 ⊆ ({({0, 4, 5} : Block)} : Finset Block) :=
        Finset.subset_singleton_iff'.mpr hforced
      have hle : (blocksThroughPair T0 0 4).card ≤ 1 := by
        simpa using! (Finset.card_le_card hsubset)
      have : (blocksThroughPair T0 0 4).card ≠ 2 := by
        have : (blocksThroughPair T0 0 4).card ≤ 1 := hle
        exact ne_of_lt (lt_of_le_of_lt this (by decide : 1 < 2))
      exact this (by simpa using! h04card)
    · -- a = b = 4: symmetric case, use pair `03` (forced to be `035`)
      have h03card : (blocksThroughPair T0 0 3).card = 2 := by
        simpa [blocksThroughPair_card] using! (hT0.2.2 0 3 (by decide))
      have hforced : ∀ B ∈ blocksThroughPair T0 0 3, B = ({0, 3, 5} : Block) := by
        intro B hB
        rcases shape_of_mem_pair T0 hT0 (x := 0) (y := 3) (by decide) hB with ⟨u, hu0, hu3, rfl⟩
        fin_cases u
        · cases hu0 (by decide)
        · -- u = 1: would give three blocks through `01` (012,014,013)
          have h013T : ({0, 1, 3} : Block) ∈ T0 := by
            have hmem : ({0, 3, 1} : Block) ∈ T0 := (mem_blocksThroughPair.1 hB).1
            simpa [show ({0, 3, 1} : Block) = ({0, 1, 3} : Block) from by decide] using! hmem
          have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T0 0 1 := by simp [h012]
          have h014bp : ({0, 1, 4} : Block) ∈ blocksThroughPair T0 0 1 := by simp [h01a]
          have h013bp : ({0, 1, 3} : Block) ∈ blocksThroughPair T0 0 1 := by simp [h013T]
          exact (three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := 1) (by decide)
            ({0, 1, 2} : Block) ({0, 1, 4} : Block) ({0, 1, 3} : Block)
            h012bp h014bp h013bp (by decide)).elim
        · -- u = 2: would give three blocks through `02` (012,024,023)
          have h023T : ({0, 2, 3} : Block) ∈ T0 := by
            have hmem : ({0, 3, 2} : Block) ∈ T0 := (mem_blocksThroughPair.1 hB).1
            simpa [show ({0, 3, 2} : Block) = ({0, 2, 3} : Block) from by decide] using! hmem
          have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T0 0 2 := by simp [h012]
          have h024bp : ({0, 2, 4} : Block) ∈ blocksThroughPair T0 0 2 := by simp [h02b]
          have h023bp : ({0, 2, 3} : Block) ∈ blocksThroughPair T0 0 2 := by simp [h023T]
          exact (three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := 2) (by decide)
            ({0, 1, 2} : Block) ({0, 2, 4} : Block) ({0, 2, 3} : Block)
            h012bp h024bp h023bp (by decide)).elim
        · cases hu3 (by decide)
        · -- u = 4: would give three blocks through `04` (014,024,034)
          have h034T : ({0, 3, 4} : Block) ∈ T0 := by
            simpa using! (mem_blocksThroughPair.1 hB).1
          have h014bp : ({0, 1, 4} : Block) ∈ blocksThroughPair T0 0 4 := by simp [h01a]
          have h024bp : ({0, 2, 4} : Block) ∈ blocksThroughPair T0 0 4 := by simp [h02b]
          have h034bp : ({0, 3, 4} : Block) ∈ blocksThroughPair T0 0 4 := by simp [h034T]
          exact (three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := 4) (by decide)
            ({0, 1, 4} : Block) ({0, 2, 4} : Block) ({0, 3, 4} : Block)
            h014bp h024bp h034bp (by decide)).elim
        · decide
      have hsubset : blocksThroughPair T0 0 3 ⊆ ({({0, 3, 5} : Block)} : Finset Block) := by
        exact Finset.subset_singleton_iff'.mpr hforced
      have hle : (blocksThroughPair T0 0 3).card ≤ 1 := by simpa using! (Finset.card_le_card hsubset)
      have : (blocksThroughPair T0 0 3).card ≠ 2 :=
        ne_of_lt (lt_of_le_of_lt hle (by decide : 1 < 2))
      exact this (by simpa using! h03card)
    · -- a = b = 5: similar, use pair `03` forced to be `034`
      have h03card : (blocksThroughPair T0 0 3).card = 2 := by
        simpa [blocksThroughPair_card] using! (hT0.2.2 0 3 (by decide))
      have hforced : ∀ B ∈ blocksThroughPair T0 0 3, B = ({0, 3, 4} : Block) := by
        intro B hB
        rcases shape_of_mem_pair T0 hT0 (x := 0) (y := 3) (by decide) hB with ⟨u, hu0, hu3, rfl⟩
        fin_cases u
        · cases hu0 (by decide)
        · -- u = 1: would give three blocks through `01` (012,015,013)
          have h013T : ({0, 1, 3} : Block) ∈ T0 := by
            have hmem : ({0, 3, 1} : Block) ∈ T0 := (mem_blocksThroughPair.1 hB).1
            simpa [show ({0, 3, 1} : Block) = ({0, 1, 3} : Block) from by decide] using! hmem
          have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T0 0 1 := by simp [h012]
          have h015bp : ({0, 1, 5} : Block) ∈ blocksThroughPair T0 0 1 := by simp [h01a]
          have h013bp : ({0, 1, 3} : Block) ∈ blocksThroughPair T0 0 1 := by simp [h013T]
          exact (three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := 1) (by decide)
            ({0, 1, 2} : Block) ({0, 1, 5} : Block) ({0, 1, 3} : Block)
            h012bp h015bp h013bp (by decide)).elim
        · -- u = 2: would give three blocks through `02` (012,025,023)
          have h023T : ({0, 2, 3} : Block) ∈ T0 := by
            have hmem : ({0, 3, 2} : Block) ∈ T0 := (mem_blocksThroughPair.1 hB).1
            simpa [show ({0, 3, 2} : Block) = ({0, 2, 3} : Block) from by decide] using! hmem
          have h012bp : ({0, 1, 2} : Block) ∈ blocksThroughPair T0 0 2 := by simp [h012]
          have h025bp : ({0, 2, 5} : Block) ∈ blocksThroughPair T0 0 2 := by simp [h02b]
          have h023bp : ({0, 2, 3} : Block) ∈ blocksThroughPair T0 0 2 := by simp [h023T]
          exact (three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := 2) (by decide)
            ({0, 1, 2} : Block) ({0, 2, 5} : Block) ({0, 2, 3} : Block)
            h012bp h025bp h023bp (by decide)).elim
        · cases hu3 (by decide)
        · decide
        · -- u = 5: would give three blocks through `05` (015,025,035)
          have h035T : ({0, 3, 5} : Block) ∈ T0 := by
            simpa using! (mem_blocksThroughPair.1 hB).1
          have h015bp : ({0, 1, 5} : Block) ∈ blocksThroughPair T0 0 5 := by simp [h01a]
          have h025bp : ({0, 2, 5} : Block) ∈ blocksThroughPair T0 0 5 := by simp [h02b]
          have h035bp : ({0, 3, 5} : Block) ∈ blocksThroughPair T0 0 5 := by simp [h035T]
          exact (three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := 5) (by decide)
            ({0, 1, 5} : Block) ({0, 2, 5} : Block) ({0, 3, 5} : Block)
            h015bp h025bp h035bp (by decide)).elim
      have hsubset : blocksThroughPair T0 0 3 ⊆ ({({0, 3, 4} : Block)} : Finset Block) :=
        Finset.subset_singleton_iff'.mpr hforced
      have hle : (blocksThroughPair T0 0 3).card ≤ 1 := by simpa using! (Finset.card_le_card hsubset)
      have : (blocksThroughPair T0 0 3).card ≠ 2 :=
        ne_of_lt (lt_of_le_of_lt hle (by decide : 1 < 2))
      exact this (by simpa using! h03card)
  have hac : a ≠ c := by
    intro hac
    subst hac
    rcases exists_third_345 (a := a) (b := b) ha345 hb345 hab with ⟨d, hd345, hda, hdb, habd345⟩
    have hd0 : d ≠ 0 := by rcases hd345 with rfl | rfl | rfl <;> decide
    have hd1 : d ≠ 1 := by rcases hd345 with rfl | rfl | rfl <;> decide
    have hd2 : d ≠ 2 := by rcases hd345 with rfl | rfl | rfl <;> decide
    have h0d : (0 : Point) ≠ d := by simpa [eq_comm] using! hd0
    have h2d : (2 : Point) ≠ d := by simpa [eq_comm] using! hd2
    have h12a : ({1, 2, a} : Block) ∈ T0 := by simpa using! h12c
    -- Obtain `{0,d,a}` and `{2,d,a}` as blocks of the design.
    have h0dcard : (blocksThroughPair T0 0 d).card = 2 := by
      simpa [blocksThroughPair_card] using! (hT0.2.2 0 d h0d)
    rcases Finset.card_eq_two.1 h0dcard with ⟨B₁, B₂, hneB, hEqB⟩
    have hB₁ : B₁ ∈ blocksThroughPair T0 0 d := by simp [hEqB]
    have hB₂ : B₂ ∈ blocksThroughPair T0 0 d := by simp [hEqB]
    rcases third_eq_a_or_b_of_mem_blocksThroughPair_0d (T := T0) hT0 (a := a) (b := b) (d := d)
        hd345 habd345 hda hdb ha0 ha1 ha2 hb0 hb1 hb2 h012 h01a h02b hB₁ with
      ⟨u₁, hu₁ab, hB₁eq⟩
    rcases third_eq_a_or_b_of_mem_blocksThroughPair_0d (T := T0) hT0 (a := a) (b := b) (d := d)
        hd345 habd345 hda hdb ha0 ha1 ha2 hb0 hb1 hb2 h012 h01a h02b hB₂ with
      ⟨u₂, hu₂ab, hB₂eq⟩
    have hB₁T : B₁ ∈ T0 := (mem_blocksThroughPair.1 hB₁).1
    have hB₂T : B₂ ∈ T0 := (mem_blocksThroughPair.1 hB₂).1
    have hu₁T : ({0, d, u₁} : Block) ∈ T0 := by simpa [hB₁eq] using! hB₁T
    have hu₂T : ({0, d, u₂} : Block) ∈ T0 := by simpa [hB₂eq] using! hB₂T
    have hneU : u₁ ≠ u₂ := by
      intro h
      exact hneB (by simp [hB₁eq, hB₂eq, h])
    have h0daT : ({0, d, a} : Block) ∈ T0 := by
      rcases hu₁ab with rfl | rfl
      · simpa using! hu₁T
      · have : u₂ = a := by
          rcases hu₂ab with h | h
          · exact h
          · exact (hneU (by simp [h])).elim
        simpa [this] using! hu₂T
    have h2dcard : (blocksThroughPair T0 2 d).card = 2 := by
      simpa [blocksThroughPair_card] using! (hT0.2.2 2 d h2d)
    rcases Finset.card_eq_two.1 h2dcard with ⟨C₁, C₂, hneC, hEqC⟩
    have hC₁ : C₁ ∈ blocksThroughPair T0 2 d := by simp [hEqC]
    have hC₂ : C₂ ∈ blocksThroughPair T0 2 d := by simp [hEqC]
    rcases third_eq_a_or_b_of_mem_blocksThroughPair_2d (T := T0) hT0 (a := a) (b := b) (d := d)
        hd345 habd345 hda hdb ha0 ha1 ha2 hb0 hb1 hb2 h012 h02b h12a hC₁ with
      ⟨v₁, hv₁ab, hC₁eq⟩
    rcases third_eq_a_or_b_of_mem_blocksThroughPair_2d (T := T0) hT0 (a := a) (b := b) (d := d)
        hd345 habd345 hda hdb ha0 ha1 ha2 hb0 hb1 hb2 h012 h02b h12a hC₂ with
      ⟨v₂, hv₂ab, hC₂eq⟩
    have hC₁T : C₁ ∈ T0 := (mem_blocksThroughPair.1 hC₁).1
    have hC₂T : C₂ ∈ T0 := (mem_blocksThroughPair.1 hC₂).1
    have hv₁T : ({2, d, v₁} : Block) ∈ T0 := by simpa [hC₁eq] using! hC₁T
    have hv₂T : ({2, d, v₂} : Block) ∈ T0 := by simpa [hC₂eq] using! hC₂T
    have hneV : v₁ ≠ v₂ := by
      intro h
      exact hneC (by simp [hC₁eq, hC₂eq, h])
    have h2daT : ({2, d, a} : Block) ∈ T0 := by
      rcases hv₁ab with rfl | rfl
      · simpa using! hv₁T
      · have : v₂ = a := by
          rcases hv₂ab with h | h
          · exact h
          · exact (hneV (by simp [h])).elim
        simpa [this] using! hv₂T
    -- Contradict `pairCount {a,b} = 2` by ruling out any third point.
    have habcard : (blocksThroughPair T0 a b).card = 2 := by
      simpa [blocksThroughPair_card] using! (hT0.2.2 a b hab)
    have habpos : 0 < (blocksThroughPair T0 a b).card := by simp [habcard]
    rcases Finset.card_pos.1 habpos with ⟨B, hB⟩
    have hBT : B ∈ T0 := (mem_blocksThroughPair.1 hB).1
    rcases shape_of_mem_pair T0 hT0 (x := a) (y := b) hab hB with ⟨u, hua, hub, rfl⟩
    fin_cases u
    · -- u = 0: three blocks through `{0,a}`
      have h0abT : ({a, b, 0} : Block) ∈ T0 := by simpa using! hBT
      have h01abp : ({0, 1, a} : Block) ∈ blocksThroughPair T0 0 a := by simp [h01a]
      have h0dabp : ({0, d, a} : Block) ∈ blocksThroughPair T0 0 a := by simp [h0daT]
      have h0abp : ({a, b, 0} : Block) ∈ blocksThroughPair T0 0 a := by simp [h0abT]
      have hcard3 :
          ({({0,1,a} : Block), ({0,d,a} : Block), ({a,b,0} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, ha1, hd1])
        · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, ha1, hb1])
        · refine block_ne_of_mem_not_mem (x := d) (by simp) ?_
          simp [hd0, hda, hdb]
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := a) ha0.symm
        ({0, 1, a} : Block) ({0, d, a} : Block) ({a, b, 0} : Block)
        h01abp h0dabp h0abp hcard3
    · -- u = 1: three blocks through `{1,a}`
      have h1abT : ({a, b, 1} : Block) ∈ T0 := by simpa using! hBT
      have h01abp : ({0, 1, a} : Block) ∈ blocksThroughPair T0 1 a := by simp [h01a]
      have h12abp : ({1, 2, a} : Block) ∈ blocksThroughPair T0 1 a := by simp [h12a]
      have h1abp : ({a, b, 1} : Block) ∈ blocksThroughPair T0 1 a := by simp [h1abT]
      have hcard3 :
          ({({0,1,a} : Block), ({1,2,a} : Block), ({a,b,1} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0])
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0, hb0])
        · refine block_ne_of_mem_not_mem (x := 2) (by simp) ?_
          simp [eq_comm, ha2, hb2]
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := 1) (y := a) ha1.symm
        ({0, 1, a} : Block) ({1, 2, a} : Block) ({a, b, 1} : Block)
        h01abp h12abp h1abp hcard3
    · -- u = 2: three blocks through `{2,a}`
      have h2abT : ({a, b, 2} : Block) ∈ T0 := by simpa using! hBT
      have h12abp : ({1, 2, a} : Block) ∈ blocksThroughPair T0 2 a := by simp [h12a]
      have h2dabp : ({2, d, a} : Block) ∈ blocksThroughPair T0 2 a := by simp [h2daT]
      have h2abp : ({a, b, 2} : Block) ∈ blocksThroughPair T0 2 a := by simp [h2abT]
      have hcard3 :
          ({({1,2,a} : Block), ({2,d,a} : Block), ({a,b,2} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, ha1, hd1])
        · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, ha1, hb1])
        · refine block_ne_of_mem_not_mem (x := d) (by simp) ?_
          simp [hd2, hda, hdb]
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := 2) (y := a) ha2.symm
        ({1, 2, a} : Block) ({2, d, a} : Block) ({a, b, 2} : Block)
        h12abp h2dabp h2abp hcard3
    · -- u = 3: then `u = d`, giving three blocks through `{a,d}`
      have huMemABD : (3 : Point) ∈ ({a, b, d} : Finset Point) := by simp [habd345]
      have huABD : (3 : Point) = a ∨ (3 : Point) = b ∨ (3 : Point) = d := by simpa using! huMemABD
      have hud : (3 : Point) = d := by
        rcases huABD with h | h | h
        · exact (hua h).elim
        · exact (hub h).elim
        · exact h
      subst hud
      have h0dabp : ({0, 3, a} : Block) ∈ blocksThroughPair T0 a 3 := by simp [h0daT]
      have h2dabp : ({2, 3, a} : Block) ∈ blocksThroughPair T0 a 3 := by simp [h2daT]
      have habdT : ({a, b, 3} : Block) ∈ T0 := by simpa using! hBT
      have habdbp : ({a, b, 3} : Block) ∈ blocksThroughPair T0 a 3 := by simp [habdT]
      have hcard3 :
          ({({0,3,a} : Block), ({2,3,a} : Block), ({a,b,3} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0])
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0, hb0])
        · exact block_ne_of_mem_not_mem (x := 2) (by simp) (by simp [eq_comm, ha2, hb2])
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := a) (y := 3) hda.symm
        ({0, 3, a} : Block) ({2, 3, a} : Block) ({a, b, 3} : Block)
        h0dabp h2dabp habdbp hcard3
    · -- u = 4: same as u = 3
      have huMemABD : (4 : Point) ∈ ({a, b, d} : Finset Point) := by simp [habd345]
      have huABD : (4 : Point) = a ∨ (4 : Point) = b ∨ (4 : Point) = d := by simpa using! huMemABD
      have hud : (4 : Point) = d := by
        rcases huABD with h | h | h
        · exact (hua h).elim
        · exact (hub h).elim
        · exact h
      subst hud
      have h0dabp : ({0, 4, a} : Block) ∈ blocksThroughPair T0 a 4 := by simp [h0daT]
      have h2dabp : ({2, 4, a} : Block) ∈ blocksThroughPair T0 a 4 := by simp [h2daT]
      have habdT : ({a, b, 4} : Block) ∈ T0 := by simpa using! hBT
      have habdbp : ({a, b, 4} : Block) ∈ blocksThroughPair T0 a 4 := by simp [habdT]
      have hcard3 :
          ({({0,4,a} : Block), ({2,4,a} : Block), ({a,b,4} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0])
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0, hb0])
        · exact block_ne_of_mem_not_mem (x := 2) (by simp) (by simp [eq_comm, ha2, hb2])
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := a) (y := 4) hda.symm
        ({0, 4, a} : Block) ({2, 4, a} : Block) ({a, b, 4} : Block)
        h0dabp h2dabp habdbp hcard3
    · -- u = 5: same as u = 3
      have huMemABD : (5 : Point) ∈ ({a, b, d} : Finset Point) := by simp [habd345]
      have huABD : (5 : Point) = a ∨ (5 : Point) = b ∨ (5 : Point) = d := by simpa using! huMemABD
      have hud : (5 : Point) = d := by
        rcases huABD with h | h | h
        · exact (hua h).elim
        · exact (hub h).elim
        · exact h
      subst hud
      have h0dabp : ({0, 5, a} : Block) ∈ blocksThroughPair T0 a 5 := by simp [h0daT]
      have h2dabp : ({2, 5, a} : Block) ∈ blocksThroughPair T0 a 5 := by simp [h2daT]
      have habdT : ({a, b, 5} : Block) ∈ T0 := by simpa using! hBT
      have habdbp : ({a, b, 5} : Block) ∈ blocksThroughPair T0 a 5 := by simp [habdT]
      have hcard3 :
          ({({0,5,a} : Block), ({2,5,a} : Block), ({a,b,5} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0])
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0, hb0])
        · exact block_ne_of_mem_not_mem (x := 2) (by simp) (by simp [eq_comm, ha2, hb2])
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := a) (y := 5) hda.symm
        ({0, 5, a} : Block) ({2, 5, a} : Block) ({a, b, 5} : Block)
        h0dabp h2dabp habdbp hcard3
  have hbc : b ≠ c := by
    intro hbc
    subst hbc
    rcases exists_third_345 (a := a) (b := b) ha345 hb345 hab with ⟨d, hd345, hda, hdb, habd345⟩
    have hd0 : d ≠ 0 := by rcases hd345 with rfl | rfl | rfl <;> decide
    have hd1 : d ≠ 1 := by rcases hd345 with rfl | rfl | rfl <;> decide
    have hd2 : d ≠ 2 := by rcases hd345 with rfl | rfl | rfl <;> decide
    have h0d : (0 : Point) ≠ d := hd0.symm
    have h1d : (1 : Point) ≠ d := hd1.symm
    have h12b : ({1, 2, b} : Block) ∈ T0 := by simpa using! h12c
    -- Get `{0,d,a}` and `{1,d,a}` as blocks.
    have h0dcard : (blocksThroughPair T0 0 d).card = 2 := by
      simpa [blocksThroughPair_card] using! (hT0.2.2 0 d h0d)
    rcases Finset.card_eq_two.1 h0dcard with ⟨B₁, B₂, hneB, hEqB⟩
    have hB₁ : B₁ ∈ blocksThroughPair T0 0 d := by simp [hEqB]
    have hB₂ : B₂ ∈ blocksThroughPair T0 0 d := by simp [hEqB]
    rcases third_eq_a_or_b_of_mem_blocksThroughPair_0d (T := T0) hT0 (a := a) (b := b) (d := d)
        hd345 habd345 hda hdb ha0 ha1 ha2 hb0 hb1 hb2 h012 h01a h02b hB₁ with
      ⟨u₁, hu₁ab, hB₁eq⟩
    rcases third_eq_a_or_b_of_mem_blocksThroughPair_0d (T := T0) hT0 (a := a) (b := b) (d := d)
        hd345 habd345 hda hdb ha0 ha1 ha2 hb0 hb1 hb2 h012 h01a h02b hB₂ with
      ⟨u₂, hu₂ab, hB₂eq⟩
    have hB₁T : B₁ ∈ T0 := (mem_blocksThroughPair.1 hB₁).1
    have hB₂T : B₂ ∈ T0 := (mem_blocksThroughPair.1 hB₂).1
    have hu₁T : ({0, d, u₁} : Block) ∈ T0 := by simpa [hB₁eq] using! hB₁T
    have hu₂T : ({0, d, u₂} : Block) ∈ T0 := by simpa [hB₂eq] using! hB₂T
    have hneU : u₁ ≠ u₂ := by
      intro h
      exact hneB (by simp [hB₁eq, hB₂eq, h])
    have h0daT : ({0, d, a} : Block) ∈ T0 := by
      rcases hu₁ab with rfl | rfl
      · simpa using! hu₁T
      · have : u₂ = a := by
          rcases hu₂ab with h | h
          · exact h
          · exact (hneU (by simp [h])).elim
        simpa [this] using! hu₂T
    have h1dcard : (blocksThroughPair T0 1 d).card = 2 := by
      simpa [blocksThroughPair_card] using! (hT0.2.2 1 d h1d)
    rcases Finset.card_eq_two.1 h1dcard with ⟨C₁, C₂, hneC, hEqC⟩
    have hC₁ : C₁ ∈ blocksThroughPair T0 1 d := by simp [hEqC]
    have hC₂ : C₂ ∈ blocksThroughPair T0 1 d := by simp [hEqC]
    rcases third_eq_a_or_b_of_mem_blocksThroughPair_1d (T := T0) hT0 (a := a) (b := b) (d := d)
        hd345 habd345 hda hdb ha0 ha1 ha2 hb0 hb1 hb2 h012 h01a h12b hC₁ with
      ⟨v₁, hv₁ab, hC₁eq⟩
    rcases third_eq_a_or_b_of_mem_blocksThroughPair_1d (T := T0) hT0 (a := a) (b := b) (d := d)
        hd345 habd345 hda hdb ha0 ha1 ha2 hb0 hb1 hb2 h012 h01a h12b hC₂ with
      ⟨v₂, hv₂ab, hC₂eq⟩
    have hC₁T : C₁ ∈ T0 := (mem_blocksThroughPair.1 hC₁).1
    have hC₂T : C₂ ∈ T0 := (mem_blocksThroughPair.1 hC₂).1
    have hv₁T : ({1, d, v₁} : Block) ∈ T0 := by simpa [hC₁eq] using! hC₁T
    have hv₂T : ({1, d, v₂} : Block) ∈ T0 := by simpa [hC₂eq] using! hC₂T
    have hneV : v₁ ≠ v₂ := by
      intro h
      exact hneC (by simp [hC₁eq, hC₂eq, h])
    have h1daT : ({1, d, a} : Block) ∈ T0 := by
      rcases hv₁ab with rfl | rfl
      · simpa using! hv₁T
      · have : v₂ = a := by
          rcases hv₂ab with h | h
          · exact h
          · exact (hneV (by simp [h])).elim
        simpa [this] using! hv₂T
    -- Contradict `pairCount {a,b} = 2`.
    have habcard : (blocksThroughPair T0 a b).card = 2 := by
      simpa [blocksThroughPair_card] using! (hT0.2.2 a b hab)
    have habpos : 0 < (blocksThroughPair T0 a b).card := by simp [habcard]
    rcases Finset.card_pos.1 habpos with ⟨B, hB⟩
    have hBT : B ∈ T0 := (mem_blocksThroughPair.1 hB).1
    rcases shape_of_mem_pair T0 hT0 (x := a) (y := b) hab hB with ⟨u, hua, hub, rfl⟩
    fin_cases u
    · -- u = 0: three blocks through `{0,a}`
      have h0abT : ({a, b, 0} : Block) ∈ T0 := by simpa using! hBT
      have h01abp : ({0, 1, a} : Block) ∈ blocksThroughPair T0 0 a := by simp [h01a]
      have h0dabp : ({0, d, a} : Block) ∈ blocksThroughPair T0 0 a := by simp [h0daT]
      have h0abp : ({a, b, 0} : Block) ∈ blocksThroughPair T0 0 a := by simp [h0abT]
      have hcard3 :
          ({({0,1,a} : Block), ({0,d,a} : Block), ({a,b,0} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, ha1, hd1])
        · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, ha1, hb1])
        · refine block_ne_of_mem_not_mem (x := d) (by simp) ?_
          simp [hd0, hda, hdb]
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := 0) (y := a) ha0.symm
        ({0, 1, a} : Block) ({0, d, a} : Block) ({a, b, 0} : Block)
        h01abp h0dabp h0abp hcard3
    · -- u = 1: three blocks through `{1,a}`
      have h1abT : ({a, b, 1} : Block) ∈ T0 := by simpa using! hBT
      have h01abp : ({0, 1, a} : Block) ∈ blocksThroughPair T0 1 a := by simp [h01a]
      have h1dabp : ({1, d, a} : Block) ∈ blocksThroughPair T0 1 a := by simp [h1daT]
      have h1abp : ({a, b, 1} : Block) ∈ blocksThroughPair T0 1 a := by simp [h1abT]
      have hcard3 :
          ({({0,1,a} : Block), ({1,d,a} : Block), ({a,b,1} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0, hd0])
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0, hb0])
        · refine block_ne_of_mem_not_mem (x := d) (by simp) ?_
          simp [hda, hdb, hd1]
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := 1) (y := a) ha1.symm
        ({0, 1, a} : Block) ({1, d, a} : Block) ({a, b, 1} : Block)
        h01abp h1dabp h1abp hcard3
    · -- u = 2: three blocks through `{2,b}`
      have h2bbT : ({a, b, 2} : Block) ∈ T0 := by simpa using! hBT
      have h02bbp : ({0, 2, b} : Block) ∈ blocksThroughPair T0 2 b := by simp [h02b]
      have h12bbp : ({1, 2, b} : Block) ∈ blocksThroughPair T0 2 b := by simp [h12b]
      have h2bbp : ({a, b, 2} : Block) ∈ blocksThroughPair T0 2 b := by simp [h2bbT]
      have hcard3 :
          ({({0,2,b} : Block), ({1,2,b} : Block), ({a,b,2} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, hb0])
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0, hb0])
        · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, ha1, hb1])
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := 2) (y := b) hb2.symm
        ({0, 2, b} : Block) ({1, 2, b} : Block) ({a, b, 2} : Block)
        h02bbp h12bbp h2bbp hcard3
    · -- u = 3: then `u = d`, giving three blocks through `{a,d}`
      have huMemABD : (3 : Point) ∈ ({a, b, d} : Finset Point) := by simp [habd345]
      have huABD : (3 : Point) = a ∨ (3 : Point) = b ∨ (3 : Point) = d := by simpa using! huMemABD
      have hud : (3 : Point) = d := by
        rcases huABD with h | h | h
        · exact (hua h).elim
        · exact (hub h).elim
        · exact h
      subst hud
      have h0dabp : ({0, 3, a} : Block) ∈ blocksThroughPair T0 a 3 := by simp [h0daT]
      have h1dabp : ({1, 3, a} : Block) ∈ blocksThroughPair T0 a 3 := by simp [h1daT]
      have habdT : ({a, b, 3} : Block) ∈ T0 := by simpa using! hBT
      have habdbp : ({a, b, 3} : Block) ∈ blocksThroughPair T0 a 3 := by simp [habdT]
      have hcard3 :
          ({({0,3,a} : Block), ({1,3,a} : Block), ({a,b,3} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0])
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0, hb0])
        · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, ha1, hb1])
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := a) (y := 3) hda.symm
        ({0, 3, a} : Block) ({1, 3, a} : Block) ({a, b, 3} : Block)
        h0dabp h1dabp habdbp hcard3
    · -- u = 4: same as u = 3
      have huMemABD : (4 : Point) ∈ ({a, b, d} : Finset Point) := by simp [habd345]
      have huABD : (4 : Point) = a ∨ (4 : Point) = b ∨ (4 : Point) = d := by simpa using! huMemABD
      have hud : (4 : Point) = d := by
        rcases huABD with h | h | h
        · exact (hua h).elim
        · exact (hub h).elim
        · exact h
      subst hud
      have h0dabp : ({0, 4, a} : Block) ∈ blocksThroughPair T0 a 4 := by simp [h0daT]
      have h1dabp : ({1, 4, a} : Block) ∈ blocksThroughPair T0 a 4 := by simp [h1daT]
      have habdT : ({a, b, 4} : Block) ∈ T0 := by simpa using! hBT
      have habdbp : ({a, b, 4} : Block) ∈ blocksThroughPair T0 a 4 := by simp [habdT]
      have hcard3 :
          ({({0,4,a} : Block), ({1,4,a} : Block), ({a,b,4} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0])
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0, hb0])
        · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, ha1, hb1])
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := a) (y := 4) hda.symm
        ({0, 4, a} : Block) ({1, 4, a} : Block) ({a, b, 4} : Block)
        h0dabp h1dabp habdbp hcard3
    · -- u = 5: same as u = 3
      have huMemABD : (5 : Point) ∈ ({a, b, d} : Finset Point) := by simp [habd345]
      have huABD : (5 : Point) = a ∨ (5 : Point) = b ∨ (5 : Point) = d := by simpa using! huMemABD
      have hud : (5 : Point) = d := by
        rcases huABD with h | h | h
        · exact (hua h).elim
        · exact (hub h).elim
        · exact h
      subst hud
      have h0dabp : ({0, 5, a} : Block) ∈ blocksThroughPair T0 a 5 := by simp [h0daT]
      have h1dabp : ({1, 5, a} : Block) ∈ blocksThroughPair T0 a 5 := by simp [h1daT]
      have habdT : ({a, b, 5} : Block) ∈ T0 := by simpa using! hBT
      have habdbp : ({a, b, 5} : Block) ∈ blocksThroughPair T0 a 5 := by simp [habdT]
      have hcard3 :
          ({({0,5,a} : Block), ({1,5,a} : Block), ({a,b,5} : Block)} : Finset Block).card = 3 := by
        refine card_three_blocks ?_ ?_ ?_
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0])
        · exact block_ne_of_mem_not_mem (x := 0) (by simp) (by simp [eq_comm, ha0, hb0])
        · exact block_ne_of_mem_not_mem (x := 1) (by simp) (by simp [eq_comm, ha1, hb1])
      exact three_blocks_through_pair_contra (T := T0) hT0 (x := a) (y := 5) hda.symm
        ({0, 5, a} : Block) ({1, 5, a} : Block) ({a, b, 5} : Block)
        h0dabp h1dabp habdbp hcard3
  rcases exists_perm_fix012_send_abc (a := a) (b := b) (c := c) ha345 hb345 hc345 hab hac hbc with
    ⟨τ, hτ0, hτ1, hτ2, hτa, hτb, hτc⟩
  let T1 : Finset Block := mapDesign τ T0
  have hT1 : Is23632 T1 := Is23632.map (T := T0) hT0 τ
  have h012T1 : ({0, 1, 2} : Block) ∈ T1 := by
    refine (mem_mapDesign (σ := τ) (T := T0) (B := ({0, 1, 2} : Block))).2 ?_
    refine ⟨({0, 1, 2} : Block), h012, ?_⟩
    ext t
    fin_cases t <;> simp [hτ0, hτ1, hτ2]
  have h014T1 : ({0, 1, 4} : Block) ∈ T1 := by
    refine (mem_mapDesign (σ := τ) (T := T0) (B := ({0, 1, 4} : Block))).2 ?_
    refine ⟨({0, 1, a} : Block), h01a, ?_⟩
    ext t
    fin_cases t <;> simp [hτ0, hτ1, hτa]
  have h023T1 : ({0, 2, 3} : Block) ∈ T1 := by
    refine (mem_mapDesign (σ := τ) (T := T0) (B := ({0, 2, 3} : Block))).2 ?_
    refine ⟨({0, 2, b} : Block), h02b, ?_⟩
    ext t
    fin_cases t <;> simp [hτ0, hτ2, hτb]
  have h125T1 : ({1, 2, 5} : Block) ∈ T1 := by
    refine (mem_mapDesign (σ := τ) (T := T0) (B := ({1, 2, 5} : Block))).2 ?_
    refine ⟨({1, 2, c} : Block), h12c, ?_⟩
    -- Compute the image of `{1,2,c}` under `τ`.
    simp [Finset.map_insert, Finset.map_singleton, hτ1, hτ2, hτc]
  have hT1eq : T1 = canonicalBlocks :=
    forced_of_initial_blocks (T := T1) hT1 h012T1 h014T1 h023T1 h125T1
  refine ⟨σ0.trans τ, ?_⟩
  simpa [T0, T1, mapDesign_trans] using! hT1eq

end Design23632

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
