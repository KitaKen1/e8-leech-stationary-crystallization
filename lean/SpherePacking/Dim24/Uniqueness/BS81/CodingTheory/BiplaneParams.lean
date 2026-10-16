-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.BiplaneBasic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Parameters of the `2-(11,5,2)` biplane

This file formalizes the argument in the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`, Lemma `biplane_from_intersections`.

Starting from a family of `11` blocks of size `5` on `11` points with constant pairwise
intersection size `2`, we prove:
- each point lies in exactly `5` blocks, and
- each pair of distinct points lies in exactly `2` blocks.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open scoped BigOperators

namespace Biplane.Structure

open Finset

variable (D : Structure)

lemma blocks_erase_card (B : Block) (hB : B ∈ D.blocks) :
    (D.blocks.erase B).card = 10 := by
  have hcard : D.blocks.card = 11 := D.blocks_card
  simp [Finset.card_erase_of_mem hB, hcard]

lemma sum_intersections_with_block (B : Block) (hB : B ∈ D.blocks) :
    (∑ B' ∈ D.blocks.erase B, (B ∩ B').card) = 20 := by
  have hterm : ∀ B' ∈ D.blocks.erase B, (B ∩ B').card = 2 := by
    intro B' hB'
    have hB'mem : B' ∈ D.blocks := (Finset.mem_erase.mp hB').2
    have hne : B' ≠ B := (Finset.mem_erase.mp hB').1
    simpa [Finset.inter_comm] using! D.inter_card (B := B) (B' := B') hB hB'mem (Ne.symm hne)
  calc
    (∑ B' ∈ D.blocks.erase B, (B ∩ B').card) = ∑ _B' ∈ D.blocks.erase B, 2 := by
      exact sum_congr rfl hterm
    _ = (D.blocks.erase B).card * 2 := by simp
    _ = 20 := by simp [blocks_erase_card (D := D) (B := B) hB]

lemma sum_intersections_row (B : Block) (hB : B ∈ D.blocks) :
    (∑ B' ∈ D.blocks, (B ∩ B').card) = 25 := by
  have hsplit :
      (∑ B' ∈ D.blocks, (B ∩ B').card) =
        (B ∩ B).card + ∑ B' ∈ D.blocks.erase B, (B ∩ B').card := by
    simpa [add_comm, add_left_comm, add_assoc] using!
      (D.blocks.add_sum_erase (a := B) (f := fun B' => (B ∩ B').card) hB).symm
  have hoff : (∑ B' ∈ D.blocks.erase B, (B ∩ B').card) = 20 :=
    sum_intersections_with_block (D := D) (B := B) hB
  have hBcard : B.card = 5 := D.block_card B hB
  calc
    (∑ B' ∈ D.blocks, (B ∩ B').card)
        = (B ∩ B).card + ∑ B' ∈ D.blocks.erase B, (B ∩ B').card := hsplit
    _ = 5 + 20 := by simp [Finset.inter_self, hBcard, hoff]
    _ = 25 := by decide

lemma card_inter_eq_sum_indicator (B B' : Block) :
    (B ∩ B').card = ∑ x : Point, (if x ∈ B ∧ x ∈ B' then 1 else 0) := by
  have hfilter : (Finset.univ.filter fun x : Point => x ∈ B ∩ B') = (B ∩ B') := by
    ext x
    simp [Finset.mem_inter]
  simp_all

lemma sum_sq_filterCard_eq_sum_intersections (S : Finset Block) :
    (∑ x : Point, ((S.filter fun B => x ∈ B).card) ^ 2) =
      ∑ B ∈ S, ∑ B' ∈ S, (B ∩ B').card := by
  -- Use dependent sum-commutation (`Finset.sum_comm'`) to avoid expanding indicator algebra.
  let U : Finset Point := Finset.univ
  let T : Point → Finset Block := fun x => S.filter fun B : Block => x ∈ B
  -- switch the outer `Fintype` sum to an explicit `Finset.univ` sum
  change U.sum (fun x : Point => ((T x).card) ^ 2) = ∑ B ∈ S, ∑ B' ∈ S, (B ∩ B').card
  -- expand the square as a double sum over blocks through `x`
  have hsq :
      ∀ x : Point, ((T x).card) ^ 2 = ∑ B ∈ T x, ∑ B' ∈ T x, (1 : ℕ) := by
    intro x
    -- `card^2 = (∑ 1) * (∑ 1) = ∑∑ 1`
    calc
      ((T x).card) ^ 2 = (∑ _B ∈ T x, (1 : ℕ)) ^ 2 := by
        exact congrArg (fun n : ℕ => n ^ 2) (Finset.card_eq_sum_ones (s := (T x)))
      _ = (∑ _B ∈ T x, (1 : ℕ)) * (∑ _B' ∈ T x, (1 : ℕ)) := by
        simp [pow_two]
      _ = ∑ B ∈ T x, ∑ B' ∈ T x, (1 : ℕ) := by
        simp
  -- rewrite using `hsq`
  have hL :
      U.sum (fun x : Point => ((T x).card) ^ 2) =
        ∑ x ∈ U, ∑ B ∈ T x, ∑ B' ∈ T x, (1 : ℕ) := by
    -- everything is already a finset sum; just expand with `hsq`
    simp [hsq, U]
  -- swap `x` and the first block using `sum_comm'`
  have hswap₁ :
      (∑ x ∈ U, ∑ B ∈ T x, ∑ B' ∈ T x, (1 : ℕ)) =
        ∑ B ∈ S, ∑ x ∈ B, ∑ B' ∈ T x, (1 : ℕ) := by
    -- `x ∈ univ` and `B ∈ T x` is the same as `x ∈ B` and `B ∈ S`
    have hmem :
        ∀ (x : Point) (B : Block),
          x ∈ U ∧ B ∈ T x ↔ x ∈ B ∧ B ∈ S := by
      intro x B
      constructor
      · intro h
        have h' : B ∈ S ∧ x ∈ B := by
          simpa [U, T, and_assoc] using! h
        exact ⟨h'.2, h'.1⟩
      · intro h
        have h' : B ∈ S ∧ x ∈ B := ⟨h.2, h.1⟩
        simpa [U, T, and_assoc] using! h'
    -- apply dependent commutation
    exact sum_comm' hmem
  -- swap `x` and the second block inside each fixed `B`
  have hswap₂ :
      (∑ B ∈ S, ∑ x ∈ B, ∑ B' ∈ T x, (1 : ℕ)) =
        ∑ B ∈ S, ∑ B' ∈ S, ∑ x ∈ B ∩ B', (1 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro B hB
    -- `x ∈ B` and `B' ∈ T x` is the same as `x ∈ B ∩ B'` and `B' ∈ S`
    have hmem :
        ∀ (x : Point) (B' : Block),
          x ∈ B ∧ B' ∈ T x ↔ x ∈ (B ∩ B') ∧ B' ∈ S := by
      intro x B'
      constructor
      · intro h
        have hB' : B' ∈ S ∧ x ∈ B' := by
          simpa [T, and_assoc] using! h.2
        refine ⟨?_, hB'.1⟩
        -- membership in the intersection
        exact Finset.mem_inter.2 ⟨h.1, hB'.2⟩
      · intro h
        have hxB : x ∈ B := (Finset.mem_inter.1 h.1).1
        have hxB' : x ∈ B' := (Finset.mem_inter.1 h.1).2
        refine ⟨hxB, ?_⟩
        -- `B' ∈ T x`
        simp [T, h.2, hxB']
    exact sum_comm' hmem
  -- finish: `∑ 1 = card`
  have hcard :
      (∑ B ∈ S, ∑ B' ∈ S, ∑ x ∈ B ∩ B', (1 : ℕ)) =
        ∑ B ∈ S, ∑ B' ∈ S, (B ∩ B').card := by
    refine Finset.sum_congr rfl ?_
    intro B hB
    refine Finset.sum_congr rfl ?_
    intro B' hB'
    exact (Finset.card_eq_sum_ones (s := (B ∩ B'))).symm
  -- chain everything together
  calc
    U.sum (fun x : Point => ((T x).card) ^ 2)
        = ∑ x ∈ U, ∑ B ∈ T x, ∑ B' ∈ T x, (1 : ℕ) := hL
    _ = ∑ B ∈ S, ∑ x ∈ B, ∑ B' ∈ T x, (1 : ℕ) := hswap₁
    _ = ∑ B ∈ S, ∑ B' ∈ S, ∑ x ∈ B ∩ B', (1 : ℕ) := hswap₂
    _ = ∑ B ∈ S, ∑ B' ∈ S, (B ∩ B').card := hcard

lemma sum_r_sq_eq_275 : (∑ x : Point, (D.r x) ^ 2) = 275 := by
  have hdc :
      (∑ x : Point, (D.r x) ^ 2) =
        ∑ B ∈ D.blocks, ∑ B' ∈ D.blocks, (B ∩ B').card := by
    -- unfold `r` and use the generic identity
    simpa [Biplane.Structure.r] using!
      (sum_sq_filterCard_eq_sum_intersections (S := D.blocks))
  have hrow : ∀ B ∈ D.blocks, (∑ B' ∈ D.blocks, (B ∩ B').card) = 25 := by
    intro B hB
    exact sum_intersections_row (D := D) (B := B) hB
  calc
    (∑ x : Point, (D.r x) ^ 2) = ∑ B ∈ D.blocks, ∑ B' ∈ D.blocks, (B ∩ B').card := hdc
    _ = ∑ B ∈ D.blocks, 25 := by
          exact sum_congr rfl hrow
    _ = D.blocks.card * 25 := by simp
    _ = 275 := by simp [D.blocks_card]

/-!
## Constant point and pair counts
-/

private lemma sum_sq_sub_const {α : Type} (S : Finset α) (f : α → ℤ) (c : ℤ) :
    (∑ x ∈ S, (f x - c) ^ 2) =
      (∑ x ∈ S, (f x) ^ 2) - (2 * c) * (∑ x ∈ S, f x) + (S.card : ℤ) * c ^ 2 := by
  calc
    (∑ x ∈ S, (f x - c) ^ 2) = ∑ x ∈ S, ((f x) ^ 2 - (2 * c) * f x + c ^ 2) := by
      refine sum_congr rfl ?_
      intro y hy
      ring
    _ = (∑ x ∈ S, ((f x) ^ 2 - (2 * c) * f x)) + ∑ _x ∈ S, c ^ 2 := by
          simp [sum_add_distrib]
    _ = ((∑ x ∈ S, (f x) ^ 2) - ∑ x ∈ S, (2 * c) * f x) + (S.card : ℤ) * c ^ 2 := by
          simp [sum_sub_distrib]
    _ = ((∑ x ∈ S, (f x) ^ 2) - (2 * c) * (∑ x ∈ S, f x)) + (S.card : ℤ) * c ^ 2 := by
          simp [mul_sum]
    _ = (∑ x ∈ S, (f x) ^ 2) - (2 * c) * (∑ x ∈ S, f x) + (S.card : ℤ) * c ^ 2 := by
          ring

/-- Each point of the biplane lies in exactly `5` blocks. -/
public theorem r_eq_five (x : Point) : D.r x = 5 := by
  have hsum_r : (∑ x : Point, (D.r x : ℤ)) = 55 := by
    simpa using! congrArg (fun n : ℕ => (n : ℤ)) (sum_r_eq_55 (D := D))
  have hsum_rsq : (∑ x : Point, (D.r x : ℤ) ^ 2) = 275 := by
    have := sum_r_sq_eq_275 (D := D)
    simpa using! congrArg (fun n : ℕ => (n : ℤ)) this
  have hvar : (∑ x : Point, ((D.r x : ℤ) - 5) ^ 2) = 0 := by
    have hcard : ((Finset.univ : Finset Point).card : ℤ) = 11 := by simp [Biplane.Point]
    have hrewrite :
        (∑ x : Point, ((D.r x : ℤ) - 5) ^ 2) =
          (∑ x : Point, (D.r x : ℤ) ^ 2) - (10 : ℤ) * (∑ x : Point, (D.r x : ℤ)) +
            (11 : ℤ) * 25 := by
      simpa [pow_two, hcard, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
        (sum_sq_sub_const (S := Finset.univ) (f := fun y => (D.r y : ℤ)) (c := 5))
    have hnum : (275 : ℤ) - (10 : ℤ) * 55 + (11 : ℤ) * 25 = 0 := by norm_num
    calc
      (∑ x : Point, ((D.r x : ℤ) - 5) ^ 2) =
          (275 : ℤ) - (10 : ℤ) * 55 + (11 : ℤ) * 25 := by simp [hrewrite, hsum_r, hsum_rsq]
      _ = 0 := hnum
  have hnonneg : ∀ x : Point, 0 ≤ ((D.r x : ℤ) - 5) ^ 2 := by intro x; exact sq_nonneg _
  have hall : ∀ y : Point, ((D.r y : ℤ) - 5) ^ 2 = 0 := by
    -- `sum = 0` with nonnegative terms implies all terms are `0`.
    have h' : ∀ y ∈ (Finset.univ : Finset Point), 0 ≤ ((D.r y : ℤ) - 5) ^ 2 := by
      intro y hy
      simpa using! hnonneg y
    have hall' := (Finset.sum_eq_zero_iff_of_nonneg h').1 (by simpa using! hvar)
    intro y
    simpa using! hall' y (by simp)
  have hx0 : ((D.r x : ℤ) - 5) ^ 2 = 0 := hall x
  have hx' : (D.r x : ℤ) - 5 = 0 := sq_eq_zero_iff.mp (by simpa [pow_two] using! hx0)
  have : (D.r x : ℤ) = 5 := by linarith
  exact Int.ofNat_inj.mp (by simpa using! this)

/-- Any two distinct points of the biplane lie in exactly `2` blocks. -/
public theorem lam_eq_two {x y : Point} (hxy : x ≠ y) : D.lam x y = 2 := by
  have hr : D.r x = 5 := r_eq_five (D := D) x
  let blocksX : Finset Block := D.blocks.filter (fun B => x ∈ B)
  have hblocksX : blocksX.card = 5 := by simpa [Biplane.Structure.r, blocksX] using! hr
  have hlam : ∀ y : Point, D.lam x y = (blocksX.filter fun B => y ∈ B).card := by
    intro y
    have hfilter :
        (blocksX.filter fun B : Block => y ∈ B) =
          D.blocks.filter (fun B : Block => x ∈ B ∧ y ∈ B) := by
        -- `(filter p).filter q = filter (p ∧ q)`
        simpa [blocksX, and_assoc] using!
          (Finset.filter_filter (s := D.blocks) (p := fun B => x ∈ B) (q := fun B => y ∈ B))
    -- take cards and unfold `lam`
    simpa [Biplane.Structure.lam] using! (congrArg Finset.card hfilter).symm
  have hsum_lam_all : (∑ y : Point, D.lam x y) = 25 := by
    -- sum over all points counts incidences in the blocks through `x`
    change (Finset.univ.sum (fun y : Point => D.lam x y)) = 25
    have hlamSum :
        (Finset.univ.sum (fun y : Point => D.lam x y)) =
          Finset.univ.sum (fun y : Point => (blocksX.filter fun B : Block => y ∈ B).card) := by
      refine Finset.sum_congr rfl ?_
      intro y hy
      simp [hlam y]
    have hdouble :
        (Finset.univ.sum (fun y : Point => (blocksX.filter fun B : Block => y ∈ B).card)) =
          ∑ B ∈ blocksX, B.card := by
      -- rewrite `card` as `∑ 1`, then commute the dependent double sum
      have hcard :
          (Finset.univ.sum (fun y : Point => (blocksX.filter fun B : Block => y ∈ B).card)) =
            ∑ y ∈ (Finset.univ : Finset Point),
              ∑ B ∈ (blocksX.filter fun B : Block => y ∈ B), (1 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro y hy
        exact Finset.card_eq_sum_ones (s := (blocksX.filter fun B : Block => y ∈ B))
      have hmem :
          ∀ (y : Point) (B : Block),
            y ∈ (Finset.univ : Finset Point) ∧ B ∈ (blocksX.filter fun B : Block => y ∈ B) ↔
              y ∈ B ∧ B ∈ blocksX := by
        intro y B
        constructor
        · intro h
          have hB : B ∈ blocksX.filter (fun B : Block => y ∈ B) := h.2
          have h' : B ∈ blocksX ∧ y ∈ B := by
            simpa [Finset.mem_filter, and_assoc] using! hB
          exact ⟨h'.2, h'.1⟩
        · intro h
          refine ⟨by simp, ?_⟩
          exact (Finset.mem_filter.2 ⟨h.2, h.1⟩)
      have hcomm :
          (∑ y ∈ (Finset.univ : Finset Point),
              ∑ B ∈ (blocksX.filter fun B : Block => y ∈ B), (1 : ℕ)) =
            ∑ B ∈ blocksX, ∑ y ∈ B, (1 : ℕ) := by
        exact sum_comm' hmem
      -- convert `∑ y ∈ B, 1` to `B.card`
      have hcardB : ∀ B : Block, (∑ y ∈ B, (1 : ℕ)) = B.card := by
        intro B
        exact (Finset.card_eq_sum_ones (s := B)).symm
      calc
        (Finset.univ.sum (fun y : Point => (blocksX.filter fun B : Block => y ∈ B).card))
            = ∑ y ∈ (Finset.univ : Finset Point),
                ∑ B ∈ (blocksX.filter fun B : Block => y ∈ B), (1 : ℕ) := hcard
        _ = ∑ B ∈ blocksX, ∑ y ∈ B, (1 : ℕ) := hcomm
        _ = ∑ B ∈ blocksX, B.card :=
              sum_congr rfl fun x a => hcardB x
    -- evaluate the block-card sum
    have hblocks : (∑ B ∈ blocksX, B.card) = 25 := by
      calc
        (∑ B ∈ blocksX, B.card) = ∑ B ∈ blocksX, 5 := by
              refine Finset.sum_congr rfl ?_
              intro B hB
              have hBmem : B ∈ D.blocks := (Finset.mem_filter.mp hB).1
              simp [D.block_card B hBmem]
        _ = blocksX.card * 5 := by simp
        _ = 25 := by simp [hblocksX]
    calc
      (Finset.univ.sum (fun y : Point => D.lam x y)) =
          Finset.univ.sum (fun y : Point => (blocksX.filter fun B => y ∈ B).card) := hlamSum
      _ = ∑ B ∈ blocksX, B.card := hdouble
      _ = 25 := hblocks
  have hlam_xx : D.lam x x = D.r x := by
    simp [Biplane.Structure.lam, Biplane.Structure.r, and_self]
  have hsum_lam : (∑ y ∈ (Finset.univ.erase x), (D.lam x y : ℤ)) = 20 := by
    have hsplit :
        (∑ y : Point, (D.lam x y : ℤ)) =
          (D.lam x x : ℤ) + ∑ y ∈ (Finset.univ.erase x), (D.lam x y : ℤ) := by
      change ((Finset.univ : Finset Point).sum (fun y : Point => (D.lam x y : ℤ))) =
        (D.lam x x : ℤ) + ∑ y ∈ (Finset.univ.erase x), (D.lam x y : ℤ)
      exact
        ((Finset.univ : Finset Point).add_sum_erase (a := x) (f := fun y => (D.lam x y : ℤ))
          (Finset.mem_univ x)).symm
    have hall : (∑ y : Point, (D.lam x y : ℤ)) = 25 := by
      simpa using! congrArg (fun n : ℕ => (n : ℤ)) hsum_lam_all
    simp_all
  have hsum_lam_sq_all : (∑ y : Point, (D.lam x y) ^ 2) = 65 := by
    -- apply the generic identity to `blocksX`
    have hdc :
        (∑ y : Point, (D.lam x y) ^ 2) = ∑ B ∈ blocksX, ∑ B' ∈ blocksX, (B ∩ B').card := by
      -- unfold `lam` via `hlam`
      have :
          (∑ y, (D.lam x y) ^ 2) = ∑ y, ((blocksX.filter fun B => y ∈ B).card) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro y hy
        simp [hlam y]
      calc
        (∑ y, (D.lam x y) ^ 2) = ∑ y, ((blocksX.filter fun B => y ∈ B).card) ^ 2 := this
        _ = ∑ B ∈ blocksX, ∑ B' ∈ blocksX, (B ∩ B').card :=
              sum_sq_filterCard_eq_sum_intersections (S := blocksX)
    -- compute RHS row-by-row inside `blocksX`
    have hrow : ∀ B ∈ blocksX, (∑ B' ∈ blocksX, (B ∩ B').card) = 13 := by
      intro B hB
      have hBmem : B ∈ D.blocks := (Finset.mem_filter.mp hB).1
      have hsplit :
          (∑ B' ∈ blocksX, (B ∩ B').card) =
            (B ∩ B).card + ∑ B' ∈ blocksX.erase B, (B ∩ B').card := by
        simpa [add_comm, add_left_comm, add_assoc] using!
          (blocksX.add_sum_erase (a := B) (f := fun B' => (B ∩ B').card) hB).symm
      have hBcard : B.card = 5 := D.block_card B hBmem
      have hoff : (∑ B' ∈ blocksX.erase B, (B ∩ B').card) = 8 := by
        have hterm : ∀ B' ∈ blocksX.erase B, (B ∩ B').card = 2 := by
          intro B' hB'
          have hB'X : B' ∈ blocksX := (Finset.mem_erase.mp hB').2
          have hB'mem : B' ∈ D.blocks := (Finset.mem_filter.mp hB'X).1
          have hne : B' ≠ B := (Finset.mem_erase.mp hB').1
          simpa [Finset.inter_comm] using! D.inter_card hBmem hB'mem (Ne.symm hne)
        calc
          (∑ B' ∈ blocksX.erase B, (B ∩ B').card) = ∑ _B' ∈ blocksX.erase B, 2 :=
            sum_congr rfl hterm
          _ = (blocksX.erase B).card * 2 := by simp
          _ = 8 := by
            have hcard : (blocksX.erase B).card = 4 := by
              simpa [hblocksX] using! Finset.card_erase_of_mem hB
            simp [hcard]
      calc
        (∑ B' ∈ blocksX, (B ∩ B').card)
            = (B ∩ B).card + ∑ B' ∈ blocksX.erase B, (B ∩ B').card := hsplit
        _ = 5 + 8 := by simp [Finset.inter_self, hBcard, hoff]
        _ = 13 := by decide
    calc
      (∑ y : Point, (D.lam x y) ^ 2) = ∑ B ∈ blocksX, ∑ B' ∈ blocksX, (B ∩ B').card := hdc
      _ = ∑ B ∈ blocksX, 13 :=
            sum_congr rfl hrow
      _ = blocksX.card * 13 := by simp
      _ = 65 := by simp [hblocksX]
  have hsum_lam_sq : (∑ y ∈ (Finset.univ.erase x), (D.lam x y : ℤ) ^ 2) = 40 := by
    have hsplit :
        (∑ y : Point, (D.lam x y : ℤ) ^ 2) =
          (D.lam x x : ℤ) ^ 2 + ∑ y ∈ (Finset.univ.erase x), (D.lam x y : ℤ) ^ 2 := by
      change ((Finset.univ : Finset Point).sum (fun y : Point => (D.lam x y : ℤ) ^ 2)) =
        (D.lam x x : ℤ) ^ 2 + ∑ y ∈ (Finset.univ.erase x), (D.lam x y : ℤ) ^ 2
      exact
        ((Finset.univ : Finset Point).add_sum_erase (a := x)
          (f := fun y => (D.lam x y : ℤ) ^ 2) (Finset.mem_univ x)).symm
    have hall : (∑ y : Point, (D.lam x y : ℤ) ^ 2) = 65 := by
      have := congrArg (fun n : ℕ => (n : ℤ)) hsum_lam_sq_all
      simpa using! this
    simp_all
  have hvar : (∑ y ∈ (Finset.univ.erase x), ((D.lam x y : ℤ) - 2) ^ 2) = 0 := by
    let Sx : Finset Point := Finset.univ.erase x
    have hcardSx : (Sx.card : ℤ) = 10 := by
      simp [Sx]
    have hrewrite :
        (∑ y ∈ Sx, ((D.lam x y : ℤ) - 2) ^ 2) =
          (∑ y ∈ Sx, (D.lam x y : ℤ) ^ 2) -
            (4 : ℤ) * (∑ y ∈ Sx, (D.lam x y : ℤ)) + (10 : ℤ) * 4 := by
      simpa [pow_two, hcardSx, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
        (sum_sq_sub_const (S := Sx) (f := fun y : Point => D.lam x y) (c := (2 : ℤ)))
    calc
      (∑ y ∈ Sx, ((D.lam x y : ℤ) - 2) ^ 2)
          = (40 : ℤ) - (4 : ℤ) * 20 + (10 : ℤ) * 4 := by
              simp [hrewrite, hsum_lam_sq, hsum_lam, Sx]
      _ = 0 := by norm_num
  have hnonneg : ∀ y ∈ (Finset.univ.erase x), 0 ≤ ((D.lam x y : ℤ) - 2) ^ 2 := by
    intro y hy
    exact sq_nonneg _
  have hall : ∀ y ∈ (Finset.univ.erase x), ((D.lam x y : ℤ) - 2) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 (by simpa using! hvar)
  have hyne : y ≠ x := Ne.symm hxy
  have hy0 : ((D.lam x y : ℤ) - 2) ^ 2 = 0 := hall y (by simp [hyne])
  have hy' : (D.lam x y : ℤ) - 2 = 0 := sq_eq_zero_iff.mp (by simpa [pow_two] using! hy0)
  have : (D.lam x y : ℤ) = 2 := by linarith
  exact Int.ofNat_inj.mp (by simpa using! this)

end Biplane.Structure
end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
