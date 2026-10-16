-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Defs

import Mathlib.Data.Set.Card.Arithmetic

/-!
# Inner product support in the BS81 equality case

Fix `C : Set ℝ²⁴` satisfying `EqCase24 C`. The explicit distance distribution (equation (11) in
BS81) forces that, for each `u ∈ C`, every `v ∈ C` has inner product with `u` in the finite support
set `{1, -1, ±1/2, ±1/4, 0}`.

This file packages the fibers `distSet C u t` and proves the corresponding support lemma
`inner_eq_one_or_eq_neg_one_or_eq_half_or_eq_neg_half_or_eq_quarter_or_eq_neg_quarter_or_eq_zero`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81

noncomputable section

open scoped BigOperators RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The fiber `{v ∈ C | ⟪u,v⟫ = t}`. -/
@[expose] public def distSet (C : Set ℝ²⁴) (u : ℝ²⁴) (t : ℝ) : Set ℝ²⁴ :=
  {v : ℝ²⁴ | v ∈ C ∧ (⟪u, v⟫ : ℝ) = t}

@[grind =]
lemma mem_distSet (C : Set ℝ²⁴) (u : ℝ²⁴) (t : ℝ) (v : ℝ²⁴) :
    v ∈ distSet C u t ↔ v ∈ C ∧ (⟪u, v⟫ : ℝ) = t := by
  rfl

lemma distSet_subset (C : Set ℝ²⁴) (u : ℝ²⁴) (t : ℝ) :
    distSet C u t ⊆ C := by
  intro v hv
  exact hv.1

lemma distSet_disjoint (C : Set ℝ²⁴) (u : ℝ²⁴) {t₁ t₂ : ℝ} (h : t₁ ≠ t₂) :
    Disjoint (distSet C u t₁) (distSet C u t₂) := by
  refine Set.disjoint_left.2 ?_
  intro v hv₁ hv₂
  exact h (by simpa [distSet] using! hv₁.2.symm.trans hv₂.2)

lemma union_distSet_ncard_eq_196560
    (C : Set ℝ²⁴) (hEq : EqCase24 C) {u : ℝ²⁴} (hu : u ∈ C) :
    ((distSet C u (1 : ℝ)) ∪
        ((distSet C u (-1 : ℝ)) ∪
          ((distSet C u (1 / 2 : ℝ)) ∪
            ((distSet C u (-1 / 2 : ℝ)) ∪
              ((distSet C u (1 / 4 : ℝ)) ∪
                ((distSet C u (-1 / 4 : ℝ)) ∪ (distSet C u (0 : ℝ)))))))).ncard = 196560 := by
  rcases hEq.distCount_eq hu with ⟨h1, hneg1, hhalf, hneghalf, hquart, hnegquart, hzero⟩
  have hS1 : (distSet C u (1 : ℝ)).ncard = 1 := by
    simpa [distCount, distSet] using! h1
  have hS_1 : (distSet C u (-1 : ℝ)).ncard = 1 := by
    simpa [distCount, distSet] using! hneg1
  have hS12 : (distSet C u (1 / 2 : ℝ)).ncard = 4600 := by
    simpa [distCount, distSet] using! hhalf
  have hS_12 : (distSet C u (-1 / 2 : ℝ)).ncard = 4600 := by
    simpa [distCount, distSet] using! hneghalf
  have hS14 : (distSet C u (1 / 4 : ℝ)).ncard = 47104 := by
    simpa [distCount, distSet] using! hquart
  have hS_14 : (distSet C u (-1 / 4 : ℝ)).ncard = 47104 := by
    simpa [distCount, distSet] using! hnegquart
  have hS0 : (distSet C u (0 : ℝ)).ncard = 93150 := by
    simpa [distCount, distSet] using! hzero
  have hfinC : C.Finite := hEq.code.finite
  -- The 7 support values as a `Finset`, written in the same nesting order as the statement's union.
  let supp₆ : Finset ℝ := ({0} : Finset ℝ)
  let supp₅ : Finset ℝ := insert (-1 / 4 : ℝ) supp₆
  let supp₄ : Finset ℝ := insert (1 / 4 : ℝ) supp₅
  let supp₃ : Finset ℝ := insert (-1 / 2 : ℝ) supp₄
  let supp₂ : Finset ℝ := insert (1 / 2 : ℝ) supp₃
  let supp₁ : Finset ℝ := insert (-1 : ℝ) supp₂
  let supp : Finset ℝ := insert (1 : ℝ) supp₁
  have hsupp : ((supp : Set ℝ)).Finite := supp.finite_toSet
  have hSuppF : ∀ t ∈ (supp : Set ℝ), (distSet C u t).Finite := by
    intro t ht
    exact hfinC.subset (distSet_subset C u t)
  have hSuppDisj : (supp : Set ℝ).PairwiseDisjoint (fun t : ℝ => distSet C u t) := by
    intro t₁ ht₁ t₂ ht₂ ht
    exact distSet_disjoint C u ht
  have hcard :
      (⋃ t ∈ (supp : Set ℝ), distSet C u t).ncard =
        ∑ᶠ t ∈ (supp : Set ℝ), (distSet C u t).ncard :=
    hsupp.ncard_biUnion hSuppF hSuppDisj
  have hsum : (∑ᶠ t ∈ (supp : Set ℝ), (distSet C u t).ncard) = 196560 := by
    have htoSum :
        (∑ᶠ t ∈ (supp : Set ℝ), (distSet C u t).ncard) =
          supp.sum (fun t : ℝ => (distSet C u t).ncard) := by
      -- `finsum` over a `Finset`-coerced set becomes a `Finset.sum`.
      simpa using! (finsum_mem_coe_finset (f := fun t : ℝ => (distSet C u t).ncard) supp)
    have hsumSupp : supp.sum (fun t : ℝ => (distSet C u t).ncard) = 196560 := by
      have hnot1 : (1 : ℝ) ∉ supp₁ := by
        simp [supp₁, supp₂, supp₃, supp₄, supp₅, supp₆]; norm_num
      have hnotNeg1 : (-1 : ℝ) ∉ supp₂ := by
        simp [supp₂, supp₃, supp₄, supp₅, supp₆]; norm_num
      have hnotHalf : (1 / 2 : ℝ) ∉ supp₃ := by
        simp [supp₃, supp₄, supp₅, supp₆]; norm_num
      have hnotNegHalf : (-1 / 2 : ℝ) ∉ supp₄ := by
        simp [supp₄, supp₅, supp₆]; norm_num
      have hnotQuart : (1 / 4 : ℝ) ∉ supp₅ := by
        simp [supp₅, supp₆]; norm_num
      have hnotNegQuart : (-1 / 4 : ℝ) ∉ supp₆ := by simp [supp₆]
      -- Peel off the `insert`s in `supp` and use the distance-distribution counts.
      dsimp [supp]
      rw [Finset.sum_insert hnot1]
      dsimp [supp₁]
      rw [Finset.sum_insert hnotNeg1]
      dsimp [supp₂]
      rw [Finset.sum_insert hnotHalf]
      dsimp [supp₃]
      rw [Finset.sum_insert hnotNegHalf]
      dsimp [supp₄]
      rw [Finset.sum_insert hnotQuart]
      dsimp [supp₅]
      rw [Finset.sum_insert hnotNegQuart]
      -- `supp₆ = {0}`.
      dsimp [supp₆]
      rw [Finset.sum_singleton]
      rw [hS1, hS_1, hS12, hS_12, hS14, hS_14, hS0]
      norm_num
    calc
      (∑ᶠ t ∈ (supp : Set ℝ), (distSet C u t).ncard)
          = supp.sum (fun t : ℝ => (distSet C u t).ncard) := htoSum
      _ = 196560 := hsumSupp
  -- Finish by rewriting the biUnion back into the explicit right-associated union.
  -- (The `supp` nesting order is chosen to match the statement.)
  have : (⋃ t ∈ (supp : Set ℝ), distSet C u t).ncard = 196560 :=
    hcard.trans hsum
  simpa [supp, supp₁, supp₂, supp₃, supp₄, supp₅, supp₆] using! this

/-- In the equality case, `⟪u, v⟫` lies in the support set. -/
public theorem
  inner_eq_one_or_eq_neg_one_or_eq_half_or_eq_neg_half_or_eq_quarter_or_eq_neg_quarter_or_eq_zero
    (C : Set ℝ²⁴) (hEq : EqCase24 C) {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ C) :
    (⟪u, v⟫ : ℝ) = (1 : ℝ) ∨
      (⟪u, v⟫ : ℝ) = (-1 : ℝ) ∨
        (⟪u, v⟫ : ℝ) = (1 / 2 : ℝ) ∨
          (⟪u, v⟫ : ℝ) = (-1 / 2 : ℝ) ∨
              (⟪u, v⟫ : ℝ) = (1 / 4 : ℝ) ∨
              (⟪u, v⟫ : ℝ) = (-1 / 4 : ℝ) ∨
                (⟪u, v⟫ : ℝ) = (0 : ℝ) := by
  -- Let `D` be the union of the seven fibers specified by EqCase24.
  let D : Set ℝ²⁴ :=
      distSet C u (1 : ℝ) ∪
        (distSet C u (-1 : ℝ) ∪
          (distSet C u (1 / 2 : ℝ) ∪
            (distSet C u (-1 / 2 : ℝ) ∪
              (distSet C u (1 / 4 : ℝ) ∪
                (distSet C u (-1 / 4 : ℝ) ∪
                  distSet C u (0 : ℝ))))))
  have hDsub : D ⊆ C := by
    dsimp [D]
    refine Set.union_subset (distSet_subset C u (1 : ℝ)) ?_
    refine Set.union_subset (distSet_subset C u (-1 : ℝ)) ?_
    refine Set.union_subset (distSet_subset C u (1 / 2 : ℝ)) ?_
    refine Set.union_subset (distSet_subset C u (-1 / 2 : ℝ)) ?_
    refine Set.union_subset (distSet_subset C u (1 / 4 : ℝ)) ?_
    refine Set.union_subset (distSet_subset C u (-1 / 4 : ℝ)) ?_
    simpa using! (distSet_subset C u (0 : ℝ))
  have hDcard : Set.ncard D = 196560 :=
    union_distSet_ncard_eq_196560 (C := C) hEq hu
  have hCcard : Set.ncard C = 196560 := hEq.card_eq
  have hDC : D = C := by
    refine Set.eq_of_subset_of_ncard_le hDsub ?_ hEq.code.finite
    -- `Set.ncard C ≤ Set.ncard D` by rewriting both to `196560`.
    simp [hCcard, hDcard]
  have hvD : v ∈ D := by
    simpa [hDC] using! hv
  have hvD' :
      (v ∈ C ∧ (⟪u, v⟫ : ℝ) = (1 : ℝ)) ∨
        (v ∈ C ∧ (⟪u, v⟫ : ℝ) = (-1 : ℝ)) ∨
          (v ∈ C ∧ (⟪u, v⟫ : ℝ) = (1 / 2 : ℝ)) ∨
            (v ∈ C ∧ (⟪u, v⟫ : ℝ) = (-1 / 2 : ℝ)) ∨
              (v ∈ C ∧ (⟪u, v⟫ : ℝ) = (1 / 4 : ℝ)) ∨
                (v ∈ C ∧ (⟪u, v⟫ : ℝ) = (-1 / 4 : ℝ)) ∨
                  (v ∈ C ∧ (⟪u, v⟫ : ℝ) = (0 : ℝ)) := by
    simpa [D] using! hvD
  rcases hvD' with h | h | h | h | h | h | h
  · exact Or.inl h.2
  · exact Or.inr (Or.inl h.2)
  · exact Or.inr (Or.inr (Or.inl h.2))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.2)))))

end

end SpherePacking.Dim24.Uniqueness.BS81
