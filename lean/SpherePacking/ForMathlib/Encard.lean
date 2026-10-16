-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Instances.ENat

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.T5

/-!
# `ENat` sums and `Set.encard`

This file collects lemmas about infinite sums valued in `ENat` and about `Set.encard` that are used
throughout this repository.
-/

/-- The infinite sum of a constant `c : ENat` over a type `α` is `ENat.card α * c`. -/
public theorem ENat.tsum_const {α : Type*} (c : ENat) :
    ∑' (_ : α), c = ENat.card α * c := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  obtain hfin | hinf := fintypeOrInfinite α
  · simp [tsum_fintype]
  · simp only [card_eq_top_of_infinite]
    refine HasSum.tsum_eq (by
      change Filter.Tendsto _ _ _
      simp only [Finset.sum_const, nsmul_eq_mul, ne_eq, hc, not_false_eq_true, top_mul]
      refine (tendsto_nhds_top_iff_natCast_lt.2 ?_)
      intro n
      obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α (n + 1)
      filter_upwards [Filter.eventually_ge_atTop s] with t ht
      refine lt_of_lt_of_le ?_ (le_mul_of_one_le_right' (ENat.one_le_iff_ne_zero.2 hc))
      refine lt_of_lt_of_le (b := (s.card : ℕ∞)) ?_ (by exact_mod_cast (Finset.card_le_card ht))
      simp only [Nat.cast_lt, hs, Nat.lt_succ_self n])

/-- The infinite sum of a constant `c : ENat` over a set `s` is `s.encard * c`. -/
public theorem ENat.tsum_set_const {α : Type*} (s : Set α) (c : ENat) :
    ∑' (_ : s), c = s.encard * c := by
  rw [ENat.tsum_const, Set.encard]

/-- The infinite sum of `1 : ENat` over a type `α` is `ENat.card α`. -/
public theorem ENat.tsum_one {α : Type*} : ∑' (_ : α), 1 = ENat.card α := by
  simp [ENat.tsum_const]

/-- The infinite sum of `1 : ENat` over a set `s` is `s.encard`. -/
public theorem ENat.tsum_set_one {α : Type*} (s : Set α) : ∑' (_ : s), 1 = s.encard := by
  rw [ENat.tsum_one, Set.encard]

namespace ENat

open Function Set

section tsum

variable {α β : Type*} {f : α → ℕ∞}

/-- The sum of an `ENat`-valued series is the supremum of its finite partial sums. -/
public theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

/-- Any `ENat`-valued series is summable. -/
@[simp] public theorem summable : Summable f :=
  hasSum.summable

/-- `tsum f` is the supremum of the finite partial sums `∑ a ∈ s, f a`. -/
public theorem tsum_eq_iSup_sum : ∑' x, f x = (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  hasSum.tsum_eq

theorem tsum_comp_le_tsum_of_injective {φ : α → β} (hφ : Injective φ) (g : β → ℕ∞) :
    ∑' x, g (φ x) ≤ ∑' y, g y :=
  (summable (f := fun x => g (φ x))).tsum_le_tsum_of_inj φ hφ (fun _ _ ↦ zero_le ..)
    (fun _ ↦ le_rfl) (summable (f := g))

theorem tsum_le_tsum_comp_of_surjective {φ : α → β} (hφ : Surjective φ) (g : β → ℕ∞) :
    ∑' y, g y ≤ ∑' x, g (φ x) :=
  calc ∑' y, g y = ∑' y, g (φ (surjInv hφ y)) := by simp [surjInv_eq hφ]
    _ ≤ ∑' x, g (φ x) := tsum_comp_le_tsum_of_injective (injective_surjInv hφ) _

theorem tsum_comp_eq_tsum_of_bijective {φ : α → β} (hφ : φ.Bijective) (g : β → ℕ∞) :
    ∑' x, g (φ x) = ∑' y, g y :=
  (tsum_comp_le_tsum_of_injective hφ.1 g).antisymm (tsum_le_tsum_comp_of_surjective hφ.2 g)

theorem tsum_comp_eq_tsum_of_equiv (e : α ≃ β) (g : β → ℕ∞) :
    ∑' x, g (e x) = ∑' y, g y :=
  tsum_comp_eq_tsum_of_bijective e.bijective g

theorem tsum_subtype_sigma' {β : α → Type*} (f : (Σ a, β a) → ℕ∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  Summable.tsum_sigma' (fun _ ↦ summable) summable

variable {ι : Type*}

theorem tsum_subtype_iUnion_eq_tsum (f : α → ℕ∞) (t : ι → Set α) (ht : Pairwise (Disjoint on t)) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  (tsum_comp_eq_tsum_of_bijective (sigmaToiUnion_bijective t (fun _ _ hij => ht hij)) _).symm.trans
    (tsum_subtype_sigma' (f := fun x : Σ i, t i => f x.2))

end ENat.tsum
open Function

/-- `encard` is additive on pairwise disjoint unions. -/
public theorem Set.encard_iUnion_of_pairwiseDisjoint {ι α : Type*} {s : ι → Set α}
    (hs : Set.PairwiseDisjoint Set.univ s) :
    (⋃ i, s i).encard = ∑' i, (s i).encard := by
  have ht : Pairwise (Disjoint on s) := by simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using hs
  simpa [ENat.tsum_set_one] using ENat.tsum_subtype_iUnion_eq_tsum (f := fun _ => 1) s ht
