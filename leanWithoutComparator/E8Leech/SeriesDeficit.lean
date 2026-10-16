import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Removing large terms from a nonnegative summable deficit

A positive threshold leaves only finitely many bad indices. Their number is
bounded by the total deficit divided by the threshold. This applies to all
lattice translates, rather than just a chosen finite window.
-/
noncomputable section
namespace E8Leech
open scoped BigOperators

theorem finite_large_deficit {ι : Type*} {a : ι → ℝ} (_ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) {τ : ℝ} (hτ : 0 < τ) : {i | τ ≤ a i}.Finite := by
  have hsub : Summable (fun i : {i | τ ≤ a i} => a i) := hs.subtype _
  have hc : Summable (fun _ : {i | τ ≤ a i} => τ) :=
    Summable.of_nonneg_of_le (fun _ => hτ.le) (fun i => i.property) hsub
  have : Finite {i | τ ≤ a i} := Finite.of_summable_const hτ hc
  exact Set.toFinite _

theorem large_deficit_card_mul_le {ι : Type*} {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) {τ : ℝ} (hτ : 0 < τ) :
    ((finite_large_deficit ha hs hτ).toFinset.card : ℝ) * τ ≤ ∑' i, a i := by
  classical
  let s := (finite_large_deficit ha hs hτ).toFinset
  calc
    (s.card : ℝ) * τ = ∑ i ∈ s, τ := by simp
    _ ≤ ∑ i ∈ s, a i := Finset.sum_le_sum (fun i hi => by
      simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hi)
    _ ≤ ∑' i, a i := hs.sum_le_tsum s (fun i _ => ha i)

theorem large_deficit_card_le_budget {ι : Type*} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {τ B : ℝ} (hτ : 0 < τ)
    (hB : (∑' i, a i) ≤ B) :
    ((finite_large_deficit ha hs hτ).toFinset.card : ℝ) ≤ B / τ :=
  (le_div_iff₀ hτ).mpr ((large_deficit_card_mul_le ha hs hτ).trans hB)
end E8Leech
