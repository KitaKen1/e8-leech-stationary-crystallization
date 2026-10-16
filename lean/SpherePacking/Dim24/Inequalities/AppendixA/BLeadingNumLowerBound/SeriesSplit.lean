/- Series head/tail decomposition lemmas. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt


/-!
### Series head/tail decomposition lemmas

These are small, reusable bookkeeping lemmas:
they rewrite `qseries`/`rseries` as a finite head (`Finset.range N`) plus an infinite tail.
-/


open scoped BigOperators
open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA

private lemma tsum_nat_add_eq_tsum_add_nat {α : Type} [TopologicalSpace α] [AddCommMonoid α]
    [T0Space α] (f : ℕ → α) (N : ℕ) :
    (∑' m : ℕ, f (m + N)) = ∑' m : ℕ, f (N + m) := by
  refine tsum_congr (fun m => by simp [Nat.add_comm])

/-- Finite head of a `qseries`: sum of the first `N` terms. -/
@[expose] public def qhead (a : ℕ → ℂ) (z : ℍ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * qterm z n

/-- Infinite tail of a `qseries`: sum of the terms starting at index `N`. -/
@[expose] public def qtail (a : ℕ → ℂ) (z : ℍ) (N : ℕ) : ℂ :=
  ∑' m : ℕ, a (N + m) * qterm z (N + m)

/-- Finite head of an `rseries`: sum of the first `N` terms. -/
@[expose] public def rhead (a : ℕ → ℤ) (t : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (a n : ℂ) * (rC t) ^ n

/-- Infinite tail of an `rseries`: sum of the terms starting at index `N`. -/
@[expose] public def rtail (a : ℕ → ℤ) (t : ℝ) (N : ℕ) : ℂ :=
  ∑' m : ℕ, (a (N + m) : ℂ) * (rC t) ^ (N + m)

/-- Decompose `qseries` into a finite head plus an infinite tail, using `qhead` and `qtail`. -/
public lemma qseries_eq_qhead_add_qtail (a : ℕ → ℂ) (z : ℍ) (N : ℕ)
    (ha : Summable (fun n : ℕ => a n * qterm z n)) :
    qseries a z = qhead a z N + qtail a z N := by
  simpa [qseries, qhead, qtail, tsum_nat_add_eq_tsum_add_nat, add_comm, add_left_comm, add_assoc]
    using! (ha.sum_add_tsum_nat_add N).symm

/-- Decompose `rseries` into a finite head plus an infinite tail, using `rhead` and `rtail`. -/
public lemma rseries_eq_rhead_add_rtail (a : ℕ → ℤ) (t : ℝ) (N : ℕ)
    (ha : Summable (fun n : ℕ => (a n : ℂ) * (rC t) ^ n)) :
    rseries a t = rhead a t N + rtail a t N := by
  simpa [rseries, rhead, rtail, tsum_nat_add_eq_tsum_add_nat, add_comm, add_left_comm, add_assoc]
    using! (ha.sum_add_tsum_nat_add N).symm

end SpherePacking.Dim24.AppendixA
