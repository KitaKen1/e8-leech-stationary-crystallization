/- Reindexing lemmas for even/odd parts of `r`-series. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Data.Complex.BigOperators


/-!
# Reindexing finite sums over even indices

We frequently rewrite a finite head `∑ n < N` into a sum over `i < 2*N` with an `if i % 2 = 0`
guard. This is used to express `q`-series heads in terms of `r`-series coefficients when
`q = r^2`.

## Main statements
* `range_filter_mod_two_eq_zero`
* `sum_range_even_ite`
-/

open scoped BigOperators

namespace SpherePacking.Dim24.AppendixA

/-- The even elements of `range (2*N)` are exactly the image of `range N` under `n ↦ 2*n`. -/
public lemma range_filter_mod_two_eq_zero (N : ℕ) :
    (Finset.range (2 * N)).filter (fun i : ℕ => i % 2 = 0) =
      (Finset.range N).image (fun n : ℕ => 2 * n) := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_filter.1 hi with ⟨hi, himod⟩
    refine Finset.mem_image.2 ?_
    refine ⟨i / 2, ?_, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero himod)⟩
    exact Finset.mem_range.2 <| Nat.div_lt_of_lt_mul <| by
      simpa [Nat.mul_comm] using! (Finset.mem_range.1 hi)
  · intro hi
    rcases Finset.mem_image.1 hi with ⟨n, hn, rfl⟩
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, by simp⟩
    exact Finset.mem_range.2 <|
      Nat.mul_lt_mul_of_pos_left (Finset.mem_range.1 hn) (Nat.succ_pos 1)

/--
Reindex a sum over `i < 2*N` with an evenness guard as a sum over `n < N`.

This is the form used to turn an even-indexed head `∑ n, c n * x^(2*n)` into a guarded sum
`∑ i, if i % 2 = 0 then c (i/2) * x^i else 0`.
-/
public lemma sum_range_even_ite (N : ℕ) (c : ℕ → ℂ) (x : ℂ) :
    (∑ i ∈ Finset.range (2 * N), (if i % 2 = 0 then c (i / 2) * x ^ i else 0)) =
      ∑ n ∈ Finset.range N, c n * x ^ (2 * n) := by
  calc
    (∑ i ∈ Finset.range (2 * N), (if i % 2 = 0 then c (i / 2) * x ^ i else 0)) =
        ∑ i ∈ (Finset.range (2 * N)).filter (fun i : ℕ => i % 2 = 0), c (i / 2) * x ^ i := by
          exact Eq.symm (Finset.sum_filter (fun a => a % 2 = 0) fun a => c (a / 2) * x ^ a)
    _ = ∑ i ∈ (Finset.range N).image (fun n : ℕ => 2 * n), c (i / 2) * x ^ i := by
          simp [range_filter_mod_two_eq_zero]
    _ = ∑ n ∈ Finset.range N, c ((2 * n) / 2) * x ^ (2 * n) := by
          exact
            (Finset.sum_image (s := Finset.range N) (f := fun i : ℕ => c (i / 2) * x ^ i)
              (g := fun n : ℕ => 2 * n) fun a ha b hb hab =>
                Nat.mul_left_cancel (Nat.succ_pos 1) hab)
    _ = ∑ n ∈ Finset.range N, c n * x ^ (2 * n) := by simp

end SpherePacking.Dim24.AppendixA
