-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumOps
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases


/-!
# Fast range sums for the `psiS_num` coefficient certificate

To certify the definitional computation `psiSnumCoeffs_calc` against the hard-coded table
`Ineq2GeOneCoeffs.psiSnumCoeffs`, we replace `Finset.range` sums by primitive-recursive range sums
(`sumRangeZ`) and a chunked variant (`sumRangeZ_fast`). This keeps kernel reduction small when
computing convolution products of truncated coefficient lists.

## Main definitions
* `sumRangeZ`
* `sumRangeZ_fast`
* `psiSnumCoeffs_calc_fast`

## Main statements
* `psiSnumCoeffs_calc_fast_eq_slow`
-/

open scoped BigOperators

namespace SpherePacking.Dim24.Ineq2PsiSnum
/-- Primitive-recursive integer range sum `∑_{k < n} f k`. -/
@[expose] public def sumRangeZ : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, f => sumRangeZ n f + f n

lemma sumRangeZ_eq_sum_finset_range (n : ℕ) (f : ℕ → ℤ) :
    sumRangeZ n f = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero =>
      simp [sumRangeZ]
  | succ n ih =>
      simp [sumRangeZ, ih, Finset.sum_range_succ]

/-!
For the convolution computations in the certificate we use a chunked range sum to reduce the
kernel's definitional recursion depth.

We sum in blocks of `20`:
`sumRangeZ_fast (n+20) f = sumRangeZ_fast n f + sumRangeZ 20 (fun i => f (n+i))`.

The base case delegates to the linear `sumRangeZ`, which is inexpensive for `n < 20`.
-/

/-- A chunked range sum, evaluating `sumRangeZ` in blocks of `20` to reduce definitional recursion
depth during kernel reduction. -/
@[expose] public def sumRangeZ_fast : ℕ → (ℕ → ℤ) → ℤ
  | n + 20, f => sumRangeZ_fast n f + sumRangeZ 20 (fun i => f (n + i))
  | n, f => sumRangeZ n f

lemma sumRangeZ_fast_eq_sum_finset_range (n : ℕ) (f : ℕ → ℤ) :
    sumRangeZ_fast n f = ∑ k ∈ Finset.range n, f k := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  by_cases hlt : n < 20
  · -- Base case: the `n+20` equation does not apply.
    have hsmall : sumRangeZ_fast n f = sumRangeZ n f := by
      have hn0 : 0 ≤ n := Nat.zero_le n
      interval_cases n using hn0, hlt <;> rfl
    simpa [hsmall] using! sumRangeZ_eq_sum_finset_range (n := n) (f := f)
  · have hge : 20 ≤ n := Nat.le_of_not_gt hlt
    set m : ℕ := n - 20
    have hn : n = m + 20 := by
      simpa [m] using! (Nat.sub_add_cancel hge).symm
    have hrec :
        sumRangeZ_fast n f = sumRangeZ_fast m f + sumRangeZ 20 (fun i => f (m + i)) := by
      simp [hn, sumRangeZ_fast]
    have hm_lt : m < n := by
      have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 20) hge
      simpa [m] using! Nat.sub_lt hnpos (by decide : 0 < 20)
    have ihm : sumRangeZ_fast m f = ∑ k ∈ Finset.range m, f k := ih m hm_lt
    have hblock :
        sumRangeZ 20 (fun i => f (m + i)) = ∑ i ∈ Finset.range 20, f (m + i) := by
      simpa using! sumRangeZ_eq_sum_finset_range (n := 20) (f := fun i => f (m + i))
    have hdisj :
        Disjoint (Finset.range m) ((Finset.range 20).map (addLeftEmbedding m)) := by
      refine Finset.disjoint_left.2 ?_
      intro x hx hm2
      have hxlt : x < m := by simpa [Finset.mem_range] using! hx
      rcases Finset.mem_map.1 hm2 with ⟨y, hy, rfl⟩
      exact (Nat.not_lt_of_ge (Nat.le_add_right m y)) hxlt
    have hsplit :
        (∑ k ∈ Finset.range n, f k) =
          (∑ k ∈ Finset.range m, f k) + (∑ i ∈ Finset.range 20, f (m + i)) := by
      calc
        (∑ k ∈ Finset.range n, f k) = ∑ k ∈ Finset.range (m + 20), f k := by
          simp [hn]
        _ = ∑ k ∈ Finset.range m ∪ (Finset.range 20).map (addLeftEmbedding m), f k := by
          simp [Finset.range_add_eq_union]
        _ =
            (∑ k ∈ Finset.range m, f k) +
              (∑ k ∈ (Finset.range 20).map (addLeftEmbedding m), f k) := by
          simp [Finset.sum_union, hdisj]
        _ = (∑ k ∈ Finset.range m, f k) + (∑ i ∈ Finset.range 20, f (m + i)) := by
          simp [Finset.sum_map]
    calc
      sumRangeZ_fast n f = sumRangeZ_fast m f + sumRangeZ 20 (fun i => f (m + i)) := hrec
      _ = (∑ k ∈ Finset.range m, f k) + (∑ i ∈ Finset.range 20, f (m + i)) := by
            simp [ihm, hblock]
      _ = ∑ k ∈ Finset.range n, f k := by simp [hsplit]

/-! Fast versions of theta coefficient functions (defined using `sumRangeZ`). -/

/-- A definitional version of `theta01CoeffTrunc` that uses `sumRangeZ` instead of `Finset.sum`. -/
@[expose] public def theta01CoeffTrunc_fast (n : ℕ) : ℤ :=
  sumRangeZ (AppendixA.BleadingCoeffs.thetaCutoff + 1) fun k =>
    if k ^ (2 : ℕ) = n then (if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k)) else 0

/-- A definitional version of `theta10CoeffTrunc` that uses `sumRangeZ` instead of `Finset.sum`. -/
@[expose] public def theta10CoeffTrunc_fast (n : ℕ) : ℤ :=
  sumRangeZ (AppendixA.BleadingCoeffs.thetaCutoff + 1) fun k =>
    if k * (k + 1) = n then (2 : ℤ) else 0

lemma theta01CoeffTrunc_fast_eq_fun :
    theta01CoeffTrunc_fast = theta01CoeffTrunc := by
  funext n
  simp [theta01CoeffTrunc_fast, theta01CoeffTrunc, sumRangeZ_eq_sum_finset_range]

lemma theta10CoeffTrunc_fast_eq_fun :
    theta10CoeffTrunc_fast = theta10CoeffTrunc := by
  funext n
  simp [theta10CoeffTrunc_fast, theta10CoeffTrunc, sumRangeZ_eq_sum_finset_range]

/-- Fast truncated convolution product, implemented using the chunked range sum `sumRangeZ_fast`. -/
@[expose] public def mulZ_fast (a b : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin Ineq2GeOneCoeffs.N =>
    let n := i.1
    sumRangeZ_fast (n + 1) fun k => a.getD k 0 * b.getD (n - k) 0

lemma mulZ_fast_eq (a b : List ℤ) :
    mulZ_fast a b = mulZ a b := by
  refine List.ext_getElem ?_ ?_
  · -- Both sides are `List.ofFn`, hence have length `N`.
    have hlen1 : (mulZ_fast a b).length = Ineq2GeOneCoeffs.N := by
      unfold mulZ_fast
      rw [List.length_ofFn]
    have hlen2 : (mulZ a b).length = Ineq2GeOneCoeffs.N := by
      unfold mulZ
      rw [List.length_ofFn]
    simp [hlen1, hlen2]
  · intro n hn1 hn2
    have hlenL : (mulZ_fast a b).length = Ineq2GeOneCoeffs.N := by
      unfold mulZ_fast
      rw [List.length_ofFn]
    have hn : n < Ineq2GeOneCoeffs.N :=
      lt_of_lt_of_eq hn1 hlenL
    have hsum :
        sumRangeZ_fast (n + 1) (fun k => a.getD k 0 * b.getD (n - k) 0) =
          ∑ k ∈ Finset.range (n + 1), a.getD k 0 * b.getD (n - k) 0 :=
      sumRangeZ_fast_eq_sum_finset_range (n + 1) fun k => a.getD k 0 * b.getD (n - k) 0
    have hL :
        (mulZ_fast a b)[n] =
          sumRangeZ_fast (n + 1) (fun k => a.getD k 0 * b.getD (n - k) 0) := by
      unfold mulZ_fast
      exact
        (List.getElem_ofFn
          (f := fun i : Fin Ineq2GeOneCoeffs.N =>
            let n := i.1
            sumRangeZ_fast (n + 1) fun k => a.getD k 0 * b.getD (n - k) 0)
          (i := n) hn)
    have hR :
        (mulZ a b)[n] =
          ∑ k ∈ Finset.range (n + 1), a.getD k 0 * b.getD (n - k) 0 := by
      unfold mulZ
      exact
        (List.getElem_ofFn
          (f := fun i : Fin Ineq2GeOneCoeffs.N =>
            let n := i.1
            ∑ k ∈ Finset.range (n + 1), a.getD k 0 * b.getD (n - k) 0)
          (i := n) hn)
    -- Combine.
    grind only

/-- Fast truncated power, defined using `mulZ_fast`. -/
@[expose] public def powZ_fast (a : List ℤ) : ℕ → List ℤ
  | 0 => List.ofFn fun i : Fin Ineq2GeOneCoeffs.N => if i.1 = 0 then (1 : ℤ) else 0
  | Nat.succ k => mulZ_fast a (powZ_fast a k)

lemma powZ_fast_eq (a : List ℤ) : ∀ m : ℕ, powZ_fast a m = powZ a m
  | 0 => by simp [powZ_fast, powZ]
  | Nat.succ m => by
      simp [powZ_fast, powZ, powZ_fast_eq, mulZ_fast_eq]

/-- Truncated coefficient list of `theta01CoeffTrunc_fast`. -/
@[expose] public def theta01Z_fast : List ℤ :=
  coeffList theta01CoeffTrunc_fast

/-- Truncated coefficient list of `theta10CoeffTrunc_fast`. -/
@[expose] public def theta10Z_fast : List ℤ :=
  coeffList theta10CoeffTrunc_fast

/-- The staged list `H4Z = theta01Z_fast^4` used in the `psiSnumCoeffs_calc_fast` certificate. -/
@[expose] public def H4Z_fast : List ℤ :=
  powZ_fast theta01Z_fast 4

/-- The staged list `H2Z = shift1Z (theta10Z_fast^4)` used in the `psiSnumCoeffs_calc_fast`
certificate. -/
@[expose] public def H2Z_fast : List ℤ :=
  shift1Z (powZ_fast theta10Z_fast 4)

/-- Fast definitional computation of the `psiS_num` numerator coefficient list, using `mulZ_fast`
and `powZ_fast` for kernel efficiency. -/
@[expose] public def psiSnumCoeffs_calc_fast : List ℤ :=
  negZ <|
    addZ
        (addZ
          (smulZ 7 (mulZ_fast (powZ_fast H2Z_fast 5) (powZ_fast H4Z_fast 2)))
          (smulZ 7 (mulZ_fast (powZ_fast H2Z_fast 6) H4Z_fast)))
        (smulZ 2 (powZ_fast H2Z_fast 7))

/-- The fast definitional computation `psiSnumCoeffs_calc_fast` agrees with the original
definition `psiSnumCoeffs_calc`. -/
public lemma psiSnumCoeffs_calc_fast_eq_slow :
    psiSnumCoeffs_calc_fast = psiSnumCoeffs_calc := by
  -- Unfold only the outer structure and rewrite fast primitives to the original ones.
  unfold psiSnumCoeffs_calc_fast H2Z_fast H4Z_fast theta01Z_fast theta10Z_fast psiSnumCoeffs_calc
  -- Rewrite the theta coefficient functions.
  rw [theta01CoeffTrunc_fast_eq_fun, theta10CoeffTrunc_fast_eq_fun]
  -- Rewrite `powZ_fast` / `mulZ_fast` occurrences without unfolding `powZ` itself.
  simp only [powZ_fast_eq, mulZ_fast_eq]


end SpherePacking.Dim24.Ineq2PsiSnum
