-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.Basic


/-!
### Sparse theta coefficient functions

The theta-series in the `ψI` numerator have coefficients supported on squares and triangular
numbers. This file defines the corresponding dense coefficient functions
`theta01CoeffFun`/`theta10CoeffFun : ℕ → ℤ`, proves basic support and size lemmas, and reindexes the
associated `rseries` as `tsum`s over squares or triangular numbers.
-/


namespace SpherePacking.Dim24.AppendixA


open scoped BigOperators

/-!
#### Splitting `ℤ`-indexed sums

We use `Equiv.intEquivNatSumNat : ℤ ≃ ℕ ⊕ ℕ` (inverse `Int.ofNat`/`Int.negSucc`) to split
`ℤ`-indexed `tsum`s into a nonnegative part and a negative part.
-/

/-- Split a `tsum` over `ℤ` into a sum over nonnegative integers and over negative `Int.negSucc`. -/
public lemma tsum_int_eq_tsum_nat_add_tsum_negSucc (f : ℤ → ℂ) (hf : Summable f) :
    (∑' z : ℤ, f z) = (∑' n : ℕ, f n) + ∑' n : ℕ, f (Int.negSucc n) := by
  let e : ℤ ≃ ℕ ⊕ ℕ := Equiv.intEquivNatSumNat
  have he : (∑' z : ℤ, f z) = ∑' s : ℕ ⊕ ℕ, f (e.symm s) := by
    simpa [e] using! (e.tsum_eq fun s : ℕ ⊕ ℕ => f (e.symm s))
  have h1 : Summable fun n : ℕ => f (e.symm (Sum.inl n)) := by
    simpa [e] using! hf.comp_injective (fun a b h => Int.ofNat.inj h)
  have h2 : Summable fun n : ℕ => f (e.symm (Sum.inr n)) := by
    simpa [e] using! hf.comp_injective (fun a b h => Int.negSucc.inj h)
  have hsplit :
      (∑' s : ℕ ⊕ ℕ, f (e.symm s)) =
        (∑' n : ℕ, f (e.symm (Sum.inl n))) + ∑' n : ℕ, f (e.symm (Sum.inr n)) := by
    simpa using! (Summable.tsum_sum (f := fun s : ℕ ⊕ ℕ => f (e.symm s)) h1 h2)
  -- Unfold `e.symm` on the two summands.
  have hinl : (∑' n : ℕ, f (e.symm (Sum.inl n))) = ∑' n : ℕ, f n := by
    rfl
  have hinr : (∑' n : ℕ, f (e.symm (Sum.inr n))) = ∑' n : ℕ, f (Int.negSucc n) := by
    rfl
  simpa [hinl, hinr] using! (he.trans hsplit)

/-!
#### Sparse theta coefficient functions

The theta-series involved in `ψI` are supported on squares and triangular numbers.
We model them as "dense" coefficient functions `ℕ → ℤ` so that we can use Cauchy products.
-/

/-- The square map `k ↦ k^2`, used to describe the support of `theta01CoeffFun`. -/
@[expose] public def square (k : ℕ) : ℕ := k ^ (2 : ℕ)

private lemma square_injective : Function.Injective square := by
  simpa [square] using! (Nat.pow_left_injective (n := 2) (Nat.succ_ne_zero 1))

/--
The triangular-number map `k ↦ k * (k + 1)`, used to describe the support of
`theta10CoeffFun`. -/
@[expose] public def triangular (k : ℕ) : ℕ := k * (k + 1)

private lemma triangular_injective : Function.Injective triangular := by
  refine (show StrictMono triangular from ?_).injective
  intro a b hab
  dsimp [triangular]
  nlinarith

/-- Dense coefficient function supported on squares, matching the `θ_{01}` coefficients. -/
@[expose] public def theta01CoeffFun (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    if k ^ (2 : ℕ) = n then (if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k)) else 0

/--
Dense coefficient function supported on triangular numbers,
matching the `θ_{10}` coefficients. -/
@[expose] public def theta10CoeffFun (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if k * (k + 1) = n then (2 : ℤ) else 0

/-- On a square index `k^2`, `theta01CoeffFun` returns the expected `θ_{01}` coefficient. -/
public lemma theta01CoeffFun_sq (k : ℕ) :
    theta01CoeffFun (k ^ (2 : ℕ)) = (if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k)) := by
  dsimp [theta01CoeffFun]
  have hk : k ∈ Finset.range (k ^ (2 : ℕ) + 1) := by
    have hk' : k ≤ k ^ (2 : ℕ) := by
      cases k with
      | zero => simp
      | succ k =>
          rw [pow_two]
          exact Nat.le_mul_of_pos_right (m := Nat.succ k) (Nat.succ k) (Nat.succ_pos k)
    simpa [Finset.mem_range] using! (Nat.lt_succ_of_le hk')
  have hsingle :
      (∑ k' ∈ Finset.range (k ^ (2 : ℕ) + 1),
          if k' ^ (2 : ℕ) = k ^ (2 : ℕ) then
            if k' = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k')
          else
            0) =
        if k ^ (2 : ℕ) = k ^ (2 : ℕ) then if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k) else 0 := by
    refine Finset.sum_eq_single_of_mem (s := Finset.range (k ^ (2 : ℕ) + 1)) (f := fun k' =>
      if k' ^ (2 : ℕ) = k ^ (2 : ℕ) then
        if k' = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k')
      else
        0) k hk ?_
    simp_all
  simpa using! hsingle

/-- If `n` is not a square, then `theta01CoeffFun n = 0`. -/
public lemma theta01CoeffFun_eq_zero_of_not_square (n : ℕ)
    (hn : n ∉ Set.range square) : theta01CoeffFun n = 0 := by
  dsimp [theta01CoeffFun]
  refine Finset.sum_eq_zero ?_
  intro k _hk
  by_cases hkn : k ^ (2 : ℕ) = n
  · exact (hn ⟨k, by simpa [square] using! hkn⟩).elim
  · simp [hkn]

/-- On a triangular index `triangular k`, `theta10CoeffFun` equals `2`. -/
public lemma theta10CoeffFun_tri (k : ℕ) : theta10CoeffFun (triangular k) = 2 := by
  dsimp [theta10CoeffFun, triangular]
  have hk : k ∈ Finset.range (k * (k + 1) + 1) := by
    grind only [= Finset.mem_range]
  have hsingle :
      (∑ k' ∈ Finset.range (k * (k + 1) + 1),
          if k' * (k' + 1) = k * (k + 1) then (2 : ℤ) else 0) =
        if k * (k + 1) = k * (k + 1) then (2 : ℤ) else 0 := by
    refine Finset.sum_eq_single_of_mem (s := Finset.range (k * (k + 1) + 1)) (f := fun k' =>
      if k' * (k' + 1) = k * (k + 1) then (2 : ℤ) else 0) k hk ?_
    intro k' hk' hkne
    have htri : k' * (k' + 1) ≠ k * (k + 1) := by
      intro htri
      exact hkne (triangular_injective (by simpa [triangular] using! htri))
    simp [htri]
  simpa using! hsingle

/-- If `n` is not triangular, then `theta10CoeffFun n = 0`. -/
public lemma theta10CoeffFun_eq_zero_of_not_triangular (n : ℕ)
    (hn : n ∉ Set.range triangular) : theta10CoeffFun n = 0 := by
  dsimp [theta10CoeffFun]
  refine Finset.sum_eq_zero ?_
  intro k _hk
  by_cases hkn : k * (k + 1) = n
  · exact (hn ⟨k, by simpa [triangular] using! hkn⟩).elim
  · simp [hkn]

/-- Reindex a `tsum` along an injective map `g`, assuming the summand is zero off `Set.range g`. -/
public lemma tsum_eq_tsum_comp_of_eq_zero_off_range {f : ℕ → ℂ} (hs : Summable f)
    {g : ℕ → ℕ} (hg : Function.Injective g) (hzero : ∀ n : ℕ, n ∉ Set.range g → f n = 0) :
    (∑' n : ℕ, f n) = ∑' k : ℕ, f (g k) := by
  have hcompl : (∑' n : {n // n ∈ (Set.range g)ᶜ}, f n.1) = 0 := by
    have hcongr :
        (∑' n : {n // n ∈ (Set.range g)ᶜ}, f n.1) = ∑' _n : {n // n ∈ (Set.range g)ᶜ}, (0 : ℂ) := by
      refine tsum_congr ?_
      intro n
      simpa using! hzero n.1 n.2
    simpa using! hcongr.trans (tsum_zero : (∑' _n : {n // n ∈ (Set.range g)ᶜ}, (0 : ℂ)) = 0)
  calc
    (∑' n : ℕ, f n) =
        (∑' n : {n // n ∈ Set.range g}, f n.1) +
          (∑' n : {n // n ∈ (Set.range g)ᶜ}, f n.1) := by
      simpa using! (hs.tsum_subtype_add_tsum_subtype_compl (Set.range g)).symm
    _ = (∑' n : {n // n ∈ Set.range g}, f n.1) := by simp [hcompl]
    _ = ∑' k : ℕ, f (g k) := by
      simpa using!
        ((Equiv.ofInjective g hg).tsum_eq (fun n : {n // n ∈ Set.range g} => f n.1)).symm

/-- Coefficients of `theta01CoeffFun` are uniformly bounded in absolute value by `2`. -/
public lemma abs_theta01CoeffFun_le_two (n : ℕ) : |theta01CoeffFun n| ≤ (2 : ℤ) := by
  by_cases hn : n ∈ Set.range square
  · rcases hn with ⟨k, rfl⟩
    simpa [square, theta01CoeffFun_sq] using!
      (show |(if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k))| ≤ (2 : ℤ) by
        cases k <;> simp)
  · simp [theta01CoeffFun_eq_zero_of_not_square (n := n) hn]

/-- Coefficients of `theta10CoeffFun` are uniformly bounded in absolute value by `2`. -/
public lemma abs_theta10CoeffFun_le_two (n : ℕ) : |theta10CoeffFun n| ≤ (2 : ℤ) := by
  by_cases hn : n ∈ Set.range triangular
  · rcases hn with ⟨k, rfl⟩
    simp [theta10CoeffFun_tri]
  · simp [theta10CoeffFun_eq_zero_of_not_triangular (n := n) hn]

/-!
#### Reindexing the sparse theta coefficient `r`-series

We will compare the Jacobi-theta definitions (as `ℤ`-indexed sums) with the `rseries` defined from
the "dense" coefficient functions `theta01CoeffFun`/`theta10CoeffFun`.
-/

private lemma summable_norm_rseries_of_abs_le (t : ℝ) (ht : 1 ≤ t) (a : ℕ → ℤ) (C : ℝ)
    (ha : ∀ n : ℕ, ‖(a n : ℂ)‖ ≤ C) :
    Summable (fun n : ℕ => ‖((a n : ℂ) * (rC t) ^ n)‖) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have habs : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ (0 : ℕ)) := by
    intro n
    simpa [Complex.norm_intCast, pow_zero] using! (ha n)
  simpa using!
    (summable_norm_rseries_of_coeffBound (t := t) (ht0 := ht0) (a := a) (C := C) (k := 0) habs)

private lemma summable_rseries_of_abs_le (t : ℝ) (ht : 1 ≤ t) (a : ℕ → ℤ) (C : ℝ)
    (ha : ∀ n : ℕ, ‖(a n : ℂ)‖ ≤ C) :
    Summable (fun n : ℕ => (a n : ℂ) * (rC t) ^ n) :=
  Summable.of_norm (summable_norm_rseries_of_abs_le (t := t) ht a C ha)

/-- Reindex `rseries theta01CoeffFun` as a `tsum` over squares. -/
public lemma rseries_theta01_eq_tsum_squares (t : ℝ) (ht : 1 ≤ t) :
    rseries theta01CoeffFun t =
      ∑' k : ℕ,
        ((if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k) : ℤ) : ℂ) * (rC t) ^ (k ^ (2 : ℕ)) := by
  let f : ℕ → ℂ := fun n => (theta01CoeffFun n : ℂ) * (rC t) ^ n
  have hs : Summable f := by
    refine summable_rseries_of_abs_le (t := t) ht theta01CoeffFun 2 ?_
    intro n
    have : |(theta01CoeffFun n : ℝ)| ≤ (2 : ℝ) := by
      exact_mod_cast abs_theta01CoeffFun_le_two (n := n)
    simpa [Complex.norm_intCast] using! this
  have hzero : ∀ n : ℕ, n ∉ Set.range square → f n = 0 := by
    intro n hn
    simp [f, theta01CoeffFun_eq_zero_of_not_square (n := n) hn]
  have hreindex :
      (∑' n : ℕ, f n) = ∑' k : ℕ, f (square k) :=
    tsum_eq_tsum_comp_of_eq_zero_off_range (f := f) hs (g := square) square_injective hzero
  have hcoeff :
      (∑' k : ℕ, f (square k)) =
        ∑' k : ℕ,
          ((if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k) : ℤ) : ℂ) * (rC t) ^ (k ^ (2 : ℕ)) := by
    refine tsum_congr ?_
    intro k
    simp [f, square, theta01CoeffFun_sq]
  simpa [rseries, f] using! (hreindex.trans hcoeff)

/-- Reindex `rseries theta10CoeffFun` as a `tsum` over triangular numbers. -/
public lemma rseries_theta10_eq_tsum_triangular (t : ℝ) (ht : 1 ≤ t) :
    rseries theta10CoeffFun t =
      ∑' k : ℕ, ((2 : ℤ) : ℂ) * (rC t) ^ triangular k := by
  let f : ℕ → ℂ := fun n => (theta10CoeffFun n : ℂ) * (rC t) ^ n
  have hs : Summable f := by
    refine summable_rseries_of_abs_le (t := t) ht theta10CoeffFun 2 ?_
    intro n
    have : |(theta10CoeffFun n : ℝ)| ≤ (2 : ℝ) := by
      exact_mod_cast abs_theta10CoeffFun_le_two (n := n)
    simpa [Complex.norm_intCast] using! this
  have hzero : ∀ n : ℕ, n ∉ Set.range triangular → f n = 0 := by
    intro n hn
    simp [f, theta10CoeffFun_eq_zero_of_not_triangular (n := n) hn]
  have hreindex :
      (∑' n : ℕ, f n) = ∑' k : ℕ, f (triangular k) :=
    tsum_eq_tsum_comp_of_eq_zero_off_range (f := f) hs (g := triangular) triangular_injective hzero
  have hcoeff :
      (∑' k : ℕ, f (triangular k)) = ∑' k : ℕ, ((2 : ℤ) : ℂ) * (rC t) ^ triangular k := by
    refine tsum_congr ?_
    intro k
    simp [f, theta10CoeffFun_tri]
  simpa [rseries, f] using! (hreindex.trans hcoeff)


end SpherePacking.Dim24.AppendixA
