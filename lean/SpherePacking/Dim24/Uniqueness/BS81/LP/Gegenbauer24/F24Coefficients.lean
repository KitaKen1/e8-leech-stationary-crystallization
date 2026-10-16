-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.F24
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Gegenbauer expansion of `f24`

With the normalization `(Gegenbauer24 k).eval 1 = 1`, the BS81 polynomial `f24` has a unique
finite expansion

`f24(t) = ∑ k in Finset.range 11, a_k * (Gegenbauer24 k).eval t`,

with all coefficients `a_k ≥ 0`. This is the input needed for the LP dual certificate.

The rational coefficients were cross-checked against the standard Gegenbauer basis
(`lam = 11`, i.e. `S^{23}`) using a symbolic computation.

## Main definitions
* `f24GegenbauerCoeffNat`, `f24GegenbauerCoeff`

## Main statements
* `f24GegenbauerCoeff_nonneg`
* `f24_eq_sum_coeff_mul_gegenbauer24`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP
noncomputable section

open scoped BigOperators

open Polynomial

/-- Coefficients `a_k ∈ ℚ` for the normalized Gegenbauer expansion of `f24`.

Indexing convention: `k = 0..10` (since `deg f24 = 10`).
-/
@[expose] public def f24GegenbauerCoeffNat : ℕ → ℚ
  | 0  => 15 / 1490944
  | 1  => 45 / 186368
  | 2  => 3795 / 1949696
  | 3  => 10005 / 905216
  | 4  => 3983025 / 101384192
  | 5  => 56235 / 487424
  | 6  => 2040905 / 8716288
  | 7  => 270135 / 661504
  | 8  => 16675 / 34816
  | 9  => 150075 / 330752
  | 10 => 310155 / 1323008
  | _  => 0

/-- The coefficient `a_k` as a real number. -/
@[expose] public def f24GegenbauerCoeff (k : ℕ) : ℝ := (f24GegenbauerCoeffNat k : ℝ)

/-- The explicit Gegenbauer expansion polynomial `∑_{k=0}^{10} a_k P_k`. -/
def f24GegenbauerExpansion : Polynomial ℝ :=
  (Finset.range 11).sum (fun k => (C (f24GegenbauerCoeff k)) * Gegenbauer24 k)

/-- The difference `f24 - ∑ a_k P_k`. -/
def f24GegenbauerDiff : Polynomial ℝ :=
  (Uniqueness.BS81.f24 : Polynomial ℝ) - f24GegenbauerExpansion

/-- All explicit rational coefficients `f24GegenbauerCoeffNat k` are nonnegative. -/
public lemma f24GegenbauerCoeffNat_nonneg (k : ℕ) : 0 ≤ f24GegenbauerCoeffNat k := by
  -- All listed coefficients are nonnegative rationals; outside `0..10` the coefficient is `0`.
  -- We do a brute-force case split up to `10`; afterwards the definition reduces to `0`.
  cases k with
  | zero =>
      norm_num [f24GegenbauerCoeffNat]
  | succ k =>
      cases k with
      | zero =>
          norm_num [f24GegenbauerCoeffNat]
      | succ k =>
          cases k with
          | zero =>
              norm_num [f24GegenbauerCoeffNat]
          | succ k =>
              cases k with
              | zero =>
                  norm_num [f24GegenbauerCoeffNat]
              | succ k =>
                  cases k with
                  | zero =>
                      norm_num [f24GegenbauerCoeffNat]
                  | succ k =>
                      cases k with
                      | zero =>
                          norm_num [f24GegenbauerCoeffNat]
                      | succ k =>
                          cases k with
                          | zero =>
                              norm_num [f24GegenbauerCoeffNat]
                          | succ k =>
                              cases k with
                              | zero =>
                                  norm_num [f24GegenbauerCoeffNat]
                              | succ k =>
                                  cases k with
                                  | zero =>
                                      norm_num [f24GegenbauerCoeffNat]
                                  | succ k =>
                                      cases k with
                                      | zero =>
                                          norm_num [f24GegenbauerCoeffNat]
                                      | succ k =>
                                          -- Now the original index is `k + 10`. Split once more:
                                          -- `k = 0` gives the `10`-th coefficient;
                                          -- otherwise we are in the `_ => 0` case.
                                          cases k with
                                          | zero =>
                                              norm_num [f24GegenbauerCoeffNat]
                                          | succ k =>
                                              simp [f24GegenbauerCoeffNat]

/-- All real coefficients `f24GegenbauerCoeff k` are nonnegative. -/
public lemma f24GegenbauerCoeff_nonneg (k : ℕ) : 0 ≤ f24GegenbauerCoeff k := by
  -- Cast from `ℚ` to `ℝ` preserves order.
  simpa [f24GegenbauerCoeff] using!
    (show (0 : ℚ) ≤ f24GegenbauerCoeffNat k from f24GegenbauerCoeffNat_nonneg k)

/-- The constant coefficient `a_0` (BS81's `f_0`). -/
public lemma f24GegenbauerCoeff_zero : f24GegenbauerCoeff 0 = (15 / 1490944 : ℝ) := by
  norm_num [f24GegenbauerCoeff, f24GegenbauerCoeffNat]

/-- The normalization identity `f24(1) = ∑ a_k` (since `Gegenbauer24 k (1) = 1`). -/
lemma f24_eval_one_eq_sum_coeff :
    f24.eval (1 : ℝ) = (Finset.range 11).sum (fun k => f24GegenbauerCoeff k) := by
  -- This is a one-line corollary of the expansion lemma `f24_eq_sum_coeff_mul_gegenbauer24`.
  -- We keep it separate because it is used to check `f24(1)/a0 = 196560`.
  -- Compute `f24.eval 1` from the explicit product definition, and compute the finite sum of
  -- (rational) coefficients directly.
  have hsum :
      (Finset.range 11).sum (fun k => f24GegenbauerCoeff k) = (2025 / 1024 : ℝ) := by
    -- `simp` expands the `range` sum into `0..10` and evaluates the coefficient function;
    -- `norm_num` then closes the rational identity.
    norm_num [f24GegenbauerCoeff, f24GegenbauerCoeffNat, Finset.sum_range_succ]
  -- Finish by comparing both sides to the same explicit rational.
  calc
    f24.eval (1 : ℝ) = (2025 / 1024 : ℝ) := Uniqueness.BS81.f24_eval_one
    _ = (Finset.range 11).sum (fun k => f24GegenbauerCoeff k) := by
      simpa using! hsum.symm

/-!
## Polynomial interpolation proof of the expansion identity

We prove that `f24GegenbauerDiff = 0` by showing:
- `natDegree f24GegenbauerDiff < 11`, and
- it evaluates to `0` at the 11 points `x_i = i/8 - 1` for `i = 0..10`.

The numeric evaluations use local precomputed evaluation lemmas for `Gegenbauer24Val` at these
11 points, to avoid unfolding large recursive computations inside a big `Finset.sum`.
-/

private lemma natDegree_gegenbauer_le (lam : ℝ) : ∀ n : ℕ, (gegenbauer lam n).natDegree ≤ n
  | 0 => by
      simp [gegenbauer]
  | 1 => by
      -- `gegenbauer lam 1 = C (2*lam) * X`.
      simpa [gegenbauer] using!
        (natDegree_C_mul_le (2 * lam : ℝ) (X : Polynomial ℝ)).trans (by simp [natDegree_X])
  | n + 2 => by
      -- Recurrence step: `natDegree (p - q) ≤ max`, and products add degrees.
      have ih₁ : (gegenbauer lam (n + 1)).natDegree ≤ n + 1 := natDegree_gegenbauer_le lam (n + 1)
      have ih₀ : (gegenbauer lam n).natDegree ≤ n := natDegree_gegenbauer_le lam n
      -- Notation for the recurrence scalars.
      let nR : ℝ := n
      let denom : ℝ := (n + 2 : ℝ)
      let a : ℝ := (2 * (nR + 1 + lam)) / denom
      let b : ℝ := (nR + 2 * lam) / denom
      have hCX : (C a * (X : Polynomial ℝ)).natDegree ≤ 1 :=
        (natDegree_C_mul_le a (X : Polynomial ℝ)).trans (by simp [natDegree_X])
      have hA :
          (C a * X * gegenbauer lam (n + 1)).natDegree ≤ n + 2 := by
        -- View as `((C a * X) * gegenbauer lam (n+1))`.
        have :=
          natDegree_mul_le_of_le (p := (C a * (X : Polynomial ℝ))) (q := gegenbauer lam (n + 1))
            (m := 1) (n := n + 1) hCX ih₁
        -- `1 + (n+1) = n+2`.
        simpa [mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using! this
      have hB :
          (C b * gegenbauer lam n).natDegree ≤ n :=
        (natDegree_C_mul_le b (gegenbauer lam n)).trans ih₀
      -- Combine with `natDegree_sub_le` and simplify the `max`.
      have hsub :
          (C a * X * gegenbauer lam (n + 1) - C b * gegenbauer lam n).natDegree ≤
            max (n + 2) n := by
        have := natDegree_sub_le (C a * X * gegenbauer lam (n + 1)) (C b * gegenbauer lam n)
        exact this.trans (max_le_max hA hB)
      have hmax : max (n + 2) n = n + 2 :=
        Nat.max_eq_left (Nat.le_succ_of_le (Nat.le_succ n))
      -- Unfold the definition and finish.
      simpa [gegenbauer, a, b, nR, denom, hmax] using! hsub

private lemma natDegree_Gegenbauer24_le (n : ℕ) : (Gegenbauer24 n).natDegree ≤ n := by
  -- Multiplying by a constant (`C _`) does not increase natDegree.
  have hC :
      (C ((gegenbauer gegenbauer24Param n).eval (1 : ℝ))⁻¹ *
          gegenbauer gegenbauer24Param n).natDegree ≤
        (gegenbauer gegenbauer24Param n).natDegree :=
    natDegree_C_mul_le _ _
  exact hC.trans (natDegree_gegenbauer_le gegenbauer24Param n)

private lemma natDegree_f24_le :
    (Uniqueness.BS81.f24 : Polynomial ℝ).natDegree ≤ 10 := by
  -- Each linear factor has natDegree `1`, and squaring gives `2`.
  have h1 : ((X + C (1 : ℝ) : Polynomial ℝ)).natDegree ≤ 1 := by
    have h : ((X + C (1 : ℝ) : Polynomial ℝ)).natDegree = 1 := by
      simpa using! (natDegree_X_add_C (R := ℝ) (x := (1 : ℝ)))
    have h' : ((X + (1 : Polynomial ℝ) : Polynomial ℝ)).natDegree = 1 := by simpa using! h
    simp [h']
  have h2lin : ((X + C (1 / 2 : ℝ) : Polynomial ℝ)).natDegree ≤ 1 := by
    have h : ((X + C (1 / 2 : ℝ) : Polynomial ℝ)).natDegree = 1 :=
      natDegree_X_add_C (R := ℝ) (x := (1 / 2 : ℝ))
    exact le_of_eq h
  have h2 : ((X + C (1 / 2 : ℝ) : Polynomial ℝ) ^ 2).natDegree ≤ 2 :=
    natDegree_pow_le_of_le (p := (X + C (1 / 2 : ℝ) : Polynomial ℝ)) (n := 2) (m := 1) h2lin
  have h3lin : ((X + C (1 / 4 : ℝ) : Polynomial ℝ)).natDegree ≤ 1 := by
    have h : ((X + C (1 / 4 : ℝ) : Polynomial ℝ)).natDegree = 1 :=
      natDegree_X_add_C (R := ℝ) (x := (1 / 4 : ℝ))
    exact le_of_eq h
  have h3 : ((X + C (1 / 4 : ℝ) : Polynomial ℝ) ^ 2).natDegree ≤ 2 :=
    natDegree_pow_le_of_le (p := (X + C (1 / 4 : ℝ) : Polynomial ℝ)) (n := 2) (m := 1) h3lin
  have hX : ((X : Polynomial ℝ)).natDegree ≤ 1 := by
    simp [natDegree_X]
  have h4 : ((X : Polynomial ℝ) ^ 2).natDegree ≤ 2 :=
    natDegree_pow_le_of_le (p := (X : Polynomial ℝ)) (n := 2) (m := 1) hX
  have h5lin : ((X - C (1 / 4 : ℝ) : Polynomial ℝ)).natDegree ≤ 1 :=
    natDegree_X_sub_C_le (1 / 4)
  have h5 : ((X - C (1 / 4 : ℝ) : Polynomial ℝ) ^ 2).natDegree ≤ 2 :=
    natDegree_pow_le_of_le (p := (X - C (1 / 4 : ℝ) : Polynomial ℝ)) (n := 2) (m := 1) h5lin
  have h6 : ((X - C (1 / 2 : ℝ) : Polynomial ℝ)).natDegree ≤ 1 :=
    natDegree_X_sub_C_le (1 / 2)
  -- Combine along the product structure.
  have h12 :
      natDegree
          ((X + C (1 : ℝ) : Polynomial ℝ) *
            (X + C (1 / 2 : ℝ) : Polynomial ℝ) ^ 2) ≤
        1 + 2 :=
    natDegree_mul_le_of_le (m := 1) (n := 2) h1 h2
  have h123 :
      natDegree (((X + C (1 : ℝ) : Polynomial ℝ) * (X + C (1 / 2 : ℝ) : Polynomial ℝ) ^ 2) *
        (X + C (1 / 4 : ℝ) : Polynomial ℝ) ^ 2) ≤ (1 + 2) + 2 :=
    natDegree_mul_le_of_le (m := 1 + 2) (n := 2) h12 h3
  have h1234 :
      natDegree ((((X + C (1 : ℝ) : Polynomial ℝ) * (X + C (1 / 2 : ℝ) : Polynomial ℝ) ^ 2) *
        (X + C (1 / 4 : ℝ) : Polynomial ℝ) ^ 2) * X ^ 2) ≤ ((1 + 2) + 2) + 2 :=
    natDegree_mul_le_of_le (m := (1 + 2) + 2) (n := 2) h123 h4
  have h12345 :
      natDegree (((((X + C (1 : ℝ) : Polynomial ℝ) * (X + C (1 / 2 : ℝ) : Polynomial ℝ) ^ 2) *
        (X + C (1 / 4 : ℝ) : Polynomial ℝ) ^ 2) * X ^ 2) *
          (X - C (1 / 4 : ℝ) : Polynomial ℝ) ^ 2) ≤
        (((1 + 2) + 2) + 2) + 2 :=
    natDegree_mul_le_of_le (m := ((1 + 2) + 2) + 2) (n := 2) h1234 h5
  have h123456 :
      natDegree ((((((X + C (1 : ℝ) : Polynomial ℝ) * (X + C (1 / 2 : ℝ) : Polynomial ℝ) ^ 2) *
        (X + C (1 / 4 : ℝ) : Polynomial ℝ) ^ 2) * X ^ 2) *
          (X - C (1 / 4 : ℝ) : Polynomial ℝ) ^ 2) *
        (X - C (1 / 2 : ℝ) : Polynomial ℝ)) ≤ ((((1 + 2) + 2) + 2) + 2) + 1 :=
    natDegree_mul_le_of_le (m := (((1 + 2) + 2) + 2) + 2) (n := 1) h12345 h6
  -- Unfold `f24` and close by arithmetic.
  simpa [Uniqueness.BS81.f24, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using!
    (le_trans h123456 (by decide))

private lemma natDegree_f24GegenbauerExpansion_le : f24GegenbauerExpansion.natDegree ≤ 10 := by
  -- Each term has degree ≤ k ≤ 10 on `range 11`.
  -- Unfold so the goal is about a `Finset.sum`.
  simp only [f24GegenbauerExpansion]
  have hterm : ∀ k : ℕ, k ∈ Finset.range 11 →
      (C (f24GegenbauerCoeff k) * Gegenbauer24 k).natDegree ≤ 10 := by
    intro k hk
    have hk' : k ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hmul :
        (C (f24GegenbauerCoeff k) * Gegenbauer24 k).natDegree ≤ (Gegenbauer24 k).natDegree := by
      exact natDegree_C_mul_le _ _
    exact le_trans (le_trans hmul (natDegree_Gegenbauer24_le k)) hk'
  exact natDegree_sum_le_of_forall_le (Finset.range 11)
      (fun i => C (f24GegenbauerCoeff i) * Gegenbauer24 i) hterm

private lemma natDegree_f24GegenbauerDiff_lt : f24GegenbauerDiff.natDegree < 11 := by
  have hsub :
      f24GegenbauerDiff.natDegree ≤
        max
          (Uniqueness.BS81.f24 : Polynomial ℝ).natDegree
          f24GegenbauerExpansion.natDegree := by
    simpa [f24GegenbauerDiff, f24GegenbauerExpansion] using!
      (natDegree_sub_le (Uniqueness.BS81.f24 : Polynomial ℝ) f24GegenbauerExpansion)
  have hmax :
      max
          (Uniqueness.BS81.f24 : Polynomial ℝ).natDegree
          f24GegenbauerExpansion.natDegree ≤
        10 :=
    max_le_iff.2 ⟨natDegree_f24_le, natDegree_f24GegenbauerExpansion_le⟩
  exact lt_of_le_of_lt (hsub.trans hmax) (by decide)

/-!
### Precomputed `Gegenbauer24Val` evaluation lemmas

These are used by `simp_f24diff` to keep the interpolation proof fast and avoid unfolding
large recursive computations.
-/

macro "g24v" : tactic =>
  `(tactic| simp [Gegenbauer24Val, gegenbauerVal] <;> norm_num [gegenbauer24Param])

/-! #### x = -1 -/
private lemma g24v_negOne_0 : Gegenbauer24Val 0 (-1 : ℝ) = (1 : ℝ) := by
  g24v
private lemma g24v_negOne_1 : Gegenbauer24Val 1 (-1 : ℝ) = (-1 : ℝ) := by
  g24v
private lemma g24v_negOne_2 : Gegenbauer24Val 2 (-1 : ℝ) = (1 : ℝ) := by
  g24v
private lemma g24v_negOne_3 : Gegenbauer24Val 3 (-1 : ℝ) = (-1 : ℝ) := by
  g24v
private lemma g24v_negOne_4 : Gegenbauer24Val 4 (-1 : ℝ) = (1 : ℝ) := by
  g24v
private lemma g24v_negOne_5 : Gegenbauer24Val 5 (-1 : ℝ) = (-1 : ℝ) := by g24v
private lemma g24v_negOne_6 : Gegenbauer24Val 6 (-1 : ℝ) = (1 : ℝ) := by g24v
private lemma g24v_negOne_7 : Gegenbauer24Val 7 (-1 : ℝ) = (-1 : ℝ) := by g24v
private lemma g24v_negOne_8 : Gegenbauer24Val 8 (-1 : ℝ) = (1 : ℝ) := by g24v
private lemma g24v_negOne_9 : Gegenbauer24Val 9 (-1 : ℝ) = (-1 : ℝ) := by g24v
private lemma g24v_negOne_10 : Gegenbauer24Val 10 (-1 : ℝ) = (1 : ℝ) := by g24v

/-! #### x = -7/8 -/
private lemma g24v_negSevenEighths_0 : Gegenbauer24Val 0 (-(7 : ℝ) / 8) = (1 : ℝ) := by g24v
private lemma g24v_negSevenEighths_1 : Gegenbauer24Val 1 (-(7 : ℝ) / 8) = (-7 / 8 : ℝ) := by g24v
private lemma g24v_negSevenEighths_2 : Gegenbauer24Val 2 (-(7 : ℝ) / 8) = (139 / 184 : ℝ) := by g24v
private lemma g24v_negSevenEighths_3 :
    Gegenbauer24Val 3 (-(7 : ℝ) / 8) = (-3787 / 5888 : ℝ) := by g24v
private lemma g24v_negSevenEighths_4 :
    Gegenbauer24Val 4 (-(7 : ℝ) / 8) = (6355 / 11776 : ℝ) := by g24v
private lemma g24v_negSevenEighths_5 :
    Gegenbauer24Val 5 (-(7 : ℝ) / 8) = (-42007 / 94208 : ℝ) := by g24v
private lemma g24v_negSevenEighths_6 :
    Gegenbauer24Val 6 (-(7 : ℝ) / 8) = (8537 / 23552 : ℝ) := by g24v
private lemma g24v_negSevenEighths_7 :
    Gegenbauer24Val 7 (-(7 : ℝ) / 8) = (-109123 / 376832 : ℝ) := by g24v
private lemma g24v_negSevenEighths_8 :
    Gegenbauer24Val 8 (-(7 : ℝ) / 8) = (4962461 / 21856256 : ℝ) := by g24v
private lemma g24v_negSevenEighths_9 :
    Gegenbauer24Val 9 (-(7 : ℝ) / 8) = (-30498335 / 174850048 : ℝ) := by g24v
private lemma g24v_negSevenEighths_10 :
    Gegenbauer24Val 10 (-(7 : ℝ) / 8) = (710144533 / 5420351488 : ℝ) := by g24v

/-! #### x = -3/4 -/
private lemma g24v_negThreeQuarters_0 : Gegenbauer24Val 0 (-(3 : ℝ) / 4) = (1 : ℝ) := by g24v
private lemma g24v_negThreeQuarters_1 : Gegenbauer24Val 1 (-(3 : ℝ) / 4) = (-3 / 4 : ℝ) := by g24v
private lemma g24v_negThreeQuarters_2 : Gegenbauer24Val 2 (-(3 : ℝ) / 4) = (25 / 46 : ℝ) := by g24v
private lemma g24v_negThreeQuarters_3 :
    Gegenbauer24Val 3 (-(3 : ℝ) / 4) = (-279 / 736 : ℝ) := by g24v
private lemma g24v_negThreeQuarters_4 :
    Gegenbauer24Val 4 (-(3 : ℝ) / 4) = (4659 / 18400 : ℝ) := by g24v
private lemma g24v_negThreeQuarters_5 :
    Gegenbauer24Val 5 (-(3 : ℝ) / 4) = (-2367 / 14720 : ℝ) := by g24v
private lemma g24v_negThreeQuarters_6 :
    Gegenbauer24Val 6 (-(3 : ℝ) / 4) = (3181 / 33120 : ℝ) := by g24v
private lemma g24v_negThreeQuarters_7 :
    Gegenbauer24Val 7 (-(3 : ℝ) / 4) = (-2341 / 44160 : ℝ) := by g24v
private lemma g24v_negThreeQuarters_8 :
    Gegenbauer24Val 8 (-(3 : ℝ) / 4) = (100553 / 3841920 : ℝ) := by g24v
private lemma g24v_negThreeQuarters_9 :
    Gegenbauer24Val 9 (-(3 : ℝ) / 4) = (-91587 / 8537600 : ℝ) := by g24v
private lemma g24v_negThreeQuarters_10 :
    Gegenbauer24Val 10 (-(3 : ℝ) / 4) = (14731 / 5293312 : ℝ) := by g24v

/-! #### x = -5/8 -/
private lemma g24v_negFiveEighths_0 : Gegenbauer24Val 0 (-(5 : ℝ) / 8) = (1 : ℝ) := by g24v
private lemma g24v_negFiveEighths_1 : Gegenbauer24Val 1 (-(5 : ℝ) / 8) = (-5 / 8 : ℝ) := by g24v
private lemma g24v_negFiveEighths_2 : Gegenbauer24Val 2 (-(5 : ℝ) / 8) = (67 / 184 : ℝ) := by g24v
private lemma g24v_negFiveEighths_3 :
    Gegenbauer24Val 3 (-(5 : ℝ) / 8) = (-1145 / 5888 : ℝ) := by g24v
private lemma g24v_negFiveEighths_4 :
    Gegenbauer24Val 4 (-(5 : ℝ) / 8) = (27211 / 294400 : ℝ) := by g24v
private lemma g24v_negFiveEighths_5 :
    Gegenbauer24Val 5 (-(5 : ℝ) / 8) = (-3461 / 94208 : ℝ) := by g24v
private lemma g24v_negFiveEighths_6 :
    Gegenbauer24Val 6 (-(5 : ℝ) / 8) = (1189 / 117760 : ℝ) := by g24v
private lemma g24v_negFiveEighths_7 :
    Gegenbauer24Val 7 (-(5 : ℝ) / 8) = (79 / 376832 : ℝ) := by g24v
private lemma g24v_negFiveEighths_8 :
    Gegenbauer24Val 8 (-(5 : ℝ) / 8) = (-284111 / 109281280 : ℝ) := by g24v
private lemma g24v_negFiveEighths_9 :
    Gegenbauer24Val 9 (-(5 : ℝ) / 8) = (350099 / 174850048 : ℝ) := by g24v
private lemma g24v_negFiveEighths_10 :
    Gegenbauer24Val 10 (-(5 : ℝ) / 8) = (-1013321 / 1178337280 : ℝ) := by g24v

/-! #### x = -1/2 -/
private lemma g24v_negHalf_0 : Gegenbauer24Val 0 (-(1 : ℝ) / 2) = (1 : ℝ) := by g24v
private lemma g24v_negHalf_1 : Gegenbauer24Val 1 (-(1 : ℝ) / 2) = (-1 / 2 : ℝ) := by g24v
private lemma g24v_negHalf_2 : Gegenbauer24Val 2 (-(1 : ℝ) / 2) = (5 / 23 : ℝ) := by g24v
private lemma g24v_negHalf_3 : Gegenbauer24Val 3 (-(1 : ℝ) / 2) = (-7 / 92 : ℝ) := by g24v
private lemma g24v_negHalf_4 : Gegenbauer24Val 4 (-(1 : ℝ) / 2) = (19 / 1150 : ℝ) := by g24v
private lemma g24v_negHalf_5 : Gegenbauer24Val 5 (-(1 : ℝ) / 2) = (1 / 460 : ℝ) := by g24v
private lemma g24v_negHalf_6 : Gegenbauer24Val 6 (-(1 : ℝ) / 2) = (-1 / 230 : ℝ) := by g24v
private lemma g24v_negHalf_7 : Gegenbauer24Val 7 (-(1 : ℝ) / 2) = (1 / 460 : ℝ) := by g24v
private lemma g24v_negHalf_8 : Gegenbauer24Val 8 (-(1 : ℝ) / 2) = (-1 / 3335 : ℝ) := by g24v
private lemma g24v_negHalf_9 : Gegenbauer24Val 9 (-(1 : ℝ) / 2) = (-13 / 33350 : ℝ) := by g24v
private lemma g24v_negHalf_10 : Gegenbauer24Val 10 (-(1 : ℝ) / 2) = (7 / 20677 : ℝ) := by g24v

/-! #### x = -3/8 -/
private lemma g24v_negThreeEighths_0 : Gegenbauer24Val 0 (-(3 : ℝ) / 8) = (1 : ℝ) := by g24v
private lemma g24v_negThreeEighths_1 : Gegenbauer24Val 1 (-(3 : ℝ) / 8) = (-3 / 8 : ℝ) := by g24v
private lemma g24v_negThreeEighths_2 : Gegenbauer24Val 2 (-(3 : ℝ) / 8) = (19 / 184 : ℝ) := by g24v
private lemma g24v_negThreeEighths_3 :
    Gegenbauer24Val 3 (-(3 : ℝ) / 8) = (-63 / 5888 : ℝ) := by g24v
private lemma g24v_negThreeEighths_4 :
    Gegenbauer24Val 4 (-(3 : ℝ) / 8) = (-93 / 11776 : ℝ) := by g24v
private lemma g24v_negThreeEighths_5 :
    Gegenbauer24Val 5 (-(3 : ℝ) / 8) = (477 / 94208 : ℝ) := by g24v
private lemma g24v_negThreeEighths_6 :
    Gegenbauer24Val 6 (-(3 : ℝ) / 8) = (-167 / 211968 : ℝ) := by g24v
private lemma g24v_negThreeEighths_7 :
    Gegenbauer24Val 7 (-(3 : ℝ) / 8) = (-821 / 1130496 : ℝ) := by g24v
private lemma g24v_negThreeEighths_8 :
    Gegenbauer24Val 8 (-(3 : ℝ) / 8) = (103909 / 196706304 : ℝ) := by g24v
private lemma g24v_negThreeEighths_9 :
    Gegenbauer24Val 9 (-(3 : ℝ) / 8) = (-10011 / 174850048 : ℝ) := by g24v
private lemma g24v_negThreeEighths_10 :
    Gegenbauer24Val 10 (-(3 : ℝ) / 8) = (-681107 / 5420351488 : ℝ) := by g24v

/-! #### x = -1/4 -/
private lemma g24v_negQuarter_0 : Gegenbauer24Val 0 (-(1 : ℝ) / 4) = (1 : ℝ) := by g24v
private lemma g24v_negQuarter_1 : Gegenbauer24Val 1 (-(1 : ℝ) / 4) = (-1 / 4 : ℝ) := by g24v
private lemma g24v_negQuarter_2 : Gegenbauer24Val 2 (-(1 : ℝ) / 4) = (1 / 46 : ℝ) := by g24v
private lemma g24v_negQuarter_3 : Gegenbauer24Val 3 (-(1 : ℝ) / 4) = (11 / 736 : ℝ) := by g24v
private lemma g24v_negQuarter_4 : Gegenbauer24Val 4 (-(1 : ℝ) / 4) = (-5 / 736 : ℝ) := by g24v
private lemma g24v_negQuarter_5 : Gegenbauer24Val 5 (-(1 : ℝ) / 4) = (-1 / 2944 : ℝ) := by g24v
private lemma g24v_negQuarter_6 : Gegenbauer24Val 6 (-(1 : ℝ) / 4) = (1 / 736 : ℝ) := by g24v
private lemma g24v_negQuarter_7 : Gegenbauer24Val 7 (-(1 : ℝ) / 4) = (-1 / 2944 : ℝ) := by g24v
private lemma g24v_negQuarter_8 : Gegenbauer24Val 8 (-(1 : ℝ) / 4) = (-19 / 85376 : ℝ) := by g24v
private lemma g24v_negQuarter_9 : Gegenbauer24Val 9 (-(1 : ℝ) / 4) = (55 / 341504 : ℝ) := by g24v
private lemma g24v_negQuarter_10 : Gegenbauer24Val 10 (-(1 : ℝ) / 4) = (67 / 5293312 : ℝ) := by g24v

/-! #### x = -1/8 -/
private lemma g24v_negEighth_0 : Gegenbauer24Val 0 (-(1 : ℝ) / 8) = (1 : ℝ) := by g24v
private lemma g24v_negEighth_1 : Gegenbauer24Val 1 (-(1 : ℝ) / 8) = (-1 / 8 : ℝ) := by g24v
private lemma g24v_negEighth_2 : Gegenbauer24Val 2 (-(1 : ℝ) / 8) = (-5 / 184 : ℝ) := by g24v
private lemma g24v_negEighth_3 : Gegenbauer24Val 3 (-(1 : ℝ) / 8) = (83 / 5888 : ℝ) := by g24v
private lemma g24v_negEighth_4 : Gegenbauer24Val 4 (-(1 : ℝ) / 8) = (379 / 294400 : ℝ) := by g24v
private lemma g24v_negEighth_5 : Gegenbauer24Val 5 (-(1 : ℝ) / 8) = (-1109 / 471040 : ℝ) := by g24v
private lemma g24v_negEighth_6 : Gegenbauer24Val 6 (-(1 : ℝ) / 8) = (13 / 117760 : ℝ) := by g24v
private lemma g24v_negEighth_7 : Gegenbauer24Val 7 (-(1 : ℝ) / 8) = (919 / 1884160 : ℝ) := by g24v
private lemma g24v_negEighth_8 :
    Gegenbauer24Val 8 (-(1 : ℝ) / 8) = (-11183 / 109281280 : ℝ) := by g24v
private lemma g24v_negEighth_9 :
    Gegenbauer24Val 9 (-(1 : ℝ) / 8) = (-497729 / 4371251200 : ℝ) := by g24v
private lemma g24v_negEighth_10 :
    Gegenbauer24Val 10 (-(1 : ℝ) / 8) = (260581 / 5420351488 : ℝ) := by g24v

/-! #### x = 0 -/
private lemma g24v_zero_0 : Gegenbauer24Val 0 (0 : ℝ) = (1 : ℝ) := by
  g24v
private lemma g24v_zero_1 : Gegenbauer24Val 1 (0 : ℝ) = (0 : ℝ) := by
  g24v
private lemma g24v_zero_2 : Gegenbauer24Val 2 (0 : ℝ) = (-1 / 23 : ℝ) := by
  g24v
private lemma g24v_zero_3 : Gegenbauer24Val 3 (0 : ℝ) = (0 : ℝ) := by
  g24v
private lemma g24v_zero_4 : Gegenbauer24Val 4 (0 : ℝ) = (3 / 575 : ℝ) := by
  g24v
private lemma g24v_zero_5 : Gegenbauer24Val 5 (0 : ℝ) = (0 : ℝ) := by
  g24v
private lemma g24v_zero_6 : Gegenbauer24Val 6 (0 : ℝ) = (-1 / 1035 : ℝ) := by
  g24v
private lemma g24v_zero_7 : Gegenbauer24Val 7 (0 : ℝ) = (0 : ℝ) := by
  g24v
private lemma g24v_zero_8 : Gegenbauer24Val 8 (0 : ℝ) = (7 / 30015 : ℝ) := by
  g24v
private lemma g24v_zero_9 : Gegenbauer24Val 9 (0 : ℝ) = (0 : ℝ) := by
  g24v
private lemma g24v_zero_10 : Gegenbauer24Val 10 (0 : ℝ) = (-7 / 103385 : ℝ) := by
  g24v

/-! #### x = 1/8 -/
private lemma g24v_eighth_0 : Gegenbauer24Val 0 ((1 : ℝ) / 8) = (1 : ℝ) := by
  g24v
private lemma g24v_eighth_1 : Gegenbauer24Val 1 ((1 : ℝ) / 8) = (1 / 8 : ℝ) := by
  g24v
private lemma g24v_eighth_2 : Gegenbauer24Val 2 ((1 : ℝ) / 8) = (-5 / 184 : ℝ) := by
  g24v
private lemma g24v_eighth_3 : Gegenbauer24Val 3 ((1 : ℝ) / 8) = (-83 / 5888 : ℝ) := by
  g24v
private lemma g24v_eighth_4 : Gegenbauer24Val 4 ((1 : ℝ) / 8) = (379 / 294400 : ℝ) := by
  g24v
private lemma g24v_eighth_5 : Gegenbauer24Val 5 ((1 : ℝ) / 8) = (1109 / 471040 : ℝ) := by
  g24v
private lemma g24v_eighth_6 : Gegenbauer24Val 6 ((1 : ℝ) / 8) = (13 / 117760 : ℝ) := by
  g24v
private lemma g24v_eighth_7 : Gegenbauer24Val 7 ((1 : ℝ) / 8) = (-919 / 1884160 : ℝ) := by
  g24v
private lemma g24v_eighth_8 : Gegenbauer24Val 8 ((1 : ℝ) / 8) = (-11183 / 109281280 : ℝ) := by
  g24v
private lemma g24v_eighth_9 : Gegenbauer24Val 9 ((1 : ℝ) / 8) = (497729 / 4371251200 : ℝ) := by
  g24v
private lemma g24v_eighth_10 : Gegenbauer24Val 10 ((1 : ℝ) / 8) = (260581 / 5420351488 : ℝ) := by
  g24v

/-! #### x = 1/4 -/
private lemma g24v_quarter_0 : Gegenbauer24Val 0 ((1 : ℝ) / 4) = (1 : ℝ) := by
  g24v
private lemma g24v_quarter_1 : Gegenbauer24Val 1 ((1 : ℝ) / 4) = (1 / 4 : ℝ) := by
  g24v
private lemma g24v_quarter_2 : Gegenbauer24Val 2 ((1 : ℝ) / 4) = (1 / 46 : ℝ) := by
  g24v
private lemma g24v_quarter_3 : Gegenbauer24Val 3 ((1 : ℝ) / 4) = (-11 / 736 : ℝ) := by
  g24v
private lemma g24v_quarter_4 : Gegenbauer24Val 4 ((1 : ℝ) / 4) = (-5 / 736 : ℝ) := by
  g24v
private lemma g24v_quarter_5 : Gegenbauer24Val 5 ((1 : ℝ) / 4) = (1 / 2944 : ℝ) := by
  g24v
private lemma g24v_quarter_6 : Gegenbauer24Val 6 ((1 : ℝ) / 4) = (1 / 736 : ℝ) := by
  g24v
private lemma g24v_quarter_7 : Gegenbauer24Val 7 ((1 : ℝ) / 4) = (1 / 2944 : ℝ) := by
  g24v
private lemma g24v_quarter_8 : Gegenbauer24Val 8 ((1 : ℝ) / 4) = (-19 / 85376 : ℝ) := by
  g24v
private lemma g24v_quarter_9 : Gegenbauer24Val 9 ((1 : ℝ) / 4) = (-55 / 341504 : ℝ) := by
  g24v
private lemma g24v_quarter_10 : Gegenbauer24Val 10 ((1 : ℝ) / 4) = (67 / 5293312 : ℝ) := by
  g24v

/-! #### alias lemmas: `simp` can rewrite `1 / m` to `(m : ℝ)⁻¹` -/

private lemma g24v_invFour_0 : Gegenbauer24Val 0 ((4 : ℝ)⁻¹) = (1 : ℝ) := by
  simpa [one_div] using! g24v_quarter_0
private lemma g24v_invFour_1 : Gegenbauer24Val 1 ((4 : ℝ)⁻¹) = (1 / 4 : ℝ) := by
  simpa [one_div] using! g24v_quarter_1
private lemma g24v_invFour_2 : Gegenbauer24Val 2 ((4 : ℝ)⁻¹) = (1 / 46 : ℝ) := by
  simpa [one_div] using! g24v_quarter_2
private lemma g24v_invFour_3 : Gegenbauer24Val 3 ((4 : ℝ)⁻¹) = (-11 / 736 : ℝ) := by
  simpa [one_div] using! g24v_quarter_3
private lemma g24v_invFour_4 : Gegenbauer24Val 4 ((4 : ℝ)⁻¹) = (-5 / 736 : ℝ) := by
  simpa [one_div] using! g24v_quarter_4
private lemma g24v_invFour_5 : Gegenbauer24Val 5 ((4 : ℝ)⁻¹) = (1 / 2944 : ℝ) := by
  simpa [one_div] using! g24v_quarter_5
private lemma g24v_invFour_6 : Gegenbauer24Val 6 ((4 : ℝ)⁻¹) = (1 / 736 : ℝ) := by
  simpa [one_div] using! g24v_quarter_6
private lemma g24v_invFour_7 : Gegenbauer24Val 7 ((4 : ℝ)⁻¹) = (1 / 2944 : ℝ) := by
  simpa [one_div] using! g24v_quarter_7
private lemma g24v_invFour_8 : Gegenbauer24Val 8 ((4 : ℝ)⁻¹) = (-19 / 85376 : ℝ) := by
  simpa [one_div] using! g24v_quarter_8
private lemma g24v_invFour_9 : Gegenbauer24Val 9 ((4 : ℝ)⁻¹) = (-55 / 341504 : ℝ) := by
  simpa [one_div] using! g24v_quarter_9
private lemma g24v_invFour_10 : Gegenbauer24Val 10 ((4 : ℝ)⁻¹) = (67 / 5293312 : ℝ) := by
  simpa [one_div] using! g24v_quarter_10

private lemma g24v_invEight_0 : Gegenbauer24Val 0 ((8 : ℝ)⁻¹) = (1 : ℝ) := by
  simpa [one_div] using! g24v_eighth_0
private lemma g24v_invEight_1 : Gegenbauer24Val 1 ((8 : ℝ)⁻¹) = (1 / 8 : ℝ) := by
  simpa [one_div] using! g24v_eighth_1
private lemma g24v_invEight_2 : Gegenbauer24Val 2 ((8 : ℝ)⁻¹) = (-5 / 184 : ℝ) := by
  simpa [one_div] using! g24v_eighth_2
private lemma g24v_invEight_3 : Gegenbauer24Val 3 ((8 : ℝ)⁻¹) = (-83 / 5888 : ℝ) := by
  simpa [one_div] using! g24v_eighth_3
private lemma g24v_invEight_4 : Gegenbauer24Val 4 ((8 : ℝ)⁻¹) = (379 / 294400 : ℝ) := by
  simpa [one_div] using! g24v_eighth_4
private lemma g24v_invEight_5 : Gegenbauer24Val 5 ((8 : ℝ)⁻¹) = (1109 / 471040 : ℝ) := by
  simpa [one_div] using! g24v_eighth_5
private lemma g24v_invEight_6 : Gegenbauer24Val 6 ((8 : ℝ)⁻¹) = (13 / 117760 : ℝ) := by
  simpa [one_div] using! g24v_eighth_6
private lemma g24v_invEight_7 : Gegenbauer24Val 7 ((8 : ℝ)⁻¹) = (-919 / 1884160 : ℝ) := by
  simpa [one_div] using! g24v_eighth_7
private lemma g24v_invEight_8 : Gegenbauer24Val 8 ((8 : ℝ)⁻¹) = (-11183 / 109281280 : ℝ) := by
  simpa [one_div] using! g24v_eighth_8
private lemma g24v_invEight_9 : Gegenbauer24Val 9 ((8 : ℝ)⁻¹) = (497729 / 4371251200 : ℝ) := by
  simpa [one_div] using! g24v_eighth_9
private lemma g24v_invEight_10 : Gegenbauer24Val 10 ((8 : ℝ)⁻¹) = (260581 / 5420351488 : ℝ) := by
  simpa [one_div] using! g24v_eighth_10

macro "simp_f24diff" : tactic =>
  `(tactic|
    (simp [f24GegenbauerDiff, f24GegenbauerExpansion, Uniqueness.BS81.f24_eval, f24GegenbauerCoeff,
        f24GegenbauerCoeffNat, Gegenbauer24_eval_eq,
        g24v_negOne_1, g24v_negOne_2, g24v_negOne_3, g24v_negOne_4, g24v_negOne_5, g24v_negOne_6,
        g24v_negOne_7, g24v_negOne_8, g24v_negOne_9, g24v_negOne_10,
        g24v_negSevenEighths_1, g24v_negSevenEighths_2, g24v_negSevenEighths_3,
        g24v_negSevenEighths_4, g24v_negSevenEighths_5, g24v_negSevenEighths_6,
        g24v_negSevenEighths_7, g24v_negSevenEighths_8, g24v_negSevenEighths_9,
        g24v_negSevenEighths_10,
        g24v_negThreeQuarters_1, g24v_negThreeQuarters_2, g24v_negThreeQuarters_3,
        g24v_negThreeQuarters_4, g24v_negThreeQuarters_5, g24v_negThreeQuarters_6,
        g24v_negThreeQuarters_7, g24v_negThreeQuarters_8, g24v_negThreeQuarters_9,
        g24v_negThreeQuarters_10,
        g24v_negFiveEighths_1, g24v_negFiveEighths_2, g24v_negFiveEighths_3, g24v_negFiveEighths_4,
        g24v_negFiveEighths_5, g24v_negFiveEighths_6, g24v_negFiveEighths_7, g24v_negFiveEighths_8,
        g24v_negFiveEighths_9, g24v_negFiveEighths_10,
        g24v_negHalf_1, g24v_negHalf_2, g24v_negHalf_3, g24v_negHalf_4,
        g24v_negHalf_5, g24v_negHalf_6, g24v_negHalf_7, g24v_negHalf_8, g24v_negHalf_9,
        g24v_negHalf_10,
        g24v_negThreeEighths_1, g24v_negThreeEighths_2, g24v_negThreeEighths_3,
        g24v_negThreeEighths_4, g24v_negThreeEighths_5, g24v_negThreeEighths_6,
        g24v_negThreeEighths_7, g24v_negThreeEighths_8, g24v_negThreeEighths_9,
        g24v_negThreeEighths_10,
        g24v_negQuarter_1, g24v_negQuarter_2, g24v_negQuarter_3, g24v_negQuarter_4,
        g24v_negQuarter_5, g24v_negQuarter_6, g24v_negQuarter_7, g24v_negQuarter_8,
        g24v_negQuarter_9, g24v_negQuarter_10,
        g24v_negEighth_1, g24v_negEighth_2, g24v_negEighth_3, g24v_negEighth_4, g24v_negEighth_5,
        g24v_negEighth_6, g24v_negEighth_7, g24v_negEighth_8, g24v_negEighth_9, g24v_negEighth_10,
        g24v_zero_1, g24v_zero_2, g24v_zero_3, g24v_zero_4, g24v_zero_5, g24v_zero_6, g24v_zero_7,
        g24v_zero_8, g24v_zero_9, g24v_zero_10,
        g24v_invEight_1, g24v_invEight_2, g24v_invEight_3, g24v_invEight_4, g24v_invEight_5,
        g24v_invEight_6, g24v_invEight_7, g24v_invEight_8, g24v_invEight_9, g24v_invEight_10,
        g24v_invFour_1, g24v_invFour_2, g24v_invFour_3, g24v_invFour_4, g24v_invFour_5,
        g24v_invFour_6, g24v_invFour_7, g24v_invFour_8, g24v_invFour_9, g24v_invFour_10,
        Finset.sum_range_succ, one_div]
      ; norm_num))

-- Numeric evaluation lemmas for `f24GegenbauerDiff` at the 11 interpolation points.
lemma f24GegenbauerDiff_eval_negOne : f24GegenbauerDiff.eval (-1 : ℝ) = 0 := by
  simp_f24diff

lemma f24GegenbauerDiff_eval_negSevenEighths :
    f24GegenbauerDiff.eval (-(7 : ℝ) / 8) = 0 := by
  simp_f24diff

lemma f24GegenbauerDiff_eval_negThreeQuarters :
    f24GegenbauerDiff.eval (-(3 : ℝ) / 4) = 0 := by
  simp_f24diff

lemma f24GegenbauerDiff_eval_negFiveEighths :
    f24GegenbauerDiff.eval (-(5 : ℝ) / 8) = 0 := by
  simp_f24diff

lemma f24GegenbauerDiff_eval_negHalf :
    f24GegenbauerDiff.eval (-(1 : ℝ) / 2) = 0 := by
  simp_f24diff

lemma f24GegenbauerDiff_eval_negThreeEighths :
    f24GegenbauerDiff.eval (-(3 : ℝ) / 8) = 0 := by
  simp_f24diff

lemma f24GegenbauerDiff_eval_negQuarter :
    f24GegenbauerDiff.eval (-(1 : ℝ) / 4) = 0 := by
  simp_f24diff

lemma f24GegenbauerDiff_eval_negEighth :
    f24GegenbauerDiff.eval (-(1 : ℝ) / 8) = 0 := by
  simp_f24diff

lemma f24GegenbauerDiff_eval_zero : f24GegenbauerDiff.eval (0 : ℝ) = 0 := by
  simp_f24diff

lemma f24GegenbauerDiff_eval_invEight :
    f24GegenbauerDiff.eval ((8 : ℝ)⁻¹) = 0 := by
  simp_f24diff

lemma f24GegenbauerDiff_eval_invFour :
    f24GegenbauerDiff.eval ((4 : ℝ)⁻¹) = 0 := by
  simp_f24diff

/-- The key algebraic identity: `f24` equals its Gegenbauer expansion. -/
public lemma f24_eq_sum_coeff_mul_gegenbauer24 :
    (Uniqueness.BS81.f24 : Polynomial ℝ) =
      (Finset.range 11).sum (fun k => (C (f24GegenbauerCoeff k)) * Gegenbauer24 k) := by
  -- We prove the identity by polynomial interpolation on the 11 points `x_i = i/8 - 1`.
  let x : Fin 11 → ℝ := fun i => ((i : ℕ) : ℝ) / 8 - 1
  have hx_inj : Function.Injective x := by
    intro a b hab
    apply Fin.ext
    have hab' : (((a : ℕ) : ℝ) / 8) = (((b : ℕ) : ℝ) / 8) := by
      grind only
    simp_all
  have heval : ∀ i : Fin 11, f24GegenbauerDiff.eval (x i) = 0 := by
    intro i
    fin_cases i
    · -- i = 0, x = -1
      have hx0 : x (0 : Fin 11) = (-1 : ℝ) := by
        simp [x]
      simpa [hx0] using! f24GegenbauerDiff_eval_negOne
    · -- i = 1, x = -7/8
      have hx1 : x (1 : Fin 11) = (-(7 : ℝ) / 8) := by
        norm_num [x]
      simpa [hx1] using! f24GegenbauerDiff_eval_negSevenEighths
    · -- i = 2, x = -3/4
      have hx2 : x (2 : Fin 11) = (-(3 : ℝ) / 4) := by
        norm_num [x]
      simpa [hx2] using! f24GegenbauerDiff_eval_negThreeQuarters
    · -- i = 3, x = -5/8
      have hx3 : x (3 : Fin 11) = (-(5 : ℝ) / 8) := by
        norm_num [x]
      simpa [hx3] using! f24GegenbauerDiff_eval_negFiveEighths
    · -- i = 4, x = -1/2
      have hx4 : x (4 : Fin 11) = (-(1 : ℝ) / 2) := by
        norm_num [x]
      simpa [hx4] using! f24GegenbauerDiff_eval_negHalf
    · -- i = 5, x = -3/8
      have hx5 : x (5 : Fin 11) = (-(3 : ℝ) / 8) := by
        norm_num [x]
      simpa [hx5] using! f24GegenbauerDiff_eval_negThreeEighths
    · -- i = 6, x = -1/4
      have hx6 : x (6 : Fin 11) = (-(1 : ℝ) / 4) := by
        norm_num [x]
      simpa [hx6] using! f24GegenbauerDiff_eval_negQuarter
    · -- i = 7, x = -1/8
      have hx7 : x (7 : Fin 11) = (-(1 : ℝ) / 8) := by
        norm_num [x]
      simpa [hx7] using! f24GegenbauerDiff_eval_negEighth
    · -- i = 8, x = 0
      have hx8 : x (8 : Fin 11) = (0 : ℝ) := by
        norm_num [x]
      simpa [hx8] using! f24GegenbauerDiff_eval_zero
    · -- i = 9, x = 1/8 = (8:ℝ)⁻¹
      have hx9 : x (9 : Fin 11) = ((8 : ℝ)⁻¹) := by
        norm_num [x, one_div]
      simpa [hx9] using! f24GegenbauerDiff_eval_invEight
    · -- i = 10, x = 1/4 = (4:ℝ)⁻¹
      have hx10 : x (10 : Fin 11) = ((4 : ℝ)⁻¹) := by
        norm_num [x, one_div]
      simpa [hx10] using! f24GegenbauerDiff_eval_invFour
  have hp0 : f24GegenbauerDiff = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      f24GegenbauerDiff hx_inj heval natDegree_f24GegenbauerDiff_lt
  have : (Uniqueness.BS81.f24 : Polynomial ℝ) - f24GegenbauerExpansion = 0 := by
    simpa [f24GegenbauerDiff, f24GegenbauerExpansion] using! hp0
  -- Unfold `f24GegenbauerExpansion` to match the statement.
  simpa [f24GegenbauerExpansion] using! (sub_eq_zero.mp this)

end

end SpherePacking.Dim24.Uniqueness.BS81.LP
