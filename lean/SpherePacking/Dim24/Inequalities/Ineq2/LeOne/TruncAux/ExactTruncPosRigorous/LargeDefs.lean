-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTruncPosRigorous.Common
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases


/-!
# Large-`t` polynomial bound for the exact truncation

In the rigorous positivity proof for the `t ≤ 1` case of Appendix A, Lemma `ineq2`, we consider
`t ≥ t0` and set `x = r(t)`, so that `x ≤ rUpper = 1 / 28`.

This file defines a rational polynomial `polyLarge` whose evaluation at `x` provides a lower bound
for the exact truncation `ExactTrunc.ineq2_exact_trunc t`. It also records sign and dominance facts
about the coefficients that are used to prove positivity of `polyLarge - eps * x^12`.

## Main definitions
* `cQ`, `coeffLarge`, `coeffsLarge`, `polyLarge`

## Main statements
* `coeffLarge_pair_dom`
* `sum_range_two_mul`
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open CoeffModel

namespace ExactTruncPosRigorous

/-- The rational constant `1 / 23`, used as an upper bound for `t * r(t)` when `t ≥ 1`. -/
@[expose] public def cQ : ℚ := (1 : ℚ) / 23

/-- Coefficient function defining the polynomial lower bound in the large-`t` regime. -/
@[expose] public def coeffLarge (n : ℕ) : ℚ :=
  (B0 n) * t0Q * invPiLowerQ
    + (C0 n) * CinvBoundQ n
    + (if n + 2 < N then (A0 (n + 2)) * (cQ ^ (2 : ℕ)) else 0)

/-- The list of coefficients `coeffLarge 0, ..., coeffLarge (N-1)`. -/
@[expose] public def coeffsLarge : List ℚ := List.ofFn fun i : Fin N => coeffLarge i.1

/-- The polynomial with coefficient list `coeffsLarge` (degree `< N`). -/
@[expose] public def polyLarge : Polynomial ℚ := AppendixA.polyOfCoeffs coeffsLarge

macro "simp_A0_nonpos_goal" : tactic =>
  `(tactic|
    (simp only [
        CoeffModel.A0,
        CoeffModel.phinumCoeffQ,
        AppendixA.varphiNumCoeffsZ_table
      ] <;> try norm_num))
macro "simp_B0_nonneg_goal" : tactic =>
  `(tactic|
    (simp only [
        CoeffModel.B0,
        CoeffModel.phi1CoreCoeffQ,
        AppendixA.phi1CoreCoeffsZ_table
      ] <;> try norm_num))
macro "simp_coeffLarge_goal" : tactic =>
  `(tactic|
    (simp only
        [
          coeffLarge,
          CinvBoundQ,
          N,
          CoeffModel.N,
          CoeffModel.A0,
          CoeffModel.B0,
          CoeffModel.C0,
          CoeffModel.phinumCoeffQ,
          CoeffModel.phi1CoreCoeffQ,
          CoeffModel.phi2CoreCoeffQ,
          CoeffModel.psiInumCoeffQ,
          t0Q,
          cQ,
          invPiLowerQ,
          invPiUpperQ,
          invPiSqLowerQ,
          invPiSqUpperQ,
          rUpperQ,
          AppendixA.BleadingCoeffs.invPiLower10Q,
          AppendixA.BleadingCoeffs.invPiUpper10Q,
          AppendixA.BleadingCoeffs.piLower10Q,
          AppendixA.BleadingCoeffs.piUpper10Q,
          AppendixA.varphiNumCoeffsZ_table,
          AppendixA.phi1CoreCoeffsZ_table,
          AppendixA.phi2CoreCoeffsZ_table,
          AppendixA.psiInumCoeffs_table
        ] <;> try norm_num))

/-- For `i < N`, the coefficient `A0 i` is nonpositive. -/
public lemma A0_nonpos_of_lt (i : ℕ) (hi : i < N) : A0 i ≤ 0 := by
  have hi0 : 0 ≤ i := Nat.zero_le i
  have hi100 : i < 100 := by simpa [N, CoeffModel.N] using! hi
  interval_cases i using hi0, hi100
  all_goals simp_A0_nonpos_goal

/-- For `i < N`, the coefficient `B0 i` is nonnegative. -/
public lemma B0_nonneg_of_lt (i : ℕ) (hi : i < N) : 0 ≤ B0 i := by
  have hi0 : 0 ≤ i := Nat.zero_le i
  have hi100 : i < 100 := by simpa [N, CoeffModel.N] using! hi
  interval_cases i using hi0, hi100
  all_goals simp_B0_nonneg_goal

/-! ## Some explicit head coefficients of `coeffLarge` -/

/-- The constant coefficient of `coeffLarge` is zero. -/
public lemma coeffLarge_eq_zero_0 : coeffLarge 0 = 0 := by
  simp_coeffLarge_goal
/-- The degree-one coefficient of `coeffLarge` is zero. -/
public lemma coeffLarge_eq_zero_1 : coeffLarge 1 = 0 := by
  simp_coeffLarge_goal
/-- The degree-three coefficient of `coeffLarge` is zero. -/
public lemma coeffLarge_eq_zero_3 : coeffLarge 3 = 0 := by
  simp_coeffLarge_goal
/-- The degree-two coefficient of `coeffLarge` is strictly greater than `1`. -/
public lemma coeffLarge_pos_two : (1 : ℚ) < coeffLarge 2 := by
  simp_coeffLarge_goal

set_option maxHeartbeats 1500000 in
-- The coefficient domination checks below are proved by `interval_cases` + `norm_num` over large
-- rational constants, which needs a larger heartbeat budget.
/-- Pairwise dominance used to show the tail of `polyLarge` is nonnegative for `x ≤ rUpperQ`. -/
public lemma coeffLarge_pair_dom (k : ℕ) (hk : k < 48) :
    coeffLarge (2 * k + 4) ≥ |coeffLarge (2 * k + 5)| * rUpperQ := by
  have hk0 : 0 ≤ k := Nat.zero_le k
  interval_cases k using hk0, hk
  all_goals simp_coeffLarge_goal

/-- Split a sum over `range (2*m)` into paired terms `g (2*k) + g (2*k+1)`. -/
public lemma sum_range_two_mul {α : Type*} [AddCommMonoid α] (g : ℕ → α) (m : ℕ) :
    (∑ n ∈ Finset.range (2 * m), g n) = ∑ k ∈ Finset.range m, (g (2 * k) + g (2 * k + 1)) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hL :
          (∑ n ∈ Finset.range (2 * (m + 1)), g n) =
            (∑ n ∈ Finset.range (2 * m), g n) + g (2 * m) + g (2 * m + 1) := by
        -- Add the last two terms to `range (2*m)`.
        have h1 :
            (∑ n ∈ Finset.range (2 * m + 1), g n) =
              (∑ n ∈ Finset.range (2 * m), g n) + g (2 * m) := by
          simpa using! (Finset.sum_range_succ (f := g) (n := 2 * m))
        have h2 :
            (∑ n ∈ Finset.range (2 * m + 2), g n) =
              (∑ n ∈ Finset.range (2 * m + 1), g n) + g (2 * m + 1) := by
          simpa using! (Finset.sum_range_succ (f := g) (n := 2 * m + 1))
        have hmul : 2 * (m + 1) = 2 * m + 2 := by omega
        simp [hmul, h1, h2, add_assoc]
      have hR :
          (∑ k ∈ Finset.range (m + 1), (g (2 * k) + g (2 * k + 1))) =
            (∑ k ∈ Finset.range m, (g (2 * k) + g (2 * k + 1))) + (g (2 * m) + g (2 * m + 1)) := by
        simp [Finset.sum_range_succ]
      -- Finish.
      calc
        (∑ n ∈ Finset.range (2 * (m + 1)), g n)
            = (∑ n ∈ Finset.range (2 * m), g n) + g (2 * m) + g (2 * m + 1) := hL
        _ = (∑ k ∈ Finset.range m, (g (2 * k) + g (2 * k + 1))) + (g (2 * m) + g (2 * m + 1)) := by
              simp [ih, add_assoc, add_left_comm, add_comm]
        _ = ∑ k ∈ Finset.range (m + 1), (g (2 * k) + g (2 * k + 1)) := by
              simp [hR]

end SpherePacking.Dim24.Ineq2LeOneTruncAux.ExactTruncPosRigorous
