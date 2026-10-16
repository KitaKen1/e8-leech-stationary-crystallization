-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.RBounds
public import Mathlib.Data.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import
  SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.SparseCoeffs
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2PsiSnum.RSeries

/-!
# Summability and sparse-support reindexing for theta `r`-series

This file packages two facts we repeatedly use later:

1. If `‖(r t : ℂ)‖ < 1` and coefficients are polynomially bounded, then the associated `rseries`
   is absolutely summable.
2. Since `theta01CoeffFun` and `theta10CoeffFun` are supported on squares / triangular numbers,
   we can reindex their `rseries` as sums over those supports.

## Main statements
* `summable_norm_rseries_of_coeffBound`
-/

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

namespace Ineq2PsiSnum

open scoped BigOperators

/-!
## Basic magnitude bounds for the sparse theta coefficients

These crude bounds are enough to establish summability of the corresponding `r`-series whenever
`‖rC t‖ < 1`. We combine them with geometric-series estimates to bound the resulting tails.
-/

/-- Crude growth bound for the theta coefficient function `theta01CoeffFun`. -/
public lemma abs_theta01CoeffFun_le (n : ℕ) :
    |theta01CoeffFun n| ≤ (2 : ℤ) * (n + 1) := by
  have h : |theta01CoeffFun n| ≤ (2 : ℤ) := AppendixA.abs_theta01CoeffFun_le_two (n := n)
  lia

/-- Crude growth bound for the theta coefficient function `theta10CoeffFun`. -/
public lemma abs_theta10CoeffFun_le (n : ℕ) :
    |theta10CoeffFun n| ≤ (2 : ℤ) * (n + 1) := by
  have h : |theta10CoeffFun n| ≤ (2 : ℤ) := AppendixA.abs_theta10CoeffFun_le_two (n := n)
  lia

/--
Absolute summability of an `r`-series with polynomially bounded coefficients, for `1 ≤ t`.

This is the norm-summability hypothesis needed to use `tsum` manipulations for `rseries` when
`r t ≤ 1/23 < 1`.
-/
public lemma summable_norm_rseries_of_coeffBound (t : ℝ) (ht : 1 ≤ t)
    (a : ℕ → ℤ) (C : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    Summable (fun n : ℕ => ‖((a n : ℂ) * ((r t : ℂ) ^ n))‖) := by
  -- Compare to `C * (n+1)^k * r0^n` with `r0 = 1/23`, using `r t ≤ 1/23` for `t ≥ 1`.
  have hr0 : 0 ≤ r t := (Real.exp_pos _).le
  have hrle : r t ≤ (1 : ℝ) / 23 := by
    simpa [r] using! (AppendixA.r_le_one_div_23 (t := t) ht)
  have hr_lt_one : r t < 1 := lt_of_le_of_lt hrle (by norm_num)
  have hr_norm : ‖r t‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using! hr_lt_one
  have hC0 : 0 ≤ C :=
    le_trans (abs_nonneg (a 0 : ℝ)) (by simpa using! (ha 0))
  have hs_pow : Summable (fun n : ℕ => ((n : ℝ) ^ k : ℝ) * (r t) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hr_norm
  have hs_shift :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * (r t) ^ (n + 1)) := by
    simpa [Nat.cast_add, Nat.cast_one] using!
      (summable_nat_add_iff 1 (f := fun n : ℕ => ((n : ℝ) ^ k : ℝ) * (r t) ^ n)).2 hs_pow
  have hrpos : 0 < r t := Real.exp_pos _
  have hs_shift' :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * (r t) ^ n) := by
    have hs1 :
        Summable (fun n : ℕ => (1 / r t) * (((n + 1 : ℕ) : ℝ) ^ k * (r t) ^ (n + 1))) :=
      hs_shift.mul_left (1 / r t)
    refine hs1.congr ?_
    intro n
    field_simp [hrpos.ne']
    simp [pow_succ, mul_comm]
  have hs_major :
      Summable (fun n : ℕ => C * (((n + 1 : ℕ) : ℝ) ^ k * (r t) ^ n)) :=
    hs_shift'.mul_left C
  -- Now compare each norm term to the majorant.
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hs_major
  intro n
  have hnorm_r : ‖((r t : ℂ) ^ n)‖ = (r t) ^ n := by
    simp [norm_pow, abs_of_nonneg hr0]
  calc
    ‖(a n : ℂ) * ((r t : ℂ) ^ n)‖
        = ‖(a n : ℂ)‖ * ‖((r t : ℂ) ^ n)‖ := by simp
    _ = |(a n : ℝ)| * (r t) ^ n := by simp [hnorm_r]
    _ ≤ (C * (((n + 1 : ℕ) : ℝ) ^ k)) * (r t) ^ n := by
      exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hr0 _)
    _ = C * (((n + 1 : ℕ) : ℝ) ^ k * (r t) ^ n) := by ring

/-- Summability of the `r`-series terms as a complex series, under the same coefficient bound. -/
public lemma summable_rseries_of_coeffBound (t : ℝ) (ht : 1 ≤ t)
    (a : ℕ → ℤ) (C : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    Summable (fun n : ℕ => (a n : ℂ) * ((r t : ℂ) ^ n)) :=
  Summable.of_norm (summable_norm_rseries_of_coeffBound (t := t) ht a C k ha)

private lemma rseries_theta01_eq_tsum_squares (t : ℝ) (ht : 1 ≤ t) :
    rseries theta01CoeffFun t =
      ∑' k : ℕ,
        ((if k = 0 then (1 : ℤ) else 2 * (-1 : ℤ) ^ k) : ℂ) *
          ((r t : ℂ) ^ (k ^ (2 : ℕ))) := by
  let f : ℕ → ℂ := fun n => (theta01CoeffFun n : ℂ) * ((r t : ℂ) ^ n)
  have hs : Summable f := by
    refine summable_rseries_of_coeffBound (t := t) ht theta01CoeffFun 2 1 ?_
    intro n
    have h := abs_theta01CoeffFun_le (n := n)
    -- Turn the ℤ-bound into an ℝ-bound.
    have : |(theta01CoeffFun n : ℝ)| ≤ (2 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
      -- `abs` commutes with casts and `|z| ≤ m` implies `|z| ≤ m` after casting.
      exact_mod_cast h
    simpa [pow_one, mul_assoc] using! this
  have hzero : ∀ n : ℕ, n ∉ Set.range square → f n = 0 := by
    intro n hn
    have h0 : theta01CoeffFun n = 0 := AppendixA.theta01CoeffFun_eq_zero_of_not_square (n := n) hn
    simp [f, h0]
  have hsquare_inj : Function.Injective square := by
    simpa [square] using! (Nat.pow_left_injective (n := 2) (Nat.succ_ne_zero 1))
  have hreindex :
      (∑' n : ℕ, f n) = ∑' k : ℕ, f (square k) :=
    AppendixA.tsum_eq_tsum_comp_of_eq_zero_off_range (f := f) hs (g := square) hsquare_inj hzero
  -- Unfold `rseries` and simplify the coefficients on squares.
  have : (∑' k : ℕ, f (square k)) =
      ∑' k : ℕ,
        ((if k = 0 then (1 : ℤ) else 2 * (-1 : ℤ) ^ k) : ℂ) *
          ((r t : ℂ) ^ (k ^ (2 : ℕ))) := by
    refine tsum_congr ?_
    intro k
    cases k with
      | zero =>
          rfl
      | succ k =>
          have hk :
              theta01CoeffFun ((Nat.succ k) ^ (2 : ℕ)) = 2 * ((-1 : ℤ) ^ (Nat.succ k)) := by
            simpa [Nat.succ_ne_zero] using! (AppendixA.theta01CoeffFun_sq (k := Nat.succ k))
          simp [f, square, hk]
  -- Finish.
  simpa [rseries, f] using! (hreindex.trans this)

private lemma rseries_theta10_eq_tsum_triangular (t : ℝ) (ht : 1 ≤ t) :
    rseries theta10CoeffFun t =
      ∑' k : ℕ, ((2 : ℤ) : ℂ) * ((r t : ℂ) ^ triangular k) := by
  let f : ℕ → ℂ := fun n => (theta10CoeffFun n : ℂ) * ((r t : ℂ) ^ n)
  have hs : Summable f := by
    refine summable_rseries_of_coeffBound (t := t) ht theta10CoeffFun 2 1 ?_
    intro n
    have h := abs_theta10CoeffFun_le (n := n)
    have : |(theta10CoeffFun n : ℝ)| ≤ (2 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [pow_one, mul_assoc] using! this
  have hzero : ∀ n : ℕ, n ∉ Set.range triangular → f n = 0 := by
    intro n hn
    have h0 : theta10CoeffFun n = 0 :=
      AppendixA.theta10CoeffFun_eq_zero_of_not_triangular (n := n) hn
    simp [f, h0]
  have htri_inj : Function.Injective triangular := by
    have hmono : StrictMono triangular := by
      intro a b hab
      dsimp [triangular]
      nlinarith
    exact hmono.injective
  have hreindex :
      (∑' n : ℕ, f n) = ∑' k : ℕ, f (triangular k) :=
    AppendixA.tsum_eq_tsum_comp_of_eq_zero_off_range (f := f) hs (g := triangular) htri_inj hzero
  have : (∑' k : ℕ, f (triangular k)) =
      ∑' k : ℕ, ((2 : ℤ) : ℂ) * ((r t : ℂ) ^ triangular k) := by
    refine tsum_congr ?_
    intro k
    have hk : theta10CoeffFun (triangular k) = 2 := by
      simpa [triangular] using! (AppendixA.theta10CoeffFun_tri (k := k))
    simp [f, hk]
  simpa [rseries, f] using! (hreindex.trans this)


end SpherePacking.Dim24.Ineq2PsiSnum
