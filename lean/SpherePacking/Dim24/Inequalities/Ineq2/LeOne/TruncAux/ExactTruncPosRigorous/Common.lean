-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.AbsBoundQ
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ShiftSums
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.ExactTrunc
public import SpherePacking.Dim24.Inequalities.AppendixA.RBounds
import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Positivity


/-!
# Elementary bounds for `r(t) = exp (-Real.pi * t)`

This file provides explicit numerical bounds on `r(t)` around the cutoff `t0 = 107 / 100` used in
the rigorous positivity proof for the `t ≤ 1` case of Appendix A, Lemma `ineq2`.

In particular, we show `r(t) < 1 / 28` for `t0 ≤ t` and `1 / 30 ≤ r(t)` for `1 ≤ t ≤ t0`. We also
record rational lower/upper bounds for `1 / Real.pi` and `(1 / Real.pi)^2` that are compatible with
the coefficient tables.

## Main definitions
* `t0`, `rUpper`
* `invPiLower`, `invPiUpper`, `invPiSqLower`, `invPiSqUpper`
* `CinvBoundQ`

## Main statements
* `r_lt_one_div_28_of_t0_le`
* `r_ge_one_div_30_of_le_t0`
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open CoeffModel

namespace ExactTruncPosRigorous

/-- The cutoff value `t0 = 107 / 100` separating the "small" and "large" `t` regimes. -/
@[expose] public def t0 : ℝ := (107 / 100 : ℝ)

/-- A rational version of `t0`, used for coefficient computations. -/
@[expose] public def t0Q : ℚ := 107 / 100

/-- Coercion from `t0Q` to `ℝ` agrees with `t0`. -/
public lemma t0Q_cast : (t0Q : ℝ) = t0 := by
  norm_num [t0Q, t0]

/-- The `r`-bound `1 / 28` used for the "large `t`" regime. -/
@[expose] public def rUpper : ℝ := (1 / 28 : ℝ)

/-- A rational version of `rUpper`. -/
@[expose] public def rUpperQ : ℚ := 1 / 28

/-- A rational lower bound for `1 / Real.pi`. -/
@[expose] public def invPiLowerQ : ℚ := AppendixA.BleadingCoeffs.invPiLower10Q

/-- A rational upper bound for `1 / Real.pi`. -/
@[expose] public def invPiUpperQ : ℚ := AppendixA.BleadingCoeffs.invPiUpper10Q

/-- `invPiLowerQ` coerced to `ℝ`. -/
@[expose] public def invPiLower : ℝ := (invPiLowerQ : ℝ)

/-- `invPiUpperQ` coerced to `ℝ`. -/
@[expose] public def invPiUpper : ℝ := (invPiUpperQ : ℝ)

/-- A rational lower bound for `(1 / Real.pi)^2`. -/
@[expose] public def invPiSqLowerQ : ℚ := invPiLowerQ ^ (2 : ℕ)

/-- A rational upper bound for `(1 / Real.pi)^2`. -/
@[expose] public def invPiSqUpperQ : ℚ := invPiUpperQ ^ (2 : ℕ)

/-- `invPiSqLowerQ` coerced to `ℝ`. -/
@[expose] public def invPiSqLower : ℝ := (invPiSqLowerQ : ℝ)

/-- `invPiSqUpperQ` coerced to `ℝ`. -/
@[expose] public def invPiSqUpper : ℝ := (invPiSqUpperQ : ℝ)

/-- A coefficient-dependent choice of a bound for `(1 / Real.pi)^2`: use the lower bound when
`0 ≤ C0 i` and the upper bound when `C0 i < 0`, matching the direction needed for lower bounds. -/
@[expose] public def CinvBoundQ (i : ℕ) : ℚ := if 0 ≤ C0 i then invPiSqLowerQ else invPiSqUpperQ

lemma piLower10Q_lt_pi : (AppendixA.BleadingCoeffs.piLower10Q : ℝ) < Real.pi := by
  have hpi : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hlt : (AppendixA.BleadingCoeffs.piLower10Q : ℝ) < (3.14159265358979323846 : ℝ) := by
    norm_num [AppendixA.BleadingCoeffs.piLower10Q]
  exact lt_trans hlt hpi

lemma pi_lt_piUpper10Q : Real.pi < (AppendixA.BleadingCoeffs.piUpper10Q : ℝ) := by
  have hpi : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hlt : (3.14159265358979323847 : ℝ) < (AppendixA.BleadingCoeffs.piUpper10Q : ℝ) := by
    norm_num [AppendixA.BleadingCoeffs.piUpper10Q]
  exact lt_trans hpi hlt

/-! ## Bounds for `1 / Real.pi` and `(1 / Real.pi)^2` -/

/-- `invPiLower` is below the true value `1 / Real.pi`. -/
public lemma invPiLower_le_inv_pi : invPiLower ≤ (1 / Real.pi) := by
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hle : Real.pi ≤ (AppendixA.BleadingCoeffs.piUpper10Q : ℝ) := (le_of_lt pi_lt_piUpper10Q)
  have := one_div_le_one_div_of_le hpos hle
  simpa [invPiLower, invPiLowerQ, AppendixA.BleadingCoeffs.invPiLower10Q] using! this

/-- The true value `1 / Real.pi` is below `invPiUpper`. -/
public lemma inv_pi_le_invPiUpper : (1 / Real.pi) ≤ invPiUpper := by
  have hpos : (0 : ℝ) < (AppendixA.BleadingCoeffs.piLower10Q : ℝ) := by
    norm_num [AppendixA.BleadingCoeffs.piLower10Q]
  have hle : (AppendixA.BleadingCoeffs.piLower10Q : ℝ) ≤ Real.pi := (le_of_lt piLower10Q_lt_pi)
  have := one_div_le_one_div_of_le hpos hle
  simpa [invPiUpper, invPiUpperQ, AppendixA.BleadingCoeffs.invPiUpper10Q, one_div] using! this

/-- `invPiSqLower` is below the true value `(1 / Real.pi)^2`. -/
public lemma invPiSqLower_le_inv_pi_sq : invPiSqLower ≤ (1 / Real.pi) ^ (2 : ℕ) := by
  have h0 : 0 ≤ invPiLower := by
    have : (0 : ℚ) ≤ invPiLowerQ := by
      dsimp [
        invPiLowerQ,
        AppendixA.BleadingCoeffs.invPiLower10Q,
        AppendixA.BleadingCoeffs.piUpper10Q
      ]
      norm_num
    have : (0 : ℝ) ≤ (invPiLowerQ : ℝ) := by exact_mod_cast this
    simpa [invPiLower] using! this
  simpa [invPiSqLower, invPiSqLowerQ] using! (pow_le_pow_left₀ h0 invPiLower_le_inv_pi 2)

/-- The true value `(1 / Real.pi)^2` is below `invPiSqUpper`. -/
public lemma inv_pi_sq_le_invPiSqUpper : (1 / Real.pi) ^ (2 : ℕ) ≤ invPiSqUpper := by
  have h0 : 0 ≤ (1 / Real.pi : ℝ) := (one_div_pos.2 Real.pi_pos).le
  simpa [invPiSqUpper, invPiSqUpperQ] using! (pow_le_pow_left₀ h0 inv_pi_le_invPiUpper 2)

lemma exp_84_div_25_gt_28 : (28 : ℝ) < Real.exp (84 / 25 : ℝ) := by
  have hx : 0 ≤ (84 / 25 : ℝ) := by norm_num
  have hle := AppendixA.exp_lower_bound_range (x := (84 / 25 : ℝ)) hx 10
  have hsum_gt :
      (28 : ℝ) <
        Finset.sum (Finset.range 11) fun n : ℕ => (84 / 25 : ℝ) ^ n / (Nat.factorial n) := by
    set_option maxRecDepth 6000 in
    norm_num
  exact lt_of_lt_of_le hsum_gt (by simpa using! hle)

lemma exp_pi_mul_t0_gt_28 : (28 : ℝ) < Real.exp (Real.pi * t0) := by
  have ht0pos : (0 : ℝ) < t0 := by norm_num [t0]
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hmul : (84 / 25 : ℝ) < Real.pi * t0 := by
    have hlt : (84 / 25 : ℝ) < (3.141592 : ℝ) * t0 := by
      norm_num [t0]
    exact lt_trans hlt (mul_lt_mul_of_pos_right hpi ht0pos)
  have hexp : Real.exp (84 / 25 : ℝ) < Real.exp (Real.pi * t0) :=
    Real.exp_lt_exp.2 hmul
  exact lt_trans exp_84_div_25_gt_28 hexp

/-! ## Bounds for `r(t) = exp (-Real.pi * t)` -/

/-- If `t0 ≤ t`, then `r(t) < 1 / 28`. -/
public lemma r_lt_one_div_28_of_t0_le (t : ℝ) (ht0 : t0 ≤ t) : AppendixA.r t < (1 / 28 : ℝ) := by
  have hpos : (0 : ℝ) < (28 : ℝ) := by norm_num
  have hmono :
      Real.exp (Real.pi * t0) ≤ Real.exp (Real.pi * t) := by
    have : Real.pi * t0 ≤ Real.pi * t := by
      have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
      nlinarith [ht0, hpi0]
    exact Real.exp_le_exp.2 this
  have hgt : (28 : ℝ) < Real.exp (Real.pi * t) := lt_of_lt_of_le exp_pi_mul_t0_gt_28 hmono
  have hinv :
      (1 / Real.exp (Real.pi * t) : ℝ) < (1 / (28 : ℝ)) :=
    one_div_lt_one_div_of_lt hpos hgt
  have : Real.exp (-Real.pi * t) < (1 / 28 : ℝ) := by
    simpa [Real.exp_neg, one_div] using! hinv
  simpa [AppendixA.r, mul_assoc] using! this

lemma exp_17_div_5_lt_30 : Real.exp (17 / 5 : ℝ) < (30 : ℝ) := by
  set x : ℝ := (17 / 5 : ℝ)
  have hx0 : 0 ≤ x := by norm_num [x]
  set f : ℕ → ℝ := fun n => x ^ n / (Nat.factorial n)
  have hexp : Real.exp x = ∑' n : ℕ, f n := by
    have :
        Real.exp x = ∑' n : ℕ, x ^ n / (Nat.factorial n) := by
      simpa [Real.exp_eq_exp_ℝ] using!
        (congrArg (fun g : ℝ → ℝ => g x)
          (by simpa using! (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))))
    simpa [f] using! this
  have hf_summable : Summable f := by
    simpa [f] using! Real.summable_pow_div_factorial x
  have hsplit :
      (∑ n ∈ Finset.range 8, f n) + (∑' m : ℕ, f (m + 8)) = ∑' n : ℕ, f n := by
    simpa [add_comm, add_left_comm, add_assoc] using! (hf_summable.sum_add_tsum_nat_add 8)
  set ρ : ℝ := x / 9
  have hρ0 : 0 ≤ ρ := by
    positivity
  have hρ_lt : ρ < 1 := by
    norm_num
  have htail_step (m : ℕ) :
      f (m + 9) ≤ ρ * f (m + 8) := by
    have hratio :
        f (m + 9) = f (m + 8) * (x / (m + 9)) := by
      dsimp [f]
      have hxpow : x ^ (m + 9) = x ^ (m + 8) * x := by
        simpa [Nat.add_assoc] using! (pow_succ x (m + 8))
      have hfac : (Nat.factorial (m + 9) : ℝ) = (m + 9 : ℝ) * (Nat.factorial (m + 8) : ℝ) := by
        -- `factorial (m+9) = (m+9) * factorial (m+8)`.
        simp [Nat.factorial_succ, Nat.add_assoc, Nat.cast_mul]
      grind only
    have hden_le : (9 : ℝ) ≤ (m + 9 : ℝ) := by
      exact_mod_cast Nat.le_add_left 9 m
    have hx_nonneg : 0 ≤ x := hx0
    have hfrac : x / (m + 9 : ℝ) ≤ x / 9 := by
      have h9pos : (0 : ℝ) < (9 : ℝ) := by norm_num
      exact div_le_div_of_nonneg_left hx0 h9pos hden_le
    have hρ : x / (m + 9 : ℝ) ≤ ρ := by simpa [ρ] using! hfrac
    have hf_nonneg : 0 ≤ f (m + 8) := by
      dsimp [f]
      positivity
    have := mul_le_mul_of_nonneg_right hρ hf_nonneg
    -- Reassociate to match the target shape.
    simpa [hratio, mul_assoc, mul_left_comm, mul_comm] using! this
  have htail_bound (m : ℕ) :
      f (m + 8) ≤ f 8 * ρ ^ m := by
    induction m with
    | zero =>
        simp
    | succ m ih =>
        have hrec : f (m + 9) ≤ ρ * f (m + 8) := htail_step m
        have := le_trans hrec (mul_le_mul_of_nonneg_left ih hρ0)
        simpa [pow_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_assoc, mul_left_comm,
          mul_comm] using! this
  have htail_le :
      (∑' m : ℕ, f (m + 8)) ≤ (∑' m : ℕ, f 8 * ρ ^ m) := by
    have hsTail : Summable (fun m : ℕ => f (m + 8)) := by
      simpa using! (hf_summable.comp_injective (fun a b h => Nat.add_right_cancel h))
    have hsGeom : Summable (fun m : ℕ => f 8 * ρ ^ m) :=
      (summable_geometric_of_lt_one hρ0 hρ_lt).mul_left (f 8)
    exact hsTail.tsum_le_tsum (fun m => htail_bound m) hsGeom
  have hgeom : (∑' m : ℕ, f 8 * ρ ^ m) = f 8 * (1 - ρ)⁻¹ := by
    simp [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ_lt]
  have hupper :
      Real.exp x ≤ (∑ n ∈ Finset.range 8, f n) + f 8 * (1 - ρ)⁻¹ := by
    grind only
  have hcalc : (∑ n ∈ Finset.range 8, f n) + f 8 * (1 - ρ)⁻¹ < (30 : ℝ) := by
    norm_num
  exact lt_of_le_of_lt hupper hcalc

/-- If `1 ≤ t ≤ t0`, then `1 / 30 ≤ r(t)`. -/
public lemma r_ge_one_div_30_of_le_t0 (t : ℝ) (ht1 : 1 ≤ t) (ht0 : t ≤ t0) :
    (1 / 30 : ℝ) ≤ AppendixA.r t := by
  have _ : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht1
  have hle_pi_t : Real.pi * t ≤ Real.pi * t0 := by
    have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
    nlinarith [ht0, hpi0]
  have ht0' : Real.pi * t0 < (17 / 5 : ℝ) := by
    have hpi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
    have ht0pos : (0 : ℝ) < t0 := by norm_num [t0]
    have hpi_t0 : Real.pi * t0 < (3.15 : ℝ) * t0 := mul_lt_mul_of_pos_right hpi ht0pos
    have h315 : (3.15 : ℝ) * t0 = (13482 / 4000 : ℝ) := by norm_num [t0]
    have : Real.pi * t0 < (13482 / 4000 : ℝ) := by simpa [h315] using! hpi_t0
    have hlt : (13482 / 4000 : ℝ) < (17 / 5 : ℝ) := by norm_num
    exact lt_trans this hlt
  have hle : Real.pi * t < (17 / 5 : ℝ) := lt_of_le_of_lt hle_pi_t ht0'
  have hexp : Real.exp (Real.pi * t) < 30 := by
    have h1 : Real.exp (Real.pi * t) < Real.exp (17 / 5 : ℝ) := Real.exp_lt_exp.2 hle
    exact lt_trans h1 exp_17_div_5_lt_30
  have hinv : (1 / (30 : ℝ)) < (1 / Real.exp (Real.pi * t)) :=
    one_div_lt_one_div_of_lt (Real.exp_pos (Real.pi * t)) hexp
  have : (1 / (30 : ℝ)) ≤ Real.exp (-Real.pi * t) := by
    have : (1 / (30 : ℝ)) < Real.exp (-Real.pi * t) := by
      simpa [Real.exp_neg, one_div] using! hinv
    exact this.le
  simpa [AppendixA.r, mul_assoc, one_div] using! this

end SpherePacking.Dim24.Ineq2LeOneTruncAux.ExactTruncPosRigorous
