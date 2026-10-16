-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.MagicFunction.IntegralParametrisations
import SpherePacking.ForMathlib.DerivHelpers
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv


/-!
# Exponential bookkeeping for special values

Both the `a`- and `b`-special-value files use the same exponential `exp(π i u z)` and the same
periodicity-by-1 identities along the standard contour parametrisations `z₁'`, `z₃'`, `z₅'`.

This file factors these shared definitions/lemmas into one place to avoid import-time name
collisions when mixing the `A.SpecialValues` and `B.SpecialValues` developments.
-/


namespace SpherePacking.Dim24

noncomputable section

open scoped Real
open Complex
open MagicFunction.Parametrisations

namespace SpecialValuesAux

/-- Exponential factor `exp(π i u z)` used throughout the contour-integral decompositions. -/
@[expose]
public def expU (u : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (u : ℂ) * z)

/-- Continuity of `expU u` as a function of the contour variable `z`. -/
public lemma continuous_expU (u : ℝ) : Continuous (expU u) := by
  have : Continuous fun z : ℂ => Real.pi * Complex.I * (u : ℂ) * z := by fun_prop
  simpa [expU] using! this.cexp

/-- Complex differentiability of `expU u` at any point `z`. -/
public lemma differentiableAt_expU (u : ℝ) (z : ℂ) : DifferentiableAt ℂ (expU u) z := by
  unfold expU
  fun_prop

/-- A norm bound for `expU u z` when `u ≥ 0` and `z.im ≥ 0`. -/
public lemma norm_expU_le_one (u : ℝ) (hu0 : 0 ≤ u) (z : ℂ) (hz : 0 ≤ z.im) :
    ‖expU u z‖ ≤ 1 := by
  have hre : ((Real.pi : ℂ) * Complex.I * (u : ℂ) * z).re = -(Real.pi * u * z.im) := by
    simp [mul_left_comm, mul_comm]
  have hle : ((Real.pi : ℂ) * Complex.I * (u : ℂ) * z).re ≤ 0 := by
    have hnonneg : 0 ≤ Real.pi * u * z.im :=
      mul_nonneg (mul_nonneg Real.pi_pos.le hu0) hz
    simpa [hre] using! (neg_nonpos.2 hnonneg)
  have hnorm :
      ‖expU u z‖ = Real.exp (((Real.pi : ℂ) * Complex.I * (u : ℂ) * z).re) := by
    simpa [expU] using! (Complex.norm_exp ((Real.pi : ℂ) * Complex.I * (u : ℂ) * z))
  rw [hnorm]
  exact (Real.exp_le_one_iff.2 hle)

/-- Additivity in the contour variable for `expU`: `expU u (z + w) = expU u z * expU u w`. -/
public lemma expU_add (u : ℝ) (z w : ℂ) : expU u (z + w) = expU u z * expU u w := by
  simp [expU, mul_add, mul_assoc, Complex.exp_add]

/-- The special case of `expU_add` for `w = 1`. -/
public lemma expU_add_one_mul (u : ℝ) (z : ℂ) :
    expU u (z + 1) = expU u z * expU u 1 := by
  simpa using! expU_add (u := u) (z := z) (w := (1 : ℂ))

/-- Periodicity by `1` for `expU u` under the hypothesis `expU u 1 = 1`. -/
public lemma expU_add_one (u : ℝ) (hu : expU u 1 = 1) (z : ℂ) :
    expU u (z + 1) = expU u z := by
  simpa [hu] using! (expU_add (u := u) (z := z) (w := (1 : ℂ)))

/-- Rearrangement of `expU_add_one_mul` isolating `expU u z`. -/
public lemma expU_add_one_mul_inv (u : ℝ) (z : ℂ) (hw : expU u 1 ≠ 0) :
    expU u z = expU u (z + 1) * (expU u 1)⁻¹ := by
  have h := congrArg (fun w : ℂ => w * (expU u 1)⁻¹) (expU_add_one_mul (u := u) (z := z))
  simpa [mul_assoc, hw] using! h.symm

/-- For even integers `u = 2k`, the periodicity factor satisfies `expU u 1 = 1`. -/
public lemma expU_two_mul_nat_one (k : ℕ) : expU ((2 : ℝ) * k) 1 = 1 := by
  simpa [expU, mul_assoc, mul_left_comm, mul_comm] using! (Complex.exp_nat_mul_two_pi_mul_I k)

/-- Derivative of `u ↦ expU u 1` at a real point `u0`. -/
public lemma hasDerivAt_expU_one (u0 : ℝ) :
    HasDerivAt (fun u : ℝ => expU u 1) (expU u0 1 * ((Real.pi : ℂ) * Complex.I)) u0 := by
  simpa [expU, mul_assoc, mul_left_comm, mul_comm] using!
    (SpherePacking.ForMathlib.hasDerivAt_cexp_ofReal_mul_const
      (c := ((Real.pi : ℂ) * Complex.I)) (x := u0))

/-- Derivative of `u ↦ (expU u 1)⁻¹` at a real point `u0`. -/
public lemma hasDerivAt_expU_one_inv (u0 : ℝ) :
    HasDerivAt (fun u : ℝ => (expU u 1)⁻¹) (-(expU u0 1)⁻¹ * ((Real.pi : ℂ) * Complex.I)) u0 := by
  simpa [expU, mul_assoc, mul_left_comm, mul_comm, Complex.exp_neg] using!
    (SpherePacking.ForMathlib.hasDerivAt_cexp_ofReal_mul_const
      (c := -((Real.pi : ℂ) * Complex.I)) (x := u0))

/-- The "evenness factor" `(expU u 1)⁻¹ + expU u 1 - 2` has derivative `0` at points where
`expU u 1 = 1`. -/
public lemma hasDerivAt_factor_even (u0 : ℝ) (hu : expU u0 1 = 1) :
    HasDerivAt (fun u : ℝ => (expU u 1)⁻¹ + expU u 1 - 2) 0 u0 := by
  have hsum :=
    (hasDerivAt_expU_one_inv (u0 := u0)).add (hasDerivAt_expU_one (u0 := u0))
  have hsum0 : HasDerivAt (fun u : ℝ => (expU u 1)⁻¹ + expU u 1) 0 u0 := by
    simpa [hu, add_comm, add_left_comm, add_assoc] using! hsum
  simpa [sub_eq_add_neg, add_assoc] using! (hsum0.sub_const (2 : ℂ))

/-- Along the standard parametrisations on `Ι 0 1`, the periodicity identity identifies
`expU u (z₁' t)` with `expU u (z₅' t)` when `expU u 1 = 1`. -/
public lemma expU_z₁'_eq_z₅' (u : ℝ) (hu : expU u 1 = 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    expU u (z₁' t) = expU u (z₅' t) := by
  have hz : z₁' t + 1 = z₅' t := by
    simp [z₁'_eq_of_mem (t := t) ht, z₅'_eq_of_mem (t := t) ht,
      add_left_comm, add_comm]
  simpa [hz] using! (expU_add_one (u := u) hu (z := z₁' t)).symm

/-- Along the standard parametrisations on `Ι 0 1`, the periodicity identity identifies
`expU u (z₃' t)` with `expU u (z₅' t)` when `expU u 1 = 1`. -/
public lemma expU_z₃'_eq_z₅' (u : ℝ) (hu : expU u 1 = 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    expU u (z₃' t) = expU u (z₅' t) := by
  have hz : z₅' t + 1 = z₃' t := by
    simp [z₃'_eq_of_mem (t := t) ht, z₅'_eq_of_mem (t := t) ht, add_comm]
  simpa [hz] using! (expU_add_one (u := u) hu (z := z₅' t))

end SpecialValuesAux

end

end SpherePacking.Dim24
