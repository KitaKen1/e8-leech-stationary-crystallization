-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Defs
public import SpherePacking.Dim24.MagicFunction.MkRadial
public import SpherePacking.Dim24.MagicFunction.Radial
public import SpherePacking.ModularForms.SlashActionAuxil
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.MeasureTheory.Integral.ExpDecay


/-!
# Radial pieces `I₁` through `I₆`

This file packages the six radial Schwartz functions `I₁`, ..., `I₆` built from the
one-dimensional integrals `RealIntegrals.I₁'`, ..., `RealIntegrals.I₆'`.
It also records the decomposition of the magic function `a` as their sum.

## Main definitions
* `I₁`, `I₂`, `I₃`, `I₄`, `I₅`, `I₆`

## Main statement
* `a_eq_sum_integrals`
-/

section

open scoped SchwartzMap

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.AFourier
open MeasureTheory Set Complex Real Filter
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold

noncomputable section


/-- The radial Schwartz function `I₁` obtained from `RealIntegrals.I₁'`. -/
@[expose] public def I₁ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.I₁'
    (by
      simpa using! RadialSchwartz.cutoffC_contDiff.mul Schwartz.I1Smooth.contDiff_I₁')
    Schwartz.I1Smooth.decay_I₁'

/-- The radial Schwartz function `I₂` obtained from `RealIntegrals.I₂'`. -/
@[expose] public def I₂ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.I₂'
    (by
      simpa using! RadialSchwartz.cutoffC_contDiff.mul Schwartz.I2Smooth.contDiff_I₂')
    Schwartz.I2Smooth.decay_I₂'

/-- The radial Schwartz function `I₃` obtained from `RealIntegrals.I₃'`. -/
@[expose] public def I₃ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.I₃'
    (by
      simpa using! RadialSchwartz.cutoffC_contDiff.mul Schwartz.I3Smooth.contDiff_I₃')
    Schwartz.I3Smooth.decay_I₃'

/-- The radial Schwartz function `I₄` obtained from `RealIntegrals.I₄'`. -/
@[expose] public def I₄ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.I₄'
    (by
      simpa using! RadialSchwartz.cutoffC_contDiff.mul Schwartz.I4Smooth.contDiff_I₄')
    Schwartz.I4Smooth.decay_I₄'

/-- The radial Schwartz function `I₅` obtained from `RealIntegrals.I₅'`. -/
@[expose] public def I₅ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.I₅'
    (by
      simpa using! RadialSchwartz.cutoffC_contDiff.mul Schwartz.I5Smooth.contDiff_I₅')
    Schwartz.I5Smooth.decay_I₅'

/-- The radial Schwartz function `I₆` obtained from `RealIntegrals.I₆'`. -/
@[expose] public def I₆ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.I₆'
    (by
      simpa using!
        (RadialSchwartz.contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1
          (f := RealIntegrals.I₆') Schwartz.I6Smooth.contDiffOn_I₆'_Ioi_neg1))
    Schwartz.I6Smooth.decay_I₆'

/-! ## Simp lemmas -/

/-- Evaluate `I₁` as a radial profile. -/
@[simp] public lemma I₁_apply (x : ℝ²⁴) : (I₁ x) = RealIntegrals.I₁' (‖x‖ ^ 2) := by
  simp [I₁, mkRadial]

/-- Evaluate `I₂` as a radial profile. -/
@[simp] public lemma I₂_apply (x : ℝ²⁴) : (I₂ x) = RealIntegrals.I₂' (‖x‖ ^ 2) := by
  simp [I₂, mkRadial]

/-- Evaluate `I₃` as a radial profile. -/
@[simp] public lemma I₃_apply (x : ℝ²⁴) : (I₃ x) = RealIntegrals.I₃' (‖x‖ ^ 2) := by
  simp [I₃, mkRadial]

/-- Evaluate `I₄` as a radial profile. -/
@[simp] public lemma I₄_apply (x : ℝ²⁴) : (I₄ x) = RealIntegrals.I₄' (‖x‖ ^ 2) := by
  simp [I₄, mkRadial]

/-- Evaluate `I₅` as a radial profile. -/
@[simp] public lemma I₅_apply (x : ℝ²⁴) : (I₅ x) = RealIntegrals.I₅' (‖x‖ ^ 2) := by
  simp [I₅, mkRadial]

/-- Evaluate `I₆` as a radial profile. -/
@[simp] public lemma I₆_apply (x : ℝ²⁴) : (I₆ x) = RealIntegrals.I₆' (‖x‖ ^ 2) := by
  simp [I₆, mkRadial]

/-- Decompose the magic function `a` as the sum of the radial pieces `I₁` through `I₆`. -/
public lemma a_eq_sum_integrals : a = I₁ + I₂ + I₃ + I₄ + I₅ + I₆ := by
  ext x
  simp [Dim24.a, Dim24.aAux, aProfile, RealIntegrals.a', add_assoc, add_left_comm, add_comm]


end

end SpherePacking.Dim24.AFourier

end
