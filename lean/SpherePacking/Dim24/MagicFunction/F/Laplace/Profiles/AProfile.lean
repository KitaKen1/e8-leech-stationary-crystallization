-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.EvenU.BProfileZeros
public import SpherePacking.Dim24.MagicFunction.F.BKernelAsymptotics
public import SpherePacking.Dim24.MagicFunction.F.Laplace.KernelTools
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.LeadingCorrection
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingBounds.BKernelSubLeadingBound
public import SpherePacking.Dim24.MagicFunction.F.ProfileComplex.B
public import SpherePacking.Dim24.MagicFunction.F.Laplace.TopologyDomains
public import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Tactic.NormNumI
public import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
public import SpherePacking.Dim24.MagicFunction.Radial
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import SpherePacking.Dim24.MagicFunction.F.Laplace.A.Basic
import SpherePacking.Dim24.MagicFunction.A.LaplaceZeros


/-!
# Convergent Laplace formula for `aProfile` (`u > 4`)

In the convergent real range `u > 4`, the imaginary-axis integrals converge absolutely, so we
can rewrite `aProfile` as a Laplace transform of `varphi` without analytic continuation.

## Main definitions
* `varphiKernel0`

## Main statement
* `aProfile_eq_laplace_varphi`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Interval

open Complex MeasureTheory Real SchwartzMap Set
open RealIntegrals RealIntegrals.ComplexIntegrands
open UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Totalized imaginary-axis integrand `t ↦ (t^10) * varphi(i/t)` used below. -/
@[expose] public def varphiKernel0 (t : ℝ) : ℂ :=
  if ht : 0 < t then ((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht) else 0

/-- A Laplace-formula for `aProfile` in the convergent range `u > 4`. -/
public theorem aProfile_eq_laplace_varphi (u : ℝ) (hu : 4 < u) :
    aProfile u =
      (4 * (Complex.I : ℂ)) * (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
        ((∫ t in (0 : ℝ)..1, varphiKernel0 t * Real.exp (-Real.pi * u * t)) +
          ∫ t in Set.Ioi (1 : ℝ), varphiKernel0 t * Real.exp (-Real.pi * u * t)) := by
  -- Decompose `aProfile` into the `(135)` and `(246)` blocks and rewrite them on the imaginary
  -- axis.
  have h135 := LaplaceZeros.I₁'_add_I₃'_add_I₅'_eq_imag_axis (u := u)
  have h246 :=
    LaplaceZerosTail.TailDeform.I₂'_add_I₄'_add_I₆'_eq_imag_axis (u := u) hu
  have hsum :
      aProfile u =
        (Complex.I : ℂ) *
          ((Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
                Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
            ((∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) +
              ∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
    -- Expand `aProfile` and regroup the six contour pieces.
    dsimp [aProfile, RealIntegrals.a']
    -- Group as `(135) + (246)`.
    have hgrp :
        RealIntegrals.I₁' u + RealIntegrals.I₂' u + RealIntegrals.I₃' u + RealIntegrals.I₄' u +
              RealIntegrals.I₅' u + RealIntegrals.I₆' u =
          (RealIntegrals.I₁' u + RealIntegrals.I₃' u + RealIntegrals.I₅' u) +
            (RealIntegrals.I₂' u + RealIntegrals.I₄' u + RealIntegrals.I₆' u) := by
      ac_rfl
    -- Substitute the imaginary-axis formulas and factor out constants.
    rw [hgrp, h135, h246]
    simp [mul_add, mul_comm]
  -- Rewrite the exponential coefficient as `-4 * sin^2`.
  have hcoeff :
      Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
          Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ) =
        -((4 * (Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) :=
    LaplaceA.exp_pi_mul_I_add_exp_neg_pi_mul_I_sub_two (u := u)
  -- Convert `Φ₅'` on the imaginary axis into the Laplace-type kernel (valid for `t > 0`).
  have hΦpos (t : ℝ) (ht : 0 < t) :
      Φ₅' u ((t : ℂ) * Complex.I) = -(varphiKernel0 t * Real.exp (-Real.pi * u * t)) := by
    have hΦ := LaplaceA.Φ₅'_imag_axis_eq_laplace (u := u) (t := t) ht
    -- On `t>0`, `varphiKernel0 t` is the non-totalized kernel and `Complex.exp` is `Real.exp`.
    have hexp :
        Complex.exp (-Real.pi * u * t : ℂ) = (Real.exp (-Real.pi * u * t) : ℂ) := by
      simp
    simpa [varphiKernel0, ht, hexp, mul_assoc, mul_left_comm, mul_comm] using! hΦ
  -- Combine everything.
  rw [hsum]
  -- Replace the coefficient and the `Φ₅'`-integrand.
  rw [hcoeff]
  -- Rewrite the `Φ₅'` integrals using `hΦpos` and cancel the double negation.
  have hseg :
      (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) =
        -(∫ t in (0 : ℝ)..1, varphiKernel0 t * Real.exp (-Real.pi * u * t)) := by
    have hcongr :
        (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) =
          ∫ t in (0 : ℝ)..1, -(varphiKernel0 t * Real.exp (-Real.pi * u * t)) := by
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro t ht
      have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
      exact hΦpos t htIoc.1
    calc
      (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) =
          ∫ t in (0 : ℝ)..1, -(varphiKernel0 t * Real.exp (-Real.pi * u * t)) := hcongr
      _ = -(∫ t in (0 : ℝ)..1, varphiKernel0 t * Real.exp (-Real.pi * u * t)) := by
          simp
  have htail :
      (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
        -(∫ t in Set.Ioi (1 : ℝ), varphiKernel0 t * Real.exp (-Real.pi * u * t)) := by
    have hcongr :
        (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
          ∫ t in Set.Ioi (1 : ℝ), -(varphiKernel0 t * Real.exp (-Real.pi * u * t)) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht
      exact hΦpos t ht0
    calc
      (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
          ∫ t in Set.Ioi (1 : ℝ), -(varphiKernel0 t * Real.exp (-Real.pi * u * t)) := hcongr
      _ = -(∫ t in Set.Ioi (1 : ℝ), varphiKernel0 t * Real.exp (-Real.pi * u * t)) :=
          integral_neg fun a => varphiKernel0 a * ↑(rexp (-π * u * a))
  -- Substitute the rewritten integrals and simplify.
  rw [hseg, htail]
  -- Normalize the real-valued sine/exponential terms appearing in `hcoeff`/`hΦpos`.
  simp [Complex.ofReal_sin, Complex.ofReal_exp,
    mul_assoc, mul_left_comm, mul_comm]
  ring_nf

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles
