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
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Basic


/-!
# Complexified Fourier profile and Laplace expression

This file defines complex-analytic versions of the real Fourier-profile pieces and Laplace
integrals that appear in the Fourier-Laplace representation of the magic function.

It is used to extend the identity `fhatProfile = sin^2 * Laplace(BKernel)` from the convergent
real range `u > 4` to the larger domain `2 < Re u` via the identity theorem.

## Main definitions
* `PrivateDefs.sinSqC`
* `PrivateDefs.fhatProfileC`
* `PrivateDefs.laplaceBKernelC`
* `PrivateDefs.rhsB`

## Main statements
* `fhatProfileC_ofReal`, `rhsB_ofReal`
* `rhsB_agrees_of_four`
* `analyticOnNhd_fhatProfileC`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Topology

open Complex Filter MeasureTheory Real SchwartzMap Set
open UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace PrivateDefs

/-- The entire function `u ↦ (sin ((π/2) * u))^2` on `ℂ`. -/
@[expose] public def sinSqC (u : ℂ) : ℂ := (Complex.sin ((π : ℂ) * u / 2)) ^ (2 : ℕ)

/-- Complexified version of `LaplaceFourier.fhatProfile` built from the analytic profiles
`aPrimeC` and `bPrimeC`. -/
@[expose] public def fhatProfileC (u : ℂ) : ℂ :=
  (-(π * Complex.I) / (113218560 : ℂ)) * ProfileComplex.A.aPrimeC u +
    (Complex.I / ((262080 : ℂ) * π)) * ProfileComplex.B.bPrimeC u

/-- The complex Laplace integral of `BKernel0` (initially defined on `2 < Re u`). -/
@[expose] public def laplaceBKernelC (u : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- The product `sinSqC u * laplaceBKernelC u` appearing in the Fourier-Laplace identity. -/
@[expose] public def rhsB (u : ℂ) : ℂ := sinSqC u * laplaceBKernelC u

end PrivateDefs

open PrivateDefs

/-- `LaplaceDomains.domainTwo` is contained in the right half-plane `0 < Re u`. -/
public lemma domainTwo_subset_rightHalfPlane :
    LaplaceDomains.domainTwo ⊆ SpherePacking.rightHalfPlane :=
  fun u hu => by
    have h0 : (0 : ℝ) < 2 := by norm_num
    exact lt_trans h0 hu

/-- `fhatProfileC` restricts to the real Fourier profile `LaplaceFourier.fhatProfile`. -/
public lemma fhatProfileC_ofReal (u : ℝ) :
    fhatProfileC (u : ℂ) = LaplaceFourier.fhatProfile u := by
  simp [fhatProfileC, LaplaceFourier.fhatProfile, ProfileComplex.A.aPrimeC_ofReal,
    ProfileComplex.B.bPrimeC_ofReal]

/-- On real parameters, `sinSqC` is `sin(πu/2)^2`. -/
public lemma sinSqC_ofReal (u : ℝ) :
    sinSqC (u : ℂ) = (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
  -- Use `ofReal_sin : (Real.sin x : ℂ) = sin x`.
  have hsin :
      Complex.sin ((π : ℂ) * (u : ℂ) / 2) = (Real.sin (Real.pi * u / 2) : ℂ) := by
    -- `sin ((Real.pi*u/2 : ℝ) : ℂ) = (Real.sin (Real.pi*u/2) : ℂ)`.
    simp [div_eq_mul_inv, mul_assoc]
  -- Rewrite `sinSqC` and apply the `sin` identification.
  unfold sinSqC
  -- `((Real.sin x)^2 : ℝ)` coerces to `(Real.sin x : ℂ)^2`.
  rw [hsin]
  simp [pow_two]

/-- For real `u` and `t`, the complex exponential in the Laplace kernel equals the real
exponential. -/
public lemma laplaceBKernelC_ofReal (u t : ℝ) :
    Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ)) = (Real.exp (-Real.pi * u * t) : ℂ) := by
  simp [mul_left_comm, mul_comm]

/-- Specialize `rhsB` to a real parameter and rewrite it as a real Laplace integral. -/
public lemma rhsB_ofReal (u : ℝ) :
    rhsB (u : ℂ) =
      (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
        (∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Real.exp (-Real.pi * u * t)) := by
  simp [rhsB, sinSqC_ofReal, laplaceBKernelC, mul_assoc]

/-- On the convergent range `u > 4`, the complexified profile identity agrees with the real one. -/
public lemma rhsB_agrees_of_four (u : ℝ) (hu : 4 < u) :
    fhatProfileC (u : ℂ) = rhsB (u : ℂ) := by
  -- Convert the established real identity `u > 4` into the complexified statement.
  simpa [
    fhatProfileC_ofReal,
    rhsB_ofReal
  ] using! (LaplaceFourier.fhatProfile_eq_laplace_B_of_four u hu)

/-! #### Analyticity of the complexified Fourier profile -/

/-- Analyticity of `fhatProfileC` on the right half-plane `0 < Re u`. -/
public lemma analyticOnNhd_fhatProfileC :
    AnalyticOnNhd ℂ fhatProfileC SpherePacking.rightHalfPlane := by
  have ha : AnalyticOnNhd ℂ ProfileComplex.A.aPrimeC SpherePacking.rightHalfPlane :=
    ProfileComplex.A.analyticOnNhd_aPrimeC
  have hb : AnalyticOnNhd ℂ ProfileComplex.B.bPrimeC SpherePacking.rightHalfPlane :=
    ProfileComplex.B.analyticOnNhd_bPrimeC
  have hc1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (-(π * Complex.I) / (113218560 : ℂ)))
        SpherePacking.rightHalfPlane :=
    analyticOnNhd_const
  have hc2 :
      AnalyticOnNhd ℂ (fun u : ℂ => (Complex.I / ((262080 : ℂ) * π)))
        SpherePacking.rightHalfPlane :=
    analyticOnNhd_const
  -- Multiply by constants and add.
  simpa [fhatProfileC, mul_assoc, add_assoc] using! (hc1.mul ha).add (hc2.mul hb)

/-! #### Analyticity of the Laplace integral on `Re u > 2` -/


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont
