-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
import SpherePacking.Dim24.MagicFunction.F.Fourier
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.EvenU.BProfileZeros
public import SpherePacking.Dim24.MagicFunction.F.BKernelAsymptotics
public import SpherePacking.Dim24.MagicFunction.F.Laplace.KernelTools
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.LeadingCorrection
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingBounds.BKernelSubLeadingBound
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
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Equality.B
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Apply
public import SpherePacking.Dim24.MagicFunction.A.Eigen.Eigenfunction
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ5


/-!
# Fourier profile of `f`

We package the Fourier transform of `f` as a one-variable profile `fhatProfile` in the squared
radius `u = ‖y‖^2`. On the convergent range `u > 4` we express this profile via the Laplace
integral of `BKernel0`.

## Main definitions
* `fhatProfile`

## Main statements
* `fourier_f_apply`
* `fhatProfile_eq_laplace_B_of_four`

## References
`dim_24.tex`, around (4.3).
-/
namespace SpherePacking.Dim24.LaplaceTmp.LaplaceFourier

noncomputable section

open scoped FourierTransform SchwartzMap

open Complex MeasureTheory Real SchwartzMap Set
open UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

open LaplaceApply

/-- One-variable profile for `𝓕 f` in the parameter `u = ‖y‖^2`. -/
@[expose] public def fhatProfile (u : ℝ) : ℂ :=
  (-(π * Complex.I) / (113218560 : ℂ)) * aProfile u +
    (Complex.I / ((262080 : ℂ) * π)) * bProfile u

/-- Rewrite `𝓕 f y` as `fhatProfile (‖y‖^2)`. -/
public lemma fourier_f_apply (y : ℝ²⁴) :
    FT f y = fhatProfile (‖y‖ ^ (2 : ℕ)) := by
  rw [fourier_f]
  simp [fhatProfile, a_apply, b_apply, smul_eq_mul]

/-- Laplace representation of `fhatProfile` in the convergent range `u > 4`. -/
public lemma fhatProfile_eq_laplace_B_of_four (u : ℝ) (hu : 4 < u) :
    fhatProfile u =
      (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
        (∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Real.exp (-Real.pi * u * t)) := by
  have ha := LaplaceProfiles.aProfile_eq_laplace_varphi (u := u) hu
  have hb := LaplaceProfiles.LaplaceBProfile.bProfile_eq_laplace_psiI (u := u) hu
  set s : ℂ := (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ)
  have ha' :
      aProfile u =
        (4 * (Complex.I : ℂ)) * s * (∫ t in Set.Ioi (0 : ℝ), LaplaceEqA.gV u t) := by
    have hsplit := LaplaceEqA.integral_gV_Ioi_eq_interval_add_Ioi_one (u := u) hu
    calc
      aProfile u =
          (4 * (Complex.I : ℂ)) * s *
            ((∫ t in (0 : ℝ)..1, LaplaceEqA.gV u t) + ∫ t in Set.Ioi (1 : ℝ), LaplaceEqA.gV u t)
              := by
              simpa [LaplaceEqA.gV, s, mul_assoc] using! ha
      _ = (4 * (Complex.I : ℂ)) * s * (∫ t in Set.Ioi (0 : ℝ), LaplaceEqA.gV u t) := by
            simp [hsplit, mul_assoc]
  have hb' :
      bProfile u =
        (-4 * (Complex.I : ℂ)) * s * (∫ t in Set.Ioi (0 : ℝ), LaplaceEqA.gψ u t) := by
    simpa [LaplaceEqA.gψ, s, mul_assoc] using! hb
  have hB := LaplaceEqB.integral_BKernel0_mul_exp_eq (u := u) hu
  -- Substitute the Laplace formulas for `aProfile` and `bProfile`, then match the kernel integral.
  calc
    fhatProfile u =
        (-(π * Complex.I) / (113218560 : ℂ)) * aProfile u +
          (Complex.I / ((262080 : ℂ) * π)) * bProfile u := by
            simp [fhatProfile]
    _ =
        s *
          (((π : ℂ) / (28304640 : ℂ)) * (∫ t in Set.Ioi (0 : ℝ), LaplaceEqA.gV u t) +
            (1 / ((65520 : ℂ) * π)) * (∫ t in Set.Ioi (0 : ℝ), LaplaceEqA.gψ u t)) := by
            rw [ha', hb']
            ring_nf
            simp [Complex.I_sq]
            ring_nf
    _ = s * (∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Real.exp (-Real.pi * u * t)) := by
          rw [← hB]
    _ =
        (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
          (∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Real.exp (-Real.pi * u * t)) := by
          simp [s, mul_assoc]

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceFourier
