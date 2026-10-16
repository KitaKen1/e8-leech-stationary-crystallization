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
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Continuation.Prelude
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Continuation.Continuation


/-!
# Subtract-leading setup for the Fourier profile

For `0 < Re u`, the tail integral for `BKernel0` diverges when `Re u ≤ 2` because of
`Real.exp (2 * π * t)` growth. The standard fix is to subtract an explicit leading term on
`t > 1` and add back its closed-form Laplace transform. This produces a function analytic on
`LaplaceDomains.domainPosNeTwo`.

## Main definitions
* `BleadingTermR`
* `BleadingCorrectionC`
* `laplaceBKernelSubLeading`

## Main statements
* `fourier_f_eq_laplace_B`
* `integral_Ioi_one_BleadingTermC_mul_exp_neg_pi`
* `BleadingCorrectionC_ofReal`
-/

namespace SpherePacking.Dim24.LaplaceTmp

noncomputable section

open scoped FourierTransform SchwartzMap

open Complex MeasureTheory Real SchwartzMap Set
open UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

/-- Laplace representation for `𝓕 f` for `‖y‖ > Real.sqrt 2` (paper (4.3), convergent range). -/
public theorem fourier_f_eq_laplace_B (y : ℝ²⁴) (hy : Real.sqrt 2 < ‖y‖) :
    FT f y =
      (((Real.sin (Real.pi * (‖y‖ ^ 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
        (∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Real.exp (-Real.pi * (‖y‖ ^ 2) * t)) := by
  -- Square the inequality `sqrt 2 < ‖y‖` to get `2 < ‖y‖^2`.
  have hs0 : 0 ≤ Real.sqrt 2 := by positivity
  have hsq : (Real.sqrt 2) ^ (2 : ℕ) < ‖y‖ ^ (2 : ℕ) :=
    pow_lt_pow_left₀ hy hs0 (by decide : (2 : ℕ) ≠ 0)
  set u : ℝ := ‖y‖ ^ (2 : ℕ)
  have hu2 : (2 : ℝ) < u := by
    simpa [u] using! (by simpa using! hsq)
  have huDom : (u : ℂ) ∈ LaplaceDomains.domainTwo := by
    have : (2 : ℝ) < u := hu2
    simpa [LaplaceDomains.domainTwo] using! this
  have heq :
      LaplaceFourierCont.PrivateDefs.fhatProfileC (u : ℂ) =
        LaplaceFourierCont.PrivateDefs.rhsB (u : ℂ) :=
    LaplaceFourierCont.eqOn_domainTwo_fhatProfileC_rhsB (x := (u : ℂ)) huDom
  -- Finish by rewriting `u = ‖y‖^2`.
  calc
    FT f y = LaplaceFourier.fhatProfile u := by
      simpa [u] using! LaplaceFourier.fourier_f_apply (y := y)
    _ = LaplaceFourierCont.PrivateDefs.fhatProfileC (u : ℂ) := by
      simpa using! (LaplaceFourierCont.fhatProfileC_ofReal (u := u)).symm
    _ = LaplaceFourierCont.PrivateDefs.rhsB (u : ℂ) := heq
    _ = (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
          (∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Real.exp (-Real.pi * u * t)) := by
          simpa using! LaplaceFourierCont.rhsB_ofReal (u := u)
    _ = (((Real.sin (Real.pi * (‖y‖ ^ 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
          (∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Real.exp (-Real.pi * (‖y‖ ^ 2) * t)) := by
          simp [u, pow_two, mul_assoc]

/-- The real leading term subtracted from `BKernel0` on the tail `t ≥ 1`. -/
@[expose] public def BleadingTermR (t : ℝ) : ℝ :=
  (1 / 39 : ℝ) * t * Real.exp (2 * Real.pi * t) -
    (10 / (117 * Real.pi) : ℝ) * Real.exp (2 * Real.pi * t)

lemma BleadingTermR_eq_Blead (t : ℝ) :
    BleadingTermR t = LaplaceBleading.Blead t := by
  -- `Blead t = ((1/39) t - 10/(117π)) e^{2π t}`.
  simp [BleadingTermR, LaplaceBleading.Blead, LaplaceBleading.BleadBase, sub_eq_add_neg,
    add_mul, mul_assoc, mul_comm]

lemma integral_Ioi_one_BleadingTermR_mul_exp_neg_pi (u : ℝ) (hu : 2 < u) :
    (∫ t in Set.Ioi (1 : ℝ), BleadingTermR t * Real.exp (-Real.pi * u * t)) =
      (((10 : ℝ) - 3 * Real.pi) * (2 - u) + 3) /
            (117 * (Real.pi ^ (2 : ℕ)) * (u - 2) ^ (2 : ℕ)) *
          Real.exp (-Real.pi * (u - 2)) := by
  simpa [BleadingTermR_eq_Blead] using!
    (LaplaceBleading.integral_Ioi_one_Blead_mul_exp_neg_pi (u := u) hu)

/-- The complex-valued tail integral of `BleadingTermR` equals `BleadingCorrection`. -/
public lemma integral_Ioi_one_BleadingTermC_mul_exp_neg_pi (u : ℝ) (hu : 2 < u) :
    (∫ t in Set.Ioi (1 : ℝ), (BleadingTermR t * Real.exp (-Real.pi * u * t) : ℂ)) =
      BleadingCorrection u := by
  have hreal := integral_Ioi_one_BleadingTermR_mul_exp_neg_pi (u := u) hu
  -- Convert the real integral into a complex integral.
  have hcoe :
      (∫ t in Set.Ioi (1 : ℝ), (BleadingTermR t * Real.exp (-Real.pi * u * t) : ℂ)) =
        Complex.ofReal (∫ t in Set.Ioi (1 : ℝ), BleadingTermR t * Real.exp (-Real.pi * u * t)) := by
    let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
    -- `integral_ofReal` is stated for an explicit measure; unfold the set integral into `μ`.
    simpa [μ] using!
      (integral_ofReal (𝕜 := ℂ) (μ := μ)
        (f := fun t : ℝ => BleadingTermR t * Real.exp (-Real.pi * u * t)))
  -- Finish by rewriting the closed form as `BleadingCorrection`.
  rw [hcoe, hreal]
  simp [BleadingCorrection]


/-- A complex-analytic version of `BleadingCorrection` (with a pole at `u = 2`). -/
@[expose] public def BleadingCorrectionC (u : ℂ) : ℂ :=
  ((((10 : ℂ) - 3 * (Real.pi : ℂ)) * ((2 : ℂ) - u) + (3 : ℂ)) /
        ((117 : ℂ) * ((Real.pi : ℂ) ^ (2 : ℕ)) * (u - (2 : ℂ)) ^ (2 : ℕ))) *
    Complex.exp (-(Real.pi : ℂ) * (u - (2 : ℂ)))

/-- `BleadingCorrectionC` specializes to `BleadingCorrection` on real parameters. -/
public lemma BleadingCorrectionC_ofReal (u : ℝ) :
    BleadingCorrectionC (u : ℂ) = BleadingCorrection u := by
  -- Both sides are the same real closed form, interpreted in `ℂ`.
  simp [BleadingCorrectionC, BleadingCorrection, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg,
    add_comm]

/-- The Laplace expression with the leading tail term subtracted (valid on `domainPosNeTwo`). -/
@[expose] public def laplaceBKernelSubLeading (u : ℂ) : ℂ :=
  ((∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Complex.exp (-(π : ℂ) * u * (t : ℂ))) +
        ∫ t in Set.Ioi (1 : ℝ),
          (BKernel0 t - (BleadingTermR t : ℂ)) * Complex.exp (-(π : ℂ) * u * (t : ℂ))) +
    BleadingCorrectionC u

/-!
### Analytic continuation via subtracting the leading tail

We package the subtracted-tail Laplace expression as a holomorphic function on
`LaplaceDomains.domainPosNeTwo` and identify it with the complexified Fourier profile via the
identity theorem.
-/

end

end SpherePacking.Dim24.LaplaceTmp
