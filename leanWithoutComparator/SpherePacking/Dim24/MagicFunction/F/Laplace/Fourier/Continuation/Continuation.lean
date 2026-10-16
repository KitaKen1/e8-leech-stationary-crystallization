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
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Continuation.Differentiable


/-!
# Analytic continuation on `Re u > 2`

This file completes the analytic continuation of the Laplace expression `laplaceBKernelC` and
packages the identity `fhatProfileC = rhsB` on the half-plane `LaplaceDomains.domainTwo`.

## Main statements
* `LaplaceBKernelAnalytic.analyticOnNhd_laplaceBKernelC_domainTwo`
* `eqOn_domainTwo_fhatProfileC_rhsB`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Topology

open Complex Filter MeasureTheory Real Set SchwartzMap
open UpperHalfPlane
open PrivateDefs

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace LaplaceBKernelAnalytic

open PrivateDefs

/-- `laplaceBKernelC` is analytic on `LaplaceDomains.domainTwo` (the half-plane `2 < Re u`). -/
public lemma analyticOnNhd_laplaceBKernelC_domainTwo :
    AnalyticOnNhd ℂ laplaceBKernelC LaplaceDomains.domainTwo := by
  have hd : DifferentiableOn ℂ laplaceBKernelC LaplaceDomains.domainTwo :=
    differentiableOn_laplaceBKernelC_domainTwo
  exact (analyticOnNhd_iff_differentiableOn LaplaceDomains.domainTwo_isOpen).2 hd

end LaplaceBKernelAnalytic

lemma analyticOnNhd_sinSqC_domainTwo :
    AnalyticOnNhd ℂ sinSqC LaplaceDomains.domainTwo := by
  intro z hz
  have hlin : AnalyticAt ℂ (fun u : ℂ => ((π : ℂ) / 2) * u) z :=
    analyticAt_const.mul analyticAt_id
  have hsin_outer : AnalyticAt ℂ (sin : ℂ → ℂ) (((π : ℂ) / 2) * z) := by
    simpa using! (analyticAt_sin (x := ((π : ℂ) / 2) * z))
  have hsin : AnalyticAt ℂ (fun u : ℂ => (sin : ℂ → ℂ) (((π : ℂ) / 2) * u)) z :=
    hsin_outer.comp hlin
  have hpow :
      AnalyticAt ℂ (fun u : ℂ => ((sin : ℂ → ℂ) (((π : ℂ) / 2) * u)) ^ (2 : ℕ)) z :=
    hsin.pow 2
  have hEq : (fun u : ℂ => ((sin : ℂ → ℂ) (((π : ℂ) / 2) * u)) ^ (2 : ℕ)) = sinSqC := by
    funext u
    simp [sinSqC, div_eq_mul_inv, mul_assoc, mul_comm]
  simpa [hEq] using! hpow

lemma analyticOnNhd_rhsB_domainTwo :
    AnalyticOnNhd ℂ rhsB LaplaceDomains.domainTwo := by
  -- product of analytic functions on `domainTwo`
  have hs : AnalyticOnNhd ℂ sinSqC LaplaceDomains.domainTwo := analyticOnNhd_sinSqC_domainTwo
  have hl : AnalyticOnNhd ℂ laplaceBKernelC LaplaceDomains.domainTwo := by
    simpa using! LaplaceBKernelAnalytic.analyticOnNhd_laplaceBKernelC_domainTwo
  simpa [rhsB] using! hs.mul hl

lemma analyticOnNhd_fhatProfileC_domainTwo :
    AnalyticOnNhd ℂ fhatProfileC LaplaceDomains.domainTwo := by
  intro z hz
  exact analyticOnNhd_fhatProfileC z (domainTwo_subset_rightHalfPlane hz)

/-- On `LaplaceDomains.domainTwo`, the complexified Fourier profile `fhatProfileC` agrees with
`rhsB`. -/
public lemma eqOn_domainTwo_fhatProfileC_rhsB :
    Set.EqOn fhatProfileC rhsB LaplaceDomains.domainTwo := by
  have hana_fhat : AnalyticOnNhd ℂ fhatProfileC LaplaceDomains.domainTwo :=
    analyticOnNhd_fhatProfileC_domainTwo
  have hana_rhs : AnalyticOnNhd ℂ rhsB LaplaceDomains.domainTwo :=
    analyticOnNhd_rhsB_domainTwo
  have hfreq :
      (∃ᶠ z in 𝓝[≠] (5 : ℂ), fhatProfileC z = rhsB z) :=
    LaplaceDomains.frequently_eq_near_five (f := fhatProfileC) (g := rhsB)
      (fun u hu => rhsB_agrees_of_four (u := u) hu)
  have h5 : (5 : ℂ) ∈ LaplaceDomains.domainTwo := by
    simpa [LaplaceDomains.domainTwo] using! (show (2 : ℝ) < (5 : ℝ) by norm_num)
  simpa using!
    (AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (𝕜 := ℂ)
      (f := fhatProfileC) (g := rhsB)
      hana_fhat hana_rhs LaplaceDomains.domainTwo_isPreconnected h5 hfreq)

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont
