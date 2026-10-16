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
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Equality.A.Defs
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Kernels
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Equality.A.GPsiIntegrability


/-!
# Integral identity for `AKernel0`

On the convergent range `u > 4`, the Laplace integrand `AKernel0 t * exp(-π * u * t)` decomposes as
a fixed linear combination of the auxiliary integrands `gV u t` and `gψ u t`. This identity is used
to rewrite the Laplace transform of the `a`-kernel as a difference of two integrals.

## Main statement
* `integral_AKernel0_mul_exp_eq`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceEqA

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Interval

open Complex MeasureTheory Real SchwartzMap Set
open UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Decompose the Laplace integral of `AKernel0` into the corresponding `gV` and `gψ` integrals. -/
public lemma integral_AKernel0_mul_exp_eq (u : ℝ) (hu : 4 < u) :
    (∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * u * t)) =
      ((π : ℂ) / (28304640 : ℂ)) * (∫ t in Set.Ioi (0 : ℝ), gV u t) -
        (1 / ((65520 : ℂ) * π)) * (∫ t in Set.Ioi (0 : ℝ), gψ u t) := by
  have hu0 : 0 ≤ u := le_trans (by linarith) (le_of_lt hu)
  -- integrability of the two pieces on `Ioi 0` (needed for `integral_sub`)
  have hIntV : IntegrableOn (gV u) (Set.Ioi (0 : ℝ)) volume := by
    have hIoc : IntegrableOn (gV u) (Set.Ioc (0 : ℝ) 1) volume := integrableOn_gV_Ioc (u := u) hu0
    have hIoi : IntegrableOn (gV u) (Set.Ioi (1 : ℝ)) volume := integrableOn_gV_Ioi_one (u := u) hu
    rw [Ioi_eq_Ioc_union_Ioi_one]
    exact (MeasureTheory.integrableOn_union).2 ⟨hIoc, hIoi⟩
  have hIntψ : IntegrableOn (gψ u) (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_gψ_Ioi_zero (u := u) hu
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hIntVμ : Integrable (fun t : ℝ => gV u t) μ := by simpa [IntegrableOn, μ] using! hIntV
  have hIntψμ : Integrable (fun t : ℝ => gψ u t) μ := by simpa [IntegrableOn, μ] using! hIntψ
  -- pointwise identification of the integrand on `Ioi 0`
  have hEq :
      ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioi (0 : ℝ) →
        AKernel0 t * (Real.exp (-Real.pi * u * t) : ℂ) =
          ((π : ℂ) / (28304640 : ℂ)) * gV u t -
            (1 / ((65520 : ℂ) * π)) * gψ u t := by
    refine ae_of_all _ ?_
    intro t ht
    have ht0 : 0 < t := ht
    have hAK : AKernel0 t = AKernel t ht0 := by simp [AKernel0, ht0]
    have hker : LaplaceProfiles.varphiKernel0 t = ((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht0) := by
      simp [LaplaceProfiles.varphiKernel0, ht0]
    have hψ : ψI (it t ht0) = ψI' ((t : ℂ) * Complex.I) := by
      let z : ℂ := (t : ℂ) * Complex.I
      have hz : 0 < z.im := by simpa [z] using! ht0
      have hEq : ψI' z = ψI (⟨z, hz⟩ : ℍ) := by simp [ψI', hz]
      have hit : (⟨z, hz⟩ : ℍ) = it t ht0 := by
        ext1
        simp [z, it, mul_comm]
      simp [z, hEq, hit]
    -- Expand `AKernel` and regroup.
    simp [hAK, AKernel, gV, gψ, hker, hψ, sub_eq_add_neg, mul_add,
      mul_assoc, mul_left_comm, mul_comm]
  have hcongr :
      (∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * u * t)) =
        ∫ t in Set.Ioi (0 : ℝ),
          (((π : ℂ) / (28304640 : ℂ)) * gV u t -
              (1 / ((65520 : ℂ) * π)) * gψ u t) := by
    -- use the pointwise equality on the measurable set `Ioi 0`
    simpa [μ] using! (MeasureTheory.setIntegral_congr_ae (μ := volume) measurableSet_Ioi hEq)
  -- expand the integral on the right using `integral_sub` and `integral_const_mul`
  have hIntVsc :
      Integrable (fun t : ℝ => ((π : ℂ) / (28304640 : ℂ)) * gV u t) μ :=
    (hIntVμ.const_mul ((π : ℂ) / (28304640 : ℂ)))
  have hIntψsc :
      Integrable (fun t : ℝ => (1 / ((65520 : ℂ) * π)) * gψ u t) μ :=
    (hIntψμ.const_mul (1 / ((65520 : ℂ) * π)))
  -- rewrite everything in terms of the restricted measure `μ`
  have hsub :
      (∫ t : ℝ, (((π : ℂ) / (28304640 : ℂ)) * gV u t -
            (1 / ((65520 : ℂ) * π)) * gψ u t) ∂μ) =
        (∫ t : ℝ, ((π : ℂ) / (28304640 : ℂ)) * gV u t ∂μ) -
          (∫ t : ℝ, (1 / ((65520 : ℂ) * π)) * gψ u t ∂μ) :=
    MeasureTheory.integral_sub hIntVsc hIntψsc
  -- rewrite the set integral as an integral w.r.t. the restricted measure `μ`,
  -- apply `integral_sub`, then pull out constants.
  have hsub_set :
      (∫ t in Set.Ioi (0 : ℝ),
          ((π : ℂ) / (28304640 : ℂ)) * gV u t - (1 / ((65520 : ℂ) * π)) * gψ u t) =
        (∫ t in Set.Ioi (0 : ℝ), ((π : ℂ) / (28304640 : ℂ)) * gV u t) -
          (∫ t in Set.Ioi (0 : ℝ), (1 / ((65520 : ℂ) * π)) * gψ u t) := by
    simpa [μ] using! hsub
  have hconstV :
      (∫ t in Set.Ioi (0 : ℝ), ((π : ℂ) / (28304640 : ℂ)) * gV u t) =
        ((π : ℂ) / (28304640 : ℂ)) * (∫ t in Set.Ioi (0 : ℝ), gV u t) := by
    simpa [μ] using! (MeasureTheory.integral_const_mul (μ := μ) ((π : ℂ) / (28304640 : ℂ)) (gV u))
  have hconstψ :
      (∫ t in Set.Ioi (0 : ℝ), (1 / ((65520 : ℂ) * π)) * gψ u t) =
        (1 / ((65520 : ℂ) * π)) * (∫ t in Set.Ioi (0 : ℝ), gψ u t) := by
    simpa [μ] using!
      (MeasureTheory.integral_const_mul (μ := μ) (1 / ((65520 : ℂ) * π)) (gψ u))
  -- combine
  rw [hcongr, hsub_set, hconstV, hconstψ]


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceEqA
