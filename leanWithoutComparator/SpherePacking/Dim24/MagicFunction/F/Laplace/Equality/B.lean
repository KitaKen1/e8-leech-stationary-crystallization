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
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Equality.A.AKernelIntegralIdentity
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Profiles.BProfile.LaplaceFormula
import SpherePacking.Dim24.MagicFunction.F.Laplace.Apply


/-!
# Laplace identity for `BKernel0`

This file rewrites the Laplace integral of `BKernel0` in terms of the auxiliary integrands `gV`
and `gψ` from `LaplaceEqA`. As an application, we package the Laplace representation of `f` on the
range `‖x‖ > 2`.

## Main statements
* `integral_BKernel0_mul_exp_eq`
* `f_eq_laplace_A`

## References
`dim_24.tex`, (4.2).

-/

namespace SpherePacking.Dim24.LaplaceTmp

noncomputable section

open scoped FourierTransform SchwartzMap

open Complex MeasureTheory Real SchwartzMap Set
open UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace LaplaceEqB

open Complex MeasureTheory Real
open LaplaceEqA


/-- Rewrite the Laplace integral of `BKernel0` as a linear combination of the `gV` and `gψ`
terms. -/
public lemma integral_BKernel0_mul_exp_eq (u : ℝ) (hu : 4 < u) :
    (∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Real.exp (-Real.pi * u * t)) =
      ((π : ℂ) / (28304640 : ℂ)) * (∫ t in Set.Ioi (0 : ℝ), gV u t) +
        (1 / ((65520 : ℂ) * π)) * (∫ t in Set.Ioi (0 : ℝ), gψ u t) := by
  have hu0 : 0 ≤ u := le_trans (by linarith) (le_of_lt hu)
  -- integrability of the two pieces on `Ioi 0` (needed for `integral_add`)
  have hIntV : IntegrableOn (gV u) (Set.Ioi (0 : ℝ)) volume := by
    have hIoc : IntegrableOn (gV u) (Set.Ioc (0 : ℝ) 1) volume := integrableOn_gV_Ioc (u := u) hu0
    have hIoi : IntegrableOn (gV u) (Set.Ioi (1 : ℝ)) volume := integrableOn_gV_Ioi_one (u := u) hu
    rw [Ioi_eq_Ioc_union_Ioi_one]
    exact (MeasureTheory.integrableOn_union).2 ⟨hIoc, hIoi⟩
  have hIntψ : IntegrableOn (gψ u) (Set.Ioi (0 : ℝ)) volume := integrableOn_gψ_Ioi_zero (u := u) hu
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hIntVμ : Integrable (fun t : ℝ => gV u t) μ := by simpa [IntegrableOn, μ] using! hIntV
  have hIntψμ : Integrable (fun t : ℝ => gψ u t) μ := by simpa [IntegrableOn, μ] using! hIntψ
  -- pointwise identification of the integrand on `Ioi 0`
  have hEq :
      ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioi (0 : ℝ) →
        BKernel0 t * (Real.exp (-Real.pi * u * t) : ℂ) =
          ((π : ℂ) / (28304640 : ℂ)) * gV u t + (1 / ((65520 : ℂ) * π)) * gψ u t := by
    refine ae_of_all _ ?_
    intro t ht
    have ht0 : 0 < t := ht
    have hB : BKernel0 t = BKernel t ht0 := by simp [BKernel0, ht0]
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
    -- Expand `BKernel` and regroup.
    simp [hB, BKernel, gV, gψ, hker, hψ, mul_add, mul_assoc, mul_left_comm, mul_comm]
  have hcongr :
      (∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Real.exp (-Real.pi * u * t)) =
        ∫ t in Set.Ioi (0 : ℝ),
          (((π : ℂ) / (28304640 : ℂ)) * gV u t + (1 / ((65520 : ℂ) * π)) * gψ u t) := by
    simpa [μ] using! (MeasureTheory.setIntegral_congr_ae (μ := volume) measurableSet_Ioi hEq)
  have hIntVsc :
      Integrable (fun t : ℝ => ((π : ℂ) / (28304640 : ℂ)) * gV u t) μ :=
    hIntVμ.const_mul ((π : ℂ) / (28304640 : ℂ))
  have hIntψsc :
      Integrable (fun t : ℝ => (1 / ((65520 : ℂ) * π)) * gψ u t) μ :=
    hIntψμ.const_mul (1 / ((65520 : ℂ) * π))
  have hadd :
      (∫ t : ℝ, (((π : ℂ) / (28304640 : ℂ)) * gV u t + (1 / ((65520 : ℂ) * π)) * gψ u t) ∂μ) =
        (∫ t : ℝ, ((π : ℂ) / (28304640 : ℂ)) * gV u t ∂μ) +
          (∫ t : ℝ, (1 / ((65520 : ℂ) * π)) * gψ u t ∂μ) :=
    MeasureTheory.integral_add hIntVsc hIntψsc
  have hadd_set :
      (∫ t in Set.Ioi (0 : ℝ),
          ((π : ℂ) / (28304640 : ℂ)) * gV u t + (1 / ((65520 : ℂ) * π)) * gψ u t) =
          (∫ t in Set.Ioi (0 : ℝ), ((π : ℂ) / (28304640 : ℂ)) * gV u t) +
          (∫ t in Set.Ioi (0 : ℝ), (1 / ((65520 : ℂ) * π)) * gψ u t) := by
    simpa [μ] using! hadd
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
  rw [hcongr, hadd_set, hconstV, hconstψ]

end LaplaceEqB

/-- Laplace representation for `f` for `‖x‖ > 2` (paper (4.2)). -/
public theorem f_eq_laplace_A (x : ℝ²⁴) (hx : 2 < ‖x‖) :
    f x =
      (((Real.sin (Real.pi * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
        (∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * (‖x‖ ^ 2) * t)) := by
  have hu : 4 < ‖x‖ ^ (2 : ℕ) := by nlinarith [hx]
  set u : ℝ := ‖x‖ ^ (2 : ℕ)
  have hu' : 4 < u := by simpa [u] using! hu
  have hf := LaplaceApply.f_apply (x := x)
  have ha := LaplaceProfiles.aProfile_eq_laplace_varphi (u := u) hu'
  have hb := LaplaceProfiles.LaplaceBProfile.bProfile_eq_laplace_psiI (u := u) hu'
  set s : ℂ := (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ)
  have ha' :
      aProfile u =
        (4 * (Complex.I : ℂ)) * s * (∫ t in Set.Ioi (0 : ℝ), LaplaceEqA.gV u t) := by
    have hsplit := LaplaceEqA.integral_gV_Ioi_eq_interval_add_Ioi_one (u := u) hu'
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
  have hAK := LaplaceEqA.integral_AKernel0_mul_exp_eq (u := u) hu'
  -- Substitute the Laplace formulas for `aProfile` and `bProfile`, then match the kernel integral.
  calc
    f x =
        (- (π * Complex.I) / (113218560 : ℂ)) * aProfile (‖x‖ ^ (2 : ℕ)) -
          (Complex.I / ((262080 : ℂ) * π)) * bProfile (‖x‖ ^ (2 : ℕ)) := by
            simpa using! hf
    _ =
        (- (π * Complex.I) / (113218560 : ℂ)) * aProfile u -
          (Complex.I / ((262080 : ℂ) * π)) * bProfile u := by
            simp [u]
    _ =
        s *
          (((π : ℂ) / (28304640 : ℂ)) * (∫ t in Set.Ioi (0 : ℝ), LaplaceEqA.gV u t) -
            (1 / ((65520 : ℂ) * π)) * (∫ t in Set.Ioi (0 : ℝ), LaplaceEqA.gψ u t)) := by
            -- unfold `aProfile u` and `bProfile u`, then simplify scalar coefficients
            rw [ha', hb']
            ring_nf
            simp [Complex.I_sq]
            ring_nf
    _ =
        s * (∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * u * t)) := by
            -- replace the linear combination by the kernel integral
            rw [← hAK]
    _ = (((Real.sin (Real.pi * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
          (∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * (‖x‖ ^ 2) * t)) := by
            simp [s, u, mul_assoc]


end

end SpherePacking.Dim24.LaplaceTmp
