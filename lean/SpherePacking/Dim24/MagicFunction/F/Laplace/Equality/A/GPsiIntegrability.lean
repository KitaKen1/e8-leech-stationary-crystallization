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
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Equality.A.GVIntegralDecomposition


/-!
# Integrability of `gψ`

This file proves integrability statements for the Laplace integrand `gψ u t` on the ranges
`t > 1` and `t > 0`, used to rewrite the `AKernel0` Laplace integral.

## Main statements
* `integrableOn_gψ_Ioi_one`
* `integrableOn_gψ_Ioi_zero`
-/
namespace SpherePacking.Dim24.LaplaceTmp.LaplaceEqA

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Interval

open Complex MeasureTheory Real SchwartzMap Set
open UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Integrability of `gψ u` on the tail `t > 1` in the convergent range `u > 4`. -/
public lemma integrableOn_gψ_Ioi_one (u : ℝ) (hu : 4 < u) :
    IntegrableOn (gψ u) (Set.Ioi (1 : ℝ)) volume := by
  have hu0 : 0 ≤ u := le_trans (by linarith) (le_of_lt hu)
  have hIntS :
      IntegrableOn
          (fun t : ℝ =>
            ψS' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
          (Set.Ioi (1 : ℝ)) volume :=
    integrableOn_ψS'_imag_mul_exp (u := u) hu0
  have hIntT :
      IntegrableOn
          (fun t : ℝ =>
            ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
          (Set.Ioi (1 : ℝ)) volume :=
    integrableOn_ψT'_imag_mul_exp (u := u) hu
  have hEq :
      (gψ u) =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
        fun t : ℝ =>
          ψS' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ) +
            ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht
    let z : ℂ := (t : ℂ) * Complex.I
    have hz : 0 < z.im := by
      -- `z.im = t`
      simpa [z] using! ht0
    let zH : ℍ := ⟨z, hz⟩
    have hsum0 : ψS zH + ψT zH = ψI zH :=
      congrFun ψS_add_ψT_eq_ψI zH
    have hsum' :
        ψI' z = ψS' z + ψT' z := by
      -- avoid `simp` rewriting the `if`-conditions to `0 < t`
      exact LaplaceProfiles.LaplaceBProfile.ψI'_eq_ψS'_add_ψT' t ht0
    -- distribute the exponential factor
    simp [gψ, z, hsum', add_mul, mul_assoc]
  have hIntSum :
      IntegrableOn
          (fun t : ℝ =>
            ψS' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ) +
              ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
          (Set.Ioi (1 : ℝ)) volume := by
    simpa [MeasureTheory.IntegrableOn] using! (hIntS.add hIntT)
  exact (hIntSum.congr hEq.symm)

/-- Integrability of `gψ u` on `t > 0` in the convergent range `u > 4`. -/
public lemma integrableOn_gψ_Ioi_zero (u : ℝ) (hu : 4 < u) :
    IntegrableOn (gψ u) (Set.Ioi (0 : ℝ)) volume := by
  have hu0 : 0 ≤ u := le_trans (by linarith) (le_of_lt hu)
  have hIoc : IntegrableOn (gψ u) (Set.Ioc (0 : ℝ) 1) volume :=
    integrableOn_gψ_Ioc (u := u) hu0
  have hIoi : IntegrableOn (gψ u) (Set.Ioi (1 : ℝ)) volume :=
    integrableOn_gψ_Ioi_one (u := u) hu
  -- Combine the two parts using the decomposition `Ioi 0 = Ioc 0 1 ∪ Ioi 1`.
  rw [Ioi_eq_Ioc_union_Ioi_one]
  exact (MeasureTheory.integrableOn_union).2 ⟨hIoc, hIoi⟩


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceEqA
