-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
import SpherePacking.Dim24.ModularForms.Psi.Relations
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
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.B
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Continuation.Prelude
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Continuation.Continuation


/-!
# Subtracted tail integrand for the `B`-kernel

This file sets up the subtract-leading tail integrand used in the Laplace continuation of the
Fourier profile in the `b`-case. We package a polynomial majorant for
`‖BKernel0 t - BleadingTermR t‖` on `t ≥ 1`, and record measurability, differentiability, and
integrability lemmas on `Ioi 1`.

## Main definitions
* `rhsBSubLeading`
* `polyBound`
* `tailIntegrand`
* `tailIntegrandDeriv`

## Main statements
* `norm_BKernel0_sub_leading_le_poly`
* `integrable_polyBound_mul_exp_Ioi_one`
* `integrable_polyBoundDeriv_mul_exp_Ioi_one`

-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceBSubLeadingCont.Private

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Topology

open Complex Filter MeasureTheory Real Set SchwartzMap
open UpperHalfPlane

open LaplaceFourierCont
open LaplaceFourierCont.PrivateDefs

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


/--
Right-hand side for the subtract-leading continuation:
`sinSqC u * laplaceBKernelSubLeading u`.
-/
@[expose] public def rhsBSubLeading (u : ℂ) : ℂ := sinSqC u * laplaceBKernelSubLeading u


open AppendixA

lemma BleadingTermR_eq_BleadingLeadingTerm (t : ℝ) :
    (BleadingTermR t : ℂ) = (BleadingLeadingTerm t : ℂ) := by
  simp [BleadingTermR, BleadingLeadingTerm]

/-- Polynomial bound for `‖BKernel0 t - BleadingTermR t‖` on `t ≥ 1`. -/
public lemma norm_BKernel0_sub_leading_le_poly (t : ℝ) (ht : 1 ≤ t) :
    let cΔ : ℝ :=
      Classical.choose LaplaceBSubLeadingBounds.exists_lower_bound_norm_resToImagAxis_Ici_one
    ‖BKernel0 t - (BleadingTermR t : ℂ)‖ ≤
      ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) * Real.pi * t ^ (2 :
      ℕ) +
          (∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t +
            (∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) * (1 / Real.pi) +
              eps) /
        cΔ ^ 2 := by
  intro cΔ
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hB0 : BKernel0 t = BKernel t ht0 := by simp [BKernel0, ht0]
  have hLead : (BleadingTermR t : ℂ) = (BleadingLeadingTerm t : ℂ) :=
    BleadingTermR_eq_BleadingLeadingTerm (t := t)
  have h :=
    LaplaceBSubLeadingBounds.norm_BKernel_sub_leading_le_poly (t := t) ht
  lia

/-- The explicit polynomial majorant for `‖BKernel0 t - BleadingTermR t‖` on the tail `t ≥ 1`. -/
@[expose] public def polyBound (t : ℝ) : ℝ :=
  ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) * Real.pi * t ^ (2 : ℕ) +
        (∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t +
          (∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) * (1 / Real.pi) +
            eps) /
      (Classical.choose LaplaceBSubLeadingBounds.exists_lower_bound_norm_resToImagAxis_Ici_one) ^ 2

/-! #### Differentiability of the subtracted tail integral on `Re u > 0` -/

/-- The subtracted tail integrand `(BKernel0 t - BleadingTermR t) * exp(-π u t)`. -/
@[expose] public def tailIntegrand (u : ℂ) (t : ℝ) : ℂ :=
  (BKernel0 t - (BleadingTermR t : ℂ)) * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- The derivative of `tailIntegrand` with respect to `u`. -/
@[expose] public def tailIntegrandDeriv (u : ℂ) (t : ℝ) : ℂ :=
  (BKernel0 t - (BleadingTermR t : ℂ)) * (-(π : ℂ) * (t : ℂ)) *
    Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- `tailIntegrand` is complex-differentiable in `u`, with derivative `tailIntegrandDeriv`. -/
public lemma hasDerivAt_tailIntegrand (u : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℂ => tailIntegrand u t) (tailIntegrandDeriv u t) u := by
  -- Differentiate the exponential factor and multiply by the `t`-dependent constant.
  have hlin :
      HasDerivAt (fun u : ℂ => (-(π : ℂ)) * u * (t : ℂ)) (-(π : ℂ) * (t : ℂ)) u := by
    simpa [mul_assoc] using!
      ((hasDerivAt_mul_const (t : ℂ) : HasDerivAt (fun u : ℂ => u * (t : ℂ)) (t : ℂ) u).const_mul
        (-(π : ℂ)))
  have hexp :
      HasDerivAt (fun u : ℂ => Complex.exp (-(π : ℂ) * u * (t : ℂ)))
        (Complex.exp (-(π : ℂ) * u * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) u :=
    (Complex.hasDerivAt_exp (-(π : ℂ) * u * (t : ℂ))).comp u hlin
  simpa [tailIntegrand, tailIntegrandDeriv, mul_assoc, mul_left_comm, mul_comm] using!
    (hexp.const_mul (BKernel0 t - (BleadingTermR t : ℂ)))

/-- Measurability of `tailIntegrand u` on the tail measure `volume.restrict (Ioi 1)`. -/
public lemma aestronglyMeasurable_tailIntegrand_Ioi_one (u : ℂ) :
    AEStronglyMeasurable (tailIntegrand u) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  let s : Set ℝ := Set.Ioi (1 : ℝ)
  have hcontOn : ContinuousOn (tailIntegrand u) s := by
    -- Work on the subtype `s` where `t > 1`, so `BKernel0 t = BKernel t _`.
    let S : Type := { t : ℝ // t ∈ s }
    have hp0 : ∀ p : S, 0 < p.1 := fun p => lt_trans (by norm_num) p.2
    have h_it : Continuous fun p : S => (it p.1 (hp0 p) : ℍ) := by
      have hval : Continuous fun p : S => (p.1 : ℂ) :=
        (Complex.continuous_ofReal.comp continuous_subtype_val)
      have hbase : Continuous fun p : S => (Complex.I : ℂ) * (p.1 : ℂ) := by
        simpa using! (continuous_const.mul hval)
      simpa [Dim24.it] using!
        Continuous.upperHalfPlaneMk hbase (fun p => by
          have : 0 < p.1 := hp0 p
          simpa [Complex.mul_im] using! this)
    have h_iOverT : Continuous fun p : S => (iOverT p.1 (hp0 p) : ℍ) := by
      have hinv : Continuous fun p : S => (1 / p.1 : ℝ) := by
        have hval : Continuous fun p : S => (p.1 : ℝ) := continuous_subtype_val
        have hne : ∀ p : S, (p.1 : ℝ) ≠ 0 := fun p => ne_of_gt (hp0 p)
        simpa [one_div] using! (hval.inv₀ hne)
      have hbase : Continuous fun p : S => (Complex.I : ℂ) * ((1 / p.1 : ℝ) : ℂ) := by
        have hcast : Continuous fun p : S => ((1 / p.1 : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp hinv
        simpa using! (continuous_const.mul hcast)
      simpa [Dim24.iOverT, Dim24.it] using!
        Continuous.upperHalfPlaneMk hbase (fun p => by
          have : 0 < (1 / p.1 : ℝ) := one_div_pos.2 (hp0 p)
          simpa [Complex.mul_im] using! this)
    have hvarphi : Continuous (varphi : ℍ → ℂ) := varphi_holo'.continuous
    have hψ : Continuous (ψI : ℍ → ℂ) := SpherePacking.Dim24.continuous_ψI
    have hBK : Continuous fun p : S => BKernel p.1 (hp0 p) := by
      have ht10 : Continuous fun p : S => (p.1 : ℂ) ^ (10 : ℕ) := by
        have hval : Continuous fun p : S => (p.1 : ℂ) :=
          Complex.continuous_ofReal.comp continuous_subtype_val
        simpa using! hval.pow 10
      have hterm1 : Continuous fun p : S =>
          ((π : ℂ) / (28304640 : ℂ)) * (p.1 : ℂ) ^ (10 : ℕ) * varphi (iOverT p.1 (hp0 p)) := by
        simpa [BKernel, mul_assoc] using!
          (continuous_const.mul (ht10.mul (hvarphi.comp h_iOverT)))
      have hterm2 : Continuous fun p : S =>
          (1 / ((65520 : ℂ) * π)) * ψI (it p.1 (hp0 p)) := by
        have hc2 : Continuous fun _ : S => (1 / ((65520 : ℂ) * π) : ℂ) := continuous_const
        exact hc2.mul (hψ.comp h_it)
      simpa [BKernel, add_assoc, mul_assoc] using! hterm1.add hterm2
    have hLead : Continuous fun p : S => (BleadingTermR p.1 : ℂ) := by
      have ht : Continuous fun p : S => p.1 := continuous_subtype_val
      have hlin : Continuous fun p : S => (2 * Real.pi) * p.1 := continuous_const.mul ht
      have hexp : Continuous fun p : S => Real.exp ((2 * Real.pi) * p.1) :=
        Real.continuous_exp.comp hlin
      have hterm1 : Continuous fun p : S => (1 / 39 : ℝ) * p.1 * Real.exp ((2 * Real.pi) * p.1)
        := by
        simpa [mul_assoc] using! (continuous_const.mul (ht.mul hexp))
      have hterm2 : Continuous fun p : S =>
          (10 / (117 * Real.pi) : ℝ) * Real.exp ((2 * Real.pi) * p.1) := by
        simpa [mul_assoc] using! (continuous_const.mul hexp)
      have hreal : Continuous fun p : S => BleadingTermR p.1 := by
        dsimp [BleadingTermR]
        simpa [mul_assoc] using! hterm1.sub hterm2
      simpa using! (Complex.continuous_ofReal.comp hreal)
    have hExp : Continuous fun p : S => Complex.exp (-(π : ℂ) * u * (p.1 : ℂ)) := by
      have hval : Continuous fun p : S => (p.1 : ℂ) :=
        Complex.continuous_ofReal.comp continuous_subtype_val
      have hlin : Continuous fun p : S => (-(π : ℂ) * u) * (p.1 : ℂ) := continuous_const.mul hval
      have hexp : Continuous Complex.exp := by fun_prop
      simpa [mul_assoc] using! (hexp.comp hlin)
    have hEq :
        (fun p : S => tailIntegrand u p.1) =
          fun p : S =>
            (BKernel p.1 (hp0 p) - (BleadingTermR p.1 : ℂ)) *
              Complex.exp (-(π : ℂ) * u * (p.1 : ℂ)) := by
      funext p
      have hp0' : 0 < p.1 := hp0 p
      simp [tailIntegrand, BKernel0, hp0', mul_assoc]
    have hcont_restrict :
        Continuous fun p : S =>
          (BKernel p.1 (hp0 p) - (BleadingTermR p.1 : ℂ)) *
            Complex.exp (-(π : ℂ) * u * (p.1 : ℂ)) := by
      simpa [mul_assoc, sub_eq_add_neg, add_assoc] using!
        ((hBK.sub hLead).mul hExp)
    have hcont : Continuous fun p : S => tailIntegrand u p.1 :=
      by
        exact Continuous.congr hcont_restrict (congrFun (id (Eq.symm hEq)))
    simpa [s] using! (continuousOn_iff_continuous_restrict.2 hcont)
  simpa using! (hcontOn.aestronglyMeasurable (μ := volume) measurableSet_Ioi)

/-- Measurability of `tailIntegrandDeriv u` on the tail measure `volume.restrict (Ioi 1)`. -/
public lemma aestronglyMeasurable_tailIntegrandDeriv_Ioi_one (u : ℂ) :
    AEStronglyMeasurable (tailIntegrandDeriv u) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  let s : Set ℝ := Set.Ioi (1 : ℝ)
  have hcontOn : ContinuousOn (tailIntegrandDeriv u) s := by
    -- Work on the subtype `s` where `t > 1`, so `BKernel0 t = BKernel t _`.
    let S : Type := { t : ℝ // t ∈ s }
    have hp0 : ∀ p : S, 0 < p.1 := fun p => lt_trans (by norm_num) p.2
    have h_it : Continuous fun p : S => (it p.1 (hp0 p) : ℍ) := by
      have hval : Continuous fun p : S => (p.1 : ℂ) :=
        (Complex.continuous_ofReal.comp continuous_subtype_val)
      have hbase : Continuous fun p : S => (Complex.I : ℂ) * (p.1 : ℂ) := by
        simpa using! (continuous_const.mul hval)
      simpa [Dim24.it] using!
        Continuous.upperHalfPlaneMk hbase (fun p => by
          have : 0 < p.1 := hp0 p
          simpa [Complex.mul_im] using! this)
    have h_iOverT : Continuous fun p : S => (iOverT p.1 (hp0 p) : ℍ) := by
      have hinv : Continuous fun p : S => (1 / p.1 : ℝ) := by
        have hval : Continuous fun p : S => (p.1 : ℝ) := continuous_subtype_val
        have hne : ∀ p : S, (p.1 : ℝ) ≠ 0 := fun p => ne_of_gt (hp0 p)
        simpa [one_div] using! (hval.inv₀ hne)
      have hbase : Continuous fun p : S => (Complex.I : ℂ) * ((1 / p.1 : ℝ) : ℂ) := by
        have hcast : Continuous fun p : S => ((1 / p.1 : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp hinv
        simpa using! (continuous_const.mul hcast)
      simpa [Dim24.iOverT, Dim24.it] using!
        Continuous.upperHalfPlaneMk hbase (fun p => by
          have : 0 < (1 / p.1 : ℝ) := one_div_pos.2 (hp0 p)
          simpa [Complex.mul_im] using! this)
    have hvarphi : Continuous (varphi : ℍ → ℂ) := varphi_holo'.continuous
    have hψ : Continuous (ψI : ℍ → ℂ) := SpherePacking.Dim24.continuous_ψI
    have hBK : Continuous fun p : S => BKernel p.1 (hp0 p) := by
      have ht10 : Continuous fun p : S => (p.1 : ℂ) ^ (10 : ℕ) := by
        have hval : Continuous fun p : S => (p.1 : ℂ) :=
          Complex.continuous_ofReal.comp continuous_subtype_val
        simpa using! hval.pow 10
      have hterm1 : Continuous fun p : S =>
          ((π : ℂ) / (28304640 : ℂ)) * (p.1 : ℂ) ^ (10 : ℕ) * varphi (iOverT p.1 (hp0 p)) := by
        simpa [BKernel, mul_assoc] using!
          (continuous_const.mul (ht10.mul (hvarphi.comp h_iOverT)))
      have hterm2 : Continuous fun p : S =>
          (1 / ((65520 : ℂ) * π)) * ψI (it p.1 (hp0 p)) := by
        have hc2 : Continuous fun _ : S => (1 / ((65520 : ℂ) * π) : ℂ) := continuous_const
        exact hc2.mul (hψ.comp h_it)
      simpa [BKernel, add_assoc, mul_assoc] using! hterm1.add hterm2
    have hLead : Continuous fun p : S => (BleadingTermR p.1 : ℂ) := by
      have ht : Continuous fun p : S => p.1 := continuous_subtype_val
      have hlin : Continuous fun p : S => (2 * Real.pi) * p.1 := continuous_const.mul ht
      have hexp : Continuous fun p : S => Real.exp ((2 * Real.pi) * p.1) :=
        Real.continuous_exp.comp hlin
      have hterm1 : Continuous fun p : S => (1 / 39 : ℝ) * p.1 * Real.exp ((2 * Real.pi) * p.1)
        := by
        simpa [mul_assoc] using! (continuous_const.mul (ht.mul hexp))
      have hterm2 : Continuous fun p : S =>
          (10 / (117 * Real.pi) : ℝ) * Real.exp ((2 * Real.pi) * p.1) := by
        simpa [mul_assoc] using! (continuous_const.mul hexp)
      have hreal : Continuous fun p : S => BleadingTermR p.1 := by
        dsimp [BleadingTermR]
        simpa [mul_assoc] using! hterm1.sub hterm2
      simpa using! (Complex.continuous_ofReal.comp hreal)
    have hFactor : Continuous fun p : S => (-(π : ℂ) * (p.1 : ℂ)) := by
      have hval : Continuous fun p : S => (p.1 : ℂ) :=
        Complex.continuous_ofReal.comp continuous_subtype_val
      exact continuous_const.mul hval
    have hExp : Continuous fun p : S => Complex.exp (-(π : ℂ) * u * (p.1 : ℂ)) := by
      have hval : Continuous fun p : S => (p.1 : ℂ) :=
        Complex.continuous_ofReal.comp continuous_subtype_val
      have hlin : Continuous fun p : S => (-(π : ℂ) * u) * (p.1 : ℂ) := continuous_const.mul hval
      have hexp : Continuous Complex.exp := by fun_prop
      simpa [mul_assoc] using! (hexp.comp hlin)
    have hEq :
        (fun p : S => tailIntegrandDeriv u p.1) =
          fun p : S =>
            (BKernel p.1 (hp0 p) - (BleadingTermR p.1 : ℂ)) *
              (-(π : ℂ) * (p.1 : ℂ)) * Complex.exp (-(π : ℂ) * u * (p.1 : ℂ)) := by
      funext p
      have hp0' : 0 < p.1 := hp0 p
      simp [tailIntegrandDeriv, BKernel0, hp0', mul_assoc, mul_left_comm, mul_comm]
    have hcont_restrict :
        Continuous fun p : S =>
          (BKernel p.1 (hp0 p) - (BleadingTermR p.1 : ℂ)) *
            (-(π : ℂ) * (p.1 : ℂ)) * Complex.exp (-(π : ℂ) * u * (p.1 : ℂ)) := by
      -- `(BKernel - lead)` and the extra factor and the exponential are all continuous.
      exact (((hBK.sub hLead).mul hFactor).mul hExp)
    have hcont : Continuous fun p : S => tailIntegrandDeriv u p.1 :=
      Continuous.congr hcont_restrict (congrFun (id (Eq.symm hEq)))
    simpa [s] using! (continuousOn_iff_continuous_restrict.2 hcont)
  simpa using! (hcontOn.aestronglyMeasurable (μ := volume) measurableSet_Ioi)

/-- Integrability of the standard majorant `polyBound t * exp(-π * uMin * t)` on `t > 1`. -/
public lemma integrable_polyBound_mul_exp_Ioi_one (uMin : ℝ) (huMin : 0 < uMin) :
    IntegrableOn (fun t : ℝ => (polyBound t) * Real.exp (-Real.pi * uMin * t)) (Set.Ioi (1 :
    ℝ)) volume
      := by
  let cΔ : ℝ :=
    Classical.choose LaplaceBSubLeadingBounds.exists_lower_bound_norm_resToImagAxis_Ici_one
  let sA : ℝ := ∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|
  let sB : ℝ := ∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|
  let sC : ℝ := ∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|
  let b : ℝ := Real.pi * uMin
  have hb : 0 < b := mul_pos Real.pi_pos huMin
  have h2 : IntegrableOn (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume
    := by
    simpa using!
      (LaplaceBKernelAnalytic.integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 2) (b := b) hb)
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume := by
    simpa [
      pow_one
    ] using! (LaplaceBKernelAnalytic.integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 1) (b := b) hb)
  have h0 : IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume :=
    exp_neg_integrableOn_Ioi 1 hb
  have h2' :
      IntegrableOn (fun t : ℝ => (sA * Real.pi / (cΔ ^ 2)) * (t ^ (2 : ℕ) * Real.exp (-b * t)))
        (Set.Ioi (1 : ℝ)) volume :=
    h2.const_mul (sA * Real.pi / (cΔ ^ 2))
  have h1' :
      IntegrableOn (fun t : ℝ => (sB / (cΔ ^ 2)) * (t * Real.exp (-b * t))) (Set.Ioi (1 :
      ℝ)) volume :=
    h1.const_mul (sB / (cΔ ^ 2))
  have h0' :
      IntegrableOn (fun t : ℝ => ((sC * (1 / Real.pi) + eps) / (cΔ ^ 2)) * Real.exp (-b * t))
        (Set.Ioi (1 : ℝ)) volume :=
    h0.const_mul ((sC * (1 / Real.pi) + eps) / (cΔ ^ 2))
  -- Combine and rewrite.
  have hsum :
      IntegrableOn
          (fun t : ℝ =>
              (sA * Real.pi / (cΔ ^ 2)) * (t ^ (2 : ℕ) * Real.exp (-b * t)) +
                (sB / (cΔ ^ 2)) * (t * Real.exp (-b * t)) +
                  ((sC * (1 / Real.pi) + eps) / (cΔ ^ 2)) * Real.exp (-b * t))
          (Set.Ioi (1 : ℝ)) volume := by
    simpa [add_assoc] using! (h2'.add (h1'.add h0'))
  -- `polyBound t = (sA*pi*t^2 + sB*t + sC*(1/pi) + eps) / cΔ^2`.
  have hEq :
      (fun t : ℝ => polyBound t * Real.exp (-Real.pi * uMin * t)) =
        fun t : ℝ =>
          (sA * Real.pi / (cΔ ^ 2)) * (t ^ (2 : ℕ) * Real.exp (-b * t)) +
            (sB / (cΔ ^ 2)) * (t * Real.exp (-b * t)) +
              ((sC * (1 / Real.pi) + eps) / (cΔ ^ 2)) * Real.exp (-b * t) := by
    funext t
    have hargL : -Real.pi * uMin * t = -(t * b) := by
      dsimp [b]
      ring_nf
    have hargR : -b * t = -(t * b) := by
      ring_nf
    have hargL' : -(Real.pi * t * uMin) = -(t * b) := by
      dsimp [b]
      ring_nf
    -- Clear denominators syntactically and normalize the exponential argument.
    simp [polyBound, cΔ, sA, sB, sC, hargR]
    ring_nf
    simp [hargL']
  lia

/-- Integrability of the standard majorant used for the derivative bound on `t > 1`. -/
public lemma integrable_polyBoundDeriv_mul_exp_Ioi_one (uMin : ℝ) (huMin : 0 < uMin) :
    IntegrableOn (fun t : ℝ => (Real.pi * t) * (polyBound t) * Real.exp (-Real.pi * uMin * t))
      (Set.Ioi (1 : ℝ)) volume := by
  let cΔ : ℝ :=
    Classical.choose LaplaceBSubLeadingBounds.exists_lower_bound_norm_resToImagAxis_Ici_one
  let sA : ℝ := ∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|
  let sB : ℝ := ∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|
  let sC : ℝ := ∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|
  let b : ℝ := Real.pi * uMin
  have hb : 0 < b := mul_pos Real.pi_pos huMin
  have h3 : IntegrableOn (fun t : ℝ => t ^ (3 : ℕ) * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume
    := by
    simpa using!
      (LaplaceBKernelAnalytic.integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 3) (b := b) hb)
  have h2 : IntegrableOn (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume
    := by
    simpa using!
      (LaplaceBKernelAnalytic.integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 2) (b := b) hb)
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume := by
    simpa [
      pow_one
    ] using! (LaplaceBKernelAnalytic.integrableOn_pow_mul_exp_neg_mul_Ioi_one (n := 1) (b := b) hb)
  have h3' :
      IntegrableOn (fun t : ℝ => (Real.pi * (sA * Real.pi) / (cΔ ^ 2)) * (t ^ (3 : ℕ) * Real.exp (-b
      * t)))
        (Set.Ioi (1 : ℝ)) volume :=
    h3.const_mul (Real.pi * (sA * Real.pi) / (cΔ ^ 2))
  have h2' :
      IntegrableOn (fun t : ℝ => (Real.pi * sB / (cΔ ^ 2)) * (t ^ (2 : ℕ) * Real.exp (-b * t)))
        (Set.Ioi (1 : ℝ)) volume :=
    h2.const_mul (Real.pi * sB / (cΔ ^ 2))
  have h1' :
      IntegrableOn (fun t : ℝ => (Real.pi * (sC * (1 / Real.pi) + eps) / (cΔ ^ 2)) * (t * Real.exp
      (-b * t)))
        (Set.Ioi (1 : ℝ)) volume :=
    h1.const_mul (Real.pi * (sC * (1 / Real.pi) + eps) / (cΔ ^ 2))
  have hsum :
      IntegrableOn
          (fun t : ℝ =>
              (Real.pi * (sA * Real.pi) / (cΔ ^ 2)) * (t ^ (3 : ℕ) * Real.exp (-b * t)) +
                (Real.pi * sB / (cΔ ^ 2)) * (t ^ (2 : ℕ) * Real.exp (-b * t)) +
                  (Real.pi * (sC * (1 / Real.pi) + eps) / (cΔ ^ 2)) * (t * Real.exp (-b * t)))
          (Set.Ioi (1 : ℝ)) volume := by
    simpa [add_assoc] using! (h3'.add (h2'.add h1'))
  have hEq :
      (fun t : ℝ => (Real.pi * t) * (polyBound t) * Real.exp (-Real.pi * uMin * t)) =
        fun t : ℝ =>
          (Real.pi * (sA * Real.pi) / (cΔ ^ 2)) * (t ^ (3 : ℕ) * Real.exp (-b * t)) +
            (Real.pi * sB / (cΔ ^ 2)) * (t ^ (2 : ℕ) * Real.exp (-b * t)) +
              (Real.pi * (sC * (1 / Real.pi) + eps) / (cΔ ^ 2)) * (t * Real.exp (-b * t)) := by
    funext t
    have hexpArg : -Real.pi * uMin * t = -b * t := by
      dsimp [b]
      ring_nf
    have hexp : Real.exp (-Real.pi * uMin * t) = Real.exp (-b * t) :=
      congrArg Real.exp hexpArg
    simp [polyBound, cΔ, sA, sB, sC, b]
    ring_nf
  lia

/-! #### Differentiability and analyticity of `laplaceBKernelSubLeading` -/


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceBSubLeadingCont.Private
