-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.Function
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
public import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Basic
import SpherePacking.Dim24.MagicFunction.B.Defs.J5Smooth
public import SpherePacking.MagicFunction.IntegralParametrisations
public import SpherePacking.ModularForms.ResToImagAxis
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import SpherePacking.Dim24.MagicFunction.F.Laplace.TopologyDomains
public import SpherePacking.ForMathlib.IntegrablePowMulExp
public import SpherePacking.ForMathlib.DerivHelpers


/-!
# Complexified profiles

This file defines complex-parameter extensions of the real profile derivatives `aProfile` and
`bProfile`, together with the contour-integral pieces used to build `aPrimeC` and `bPrimeC`.

These complexified profiles are used in the Laplace/Fourier analytic continuation arguments.

## Main definitions
* `expU`
* `A.aPrimeC`
* `B.bPrimeC`

## Main statements
* `A.aPrimeC_ofReal`
* `B.bPrimeC_ofReal`
-/

namespace SpherePacking.Dim24

noncomputable section

open scoped Interval UpperHalfPlane

open Complex Real MeasureTheory
open MagicFunction.Parametrisations intervalIntegral

namespace ProfileComplex

/-- Exponential factor `exp(π i u z)` with complex parameter `u`. -/
@[expose] public def expU (u z : ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * u * z)

/-!
## Differentiability in the complex parameter

For the analytic-continuation arguments in `F/Laplace`, we need that the complexified profiles
`aPrimeC` and `bPrimeC` are holomorphic in the right half-plane.

We prove this by differentiating under the integral sign for each defining piece.
-/

open scoped Topology

lemma norm_expU_le_exp_norm_mul (u z : ℂ) :
    ‖expU u z‖ ≤ Real.exp (Real.pi * (‖u‖ * ‖z‖)) := by
  have hnorm : ‖(Real.pi : ℂ) * Complex.I * u * z‖ = |Real.pi| * (‖u‖ * ‖z‖) := by
    simp [Complex.norm_real, mul_left_comm, mul_comm]
  simpa [expU, hnorm, abs_of_nonneg Real.pi_pos.le, mul_assoc, mul_left_comm, mul_comm] using!
    (Complex.norm_exp_le_exp_norm ((Real.pi : ℂ) * Complex.I * u * z))

lemma hasDerivAt_expU (u0 z : ℂ) :
    HasDerivAt (fun u : ℂ => expU u z) ((Real.pi * Complex.I * z) * expU u0 z) u0 := by
  -- Rewrite to `u ↦ exp (u * (π i z))`.
  have hrew :
      (fun u : ℂ => expU u z) = fun u : ℂ => Complex.exp (u * (Real.pi * Complex.I * z)) := by
    funext u
    simp [expU, mul_left_comm, mul_comm]
  -- Differentiate the exponential of a linear map.
  have hlin :
      HasDerivAt (fun u : ℂ => u * (Real.pi * Complex.I * z)) (Real.pi * Complex.I * z) u0 := by
    simpa using! (hasDerivAt_mul_const (Real.pi * Complex.I * z) (x := u0))
  have hexp :
      HasDerivAt (fun u : ℂ => Complex.exp (u * (Real.pi * Complex.I * z)))
        (Complex.exp (u0 * (Real.pi * Complex.I * z)) * (Real.pi * Complex.I * z)) u0 :=
    HasDerivAt.comp u0 (Complex.hasDerivAt_exp (u0 * (Real.pi * Complex.I * z))) hlin
  -- Reorder the derivative constant to match the statement.
  simpa [hrew, expU, mul_assoc, mul_left_comm, mul_comm] using! hexp

lemma differentiableAt_intervalIntegral_mul_expU
    {base z : ℝ → ℂ} (u0 : ℂ) (Cbase Cz : ℝ)
    (hbase_meas : AEStronglyMeasurable base (volume.restrict (Ι (0 : ℝ) 1)))
    (hz_meas : AEStronglyMeasurable z (volume.restrict (Ι (0 : ℝ) 1)))
    (hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase)
    (hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ Cz) :
    DifferentiableAt ℂ (fun u : ℂ => ∫ t in (0 : ℝ)..1, base t * expU u (z t)) u0 := by
  have hab : (0 : ℝ) ≤ 1 := by norm_num
  have ht1 : (1 : ℝ) ∈ Ι (0 : ℝ) 1 := by
    -- `Ι 0 1 = Ioc 0 1` and `1 ∈ Ioc 0 1`.
    simp
  have hCbase : 0 ≤ Cbase := (norm_nonneg (base 1)).trans (hbase_bound 1 ht1)
  have hCz : 0 ≤ Cz := (norm_nonneg (z 1)).trans (hz_bound 1 ht1)
  let F : ℂ → ℝ → ℂ := fun u t => base t * expU u (z t)
  let F' : ℂ → ℝ → ℂ := fun u t => base t * ((Real.pi * Complex.I * z t) * expU u (z t))
  have hcontExpU (u : ℂ) : Continuous fun w : ℂ => expU u w := by
    have hlin : Continuous fun w : ℂ => ((Real.pi : ℂ) * Complex.I * u) * w :=
      continuous_const.mul continuous_id
    simpa [expU, mul_assoc, mul_left_comm, mul_comm] using! Complex.continuous_exp.comp hlin
  -- `IntervalIntegrable (F u0)` on `0..1`.
  have hF_int : IntervalIntegrable (F u0) volume (0 : ℝ) 1 := by
    -- Reduce to `IntegrableOn` on `Ioc 0 1` (since `0 ≤ 1`).
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := (volume : Measure ℝ)) hab]
    -- Prove integrability on a finite-measure set by a uniform bound.
    have hmeas : AEStronglyMeasurable (F u0) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      have hz' : AEStronglyMeasurable z (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
        simpa [Set.uIoc_of_le hab] using! hz_meas
      have hbase' : AEStronglyMeasurable base (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
        simpa [Set.uIoc_of_le hab] using! hbase_meas
      have hexp :
          AEStronglyMeasurable (fun t : ℝ => expU u0 (z t))
            (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        (hcontExpU u0).comp_aestronglyMeasurable hz'
      simpa [F] using! hbase'.mul hexp
    have hbound :
        ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
          ‖F u0 t‖ ≤ Cbase * Real.exp (Real.pi * (‖u0‖ * Cz)) := by
      have hmem :
          ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), t ∈ Set.Ioc (0 : ℝ) 1 :=
        ae_restrict_mem measurableSet_Ioc
      filter_upwards [hmem] with t ht
      have ht' : t ∈ Ι (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le hab] using! ht
      have hb : ‖base t‖ ≤ Cbase := hbase_bound t ht'
      have hz' : ‖z t‖ ≤ Cz := hz_bound t ht'
      have hexp :
          ‖expU u0 (z t)‖ ≤ Real.exp (Real.pi * (‖u0‖ * Cz)) := by
        have := norm_expU_le_exp_norm_mul u0 (z t)
        exact this.trans (by gcongr)
      exact norm_mul_le_of_le (hbase_bound t ht') hexp
    -- Use boundedness to get integrability.
    refine ⟨hmeas, ?_⟩
    -- Finite integral on a finite-measure set.
    exact HasFiniteIntegral.of_bounded hbound
  -- Measurability hypotheses for the derivative lemma.
  have hF_meas :
      ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (F u) (volume.restrict (Ι (0 : ℝ) 1)) := by
    -- It holds for all `u`.
    refine Filter.mem_of_superset (Filter.univ_mem : (Set.univ : Set ℂ) ∈ 𝓝 u0) ?_
    intro u _hu
    have hexp :
        AEStronglyMeasurable (fun t : ℝ => expU u (z t)) (volume.restrict (Ι (0 : ℝ) 1)) :=
      (hcontExpU u).comp_aestronglyMeasurable hz_meas
    simpa [F] using! hbase_meas.mul hexp
  have hF'_meas : AEStronglyMeasurable (F' u0) (volume.restrict (Ι (0 : ℝ) 1)) := by
    have hexp :
        AEStronglyMeasurable (fun t : ℝ => expU u0 (z t)) (volume.restrict (Ι (0 : ℝ) 1)) :=
      (hcontExpU u0).comp_aestronglyMeasurable hz_meas
    have hfac : AEStronglyMeasurable (fun t : ℝ => (Real.pi * Complex.I * z t : ℂ))
        (volume.restrict (Ι (0 : ℝ) 1)) := by
      simpa [mul_assoc] using!
        (aestronglyMeasurable_const.mul (aestronglyMeasurable_const.mul hz_meas))
    have hmul1 :
        AEStronglyMeasurable (fun t : ℝ => (Real.pi * Complex.I * z t : ℂ) * expU u0 (z t))
          (volume.restrict (Ι (0 : ℝ) 1)) := hfac.mul hexp
    simpa [F', mul_assoc] using! hbase_meas.mul hmul1
  -- Dominating bound for `F'` on a neighborhood: a constant works on a finite interval.
  let bound : ℝ → ℝ :=
    fun _t => Cbase * (Real.pi * Cz) * Real.exp (Real.pi * ((‖u0‖ + 1) * Cz))
  have bound_int : IntervalIntegrable bound volume (0 : ℝ) 1 :=
    IntervalIntegrable.symm intervalIntegrable_const
  have h_bound :
      ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 →
        ∀ u ∈ Metric.ball u0 (1 : ℝ), ‖F' u t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall (fun t ht u hu => ?_)
    have hb : ‖base t‖ ≤ Cbase := hbase_bound t ht
    have hz' : ‖z t‖ ≤ Cz := hz_bound t ht
    have hu' : ‖u‖ ≤ ‖u0‖ + 1 := by
      have hdist : ‖u - u0‖ < (1 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm] using! hu
      have hdist_le : ‖u - u0‖ ≤ (1 : ℝ) := le_of_lt hdist
      have htri : ‖u‖ ≤ ‖u0‖ + ‖u - u0‖ := by
        simpa [sub_eq_add_neg, add_assoc] using! (norm_add_le u0 (u - u0))
      exact htri.trans (by nlinarith)
    have hexp :
        ‖expU u (z t)‖ ≤ Real.exp (Real.pi * ((‖u0‖ + 1) * Cz)) := by
      have h0 := norm_expU_le_exp_norm_mul u (z t)
      have hmul : ‖u‖ * ‖z t‖ ≤ (‖u0‖ + 1) * Cz := by gcongr
      have hmul' : Real.pi * (‖u‖ * ‖z t‖) ≤ Real.pi * ((‖u0‖ + 1) * Cz) :=
        mul_le_mul_of_nonneg_left hmul Real.pi_pos.le
      exact h0.trans (Real.exp_le_exp.2 hmul')
    have hzpi : ‖(Real.pi * Complex.I * z t : ℂ)‖ ≤ Real.pi * Cz := by
      calc
        ‖(Real.pi * Complex.I * z t : ℂ)‖ = Real.pi * ‖z t‖ := by
          simp [mul_assoc, Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
        _ ≤ Real.pi * Cz := mul_le_mul_of_nonneg_left hz' Real.pi_pos.le
    calc
      ‖F' u t‖ = ‖base t‖ * ‖(Real.pi * Complex.I * z t : ℂ)‖ * ‖expU u (z t)‖ := by
        simp [F', mul_assoc, mul_left_comm, mul_comm]
      _ ≤ Cbase * (Real.pi * Cz) * Real.exp (Real.pi * ((‖u0‖ + 1) * Cz)) := by
        gcongr
      _ = bound t := by simp [bound, mul_assoc, mul_left_comm, mul_comm]
  have h_diff :
      ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 →
        ∀ u ∈ Metric.ball u0 (1 : ℝ), HasDerivAt (fun u : ℂ => F u t) (F' u t) u := by
    refine Filter.Eventually.of_forall (fun t _ u _ => ?_)
    have h := (hasDerivAt_expU (u0 := u) (z := z t)).const_mul (base t)
    simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using! h
  have h :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ))
      (F := F) (F' := F') (x₀ := u0) (s := Metric.ball u0 (1 : ℝ))
      (hs := by simpa using! Metric.ball_mem_nhds u0 (by norm_num)) (bound := bound)
      (hF_meas := hF_meas) (hF_int := hF_int)
      (hF'_meas := hF'_meas) (h_bound := h_bound) (bound_integrable := bound_int) (h_diff := h_diff)
  exact h.2.differentiableAt

/-- If an interval-integral expression agrees with a function `I`, then `I` is differentiable
at `u0`.

This is a convenience wrapper around `differentiableAt_intervalIntegral_mul_expU`. -/
public lemma differentiableAt_intervalIntegral_mul_expU_of_eq
    {base z : ℝ → ℂ} (u0 : ℂ) (Cbase Cz : ℝ)
    (hbase_meas : AEStronglyMeasurable base (volume.restrict (Ι (0 : ℝ) 1)))
    (hz_meas : AEStronglyMeasurable z (volume.restrict (Ι (0 : ℝ) 1)))
    (hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase)
    (hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ Cz)
    {I : ℂ → ℂ}
    (hI : (fun u : ℂ => ∫ t in (0 : ℝ)..1, base t * expU u (z t)) = I) :
    DifferentiableAt ℂ I u0 := by
  simpa [hI] using!
    differentiableAt_intervalIntegral_mul_expU (base := base) (z := z) u0 Cbase Cz
      hbase_meas hz_meas hbase_bound hz_bound

public lemma differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable
    {base z : ℝ → ℂ} (u0 : ℂ) (Cbase Cz : ℝ)
    (hbase : Measurable base) (hz : Continuous z)
    (hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase)
    (hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ Cz)
    {I : ℂ → ℂ}
    (hI : (fun u : ℂ => ∫ t in (0 : ℝ)..1, base t * expU u (z t)) = I) :
    DifferentiableAt ℂ I u0 := by
  refine
    differentiableAt_intervalIntegral_mul_expU_of_eq (base := base) (z := z) u0 Cbase Cz
      hbase.aestronglyMeasurable hz.aestronglyMeasurable hbase_bound hz_bound hI

/-! ### Complexified `a'` -/

namespace A

/-!
The functions `Φᵢ'` are written in terms of the contour variable `z`, while `Φᵢ` denotes the
reparametrised version along the path `zᵢ'`.
-/

/-- First complex integrand for the `a'` profile.

The prime indicates that this is a function of the contour variable `z` (before
reparametrisation by `t`). -/
@[expose] public def Φ₁' (u : ℂ) (z : ℂ) : ℂ :=
  varphi' (-1 / (z + 1)) * (z + 1) ^ (10 : ℕ) * expU u z

/-- Alias of `Φ₁'` used for indexing the contour pieces of `aPrimeC`.

The prime indicates that this is a function of the contour variable `z`. -/
@[expose] public def Φ₂' (u : ℂ) : ℂ → ℂ := Φ₁' u

/-- Third complex integrand for the `a'` profile.

The prime indicates that this is a function of the contour variable `z` (before
reparametrisation by `t`). -/
@[expose] public def Φ₃' (u : ℂ) (z : ℂ) : ℂ :=
  varphi' (-1 / (z - 1)) * (z - 1) ^ (10 : ℕ) * expU u z

/-- Alias of `Φ₃'` used for indexing the contour pieces of `aPrimeC`.

The prime indicates that this is a function of the contour variable `z`. -/
@[expose] public def Φ₄' (u : ℂ) : ℂ → ℂ := Φ₃' u

/-- Fifth complex integrand for the `a'` profile.

The prime indicates that this is a function of the contour variable `z` (before
reparametrisation by `t`). -/
@[expose] public def Φ₅' (u : ℂ) (z : ℂ) : ℂ :=
  varphi' (-1 / z) * z ^ (10 : ℕ) * expU u z

/-- Sixth complex integrand for the `a'` profile (the tail along the imaginary axis).

The prime indicates that this is a function of the contour variable `z` (before
reparametrisation by `t`). -/
@[expose] public def Φ₆' (u : ℂ) (z : ℂ) : ℂ :=
  varphi' z * expU u z

/-- Reparametrised integrand for `I₁'`, obtained by composing `Φ₁'` with the path `z₁'`. -/
@[expose] public def Φ₁ (u : ℂ) (t : ℝ) : ℂ := (Complex.I : ℂ) * Φ₁' u (z₁' t)
/-- Reparametrised integrand for `I₂'`, obtained by composing `Φ₂'` with the path `z₂'`. -/
@[expose] public def Φ₂ (u : ℂ) (t : ℝ) : ℂ := Φ₂' u (z₂' t)
/-- Reparametrised integrand for `I₃'`, obtained by composing `Φ₃'` with the path `z₃'`. -/
@[expose] public def Φ₃ (u : ℂ) (t : ℝ) : ℂ := (Complex.I : ℂ) * Φ₃' u (z₃' t)
/-- Reparametrised integrand for `I₄'`, obtained by composing `Φ₄'` with the path `z₄'`. -/
@[expose] public def Φ₄ (u : ℂ) (t : ℝ) : ℂ := (-1 : ℂ) * Φ₄' u (z₄' t)
/-- Reparametrised integrand for `I₅'`, obtained by composing `Φ₅'` with the path `z₅'`. -/
@[expose] public def Φ₅ (u : ℂ) (t : ℝ) : ℂ := (Complex.I : ℂ) * Φ₅' u (z₅' t)
/-- Reparametrised integrand for `I₆'`, obtained by composing `Φ₆'` with the path `z₆'`. -/
@[expose] public def Φ₆ (u : ℂ) (t : ℝ) : ℂ := (Complex.I : ℂ) * Φ₆' u (z₆' t)

/-- The first contour-integral piece of `aPrimeC`.

The prime matches the notation for pieces of the derivative profile `a'`. -/
@[expose] public noncomputable def I₁' (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, Φ₁ u t
/-- The second contour-integral piece of `aPrimeC`.

The prime matches the notation for pieces of the derivative profile `a'`. -/
@[expose] public noncomputable def I₂' (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, Φ₂ u t
/-- The third contour-integral piece of `aPrimeC`.

The prime matches the notation for pieces of the derivative profile `a'`. -/
@[expose] public noncomputable def I₃' (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, Φ₃ u t
/-- The fourth contour-integral piece of `aPrimeC`.

The prime matches the notation for pieces of the derivative profile `a'`. -/
@[expose] public noncomputable def I₄' (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, Φ₄ u t
/-- The fifth contour-integral piece of `aPrimeC`.

The prime matches the notation for pieces of the derivative profile `a'`. -/
@[expose] public noncomputable def I₅' (u : ℂ) : ℂ := (-2 : ℂ) * ∫ t in (0 : ℝ)..1, Φ₅ u t
/-- The tail contour-integral piece of `aPrimeC` over `Set.Ici 1`.

The prime matches the notation for pieces of the derivative profile `a'`. -/
@[expose] public noncomputable def I₆' (u : ℂ) : ℂ := (2 : ℂ) * ∫ t in Set.Ici (1 : ℝ), Φ₆ u t

/-- The complexified `a'` profile `aPrimeC`, defined as a sum of the six contour-integral pieces
`I₁'`-`I₆'`. -/
@[expose] public noncomputable def aPrimeC (u : ℂ) : ℂ :=
  I₁' u + I₂' u + I₃' u + I₄' u + I₅' u + I₆' u

/-- The restriction of the complexified profile `aPrimeC` to real parameters is the real profile
`aProfile`. -/
public lemma aPrimeC_ofReal (u : ℝ) : aPrimeC (u : ℂ) = aProfile u := by
  -- Pure unfolding: reduce both sides to the same sum of six contour integrals.
  simp [
    aPrimeC,
    aProfile,
    RealIntegrals.a',
    RealIntegrals.I₁',
    RealIntegrals.I₂',
    RealIntegrals.I₃',
    RealIntegrals.I₄',
    RealIntegrals.I₅',
    RealIntegrals.I₆',
    RealIntegrals.RealIntegrands.Φ₁,
    RealIntegrals.RealIntegrands.Φ₂,
    RealIntegrals.RealIntegrands.Φ₃,
    RealIntegrals.RealIntegrands.Φ₄,
    RealIntegrals.RealIntegrands.Φ₅,
    RealIntegrals.RealIntegrands.Φ₆,
    RealIntegrals.ComplexIntegrands.Φ₁',
    RealIntegrals.ComplexIntegrands.Φ₂',
    RealIntegrals.ComplexIntegrands.Φ₃',
    RealIntegrals.ComplexIntegrands.Φ₄',
    RealIntegrals.ComplexIntegrands.Φ₅',
    RealIntegrals.ComplexIntegrands.Φ₆',
    expU,
    A.I₁',
    A.I₂',
    A.I₃',
    A.I₄',
    A.I₅',
    A.I₆',
    A.Φ₁,
    A.Φ₂,
    A.Φ₃,
    A.Φ₄,
    A.Φ₅,
    A.Φ₆,
    A.Φ₁',
    A.Φ₂',
    A.Φ₃',
    A.Φ₄',
    A.Φ₅',
    A.Φ₆'
  ]

end A

/-! ### Complexified `b'` -/

namespace B

/-- The first contour-integral piece of `bPrimeC`.

The prime matches the notation for pieces of the derivative profile `b'`. -/
@[expose] public noncomputable def J₁' (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (Complex.I : ℂ) * ψT' (z₁' t) * expU u (z₁' t)

/-- The second contour-integral piece of `bPrimeC`.

The prime matches the notation for pieces of the derivative profile `b'`. -/
@[expose] public noncomputable def J₂' (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    ψT' (z₂' t) * expU u (z₂' t)

/-- The third contour-integral piece of `bPrimeC`.

The prime matches the notation for pieces of the derivative profile `b'`. -/
@[expose] public noncomputable def J₃' (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (Complex.I : ℂ) * ψT' (z₃' t) * expU u (z₃' t)

/-- The fourth contour-integral piece of `bPrimeC`.

The prime matches the notation for pieces of the derivative profile `b'`. -/
@[expose] public noncomputable def J₄' (u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-1 : ℂ) * ψT' (z₄' t) * expU u (z₄' t)

/-- The fifth contour-integral piece of `bPrimeC`.

The prime matches the notation for pieces of the derivative profile `b'`. -/
@[expose] public noncomputable def J₅' (u : ℂ) : ℂ :=
  (-2 : ℂ) * ∫ t in (0 : ℝ)..1,
    (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t)

/-- The tail contour-integral piece of `bPrimeC` over `Set.Ici 1`.

The prime matches the notation for pieces of the derivative profile `b'`. -/
@[expose] public noncomputable def J₆' (u : ℂ) : ℂ :=
  (-2 : ℂ) * ∫ t in Set.Ici (1 : ℝ),
    (Complex.I : ℂ) * ψS' (z₆' t) * expU u (z₆' t)

/-- The complexified `b'` profile `bPrimeC`, defined as a sum of the contour-integral pieces
`J₁'`-`J₆'`. -/
@[expose] public noncomputable def bPrimeC (u : ℂ) : ℂ :=
  J₁' u + J₂' u + J₃' u + J₄' u + J₅' u + J₆' u

/-- The restriction of the complexified profile `bPrimeC` to real parameters is the real profile
`bProfile`. -/
public lemma bPrimeC_ofReal (u : ℝ) : bPrimeC (u : ℂ) = bProfile u := by
  rfl

end B

/-! ### Differentiability of the complexified profiles -/

open scoped Interval

/-- Convert `t ∈ Ι 0 1` to membership in `Set.Ioc 0 1`. -/
public lemma mem_Ioc_of_mem_Ι {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) :
    t ∈ Set.Ioc (0 : ℝ) 1 := by
  simpa [Set.uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht

/-- Convert `t ∈ Ι 0 1` to membership in `Set.Icc 0 1`. -/
public lemma mem_Icc_of_mem_Ι {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) :
    t ∈ Set.Icc (0 : ℝ) 1 :=
  Set.mem_Icc_of_Ioc (mem_Ioc_of_mem_Ι (t := t) ht)

namespace A

open scoped Interval

/-- Uniform bound on the path parametrization `z₁'` on `Ι 0 1`. -/
public lemma norm_z₁'_le (t : ℝ) : ‖z₁' t‖ ≤ (2 : ℝ) :=
  norm_z₁'_le_two t

lemma bound_base_I₁' :
    ∃ C : ℝ, ∀ t ∈ Ι (0 : ℝ) 1,
      ‖(Complex.I : ℂ) * (varphi' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ (10 : ℕ))‖ ≤ C := by
  -- Use the exponential decay of `varphi` on the imaginary axis at `∞` with `1/t ≥ 1`.
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨C0, hC0⟩
  have hC0nonneg : 0 ≤ C0 := by
    have h := hC0 1 (le_rfl : (1 : ℝ) ≤ 1)
    have hexp_pos : 0 < Real.exp (-(2 * Real.pi) * (1 : ℝ)) := by positivity
    exact
      ForMathlib.nonneg_of_nonneg_le_mul (ha := norm_nonneg (varphi.resToImagAxis (1 : ℝ)))
        (hb := hexp_pos) (h := by simpa using! h)
  refine ⟨C0, ?_⟩
  intro t ht
  have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := mem_Ioc_of_mem_Ι ht
  have ht0 : 0 < t := ht'.1
  have ht1 : t ≤ 1 := ht'.2
  have hone : (1 : ℝ) ≤ 1 / t := by simpa using! (one_le_one_div ht0 ht1)
  have hzIcc : t ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_of_mem_Ι ht
  have hz1 : z₁' t + 1 = Complex.I * (t : ℂ) := by
    -- `z₁' t = -1 + I*t`.
    have hz : z₁' t = -1 + Complex.I * (t : ℂ) := by
      simp [MagicFunction.Parametrisations.z₁'_eq_of_mem (t := t) hzIcc]
    calc
      z₁' t + 1 = (-1 : ℂ) + Complex.I * (t : ℂ) + 1 := by
        simp [hz, add_assoc]
      _ = Complex.I * (t : ℂ) := by
        abel
  have hvar :
      ‖varphi' (-1 / (z₁' t + 1))‖ ≤ C0 := by
    -- Identify with `varphi.resToImagAxis (1/t)` and apply the decay bound.
    have hEq :
        varphi' (-1 / (z₁' t + 1)) = varphi.resToImagAxis (1 / t) := by
      -- Compute `-1/(z₁' t + 1) = I*(1/t)`.
      exact Schwartz.I1Smooth.varphi'_neg_one_div_z₁'_add_one_eq t ht'
    have h0 := hC0 (1 / t) hone
    have hexp_le : Real.exp (-(2 * Real.pi) * (1 / t)) ≤ 1 := by
      have : (-(2 * Real.pi) * (1 / t) : ℝ) ≤ 0 := by
        have : 0 ≤ (1 / t : ℝ) := (one_div_pos.2 ht0).le
        nlinarith [Real.pi_pos, this]
      simpa using! (Real.exp_le_one_iff.2 this)
    have hle : C0 * Real.exp (-(2 * Real.pi) * (1 / t)) ≤ C0 :=
      (mul_le_mul_of_nonneg_left hexp_le hC0nonneg).trans (by simp)
    -- Replace the value by the axis restriction.
    have := le_trans (by simpa [hEq] using! h0) hle
    simpa [hEq] using! this
  have hpow : ‖(z₁' t + 1) ^ (10 : ℕ)‖ ≤ 1 := by
    have ht_le_one : ‖z₁' t + 1‖ ≤ 1 := by
      -- `z₁' t + 1 = I*t` and `t ≤ 1`.
      have ht_abs' : ‖(t : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, abs_of_nonneg (le_of_lt ht0)] using! ht1
      simpa [hz1, norm_mul] using! ht_abs'.trans_eq (by simp)
    have := pow_le_pow_left₀ (norm_nonneg (z₁' t + 1)) ht_le_one 10
    simpa [norm_pow] using! this
  calc
    ‖(Complex.I : ℂ) * (varphi' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ (10 : ℕ))‖
        = ‖varphi' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ (10 : ℕ)‖ := by
            simp
    _ ≤ ‖varphi' (-1 / (z₁' t + 1))‖ * ‖(z₁' t + 1) ^ (10 : ℕ)‖ := norm_mul_le _ _
    _ ≤ C0 * 1 := by gcongr
    _ = C0 := by simp

/-- The contour-integral piece `I₁'` is differentiable in the complex parameter.

The prime on `I₁'` matches the notation for pieces of the derivative profile `a'`. -/
public lemma differentiableAt_I₁' (u0 : ℂ) : DifferentiableAt ℂ I₁' u0 := by
  -- Apply the generic interval-integral differentiability lemma.
  let base : ℝ → ℂ :=
    fun t : ℝ => (Complex.I : ℂ) * (varphi' (-1 / (z₁' t + 1)) * (z₁' t + 1) ^ (10 : ℕ))
  let z : ℝ → ℂ := fun t : ℝ => z₁' t
  have hz : Continuous z := by
    -- `z₁'` is an `IccExtend` of a continuous map.
    fun_prop [MagicFunction.Parametrisations.z₁', MagicFunction.Parametrisations.z₁]
  have hbase : Measurable base := by
    -- Combine measurability of arithmetic operations with measurability of `varphi'`.
    have hz_meas : Measurable z := hz.measurable
    have hvar : Measurable fun t : ℝ => varphi' (-1 / (z t + 1)) :=
      measurable_varphi'.comp (measurable_const.div (hz_meas.add measurable_const))
    have hpow : Measurable fun t : ℝ => (z t + 1) ^ (10 : ℕ) :=
      (hz_meas.add measurable_const).pow_const (10 : ℕ)
    have hmul : Measurable fun t : ℝ => varphi' (-1 / (z t + 1)) * (z t + 1) ^ (10 : ℕ) :=
      hvar.mul hpow
    dsimp [base]
    exact measurable_const.mul hmul
  rcases bound_base_I₁' with ⟨Cbase, hCbase⟩
  have hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ (2 : ℝ) := fun t _ => A.norm_z₁'_le t
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase := by
    intro t ht
    simpa [base] using! hCbase t ht
  refine
    differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable
      (base := base) (z := z) u0 Cbase (2 : ℝ) hbase hz hbase_bound hz_bound ?_
  funext u
  simp [I₁', Φ₁, Φ₁', base, z, mul_assoc, mul_comm]

end ProfileComplex.A
end

end SpherePacking.Dim24
