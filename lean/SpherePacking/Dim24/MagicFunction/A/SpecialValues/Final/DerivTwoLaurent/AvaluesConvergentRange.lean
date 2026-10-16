-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.Function
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivDefs
public import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegralDefs
public import SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Transform
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi1A
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi2
public import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegralDCT
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderLargeBound
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.Tactic.NormNumI

/-!
# Convergent-range form of `eq:avalues`

This file establishes the `u > 4` version of the paper's identity `eq:avalues`, rewritten in the
profile variable `u = r^2`. It provides the factorization of `aProfile u` as an integral on
`(0,∞)` and then splits this integral into `pTildeIntegral u` plus the remainder term
`avaluesRemainderIntegral u`.

## Main statements
* `aProfile_eq_neg_I_mul_coeffExp_mul_integral_pow_ten_varphi`
* `integral_pow_ten_varphi_eq_pTildeIntegral_add_avaluesRemainderIntegral`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex MeasureTheory Set intervalIntegral

/-!
### Helper lemmas

We keep these local to this file: they are purely about rewriting and integrability on `(0,∞)`.
-/

lemma measurable_imag_axis_Φ₅' (u : ℝ) :
    Measurable fun t : ℝ => RealIntegrals.ComplexIntegrands.Φ₅' u ((t : ℂ) * Complex.I) := by
  -- Everything is measurable by composition of measurable operations,
  -- using measurability of `varphi'`.
  have hz : Measurable fun t : ℝ => ((t : ℂ) * Complex.I) := by
    simpa using! ((Complex.continuous_ofReal.mul continuous_const).measurable)
  have hvar :
      Measurable fun t : ℝ => varphi' ((-1 : ℂ) / ((t : ℂ) * Complex.I)) :=
    measurable_varphi'.comp (measurable_const.div hz)
  have hpow : Measurable fun t : ℝ => (((t : ℂ) * Complex.I) ^ (10 : ℕ)) := by
    simpa using! (hz.pow_const 10)
  set c : ℂ := (Real.pi : ℂ) * Complex.I * (u : ℂ)
  have harg : Measurable fun t : ℝ => c * ((t : ℂ) * Complex.I) := measurable_const.mul hz
  have hexp : Measurable fun t : ℝ => Complex.exp (c * ((t : ℂ) * Complex.I)) :=
    (Complex.continuous_exp.measurable.comp harg)
  -- Unfold `Φ₅'` and assemble.
  simpa [RealIntegrals.ComplexIntegrands.Φ₅', c, mul_assoc] using! (hvar.mul hpow).mul hexp

/-!
### Imaginary-axis rewriting for `Φ₅'`

Goal: on `z = t * I` with `t > 0`, rewrite
`ComplexIntegrands.Φ₅' u z = varphi' (-1/z) * z^10 * exp(π i u z)`
as the `t^10 * varphi(i/t)` integrand used in `avaluesRemainderIntegral`.
-/

theorem Φ₅'_imag_axis_eq_neg_pow_ten_varphi_iOverT (u t : ℝ) (ht : 0 < t) :
    RealIntegrals.ComplexIntegrands.Φ₅' u ((t : ℂ) * Complex.I) =
      -(((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht)) * (Real.exp (-Real.pi * u * t) : ℂ) := by
  -- Unfold `Φ₅'` and simplify the modular part, `((tI)^10)`, and the kernel.
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have htI0 : ((t : ℂ) * Complex.I) ≠ 0 := mul_ne_zero ht0 Complex.I_ne_zero
  have hdiv : (-1 : ℂ) / ((t : ℂ) * Complex.I) = (iOverT t ht : ℂ) := by
    -- Multiply by `(tI)` and simplify.
    have h' : (-1 : ℂ) = ((iOverT t ht : ℂ) * ((t : ℂ) * Complex.I)) := by
      -- `iOverT t = it (1/t)`, hence `(iOverT t : ℂ) = I * (1/t)`.
      simp [Dim24.iOverT, Dim24.it, div_eq_mul_inv, mul_left_comm, mul_comm, ht0]
    exact (div_eq_iff htI0).2 h'
  have hvarphi : varphi' ((-1 : ℂ) / ((t : ℂ) * Complex.I)) = varphi (iOverT t ht) := by
    rw [hdiv]
    exact varphi'_coe_upperHalfPlane (z := iOverT t ht)
  have hpow : ((t : ℂ) * Complex.I) ^ (10 : ℕ) = -((t : ℂ) ^ (10 : ℕ)) := by
    -- `((tI)^10) = t^10 * I^10 = -t^10`.
    have hI10 : (Complex.I : ℂ) ^ (10 : ℕ) = (-1 : ℂ) := by norm_num1
    calc
      ((t : ℂ) * Complex.I) ^ (10 : ℕ) = ((t : ℂ) ^ (10 : ℕ)) * (Complex.I : ℂ) ^ (10 : ℕ) := by
        simp [mul_pow]
      _ = -((t : ℂ) ^ (10 : ℕ)) := by simp [hI10]
  have hexp :
      Complex.exp (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
        (Real.exp (-Real.pi * u * t) : ℂ) := by
    have harg :
        (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) = ((-Real.pi * u * t : ℝ) : ℂ) := by
      push_cast
      ring_nf
      simp [mul_left_comm, mul_comm]
    simp_all
  -- Assemble.
  unfold RealIntegrals.ComplexIntegrands.Φ₅'
  rw [hvarphi, hpow, hexp]
  -- Normalize signs and commutativity.
  ring_nf
  /- unfold RealIntegrals.ComplexIntegrands.Φ₅'
  set z : ℂ := (t : ℂ) * Complex.I
  have hz : (-1 : ℂ) / z = (iOverT t ht : ℂ) := by
    -- `(-1)/(tI) = I/t = it(1/t)`.
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    have hI : (Complex.I : ℂ)⁻¹ = -Complex.I := by simp
    calc
      (-1 : ℂ) / z = (-1 : ℂ) * z⁻¹ := by simp [div_eq_mul_inv]
      _ = (-1 : ℂ) * ((t : ℂ)⁻¹ * (Complex.I : ℂ)⁻¹) := by
            simp [z, mul_inv_rev₀, ht', Complex.I_ne_zero, mul_assoc]
      _ = (-1 : ℂ) * ((t : ℂ)⁻¹ * (-Complex.I : ℂ)) := by simp [hI]
      _ = (Complex.I : ℂ) * (t : ℂ)⁻¹ := by ring_nf
      _ = (iOverT t ht : ℂ) := by
            -- `iOverT t` is `it (1/t)`.
            simp
                [ Dim24.iOverT
                , Dim24.it
                , one_div
                , mul_assoc
                , mul_left_comm
                , mul_comm
                , div_eq_mul_inv
                ]
  have hvarphi : varphi' ((-1 : ℂ) / z) = varphi (iOverT t ht) := by
    -- Use the defining property of `varphi'` on the upper half plane.
    simpa [hz] using! (varphi'_coe_upperHalfPlane (z := iOverT t ht))
  have hpow : z ^ (10 : ℕ) = -((t : ℂ) ^ (10 : ℕ)) := by
    -- `((tI)^10) = t^10 * I^10 = -t^10`.
    have hI10 : (Complex.I : ℂ) ^ (10 : ℕ) = (-1 : ℂ) := by norm_num1
    calc
      z ^ (10 : ℕ) = ((t : ℂ) ^ (10 : ℕ)) * (Complex.I : ℂ) ^ (10 : ℕ) := by
        simp [z, mul_pow]
      _ = -((t : ℂ) ^ (10 : ℕ)) := by simp [hI10, mul_assoc]
  have hexp :
      cexp (Real.pi * Complex.I * (u : ℂ) * z) = (Real.exp (-Real.pi * u * t) : ℂ) := by
    have h :
        (Real.pi * Complex.I * (u : ℂ) * z) = ((-Real.pi * u * t : ℝ) : ℂ) := by
      -- `i*i = -1` and the remaining casts are real.
      push_cast
      -- Normalize multiplications before simplifying `I*I`.
      ring_nf
      simp [z, Complex.I_mul_I, mul_assoc, mul_left_comm, mul_comm, add_assoc]
    calc
      cexp (Real.pi * Complex.I * (u : ℂ) * z) = cexp ((-Real.pi * u * t : ℝ) : ℂ) := by
        simpa [h]
      _ = (Real.exp (-Real.pi * u * t) : ℂ) := by
        simpa using! (Complex.ofReal_exp (-Real.pi * u * t))
  -- Put the three pieces together.
  simp [hvarphi, hpow, hexp, z, mul_assoc, mul_left_comm, mul_comm]
  -/

/-!
### Convergent-range integral identity

Goal: for `u > 4`, relate `W u` (defined from the imaginary-axis deformation) to the Laplace
integral appearing in `avaluesRemainderIntegral`.
-/

theorem W_eq_neg_integral_pow_ten_varphi (u : ℝ) (hu : 4 < u) :
    SpecialValuesDeriv.W u =
      -∫ t : ℝ in Set.Ioi (0 : ℝ),
        (if ht : 0 < t then
            (((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht)) * (Real.exp (-Real.pi * u * t) : ℂ)
          else 0) := by
  -- Abbreviate the imaginary-axis integrand.
  let Φ : ℝ → ℂ := fun t : ℝ => RealIntegrals.ComplexIntegrands.Φ₅' u ((t : ℂ) * Complex.I)
  -- Rewrite `Vseg` as a set integral on `Ioc 0 1`.
  have hVseg :
      SpecialValuesDeriv.Vseg u = ∫ t : ℝ in Set.Ioc (0 : ℝ) 1, Φ t := by
    simp [SpecialValuesDeriv.Vseg, Φ, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  -- `Φ` is integrable on the tail by the deformation theory.
  have hIntTail : IntegrableOn Φ (Set.Ioi (1 : ℝ)) volume := by
    simpa [MeasureTheory.IntegrableOn, Φ] using!
      (LaplaceZerosTail.TailDeform.integrable_imag_axis_Φ₅' (u := u) hu)
  -- `Φ` is integrable on `(0,1]` by boundedness coming from the imaginary-axis rewrite.
  have hIntSeg : IntegrableOn Φ (Set.Ioc (0 : ℝ) 1) volume := by
    -- Use a constant bound on `‖Φ t‖` for `t ∈ (0,1]`.
    have hu0 : 0 < u := lt_trans (by norm_num) hu
    rcases Dim24.VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨C0, hC0⟩
    let C : ℝ := max C0 0
    have hC0' : ∀ s : ℝ, 1 ≤ s → ‖varphi.resToImagAxis s‖ ≤ C * Real.exp (-(2 * Real.pi) * s) := by
      intro s hs
      have h := hC0 s hs
      have hexp0 : 0 ≤ Real.exp (-(2 * Real.pi) * s) := (Real.exp_pos _).le
      have hcoef : C0 * Real.exp (-(2 * Real.pi) * s) ≤ C * Real.exp (-(2 * Real.pi) * s) :=
        mul_le_mul_of_nonneg_right (le_max_left C0 0) hexp0
      exact le_trans h hcoef
    have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖Φ t‖ ≤ C := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have htin : 1 ≤ (1 / t) := by
        -- Since `0 < t ≤ 1`, we have `1 ≤ 1/t`.
        have := one_div_le_one_div_of_le ht0 ht1
        simpa using! this
      have hvarphi :
          ‖varphi (iOverT t ht0)‖ ≤ C := by
        have hres0 := hC0' (1 / t) htin
        have hres :
            ‖ResToImagAxis varphi (t⁻¹)‖ ≤ C * Real.exp (-(2 * Real.pi) * (t⁻¹)) := by
          simpa [Function.resToImagAxis, one_div] using! hres0
        have hexp_le_one : Real.exp (-(2 * Real.pi) * (t⁻¹)) ≤ 1 := by
          refine (Real.exp_le_one_iff.2 ?_)
          nlinarith [Real.two_pi_pos, (inv_pos.2 ht0)]
        have hres' : ResToImagAxis varphi (t⁻¹) = varphi (iOverT t ht0) := by
          have htinv : 0 < (t⁻¹ : ℝ) := inv_pos.2 ht0
          -- Unfold both sides and reduce to definitional equality of the evaluation point.
          simp [ResToImagAxis, Dim24.iOverT, htinv, one_div, it]
        -- Drop the exponential factor and use `C ≥ 0`.
        have hCnonneg : 0 ≤ C := by simp [C]
        have hle : C * Real.exp (-(2 * Real.pi) * (t⁻¹)) ≤ C := by
          simpa [mul_one] using! (mul_le_mul_of_nonneg_left hexp_le_one hCnonneg)
        rw [← hres']
        exact hres.trans hle
      have hpow : ‖(t : ℂ) ^ (10 : ℕ)‖ ≤ 1 := by
        have htabs : ‖(t : ℂ)‖ = |t| := by simp
        have htabs' : |t| ≤ 1 := by
          have : 0 ≤ t := le_of_lt ht0
          simpa [abs_of_nonneg this] using! ht1
        have hnorm : ‖(t : ℂ)‖ ≤ 1 := by simpa [htabs] using! htabs'
        -- Use `‖z^n‖ = ‖z‖^n` and monotonicity of `pow`.
        have : ‖(t : ℂ)‖ ^ (10 : ℕ) ≤ 1 ^ (10 : ℕ) :=
          pow_le_pow_left₀ (norm_nonneg (t : ℂ)) hnorm 10
        simpa [norm_pow] using! this.trans_eq (by simp)
      have hexp_le_one : ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ ≤ 1 := by
        have hx : Real.exp (-Real.pi * u * t) ≤ 1 := by
          refine Real.exp_le_one_iff.2 ?_
          have hpos : 0 ≤ Real.pi * u * t := by positivity
          linarith
        simpa [-Complex.ofReal_exp, Complex.norm_real, abs_of_nonneg (Real.exp_pos _).le] using! hx
      -- Use the explicit formula for `Φ` and bound each factor.
      have hΦ : Φ t =
          -(((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht0)) * (Real.exp (-Real.pi * u * t) : ℂ) := by
        simpa [Φ] using! (Φ₅'_imag_axis_eq_neg_pow_ten_varphi_iOverT (u := u) (t := t) ht0)
      calc
        ‖Φ t‖ =
            ‖(((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht0)) *
                (Real.exp (-Real.pi * u * t) : ℂ)‖ := by
          simp [hΦ]
        _ ≤ ‖(t : ℂ) ^ (10 : ℕ)‖ * ‖varphi (iOverT t ht0)‖ *
              ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ := by
          simp [mul_assoc]
        _ ≤ 1 * C * 1 := by
              have hab : ‖(t : ℂ) ^ (10 : ℕ)‖ * ‖varphi (iOverT t ht0)‖ ≤ (1 : ℝ) * C := by
                refine mul_le_mul hpow hvarphi (norm_nonneg _) (by positivity)
              have h' :
                  (‖(t : ℂ) ^ (10 : ℕ)‖ * ‖varphi (iOverT t ht0)‖) *
                      ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ ≤
                    ((1 : ℝ) * C) * (1 : ℝ) := by
                refine mul_le_mul hab hexp_le_one (norm_nonneg _) (by positivity)
              simpa [mul_assoc] using! h'
        _ = C := by ring
    refine ⟨(measurable_imag_axis_Φ₅' (u := u)).aestronglyMeasurable, ?_⟩
    -- Convert boundedness + finiteness of `(0,1]` to `HasFiniteIntegral`.
    exact HasFiniteIntegral.of_bounded hbound
  -- Split the integral over `Ioi 0` into the segment and tail.
  have hIoi_union : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    norm_num
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
    Ioc_disjoint_Ioi_same
  have hsplit :
      (∫ t : ℝ in Set.Ioi (0 : ℝ), Φ t) =
        (∫ t : ℝ in Set.Ioc (0 : ℝ) 1, Φ t) + (∫ t : ℝ in Set.Ioi (1 : ℝ), Φ t) := by
    rw [hIoi_union]
    exact
      MeasureTheory.setIntegral_union
        (μ := volume) (f := Φ) hdisj measurableSet_Ioi hIntSeg hIntTail
  have hW :
      SpecialValuesDeriv.W u = ∫ t : ℝ in Set.Ioi (0 : ℝ), Φ t := by
    simp [SpecialValuesDeriv.W, SpecialValuesDeriv.Vtail, hVseg, hsplit, Φ]
  -- Rewrite `Φ` pointwise on `t > 0` using the previous theorem.
  let F : ℝ → ℂ := fun t : ℝ =>
    if ht : 0 < t then
      (((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht)) * (Real.exp (-Real.pi * u * t) : ℂ)
    else 0
  have hΦF : (∫ t : ℝ in Set.Ioi (0 : ℝ), Φ t) = -∫ t : ℝ in Set.Ioi (0 : ℝ), F t := by
    have hcongr :
        (fun t : ℝ => Φ t) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun t : ℝ => -F t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      simp [Φ, F, ht0, Φ₅'_imag_axis_eq_neg_pow_ten_varphi_iOverT (u := u) (t := t) ht0]
    have h' :
        (∫ t : ℝ in Set.Ioi (0 : ℝ), Φ t) = ∫ t : ℝ in Set.Ioi (0 : ℝ), -F t :=
      MeasureTheory.integral_congr_ae hcongr
    calc
      (∫ t : ℝ in Set.Ioi (0 : ℝ), Φ t) = ∫ t : ℝ in Set.Ioi (0 : ℝ), -F t := h'
      _ = -∫ t : ℝ in Set.Ioi (0 : ℝ), F t := by
        simpa using!
          (MeasureTheory.integral_neg (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := F))
  -- Finish.
  simp [hW, hΦF, F]

/-- For `u > 4`, rewrite `aProfile u` as `-(I * coeffExp u)` times the Laplace integral of
`t^10 * varphi(i/t)` over `(0,∞)`. -/
public theorem aProfile_eq_neg_I_mul_coeffExp_mul_integral_pow_ten_varphi (u : ℝ) (hu : 4 < u) :
    aProfile u =
      -(Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u) *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          (if ht : 0 < t then
              (((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht)) * (Real.exp (-Real.pi * u * t) : ℂ)
            else 0)) := by
  -- Start from the factorization `aProfile u = I * (coeffExp u * W u)` and rewrite `W`.
  have hfac :
      aProfile u =
        (Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u * SpecialValuesDeriv.W u) :=
    SpecialValuesDeriv.aProfile_eq_factorization_of_lt (u := u) hu
  rw [hfac, W_eq_neg_integral_pow_ten_varphi (u := u) hu]
  ring_nf

/-!
### Split-off `pPaper` and match `avaluesRemainderIntegral` + `pTildeIntegral`
-/

/-- For `u > 4`, split the Laplace integral of `t^10 * varphi(i/t)` into `pTildeIntegral u` plus
`avaluesRemainderIntegral u`. -/
public theorem integral_pow_ten_varphi_eq_pTildeIntegral_add_avaluesRemainderIntegral
    (u : ℝ) (hu : 4 < u) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
        (if ht : 0 < t then
            (((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht)) * (Real.exp (-Real.pi * u * t) : ℂ)
          else 0)) =
      pTildeIntegral u + avaluesRemainderIntegral u := by
  -- Work with the restricted measure on `(0,∞)`.
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  -- Abbreviate the three integrands.
  let f0 : ℝ → ℂ := fun t : ℝ =>
    if ht : 0 < t then
      (((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht)) * (Real.exp (-Real.pi * u * t) : ℂ)
    else 0
  let f1 : ℝ → ℂ := fun t : ℝ => pPaper t * (Real.exp (-Real.pi * u * t) : ℂ)
  let f2 : ℝ → ℂ := avaluesRemainderIntegrand u
  -- Rewrite RHS to match `f1` and `f2`.
  rw [pTildeIntegral, if_pos hu]
  rw [avaluesRemainderIntegral_eq_integral_integrand (u := u)]
  -- Convert all set integrals to integrals w.r.t. `μ`.
  change (∫ t : ℝ, f0 t ∂μ) = (∫ t : ℝ, f1 t ∂μ) + (∫ t : ℝ, f2 t ∂μ)
  -- Integrability: `f1` is integrable for `u > 4`; `f2` is integrable for any fixed `u > 4`.
  have hf1 : Integrable f1 μ := by
    -- `pPaper` is a sum of `exp` / `t*exp` terms; each is integrable when `u > 4`.
    have hu0 : 0 < u := lt_trans (by norm_num) hu
    have hr4 : 0 < Real.pi * (u - 4) := mul_pos Real.pi_pos (sub_pos.2 hu)
    have hr2 : 0 < Real.pi * (u - 2) := mul_pos Real.pi_pos (by linarith)
    have hr0 : 0 < Real.pi * u := mul_pos Real.pi_pos hu0
    have hExp (r : ℝ) (hr : 0 < r) : Integrable (fun t : ℝ => Real.exp (-r * t)) μ := by
      have hOn : IntegrableOn (fun t : ℝ => Real.exp (-r * t)) (Set.Ioi (0 : ℝ)) volume :=
        exp_neg_integrableOn_Ioi (a := (0 : ℝ)) hr
      simpa [MeasureTheory.IntegrableOn, μ] using! hOn
    have hMulExp (r : ℝ) (hr : 0 < r) : Integrable (fun t : ℝ => t * Real.exp (-r * t)) μ := by
      have hOn :
          IntegrableOn (fun t : ℝ => t * Real.exp (-r * t)) (Set.Ioi (0 : ℝ)) volume := by
        -- `n = 1` in the shared lemma: `t^1 * exp(-r*t)` on `(0,∞)`.
        simpa [pow_one] using!
          (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ioi (n := 1) (b := r) hr)
      simpa [MeasureTheory.IntegrableOn, μ] using! hOn
    have hExp4 : Integrable (fun t : ℝ => (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) μ :=
      (Integrable.ofReal (hExp (Real.pi * (u - 4)) hr4)).congr <|
        (Filter.Eventually.of_forall fun t => by simp)
    have hExp2 : Integrable (fun t : ℝ => (Real.exp (-Real.pi * (u - 2) * t) : ℂ)) μ :=
      (Integrable.ofReal (hExp (Real.pi * (u - 2)) hr2)).congr <|
        (Filter.Eventually.of_forall fun t => by simp)
    have hExp0 : Integrable (fun t : ℝ => (Real.exp (-Real.pi * u * t) : ℂ)) μ :=
      (Integrable.ofReal (hExp (Real.pi * u) hr0)).congr <|
        (Filter.Eventually.of_forall fun t => by simp)
    have hMulExp2 :
        Integrable (fun t : ℝ => ((t * Real.exp (-Real.pi * (u - 2) * t)) : ℂ)) μ :=
      (Integrable.ofReal (hMulExp (Real.pi * (u - 2)) hr2)).congr <|
        (Filter.Eventually.of_forall fun t => by simp)
    have hMulExp0 :
        Integrable (fun t : ℝ => ((t * Real.exp (-Real.pi * u * t)) : ℂ)) μ :=
      (Integrable.ofReal (hMulExp (Real.pi * u) hr0)).congr <|
        (Filter.Eventually.of_forall fun t => by simp)
    -- Work termwise: expand `pPaper` against the kernel and prove integrability per term.
    let E : ℝ → ℂ := fun t : ℝ => (Real.exp (-Real.pi * u * t) : ℂ)
    let h1 : ℝ → ℂ := fun t : ℝ =>
      (-(864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (4 * Real.pi * t) : ℂ) * E t
    let h2 : ℝ → ℂ := fun t : ℝ =>
      ((725760 : ℂ) / (π : ℂ)) * (t : ℂ) * (Real.exp (2 * Real.pi * t) : ℂ) * E t
    let h3 : ℝ → ℂ := fun t : ℝ =>
      (-(2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (2 * Real.pi * t) : ℂ) * E t
    let h4 : ℝ → ℂ := fun t : ℝ =>
      ((113218560 : ℂ) / (π : ℂ)) * (t : ℂ) * E t
    let h5 : ℝ → ℂ := fun t : ℝ =>
      (-(223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * E t
    have hf1_decomp : (fun t : ℝ => f1 t) =ᵐ[μ] fun t : ℝ => h1 t + h2 t + h3 t + h4 t + h5 t := by
      refine Filter.Eventually.of_forall fun t => ?_
      simp
          [ f1
          , pPaper
          , E
          , h1
          , h2
          , h3
          , h4
          , h5
          , add_mul
          , mul_assoc
          , add_assoc
          , add_left_comm
          , add_comm
          ]
    have exp_shift4 (t : ℝ) :
        (Real.exp (4 * Real.pi * t) : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ) =
          (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
      have harg : 4 * Real.pi * t + (-Real.pi * u * t) = -Real.pi * (u - 4) * t := by ring
      have hreal :
          Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
            Real.exp (-Real.pi * (u - 4) * t) := by
        calc
          Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
              Real.exp (4 * Real.pi * t + (-Real.pi * u * t)) := by
                simpa using! (Real.exp_add (4 * Real.pi * t) (-Real.pi * u * t)).symm
          _ = Real.exp (-Real.pi * (u - 4) * t) := by simpa using! congrArg Real.exp harg
      simpa using! congrArg (fun x : ℝ => (x : ℂ)) hreal
    have exp_shift2 (t : ℝ) :
        (Real.exp (2 * Real.pi * t) : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ) =
          (Real.exp (-Real.pi * (u - 2) * t) : ℂ) := by
      have harg : 2 * Real.pi * t + (-Real.pi * u * t) = -Real.pi * (u - 2) * t := by ring
      have hreal :
          Real.exp (2 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
            Real.exp (-Real.pi * (u - 2) * t) := by
        calc
          Real.exp (2 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
              Real.exp (2 * Real.pi * t + (-Real.pi * u * t)) := by
                simpa using! (Real.exp_add (2 * Real.pi * t) (-Real.pi * u * t)).symm
          _ = Real.exp (-Real.pi * (u - 2) * t) := by simpa using! congrArg Real.exp harg
      simpa using! congrArg (fun x : ℝ => (x : ℂ)) hreal
    have hMulExp2' :
        Integrable (fun t : ℝ => (t : ℂ) * (Real.exp (-Real.pi * (u - 2) * t) : ℂ)) μ := by
      assumption
    have hMulExp0' :
        Integrable (fun t : ℝ => (t : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ)) μ := by
      assumption
    have h1_int : Integrable h1 μ := by
      have hEq : h1 =ᵐ[μ] fun t : ℝ =>
          (-(864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
        refine Filter.Eventually.of_forall fun t => ?_
        grind only
      exact (hExp4.const_mul (-(864 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))).congr hEq.symm
    have h2_int : Integrable h2 μ := by
      have hEq : h2 =ᵐ[μ] fun t : ℝ =>
          ((725760 : ℂ) / (π : ℂ)) * ((t : ℂ) * (Real.exp (-Real.pi * (u - 2) * t) : ℂ)) := by
        refine Filter.Eventually.of_forall fun t => ?_
        grind only
      exact (hMulExp2'.const_mul ((725760 : ℂ) / (π : ℂ))).congr hEq.symm
    have h3_int : Integrable h3 μ := by
      have hEq : h3 =ᵐ[μ] fun t : ℝ =>
          (-(2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (-Real.pi * (u - 2) * t) : ℂ) := by
        refine Filter.Eventually.of_forall fun t => ?_
        grind only
      exact (hExp2.const_mul (-(2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))).congr hEq.symm
    have h4_int : Integrable h4 μ := by
      have hEq : h4 =ᵐ[μ] fun t : ℝ =>
          ((113218560 : ℂ) / (π : ℂ)) * ((t : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ)) := by
        refine Filter.Eventually.of_forall fun t => ?_
        simp [h4, E, mul_assoc]
      exact (hMulExp0'.const_mul ((113218560 : ℂ) / (π : ℂ))).congr hEq.symm
    have h5_int : Integrable h5 μ := by
      fun_prop
    have hsum_int : Integrable (fun t : ℝ => h1 t + h2 t + h3 t + h4 t + h5 t) μ := by
      simpa [add_assoc] using! (((h1_int.add h2_int).add h3_int).add h4_int).add h5_int
    exact hsum_int.congr hf1_decomp.symm
  have hf2 : Integrable f2 μ := by
    -- `f2` is the remainder integrand; it is integrable for fixed `u > 4` by splitting at `t=1`.
    have hmeas : AEStronglyMeasurable f2 μ := by
      simpa [μ, f2] using! (aestronglyMeasurable_avaluesRemainderIntegrand (u := u))
    -- On `(0,1]`, use boundedness (finite measure).
    let s0 : Set ℝ := Set.Ioc (0 : ℝ) 1
    have hmeas0 : AEStronglyMeasurable f2 (volume.restrict s0) := by
      have hmono : (volume.restrict s0) ≤ μ := by
        -- `restrict s0 ≤ restrict (Ioi 0)`.
        have hs : s0 ⊆ Set.Ioi (0 : ℝ) := by
          intro t ht
          exact ht.1
        simpa [μ] using! (Measure.restrict_mono_set volume hs)
      exact hmeas.mono_measure hmono
    have hInt0 : HasFiniteIntegral f2 (volume.restrict s0) := by
      -- A crude uniform bound on `(0,1]`.
      rcases Dim24.VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨C0, hC0⟩
      let C : ℝ := max C0 0
      have hC0' :
          ∀ s : ℝ, 1 ≤ s → ‖varphi.resToImagAxis s‖ ≤ C * Real.exp (-(2 * Real.pi) * s) := by
        intro s hs
        have h := hC0 s hs
        have hexp0 : 0 ≤ Real.exp (-(2 * Real.pi) * s) := (Real.exp_pos _).le
        have hcoef : C0 * Real.exp (-(2 * Real.pi) * s) ≤ C * Real.exp (-(2 * Real.pi) * s) :=
          mul_le_mul_of_nonneg_right (le_max_left C0 0) hexp0
        exact le_trans h hcoef
      have hpPaper_cont : Continuous pPaper := by
        unfold pPaper
        fun_prop
      have hcont_pPaper : Continuous fun t : Set.Icc (0 : ℝ) 1 => pPaper (t : ℝ) :=
        hpPaper_cont.comp continuous_subtype_val
      rcases
          SpecialValuesDeriv.exists_bound_norm_of_continuous
            (X := Set.Icc (0 : ℝ) 1) hcont_pPaper with
        ⟨Mp, hMp⟩
      let K : ℝ := (C + Mp) + 1
      have hbound : ∀ᵐ t : ℝ ∂(volume.restrict s0), ‖f2 t‖ ≤ K := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : 0 < t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have htin : 1 ≤ (1 / t) := by
          have := one_div_le_one_div_of_le ht0 ht1
          simpa using! this
        have hvarphi :
            ‖varphi (iOverT t ht0)‖ ≤ C := by
          have hres := hC0' (1 / t) htin
          have hexp_le_one : Real.exp (-(2 * Real.pi) * (1 / t)) ≤ 1 := by
            refine (Real.exp_le_one_iff.2 ?_)
            nlinarith [Real.two_pi_pos, (one_div_pos.2 ht0)]
          have hres' : Function.resToImagAxis varphi (1 / t) = varphi (iOverT t ht0) := by
            simp [Function.resToImagAxis, ResToImagAxis, Dim24.iOverT, Dim24.it, ht0, one_div, it]
          have hCnonneg : 0 ≤ C := by simp [C]
          have hle : C * Real.exp (-(2 * Real.pi) * (1 / t)) ≤ C := by
            simpa [mul_one] using! (mul_le_mul_of_nonneg_left hexp_le_one hCnonneg)
          have : ‖varphi (iOverT t ht0)‖ ≤ C * Real.exp (-(2 * Real.pi) * (1 / t)) :=
            le_of_eq_of_le (congrArg norm (id (Eq.symm hres'))) (hC0' (1 / t) htin)
          exact le_trans this hle
        have hpPaper_le : ‖pPaper t‖ ≤ Mp := by
          simpa using! (hMp ⟨t, ⟨le_of_lt ht0, ht1⟩⟩)
        have hexp_le_one : ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ ≤ 1 := by
          have hu0 : 0 < u := lt_trans (by norm_num) hu
          have hx : Real.exp (-Real.pi * u * t) ≤ 1 := by
            refine (Real.exp_le_one_iff.2 ?_)
            have hpos : 0 ≤ Real.pi * u * t := by positivity
            linarith
          simpa [-Complex.ofReal_exp, Complex.norm_real, abs_of_nonneg (Real.exp_pos _).le] using! hx
        have hpow : ‖(t : ℂ) ^ (10 : ℕ)‖ ≤ 1 := by
          have htabs : ‖(t : ℂ)‖ = |t| := by simp
          have htabs' : |t| ≤ 1 := by
            have : 0 ≤ t := le_of_lt ht0
            simpa [abs_of_nonneg this] using! ht1
          have hnorm : ‖(t : ℂ)‖ ≤ 1 := by simpa [htabs] using! htabs'
          have : ‖(t : ℂ)‖ ^ (10 : ℕ) ≤ 1 ^ (10 : ℕ) :=
            pow_le_pow_left₀ (norm_nonneg (t : ℂ)) hnorm 10
          simpa [norm_pow] using! this.trans_eq (by simp)
        -- Bound `‖(t^10*varphi(i/t) - pPaper t) * exp(-π u t)‖`.
        have hdiff :
            ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ ≤ C + Mp := by
          calc
            ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖
                ≤ ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖ + ‖pPaper t‖ := by
                    simpa [sub_eq_add_neg] using!
                      norm_add_le ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)) (-pPaper t)
            _ ≤ ‖(t : ℂ) ^ (10 : ℕ)‖ * ‖varphi (iOverT t ht0)‖ + Mp := by
                    have hmul :
                        ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖ ≤
                          ‖(t : ℂ) ^ (10 : ℕ)‖ * ‖varphi (iOverT t ht0)‖ := by
                      simp
                    exact add_le_add hmul hpPaper_le
            _ ≤ 1 * C + Mp := by gcongr
            _ = C + Mp := by ring
        have hval :
            ‖f2 t‖ ≤ K := by
          -- On `t > 0`, `f2` is the product of the remainder term and the kernel.
          have hdef : f2 t =
              ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t) *
                (Real.exp (-Real.pi * u * t) : ℂ) := by
            simp [f2, avaluesRemainderIntegrand, avaluesRemainderIntegrandFull, ht0]
          calc
            ‖f2 t‖ = ‖((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t) *
                (Real.exp (-Real.pi * u * t) : ℂ)‖ := by simp [hdef]
            _ = ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ *
                  ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ := by simp
            _ ≤ (C + Mp) * ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ :=
                  mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
            _ ≤ (C + Mp) * 1 := by
                  have hMp_nonneg : 0 ≤ Mp := by
                    -- Any bound on a norm is nonnegative (use the point `0 ∈ [0,1]`).
                    have : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
                    have h0 := hMp ⟨0, this⟩
                    exact le_trans (norm_nonneg _) h0
                  have hCnonneg : 0 ≤ C := by simp [C]
                  have hCMp : 0 ≤ C + Mp := by nlinarith [hCnonneg, hMp_nonneg]
                  exact mul_le_mul_of_nonneg_left hexp_le_one hCMp
            _ ≤ (C + Mp) + 1 := by nlinarith [norm_nonneg ((Real.exp (-Real.pi * u * t) : ℂ))]
            _ = K := by simp [K, add_assoc]
        exact hval
      exact HasFiniteIntegral.of_bounded hbound
    have hIntSeg : IntegrableOn f2 s0 volume := ⟨hmeas0, hInt0⟩
    -- On `[1,∞)`, use the large-`t` remainder bound and exponential decay of the kernel.
    let s1 : Set ℝ := Set.Ioi (1 : ℝ)
    have hmeas1 : AEStronglyMeasurable f2 (volume.restrict s1) := by
      have hmono : (volume.restrict s1) ≤ μ := by
        have hs : s1 ⊆ Set.Ioi (0 : ℝ) := by
          intro t ht
          exact lt_trans (by norm_num : (0 : ℝ) < 1) ht
        simpa [μ] using! (Measure.restrict_mono_set volume hs)
      exact hmeas.mono_measure hmono
    rcases exists_bound_remainder_large_proof with ⟨C, hCnonneg, hC⟩
    let b : ℝ := (2 * Real.pi) + (Real.pi * u)
    have hb : 0 < b := by
      have hu0 : 0 < u := lt_trans (by norm_num) hu
      nlinarith [Real.pi_pos, hu0]
    let bound : ℝ → ℝ := fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-b * t)
    have hboundInt : IntegrableOn bound s1 volume := by
      -- Integrability on `Ioi 1` follows from integrability on `Ioi 0`.
      have hOn0 :
          IntegrableOn (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-b * t)) (Set.Ioi (0 : ℝ)) volume := by
        simpa using!
          (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ioi (n := 2) (b := b) hb)
      have hOn0' :
          IntegrableOn
            (fun t : ℝ => C * (t ^ (2 : ℕ) * Real.exp (-b * t)))
            (Set.Ioi (0 : ℝ)) volume := by
        -- Convert to an `Integrable` statement and multiply by the constant.
        have h0 :
            Integrable (fun t : ℝ => t ^ (2 : ℕ) * Real.exp (-b * t))
              (volume.restrict (Set.Ioi (0 : ℝ))) := by
          simpa [MeasureTheory.IntegrableOn] using! hOn0
        have h0C :
            Integrable (fun t : ℝ => C * (t ^ (2 : ℕ) * Real.exp (-b * t)))
              (volume.restrict (Set.Ioi (0 : ℝ))) :=
          h0.const_mul C
        simpa [MeasureTheory.IntegrableOn, mul_assoc] using! h0C
      have hOn1 :
          IntegrableOn (fun t : ℝ => C * (t ^ (2 : ℕ) * Real.exp (-b * t))) s1 volume :=
        hOn0'.mono_set (by
          intro t ht
          exact lt_trans (by norm_num : (0 : ℝ) < 1) ht)
      simpa [bound, mul_assoc] using! hOn1
    have hInt1 : HasFiniteIntegral f2 (volume.restrict s1) := by
      -- Show `‖f2 t‖ ≤ bound t` a.e. and dominate.
      have hbound_ae : ∀ᵐ t : ℝ ∂(volume.restrict s1), ‖f2 t‖ ≤ bound t := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht1 : 1 ≤ t := le_of_lt ht
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht1
        have hrem : ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ ≤
              C * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := hC t ht1 ht0
        have hExp_norm : ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ = Real.exp (-Real.pi * u * t) := by
          simp [-Complex.ofReal_exp, Complex.norm_real, abs_of_nonneg (Real.exp_pos _).le]
        have hdef : f2 t =
            ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t) *
              (Real.exp (-Real.pi * u * t) : ℂ) := by
          simp [f2, avaluesRemainderIntegrand, avaluesRemainderIntegrandFull, ht0]
        have hExpProd :
            Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * u * t) = Real.exp (-b * t) := by
          have : (-(2 * Real.pi) * t) + (-Real.pi * u * t) = -b * t := by
            simp [b]
            ring_nf
          calc
            Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * u * t) =
                Real.exp ((-(2 * Real.pi) * t) + (-Real.pi * u * t)) := by
                  simp [Real.exp_add]
            _ = Real.exp (-b * t) := by rw [this]
        calc
          ‖f2 t‖ =
              ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ *
                Real.exp (-Real.pi * u * t) := by
                  have :
                      ‖f2 t‖ =
                        ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ *
                          ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ := by
                    simp [hdef, -Complex.ofReal_exp]
                  simpa [hExp_norm, -Complex.ofReal_exp] using! this
          _ ≤ (C * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) *
                Real.exp (-Real.pi * u * t) := by
                  -- Apply the remainder bound and rewrite the exp norm.
                  exact mul_le_mul_of_nonneg_right hrem (Real.exp_pos _).le
          _ = bound t := by
                  unfold bound
                  calc
                    (C * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) *
                          Real.exp (-Real.pi * u * t) =
                        C * (t ^ (2 : ℕ)) *
                          (Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * u * t)) := by
                          simp [mul_assoc]
                    _ = C * (t ^ (2 : ℕ)) * Real.exp (-b * t) := by
                          simpa [mul_assoc] using!
                            congrArg (fun z : ℝ => C * (t ^ (2 : ℕ)) * z) hExpProd
      -- Turn the integrable bound into `HasFiniteIntegral` domination.
      have hboundInt' : HasFiniteIntegral bound (volume.restrict s1) := by
        have hInt : Integrable bound (volume.restrict s1) := by
          simpa [MeasureTheory.IntegrableOn] using! hboundInt
        exact hInt.hasFiniteIntegral
      exact hboundInt'.mono' hbound_ae
    have hIntTail : IntegrableOn f2 s1 volume := ⟨hmeas1, hInt1⟩
    have hunion : s0 ∪ s1 = Set.Ioi (0 : ℝ) := by
      ext t
      constructor
      · intro ht
        rcases ht with ht | ht
        · exact ht.1
        · exact lt_trans (by norm_num : (0 : ℝ) < 1) ht
      · intro ht
        by_cases ht1 : t ≤ 1
        · exact Or.inl ⟨ht, ht1⟩
        · exact Or.inr (lt_of_not_ge ht1)
    -- Combine the two integrable pieces.
    have hOn : IntegrableOn f2 (s0 ∪ s1) volume := hIntSeg.union hIntTail
    simpa [hunion, MeasureTheory.IntegrableOn, μ] using! hOn
  -- Pointwise splitting on `(0,∞)` (i.e. `μ`-a.e.).
  have hEq : f0 =ᵐ[μ] fun t : ℝ => f1 t + f2 t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    -- On `t > 0`, `f2` is the remainder and `f0 = f1 + f2` by algebra.
    simp
        [ f0
        , f1
        , f2
        , avaluesRemainderIntegrand
        , avaluesRemainderIntegrandFull
        , ht0
        , sub_eq_add_neg
        , add_mul
        , add_left_comm
        , add_comm
        ]
  -- Integrate and split using linearity.
  calc
    (∫ t : ℝ, f0 t ∂μ) = ∫ t : ℝ, (f1 t + f2 t) ∂μ := by
      simpa using! (MeasureTheory.integral_congr_ae hEq)
    _ = (∫ t : ℝ, f1 t ∂μ) + (∫ t : ℝ, f2 t ∂μ) := by
      simpa using! (MeasureTheory.integral_add hf1 hf2)

end SpecialValuesDerivTwoLaurent

end
end SpherePacking.Dim24
