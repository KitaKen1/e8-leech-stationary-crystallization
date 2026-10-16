-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.Values
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivDefs
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.ModularForms.FG.AsymptoticsTools


/-!
# Derivative at `u = 4`

This file computes the derivative of `aProfile` at `u = 4`. A key analytic input is that the tail
remainder term `tailRem u` stays bounded as `u → 4⁺`, proved by dominating `tailRemIntegrand` on
the imaginary axis.

## Main statement
* `SpecialValuesDeriv.aProfile_hasDerivAt_four`
-/


open scoped Real
open scoped Topology
open Filter Complex MeasureTheory Set

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDeriv

open scoped Real

lemma continuousAt_Vseg (u0 : ℝ) : ContinuousAt Vseg u0 := by
  -- `Vseg` is a constant multiple of `I₅'`, hence continuous.
  have hI5 :
      ∀ u : ℝ, RealIntegrals.I₅' u = (-2 : ℂ) * (Complex.I : ℂ) * Vseg u := by
    intro u
    -- Expand `I₅'` and rewrite `z₅' t = i t` on `[0,1]`.
    have hparam :
        (∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) *
                RealIntegrals.ComplexIntegrands.Φ₅' u (MagicFunction.Parametrisations.z₅' t)) =
            ∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) * RealIntegrals.ComplexIntegrands.Φ₅' u ((t : ℂ) * Complex.I) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have h01 : (0 : ℝ) ≤ 1 := by norm_num
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le h01] using! ht
      simp [MagicFunction.Parametrisations.z₅'_eq_of_mem (t := t) ht', mul_comm]
    have hmain :
        ∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ u t =
            (Complex.I : ℂ) * Vseg u := by
      have :
          (∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ u t) =
              ∫ t in (0 : ℝ)..1,
                (Complex.I : ℂ) * RealIntegrals.ComplexIntegrands.Φ₅' u ((t : ℂ) * Complex.I) := by
        simp [RealIntegrals.RealIntegrands.Φ₅, hparam]
      simpa [Vseg, intervalIntegral.integral_const_mul, mul_assoc] using! this
    simp [RealIntegrals.I₅', hmain, mul_assoc]
  set c : ℂ := ((-2 : ℂ) * (Complex.I : ℂ))⁻¹
  have hVsegEq : Vseg = fun u : ℝ => c * RealIntegrals.I₅' u := by
    funext u
    have hci : ((-2 : ℂ) * (Complex.I : ℂ)) ≠ 0 := by simp
    have hI5u : RealIntegrals.I₅' u = (-2 : ℂ) * (Complex.I : ℂ) * Vseg u := hI5 u
    exact (eq_inv_mul_iff_mul_eq₀ hci).mpr (id (Eq.symm hI5u))
  have hI5cont : ContinuousAt (fun u : ℝ => RealIntegrals.I₅' u) u0 := by
    have hcont : Continuous (fun u : ℝ => RealIntegrals.I₅' u) :=
      Schwartz.I5Smooth.contDiff_I₅'.continuous
    exact hcont.continuousAt
  simpa [hVsegEq] using!
    (show ContinuousAt ((fun _ : ℝ => c) * RealIntegrals.I₅') u0 from
      continuousAt_const.mul hI5cont)

lemma tendsto_mul_Vseg_nhdsGT_four :
    Tendsto (fun u : ℝ => ((u - 4 : ℝ) : ℂ) * Vseg u) (𝓝[>] (4 : ℝ)) (𝓝 (0 : ℂ)) := by
  -- Boundedness from continuity + `u-4 → 0`.
  have hVsegCont : ContinuousAt Vseg (4 : ℝ) := continuousAt_Vseg (u0 := (4 : ℝ))
  have hVsegT :
      Tendsto Vseg (𝓝[>] (4 : ℝ)) (𝓝 (Vseg (4 : ℝ))) :=
    hVsegCont.tendsto.mono_left nhdsWithin_le_nhds
  have hBound :
      ∀ᶠ u : ℝ in 𝓝[>] (4 : ℝ), ‖Vseg u‖ ≤ ‖Vseg (4 : ℝ)‖ + 1 := by
    have hball := (hVsegT (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1)))
    filter_upwards [hball] with u hu
    have : ‖Vseg u - Vseg (4 : ℝ)‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using! hu
    have htri : ‖Vseg u‖ ≤ ‖Vseg u - Vseg (4 : ℝ)‖ + ‖Vseg (4 : ℝ)‖ := by
      simpa [sub_add_cancel] using! (norm_add_le (Vseg u - Vseg (4 : ℝ)) (Vseg (4 : ℝ)))
    have : ‖Vseg u‖ ≤ ‖Vseg (4 : ℝ)‖ + 1 := by linarith [htri, (le_of_lt this)]
    exact this
  refine
    (squeeze_zero_norm'
      (f := fun u : ℝ => ((u - 4 : ℝ) : ℂ) * Vseg u)
      (a := fun u : ℝ => |u - 4| * (‖Vseg (4 : ℝ)‖ + 1)) ?_ ?_)
  · filter_upwards [hBound] with u hu
    calc
      ‖((u - 4 : ℝ) : ℂ) * Vseg u‖ = ‖((u - 4 : ℝ) : ℂ)‖ * ‖Vseg u‖ := by
        simp
      _ ≤ ‖((u - 4 : ℝ) : ℂ)‖ * (‖Vseg (4 : ℝ)‖ + 1) := by gcongr
      _ = |u - 4| * (‖Vseg (4 : ℝ)‖ + 1) := by
        have : ‖((u - 4 : ℝ) : ℂ)‖ = |u - 4| := by
          simpa using! (Complex.norm_real (u - 4))
        rw [this]
  · have hsub0 : Tendsto (fun u : ℝ => |u - 4|) (𝓝[>] (4 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hsub0' : Tendsto (fun u : ℝ => u - 4) (𝓝[>] (4 : ℝ)) (𝓝 (0 : ℝ)) := by
        have hcont : ContinuousAt (fun u : ℝ => u - 4) (4 : ℝ) := by fun_prop
        exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using! hcont.tendsto)
      simpa [Real.norm_eq_abs] using! hsub0'.abs
    simpa [mul_assoc] using! (hsub0.mul_const (‖Vseg (4 : ℝ)‖ + 1))


open UpperHalfPlane

lemma exists_bound_norm_varphi₁_mul_q_resToImagAxis_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖(fun z : ℍ => Dim24.varphi₁ z * q (z : ℂ)).resToImagAxis t‖ ≤ C := by
  set f : ℍ → ℂ := fun z : ℍ => Dim24.varphi₁ z * q (z : ℂ)
  set l : ℂ := (725760 : ℂ) * Complex.I / (π : ℂ)
  have hf : Tendsto f UpperHalfPlane.atImInfty (nhds l) := by
    simpa [f, l, q] using! (SpecialValuesVarphi₁Limits.tendsto_varphi₁_mul_q)
  have hfAxis : Tendsto f.resToImagAxis atTop (nhds l) :=
    Function.tendsto_resToImagAxis_atImInfty (F := f) (l := l) hf
  have hEv :
      ∀ᶠ t : ℝ in atTop, ‖f.resToImagAxis t - l‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      hfAxis.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
  rcases (eventually_atTop.1 hEv) with ⟨A0, hA0⟩
  let A : ℝ := max A0 1
  have hA1 : 1 ≤ A := le_max_right _ _
  -- Bound on the compact interval `t ∈ [1,A]`.
  have hcont_f : Continuous f := by
    -- `q` is continuous and `varphi₁` is continuous on `ℍ`.
    simpa [f] using! (SpecialValuesAux.continuous_varphi₁.mul continuous_qH)
  have hcont_comp : Continuous fun x : Set.Icc (1 : ℝ) A => f.resToImagAxis (x : ℝ) := by
    have hcont_on : ContinuousOn f.resToImagAxis (Set.Icc (1 : ℝ) A) :=
      (Function.continuousOn_resToImagAxis_Ici_one_of (F := f) hcont_f).mono fun _ ht => ht.1
    simpa [continuousOn_iff_continuous_restrict] using! hcont_on
  rcases exists_bound_norm_of_continuous (X := Set.Icc (1 : ℝ) A) hcont_comp with ⟨C0, hC0⟩
  refine ⟨max C0 (‖l‖ + 1), ?_⟩
  intro t ht1
  rcases le_total t A with htA | hAt
  · -- `t ∈ [1,A]`
    have htIcc : t ∈ Set.Icc (1 : ℝ) A := ⟨ht1, htA⟩
    have hbound : ‖f.resToImagAxis t‖ ≤ C0 := by
      simpa using! hC0 ⟨t, htIcc⟩
    exact le_trans hbound (le_max_left _ _)
  · -- `A ≤ t`, use the tail bound from the `tendsto`.
    have hA0' : A0 ≤ t := le_trans (le_max_left _ _) hAt
    have hball : ‖f.resToImagAxis t - l‖ < 1 := hA0 t hA0'
    have htri : ‖f.resToImagAxis t‖ ≤ ‖f.resToImagAxis t - l‖ + ‖l‖ := by
      simpa [sub_eq_add_neg, add_assoc] using!
        (norm_add_le (f.resToImagAxis t - l) l)
    have hlt : ‖f.resToImagAxis t‖ < (‖l‖ + 1) := by
      linarith
    have hle : ‖f.resToImagAxis t‖ ≤ ‖l‖ + 1 := le_of_lt hlt
    exact le_trans hle (le_max_right _ _)

lemma exists_bound_norm_varphi₂Residual_resToImagAxis_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖(varphi₂Residual).resToImagAxis t‖ ≤ C := by
  set l : ℂ := (2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))
  have hf : Tendsto (varphi₂Residual) UpperHalfPlane.atImInfty (nhds l) := by
    -- This is exactly the `q`-expansion limit for the residual.
    simpa [varphi₂Residual, c864, q, l, div_eq_mul_inv] using!
      (SpecialValuesVarphi₂Limits.tendsto_varphi₂_mul_q_sq_sub_const_div_q)
  have hfAxis : Tendsto (varphi₂Residual).resToImagAxis atTop (nhds l) :=
    Function.tendsto_resToImagAxis_atImInfty (F := varphi₂Residual) (l := l) hf
  have hEv :
      ∀ᶠ t : ℝ in atTop, ‖(varphi₂Residual).resToImagAxis t - l‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      hfAxis.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
  rcases (eventually_atTop.1 hEv) with ⟨A0, hA0⟩
  let A : ℝ := max A0 1
  have hA1 : 1 ≤ A := le_max_right _ _
  -- Bound on the compact interval `t ∈ [1,A]`.
  have hcont_comp :
      Continuous fun x : Set.Icc (1 : ℝ) A => (varphi₂Residual).resToImagAxis (x : ℝ) := by
    have hcont_on : ContinuousOn (varphi₂Residual).resToImagAxis (Set.Icc (1 : ℝ) A) :=
      (Function.continuousOn_resToImagAxis_Ici_one_of (F := varphi₂Residual)
          continuous_varphi₂Residual).mono fun _ ht => ht.1
    simpa [continuousOn_iff_continuous_restrict] using! hcont_on
  rcases exists_bound_norm_of_continuous (X := Set.Icc (1 : ℝ) A) hcont_comp with ⟨C0, hC0⟩
  refine ⟨max C0 (‖l‖ + 1), ?_⟩
  intro t ht1
  rcases le_total t A with htA | hAt
  · have htIcc : t ∈ Set.Icc (1 : ℝ) A := ⟨ht1, htA⟩
    have hbound : ‖(varphi₂Residual).resToImagAxis t‖ ≤ C0 := by
      simpa using! hC0 ⟨t, htIcc⟩
    exact le_trans hbound (le_max_left _ _)
  · have hA0' : A0 ≤ t := le_trans (le_max_left _ _) hAt
    have hball : ‖(varphi₂Residual).resToImagAxis t - l‖ < 1 := hA0 t hA0'
    have htri :
        ‖(varphi₂Residual).resToImagAxis t‖ ≤
          ‖(varphi₂Residual).resToImagAxis t - l‖ + ‖l‖ := by
      simpa [sub_eq_add_neg, add_assoc] using!
        (norm_add_le ((varphi₂Residual).resToImagAxis t - l) l)
    have hlt : ‖(varphi₂Residual).resToImagAxis t‖ < (‖l‖ + 1) := by
      have : ‖(varphi₂Residual).resToImagAxis t - l‖ + ‖l‖ < 1 + ‖l‖ := by linarith
      have : ‖(varphi₂Residual).resToImagAxis t - l‖ + ‖l‖ < ‖l‖ + 1 := by
        simpa [add_comm, add_left_comm, add_assoc] using! this
      exact lt_of_le_of_lt htri this
    have hle : ‖(varphi₂Residual).resToImagAxis t‖ ≤ ‖l‖ + 1 := le_of_lt hlt
    exact le_trans hle (le_max_right _ _)

def tailRemBound (Cφ C1 C2 : ℝ) : ℝ → ℝ := fun t : ℝ =>
  (Cφ * (t ^ (2 : ℕ)) * Real.exp (-(6 * Real.pi) * t)) +
    (C1 * (t ^ (1 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) +
      (C2 * Real.exp (-(2 * Real.pi) * t))

lemma norm_inv_q_imag_axis (t : ℝ) :
    ‖(q ((t : ℂ) * Complex.I))⁻¹‖ = Real.exp (2 * Real.pi * t) := by
  have hq : q ((t : ℂ) * Complex.I) = (Real.exp (-2 * Real.pi * t) : ℂ) :=
    q_imag_axis (t := t)
  have hq' : q ((t : ℂ) * Complex.I) = Complex.exp (-2 * Real.pi * t) := by
    simp_all
  calc
    ‖(q ((t : ℂ) * Complex.I))⁻¹‖ = ‖(Complex.exp (-2 * Real.pi * t))⁻¹‖ := by
      simp [hq']
    _ = ‖Complex.exp (2 * Real.pi * t)‖ := by
      -- `(exp (-x))⁻¹ = exp x`.
      simp [Complex.exp_neg]
    _ = Real.exp (2 * Real.pi * t) := by
      simpa using! (Complex.norm_exp_ofReal (2 * Real.pi * t))

lemma norm_tailRemIntegrand_le_tailRemBound
    {Cφ C1 C2 u t : ℝ} (hCφ0 : 0 ≤ Cφ) (hC10 : 0 ≤ C1) (hC20 : 0 ≤ C2)
    (hCφ : ∀ s : ℝ, 1 ≤ s → ‖varphi.resToImagAxis s‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * s))
    (hC1 : ∀ s : ℝ, 1 ≤ s → ‖(fun z : ℍ => Dim24.varphi₁ z * q (z : ℂ)).resToImagAxis s‖ ≤ C1)
    (hC2 : ∀ s : ℝ, 1 ≤ s → ‖(varphi₂Residual).resToImagAxis s‖ ≤ C2)
    (hu : 4 < u) (ht : 1 < t) :
    ‖tailRemIntegrand u t‖ ≤ tailRemBound Cφ C1 C2 t := by
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  have ht1 : 1 ≤ t := le_of_lt ht
  set z : ℂ := (Complex.I : ℂ) * (t : ℂ)
  have hzIm : 0 < z.im := by simpa [z, Complex.mul_im] using! ht0
  set zH : ℍ := ⟨z, hzIm⟩
  set E : ℂ := (Real.exp (-Real.pi * u * t) : ℂ)
  have hEnorm : ‖E‖ = Real.exp (-Real.pi * u * t) := by
    -- `simp [E]` rewrites `(Real.exp _ : ℂ)` as `Complex.exp _`.
    simpa [E] using! (Complex.norm_exp_ofReal (-Real.pi * u * t))
  have hzNorm : ‖z‖ = t := by
    have : ‖z‖ = |t| := by
      simp [z, Complex.norm_I]
    simpa [abs_of_pos ht0] using! this
  have hzPow2 : ‖z ^ (2 : ℕ)‖ = t ^ (2 : ℕ) := by
    simp [norm_pow, hzNorm]
  have hvarphi :
      ‖varphi zH‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) := by
    -- Rewrite the restriction bound `hCφ` onto the explicit axis point `zH`.
    simpa [Function.resToImagAxis, ResToImagAxis, ht0, z, zH, mul_comm] using! hCφ t ht1
  have hphi1q : ‖Dim24.varphi₁ zH * q z‖ ≤ C1 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0, z, zH] using! hC1 t ht1
  have hres : ‖varphi₂Residual zH‖ ≤ C2 := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0, z, zH, mul_comm] using! hC2 t ht1
  have hqInv : ‖(q z)⁻¹‖ = Real.exp (2 * Real.pi * t) := by
    -- Reduce to the explicit formula for `q` on the imaginary axis.
    simpa [z, mul_comm] using! norm_inv_q_imag_axis (t := t)
  have hE_le : Real.exp (-Real.pi * u * t) ≤ Real.exp (-(4 * Real.pi) * t) := by
    have hu4 : (4 : ℝ) ≤ u := le_of_lt hu
    have ht0le : 0 ≤ t := le_of_lt ht0
    have hmul : (4 : ℝ) * t ≤ u * t := mul_le_mul_of_nonneg_right hu4 ht0le
    have hmulπ : Real.pi * ((4 : ℝ) * t) ≤ Real.pi * (u * t) :=
      mul_le_mul_of_nonneg_left hmul (le_of_lt Real.pi_pos)
    have hneg : -(Real.pi * (u * t)) ≤ -(Real.pi * ((4 : ℝ) * t)) := neg_le_neg hmulπ
    have harg : -Real.pi * u * t ≤ -(4 * Real.pi) * t := by
      -- Normalize associativity/commutativity.
      simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using! hneg
    exact (Real.exp_le_exp.2 harg)
  have hexp24 :
      Real.exp (2 * Real.pi * t) * Real.exp (-(4 * Real.pi) * t) =
        Real.exp (-(2 * Real.pi) * t) := by
    calc
      Real.exp (2 * Real.pi * t) * Real.exp (-(4 * Real.pi) * t) =
          Real.exp ((2 * Real.pi * t) + (-(4 * Real.pi) * t)) := by
            simpa using! (Real.exp_add (2 * Real.pi * t) (-(4 * Real.pi) * t)).symm
      _ = Real.exp (-(2 * Real.pi) * t) := by ring_nf
  have hexp26 :
      Real.exp (-(2 * Real.pi) * t) * Real.exp (-(4 * Real.pi) * t) =
        Real.exp (-(6 * Real.pi) * t) := by
    calc
      Real.exp (-(2 * Real.pi) * t) * Real.exp (-(4 * Real.pi) * t) =
          Real.exp ((-(2 * Real.pi) * t) + (-(4 * Real.pi) * t)) := by
            simpa using! (Real.exp_add (-(2 * Real.pi) * t) (-(4 * Real.pi) * t)).symm
      _ = Real.exp (-(6 * Real.pi) * t) := by ring_nf
  have hA :
      ‖(z ^ (2 : ℕ) * varphi zH) * E‖ ≤ Cφ * (t ^ (2 : ℕ)) * Real.exp (-(6 * Real.pi) * t) := by
    have hcoef0 : 0 ≤ Cφ * Real.exp (-(2 * Real.pi) * t) :=
      mul_nonneg hCφ0 (le_of_lt (Real.exp_pos _))
    have hcoef0' : 0 ≤ (t ^ (2 : ℕ)) := pow_nonneg (le_of_lt ht0) _
    have hcoef : 0 ≤ (t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) :=
      mul_nonneg hcoef0' hcoef0
    calc
      ‖(z ^ (2 : ℕ) * varphi zH) * E‖ =
          ‖z ^ (2 : ℕ)‖ * ‖varphi zH‖ * ‖E‖ := by
            simp [mul_assoc]
      _ ≤ (t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) * (Real.exp (-Real.pi * u * t)) := by
            have :
                ‖z ^ (2 : ℕ)‖ * ‖varphi zH‖ ≤
                  (t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) := by
              -- Apply bounds for `‖z^2‖` and `‖varphi‖`.
              have hzle : ‖z ^ (2 : ℕ)‖ ≤ t ^ (2 : ℕ) := by simp [hzPow2]
              have hφle : ‖varphi zH‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) := hvarphi
              -- Multiply inequalities in a nonnegative context.
              exact mul_le_mul hzle hφle (norm_nonneg _) hcoef0'
            -- Multiply by `‖E‖`.
            have hE0 : 0 ≤ ‖E‖ := norm_nonneg _
            have := mul_le_mul_of_nonneg_right this hE0
            simpa [hzPow2, hEnorm, mul_assoc, mul_left_comm, mul_comm] using! this
      _ ≤
          (t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) *
            Real.exp (-(4 * Real.pi) * t) := by
            -- Replace `exp(-π*u*t)` by `exp(-4π*t)`.
            refine mul_le_mul_of_nonneg_left ?_ hcoef
            exact hE_le
      _ = Cφ * (t ^ (2 : ℕ)) * Real.exp (-(6 * Real.pi) * t) := by
            -- Reassociate and use `exp` addition.
            grind only
  have hB :
      ‖(z * Dim24.varphi₁ zH) * E‖ ≤ C1 * (t ^ (1 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
    have hphi1 :
        ‖Dim24.varphi₁ zH‖ ≤ C1 * Real.exp (2 * Real.pi * t) := by
      have hzq : q z ≠ 0 := by
        -- `q` is `SpecialValuesVarphi₁Limits.q`.
        simpa [q] using! (SpecialValuesVarphi₁Limits.q_ne_zero z)
      have hrew : Dim24.varphi₁ zH = (Dim24.varphi₁ zH * q z) * (q z)⁻¹ := by
        -- `(a*q)*q⁻¹ = a` since `q ≠ 0`.
        exact Eq.symm (mul_inv_cancel_right₀ hzq (varphi₁ zH))
      calc
        ‖Dim24.varphi₁ zH‖ = ‖(Dim24.varphi₁ zH * q z) * (q z)⁻¹‖ := by
          simpa using! congrArg norm hrew
        _ = ‖Dim24.varphi₁ zH * q z‖ * ‖(q z)⁻¹‖ := by simp
        _ ≤ C1 * Real.exp (2 * Real.pi * t) := by
          have h := mul_le_mul_of_nonneg_right hphi1q (norm_nonneg ((q z)⁻¹))
          simpa [hqInv, mul_assoc] using! h
    have hcoef0 : 0 ≤ C1 * Real.exp (2 * Real.pi * t) :=
      mul_nonneg hC10 (le_of_lt (Real.exp_pos _))
    calc
      ‖(z * Dim24.varphi₁ zH) * E‖ = ‖z‖ * ‖Dim24.varphi₁ zH‖ * ‖E‖ := by
        simp [mul_assoc]
      _ ≤ t * (C1 * Real.exp (2 * Real.pi * t)) * (Real.exp (-Real.pi * u * t)) := by
        have hzle : ‖z‖ ≤ t := by simp [hzNorm]
        have hφle : ‖Dim24.varphi₁ zH‖ ≤ C1 * Real.exp (2 * Real.pi * t) := hphi1
        have := mul_le_mul hzle hφle (norm_nonneg _) (le_of_lt ht0)
        have hE0 : 0 ≤ ‖E‖ := norm_nonneg _
        have := mul_le_mul_of_nonneg_right this hE0
        simpa [hzNorm, hEnorm, mul_assoc, mul_left_comm, mul_comm] using! this
      _ ≤ t * (C1 * Real.exp (2 * Real.pi * t)) * (Real.exp (-(4 * Real.pi) * t)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (le_of_lt ht0) hcoef0)
        exact hE_le
      _ = C1 * (t ^ (1 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
        grind only
  have hC :
      ‖(varphi₂Residual zH / q z) * E‖ ≤ C2 * Real.exp (-(2 * Real.pi) * t) := by
    have hcoef0 : 0 ≤ C2 * Real.exp (2 * Real.pi * t) :=
      mul_nonneg hC20 (le_of_lt (Real.exp_pos _))
    calc
      ‖(varphi₂Residual zH / q z) * E‖ =
          ‖varphi₂Residual zH‖ * ‖(q z)⁻¹‖ * ‖E‖ := by
            simp [div_eq_mul_inv, mul_assoc]
      _ ≤ C2 * Real.exp (2 * Real.pi * t) * (Real.exp (-Real.pi * u * t)) := by
        have h1 :
            ‖varphi₂Residual zH‖ * ‖(q z)⁻¹‖ ≤ C2 * Real.exp (2 * Real.pi * t) := by
          have hqinv' : ‖(q z)⁻¹‖ = Real.exp (2 * Real.pi * t) := hqInv
          have := mul_le_mul_of_nonneg_right hres (norm_nonneg ((q z)⁻¹))
          simpa [hqinv', mul_assoc] using! this
        have hE0 : 0 ≤ ‖E‖ := norm_nonneg _
        have := mul_le_mul_of_nonneg_right h1 hE0
        simpa [hEnorm, mul_assoc, mul_left_comm, mul_comm] using! this
      _ ≤ C2 * Real.exp (2 * Real.pi * t) * Real.exp (-(4 * Real.pi) * t) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef0
        exact hE_le
      _ = C2 * Real.exp (-(2 * Real.pi) * t) := by
        have hexp :
            Real.exp (2 * Real.pi * t) * Real.exp (-(4 * Real.pi) * t) =
              Real.exp (-(2 * Real.pi) * t) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using! hexp24
        -- Avoid simp's cancellation rewrites; reassociate and rewrite the exponential product.
        calc
          C2 * Real.exp (2 * Real.pi * t) * Real.exp (-(4 * Real.pi) * t) =
              C2 * (Real.exp (2 * Real.pi * t) * Real.exp (-(4 * Real.pi) * t)) := by
                simp [mul_assoc]
          _ = C2 * Real.exp (-(2 * Real.pi) * t) := by
                rw [hexp]
  -- Triangle inequality after distributing `E` over the sum.
  set A : ℂ := (z ^ (2 : ℕ) * varphi zH) * E
  set B : ℂ := (z * Dim24.varphi₁ zH) * E
  set C : ℂ := (varphi₂Residual zH / q z) * E
  have htri : ‖tailRemIntegrand u t‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
    have hTail' :
        tailRemIntegrand u t = A + B + C := by
      have hform :
          tailRemIntegrand u t =
            ((z ^ (2 : ℕ)) * varphi zH + z * varphi₁ zH + varphi₂Residual zH / q z) * E := by
        simpa [z, zH, E, mul_assoc, mul_left_comm, mul_comm] using!
          (tailRemIntegrand_eq_of_pos (u := u) (t := t) ht0)
      calc
        tailRemIntegrand u t =
            ((z ^ (2 : ℕ)) * varphi zH + z * varphi₁ zH + varphi₂Residual zH / q z) * E := hform
        _ = A + B + C := by
          simp [A, B, C, add_assoc, add_mul]
    -- Reduce to `‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖`.
    rw [hTail']
    exact norm_add₃_le
  -- Substitute the bounds and match `tailRemBound`.
  refine le_trans htri ?_
  have hsum :
      ‖A‖ + ‖B‖ + ‖C‖ ≤
        (Cφ * (t ^ (2 : ℕ)) * Real.exp (-(6 * Real.pi) * t)) +
          (C1 * (t ^ (1 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) +
            (C2 * Real.exp (-(2 * Real.pi) * t)) := by
    -- `gcongr` on a 3-term sum.
    exact add_le_add_three hA hB hC
  simpa [tailRemBound] using! hsum

lemma tendsto_mul_tailRem_nhdsGT_four :
    Tendsto (fun u : ℝ => ((u - 4 : ℝ) : ℂ) * tailRem u) (𝓝[>] (4 : ℝ)) (𝓝 (0 : ℂ)) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  -- Constants bounding the modular-form factors.
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ, hCφ⟩
  rcases exists_bound_norm_varphi₁_mul_q_resToImagAxis_Ici_one with ⟨C1, hC1⟩
  rcases exists_bound_norm_varphi₂Residual_resToImagAxis_Ici_one with ⟨C2, hC2⟩
  have hb2 : 0 < (2 * Real.pi) := by positivity [Real.pi_pos]
  have hb6 : 0 < (6 * Real.pi) := by positivity [Real.pi_pos]
  -- An explicit integrable bound on `(1,∞)`.
  let bound : ℝ → ℝ := tailRemBound Cφ C1 C2
  have hCφ0 : 0 ≤ Cφ := by
    have h1 : ‖varphi.resToImagAxis (1 : ℝ)‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * (1 : ℝ)) :=
      hCφ 1 (by norm_num)
    have h0 : 0 ≤ Cφ * Real.exp (-(2 * Real.pi) * (1 : ℝ)) := le_trans (norm_nonneg _) h1
    have hpos : 0 < Real.exp (-(2 * Real.pi) * (1 : ℝ)) := Real.exp_pos _
    exact nonneg_of_mul_nonneg_left h0 hpos
  have hC10 : 0 ≤ C1 := le_trans (norm_nonneg _) (hC1 1 (by norm_num))
  have hC20 : 0 ≤ C2 := le_trans (norm_nonneg _) (hC2 1 (by norm_num))
  have hboundInt : Integrable (fun t : ℝ => bound t) μ := by
    -- Integrability on `Ici 1` (known), then restrict the measure to `Ioi 1`.
    have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ici (1 : ℝ) :=
      Ioi_subset_Ici_self
    have hμle : μ ≤ volume.restrict (Set.Ici (1 : ℝ)) := by
      -- `volume.restrict (Ioi 1) ≤ volume.restrict (Ici 1)`.
      simpa [μ] using! (Measure.restrict_mono_set volume hsub)
    have h0Ici :
        Integrable (fun t : ℝ => (t ^ (2 : ℕ)) * Real.exp (-(6 * Real.pi) * t))
          (volume.restrict (Set.Ici (1 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using!
        (ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 2) (b := (6 * Real.pi)) hb6)
    have h1Ici :
        Integrable (fun t : ℝ => (t ^ (1 : ℕ)) * Real.exp (-(2 * Real.pi) * t))
          (volume.restrict (Set.Ici (1 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using!
        (ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 1) (b := (2 * Real.pi)) hb2)
    have h2Ici :
        Integrable (fun t : ℝ => Real.exp (-(2 * Real.pi) * t))
          (volume.restrict (Set.Ici (1 : ℝ))) := by
      -- `t^0 = 1`.
      simpa [MeasureTheory.IntegrableOn, pow_zero, one_mul] using!
        (ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := (2 * Real.pi)) hb2)
    have h0 :
        Integrable (fun t : ℝ => Cφ * (t ^ (2 : ℕ)) * Real.exp (-(6 * Real.pi) * t)) μ := by
      -- Use `const_mul` and reassociate.
      have h0' :
          Integrable (fun t : ℝ => Cφ * ((t ^ (2 : ℕ)) * Real.exp (-(6 * Real.pi) * t))) μ :=
        (h0Ici.mono_measure hμle).const_mul Cφ
      simpa [mul_assoc] using! h0'
    have h1 :
        Integrable (fun t : ℝ => C1 * (t ^ (1 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) μ := by
      have h1' :
          Integrable (fun t : ℝ => C1 * ((t ^ (1 : ℕ)) * Real.exp (-(2 * Real.pi) * t))) μ :=
        (h1Ici.mono_measure hμle).const_mul C1
      simpa [mul_assoc] using! h1'
    have h2 :
        Integrable (fun t : ℝ => C2 * Real.exp (-(2 * Real.pi) * t)) μ :=
      (h2Ici.mono_measure hμle).const_mul C2
    have hsum₁ :
        Integrable
            (fun t : ℝ =>
              (Cφ * (t ^ (2 : ℕ)) * Real.exp (-(6 * Real.pi) * t)) +
                ((C1 * (t ^ (1 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) +
                  (C2 * Real.exp (-(2 * Real.pi) * t)))) μ :=
      h0.add (h1.add h2)
    have hsum₂ :
        Integrable
            (fun t : ℝ =>
              (Cφ * (t ^ (2 : ℕ)) * Real.exp (-(6 * Real.pi) * t)) +
                (C1 * (t ^ (1 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) +
                  (C2 * Real.exp (-(2 * Real.pi) * t))) μ := by
      simpa [add_assoc] using! hsum₁
    simpa [bound, tailRemBound, add_assoc] using! hsum₂
  have hBoundAE :
      ∀ᶠ u : ℝ in 𝓝[>] (4 : ℝ), ‖tailRem u‖ ≤ ∫ t : ℝ in Set.Ioi (1 : ℝ), bound t := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu4 : 4 < u := hu
    -- Dominate the integrand by `bound`, integrate, then use `‖∫ f‖ ≤ ∫ ‖f‖`.
    have hle_integrand :
        (fun t : ℝ => ‖tailRemIntegrand u t‖) ≤ᵐ[μ] fun t : ℝ => bound t := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht1 : 1 < t := ht
      exact norm_tailRemIntegrand_le_tailRemBound hCφ0 hC10 hC20 hCφ hC1 hC2 hu4 ht1
    have hIntU : Integrable (fun t : ℝ => tailRemIntegrand u t) μ := by
      simpa [μ] using! (integrable_tailRemIntegrand (u := u) hu4)
    have hnorm :
        ‖∫ t : ℝ in Set.Ioi (1 : ℝ), tailRemIntegrand u t‖ ≤
          ∫ t : ℝ in Set.Ioi (1 : ℝ), ‖tailRemIntegrand u t‖ :=
      norm_integral_le_integral_norm (tailRemIntegrand u)
    have hleInt :
        (∫ t : ℝ in Set.Ioi (1 : ℝ), ‖tailRemIntegrand u t‖) ≤
          ∫ t : ℝ in Set.Ioi (1 : ℝ), bound t := by
      -- Apply `integral_mono_of_nonneg` on the restricted measure `μ`.
      have hnonneg : 0 ≤ᵐ[μ] fun t : ℝ => ‖tailRemIntegrand u t‖ :=
        Filter.Eventually.of_forall (fun t => norm_nonneg (tailRemIntegrand u t))
      exact MeasureTheory.integral_mono_of_nonneg hnonneg hboundInt hle_integrand
    have hnorm' :
        ‖tailRem u‖ ≤ ∫ t : ℝ in Set.Ioi (1 : ℝ), ‖tailRemIntegrand u t‖ := by
      assumption
    exact le_trans hnorm' hleInt
  -- Now `|u-4| * (∫ bound)` tends to `0` and dominates the norm.
  refine
    (squeeze_zero_norm'
      (f := fun u : ℝ => ((u - 4 : ℝ) : ℂ) * tailRem u)
      (a := fun u : ℝ => |u - 4| * (∫ t : ℝ in Set.Ioi (1 : ℝ), bound t)) ?_ ?_)
  · filter_upwards [hBoundAE] with u hu
    calc
      ‖((u - 4 : ℝ) : ℂ) * tailRem u‖ = ‖((u - 4 : ℝ) : ℂ)‖ * ‖tailRem u‖ := by
        simp
      _ ≤ ‖((u - 4 : ℝ) : ℂ)‖ * (∫ t : ℝ in Set.Ioi (1 : ℝ), bound t) := by gcongr
      _ = |u - 4| * (∫ t : ℝ in Set.Ioi (1 : ℝ), bound t) := by
        have : ‖((u - 4 : ℝ) : ℂ)‖ = |u - 4| := by
          simpa using! (Complex.norm_real (u - 4))
        rw [this]
  · have hsub0 : Tendsto (fun u : ℝ => |u - 4|) (𝓝[>] (4 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hsub0' : Tendsto (fun u : ℝ => u - 4) (𝓝[>] (4 : ℝ)) (𝓝 (0 : ℝ)) := by
        have hcont : ContinuousAt (fun u : ℝ => u - 4) (4 : ℝ) := by fun_prop
        exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using! hcont.tendsto)
      simpa [Real.norm_eq_abs] using! hsub0'.abs
    simpa [mul_assoc] using! (hsub0.mul_const (∫ t : ℝ in Set.Ioi (1 : ℝ), bound t))

end SpecialValuesDeriv

lemma slope_eq_div_eventually :
    slope aProfile (4 : ℝ) =ᶠ[𝓝[>] (4 : ℝ)] fun u : ℝ => aProfile u / (u - 4) := by
  have hA4 : aProfile (4 : ℝ) = 0 := aProfile_four
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp [slope, hA4, sub_eq_add_neg, div_eq_mul_inv, mul_comm]

lemma aProfile_div_eventually_factorized :
    (fun u : ℝ => aProfile u / (u - 4)) =ᶠ[𝓝[>] (4 : ℝ)]
      fun u : ℝ =>
        (Complex.I : ℂ) *
          (SpecialValuesDeriv.coeffExp u / ((u - 4) ^ (2 : ℕ) : ℂ)) *
            (((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.W u) := by
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : 4 < u := hu
  have hfac := SpecialValuesDeriv.aProfile_eq_factorization_of_lt (u := u) hu'
  have hpi : (u - 4 : ℂ) ≠ 0 := by
    have : (u - 4 : ℝ) ≠ 0 := sub_ne_zero.2 (ne_of_gt hu')
    exact_mod_cast this
  calc
    aProfile u / (u - 4) =
        ((Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u * SpecialValuesDeriv.W u)) /
          (u - 4) := by simp [hfac]
    _ =
        (Complex.I : ℂ) *
          ((SpecialValuesDeriv.coeffExp u * SpecialValuesDeriv.W u) / (u - 4)) := by
          simp [mul_div_assoc]
    _ =
        (Complex.I : ℂ) *
          ((SpecialValuesDeriv.coeffExp u / ((u - 4) ^ (2 : ℕ) : ℂ)) *
            (((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.W u)) := by
          simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm, hpi]
    _ =
        (Complex.I : ℂ) *
          (SpecialValuesDeriv.coeffExp u / ((u - 4) ^ (2 : ℕ) : ℂ)) *
            (((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.W u) := by
          simp [mul_assoc]

lemma tendsto_mul_W_nhdsGT_four :
    Tendsto (fun u : ℝ => ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.W u) (𝓝[>] (4 : ℝ))
      (𝓝 (SpecialValuesDeriv.c864 / (π : ℂ))) := by
  have hWdecomp :
      (fun u : ℝ => ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.W u) =ᶠ[𝓝[>] (4 : ℝ)]
        fun u : ℝ =>
          ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.Vseg u +
            ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.tailRem u +
              ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.tailSing u := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : 4 < u := hu
    have htail := SpecialValuesDeriv.Vtail_eq_tailRem_add_tailSing (u := u) hu'
    simp [SpecialValuesDeriv.W, htail, mul_add, add_assoc]
  have hSing :
      Tendsto (fun u : ℝ => ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.tailSing u) (𝓝[>] (4 : ℝ))
        (𝓝 (SpecialValuesDeriv.c864 / (π : ℂ))) :=
    SpecialValuesDeriv.tendsto_mul_tailSing_nhdsGT_four
  have hVseg0 :
      Tendsto (fun u : ℝ => ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.Vseg u) (𝓝[>] (4 : ℝ))
        (𝓝 (0 : ℂ)) :=
    SpecialValuesDeriv.tendsto_mul_Vseg_nhdsGT_four
  have hRem0 :
      Tendsto (fun u : ℝ => ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.tailRem u) (𝓝[>] (4 : ℝ))
        (𝓝 (0 : ℂ)) :=
    SpecialValuesDeriv.tendsto_mul_tailRem_nhdsGT_four
  have hRHS :
      Tendsto
          (fun u : ℝ =>
            ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.Vseg u +
              ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.tailRem u +
                ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.tailSing u)
          (𝓝[>] (4 : ℝ)) (𝓝 (SpecialValuesDeriv.c864 / (π : ℂ))) := by
    simpa [add_assoc] using! (hVseg0.add (hRem0.add hSing))
  exact hRHS.congr' hWdecomp.symm

lemma neg_I_mul_pi_sq_mul_c864_div_pi :
    -((Complex.I : ℂ) * ((Real.pi : ℂ) ^ (2 : ℕ)) * (SpecialValuesDeriv.c864 / (π : ℂ))) =
      ((-864 : ℂ) * Complex.I) / (π : ℂ) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [SpecialValuesDeriv.c864, div_eq_mul_inv, mul_left_comm, mul_comm]

lemma tendsto_aProfile_div_sub_four_pre :
    Tendsto (fun u : ℝ => aProfile u / (u - 4)) (𝓝[>] (4 : ℝ))
      (𝓝 ((Complex.I : ℂ) * (-((Real.pi : ℂ) ^ (2 : ℕ))) *
        (SpecialValuesDeriv.c864 / (π : ℂ)))) := by
  -- Introduce abbreviations for the two sides.
  let f : ℝ → ℂ :=
    fun u : ℝ =>
      (Complex.I : ℂ) *
        (SpecialValuesDeriv.coeffExp u / ((u - 4) ^ (2 : ℕ) : ℂ)) *
          (((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.W u)
  let g : ℝ → ℂ := fun u : ℝ => aProfile u / (u - 4)
  have hCoeff :
      Tendsto (fun u : ℝ => SpecialValuesDeriv.coeffExp u / ((u - 4) ^ (2 : ℕ) : ℂ))
        (𝓝[>] (4 : ℝ)) (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)))) :=
    SpecialValuesDeriv.tendsto_coeffExp_div_sq_nhdsGT_four
  have hWlim :
      Tendsto (fun u : ℝ => ((u - 4 : ℝ) : ℂ) * SpecialValuesDeriv.W u) (𝓝[>] (4 : ℝ))
        (𝓝 (SpecialValuesDeriv.c864 / (π : ℂ))) :=
    tendsto_mul_W_nhdsGT_four
  have hmain :
      Tendsto f (𝓝[>] (4 : ℝ))
        (𝓝 ((Complex.I : ℂ) * (-((Real.pi : ℂ) ^ (2 : ℕ))) *
          (SpecialValuesDeriv.c864 / (π : ℂ)))) := by
    simpa [f, mul_assoc] using! (tendsto_const_nhds.mul (hCoeff.mul hWlim))
  have hfg : f =ᶠ[𝓝[>] (4 : ℝ)] g := by
    simpa [f, g] using! aProfile_div_eventually_factorized.symm
  simpa [g] using! (hmain.congr' hfg)

lemma tendsto_aProfile_div_sub_four_const :
    Tendsto (fun u : ℝ => aProfile u / (u - 4)) (𝓝[>] (4 : ℝ))
      (𝓝 (((-864 : ℂ) * Complex.I) / (π : ℂ))) := by
  have h := tendsto_aProfile_div_sub_four_pre
  have h' :
      Tendsto (fun u : ℝ => aProfile u / (u - 4)) (𝓝[>] (4 : ℝ))
        (𝓝 (-((Complex.I : ℂ) * ((Real.pi : ℂ) ^ (2 : ℕ)) *
          (SpecialValuesDeriv.c864 / (π : ℂ))))) := by
    simpa [mul_assoc] using! h
  simpa [neg_I_mul_pi_sq_mul_c864_div_pi] using! h'

lemma tendsto_slope_aProfile_four_const :
    Tendsto (slope aProfile (4 : ℝ)) (𝓝[>] (4 : ℝ)) (𝓝 (((-864 : ℂ) * Complex.I) / (π : ℂ))) :=
  (tendsto_aProfile_div_sub_four_const.congr' slope_eq_div_eventually.symm)

/-- `aProfile` has derivative `(-864) * I / π` at `u = 4`. -/
public theorem aProfile_hasDerivAt_four :
    HasDerivAt aProfile ((-864 : ℂ) * Complex.I / (π : ℂ)) (4 : ℝ) := by
  have hdiff : DifferentiableAt ℝ aProfile (4 : ℝ) :=
    differentiableAt_aProfile_of_lt (x := (4 : ℝ)) (by norm_num)
  have hderiv : HasDerivAt aProfile (deriv aProfile (4 : ℝ)) (4 : ℝ) := hdiff.hasDerivAt
  have hle : (𝓝[>] (4 : ℝ)) ≤ (𝓝[≠] (4 : ℝ)) := by
    exact nhdsGT_le_nhdsNE 4
  have hSlopeDeriv :
      Tendsto (slope aProfile (4 : ℝ)) (𝓝[>] (4 : ℝ)) (𝓝 (deriv aProfile (4 : ℝ))) :=
    (hderiv.tendsto_slope).mono_left hle
  have hEqDeriv : deriv aProfile (4 : ℝ) = ((-864 : ℂ) * Complex.I) / (π : ℂ) :=
    tendsto_nhds_unique hSlopeDeriv tendsto_slope_aProfile_four_const
  simpa [hEqDeriv] using! hderiv

end

end SpherePacking.Dim24
