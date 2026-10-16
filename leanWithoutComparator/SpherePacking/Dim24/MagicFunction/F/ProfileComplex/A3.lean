-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Init
public import SpherePacking.Dim24.MagicFunction.F.ProfileComplex.A2

/-!
# Analyticity of `aPrimeC` on the right half-plane

This file proves that the complexified profile `ProfileComplex.A.aPrimeC` is holomorphic on the
right half-plane `SpherePacking.rightHalfPlane`, by differentiating under the tail integral and
assembling the bounded pieces.
-/

namespace SpherePacking.Dim24

noncomputable section

open scoped Interval Topology UpperHalfPlane

open Complex Real MeasureTheory
open MagicFunction.Parametrisations intervalIntegral

namespace ProfileComplex

/-! ### Small real-analysis helpers -/

/-- The function `t ↦ C * exp (-b * t)` is integrable on `Set.Ici 1` when `b > 0`. -/
public lemma integrable_bound_exp (C b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => C * Real.exp (-b * t))
      ((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))) := by
  have hInt :
      IntegrableOn (fun t : ℝ => t ^ (0 : ℕ) * Real.exp (-b * t)) (Set.Ici (1 : ℝ)) volume :=
    SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := b) hb
  have :
      Integrable (fun t : ℝ => Real.exp (-b * t))
        ((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))) := by
    simpa [pow_zero, IntegrableOn] using! hInt
  simpa [mul_assoc, mul_left_comm, mul_comm] using! this.const_mul C

/-- The function `t ↦ C * (t * exp (-b * t))` is integrable on `Set.Ici 1` when `b > 0`. -/
public lemma integrable_bound_mul_exp (C b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => C * (t * Real.exp (-b * t)))
      ((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))) := by
  have hInt :
      IntegrableOn (fun t : ℝ => t ^ (1 : ℕ) * Real.exp (-b * t)) (Set.Ici (1 : ℝ)) volume :=
    SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 1) (b := b) hb
  have :
      Integrable (fun t : ℝ => t * Real.exp (-b * t))
        ((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))) := by
    simpa [pow_one, IntegrableOn] using! hInt
  simpa [mul_assoc, mul_left_comm, mul_comm] using! this.const_mul C

/-! ### Rewrites on the imaginary axis -/

public lemma expU_z₆'_eq (u : ℂ) {t : ℝ} (ht : t ∈ Set.Ici (1 : ℝ)) :
    expU u (z₆' t) = Complex.exp (-(π : ℂ) * u * (t : ℂ)) := by
  have hz : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc] using! (MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t) ht)
  have harg : (Real.pi : ℂ) * Complex.I * u * (z₆' t) = (-(π : ℂ) * u * (t : ℂ)) := by
    calc
      (Real.pi : ℂ) * Complex.I * u * (z₆' t)
          = (Real.pi : ℂ) * Complex.I * u * ((Complex.I : ℂ) * (t : ℂ)) := by simp [hz]
      _ = (Real.pi : ℂ) * u * (t : ℂ) * (Complex.I * Complex.I) := by ac_rfl
      _ = (Real.pi : ℂ) * u * (t : ℂ) * (-1 : ℂ) := by simp [Complex.I_mul_I]
      _ = (-(π : ℂ) * u * (t : ℂ)) := by ring
  simp [expU, harg]

/-! ### Measurability of the imaginary-axis restriction -/

lemma measurable_varphi_resToImagAxis : Measurable (varphi.resToImagAxis : ℝ → ℂ) := by
  let s : Set ℝ := {t : ℝ | 0 < t}
  have hs : MeasurableSet s := by
    simpa [s] using!
      (isOpen_lt (continuous_const : Continuous fun _ : ℝ => (0 : ℝ)) continuous_id).measurableSet
  have hcont_mk : Continuous fun t : s => (⟨(Complex.I : ℂ) * ((t : ℝ) : ℂ), by
      have ht : 0 < (t : ℝ) := t.property
      simpa [Complex.mul_im] using! ht⟩ : ℍ) := by
    -- Continuity of the coercion into `ℂ` suffices for continuity into the subtype.
    fun_prop
  have hf : Measurable fun t : s => varphi (⟨(Complex.I : ℂ) * ((t : ℝ) : ℂ), by
      have ht : 0 < (t : ℝ) := t.property
      simpa [Complex.mul_im] using! ht⟩ : ℍ) :=
    ((VarphiExpBounds.continuous_varphi).comp hcont_mk).measurable
  have hg : Measurable fun _t : (sᶜ : Set ℝ) => (0 : ℂ) := measurable_const
  -- `resToImagAxis` is definitionaly `ResToImagAxis`.
  simpa [Function.resToImagAxis, Function.resToImagAxis_eq_resToImagAxis, ResToImagAxis, s] using!
    (Measurable.dite (s := s) hf hg hs)

/-- Exponential bound for `‖exp (-(π : ℂ) * u * (t : ℂ))‖` when `u` stays in a ball around `u0`. -/
public lemma norm_exp_neg_pi_mul_le_of_mem_ball {u u0 : ℂ} {r : ℝ}
    (hu : u ∈ Metric.ball u0 r) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ Real.exp (-(Real.pi * (u0.re - r)) * t) := by
  have hunorm : ‖u - u0‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using! hu
  have hre_lt : |u.re - u0.re| < r := by
    have hre_le : |u.re - u0.re| ≤ ‖u - u0‖ := by
      simpa [Complex.sub_re] using! (abs_re_le_norm (u - u0))
    exact lt_of_le_of_lt hre_le hunorm
  have hu0_le : u0.re - r < u.re := by
    have h₂ : u0.re - u.re < r := (abs_sub_lt_iff.1 hre_lt).2
    exact (sub_lt_iff_lt_add).2 (by linarith [h₂])
  have hnorm :
      ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ =
        Real.exp ((-(π : ℂ) * u * (t : ℂ)).re) := by
    simpa using! (Complex.norm_exp (-(π : ℂ) * u * (t : ℂ)))
  have hre :
      (-(π : ℂ) * u * (t : ℂ)).re = (-(Real.pi * u.re) * t) := by
    simp [mul_comm, mul_left_comm]
  have hle :
      Real.exp (-(Real.pi * u.re) * t) ≤ Real.exp (-(Real.pi * (u0.re - r)) * t) := by
    have hu_re_ge : u0.re - r ≤ u.re := le_of_lt hu0_le
    have hmul : (-(Real.pi * u.re) * t) ≤ (-(Real.pi * (u0.re - r)) * t) := by
      have hpi : 0 < Real.pi := Real.pi_pos
      have : -(Real.pi * u.re) ≤ -(Real.pi * (u0.re - r)) := by
        have : Real.pi * (u0.re - r) ≤ Real.pi * u.re := by nlinarith [hu_re_ge, hpi]
        nlinarith
      exact mul_le_mul_of_nonneg_right this ht
    exact Real.exp_le_exp.2 hmul
  rw [hnorm, hre]
  simpa [mul_comm, mul_left_comm] using! hle

/-!
### Tail integral (`I₆'`) as a Laplace transform and differentiability
-/

public lemma hasDerivAt_const_mul_exp_neg_pi_mul (c u : ℂ) (t : ℝ) :
    HasDerivAt (fun z : ℂ => c * Complex.exp (z * (-(π : ℂ) * (t : ℂ))))
      (-((t : ℂ) * ((π : ℂ) * (c * Complex.exp (u * (-(π : ℂ) * (t : ℂ))))))) u := by
  have hlin :
      HasDerivAt (fun z : ℂ => z * (-(π : ℂ) * (t : ℂ))) (-(π : ℂ) * (t : ℂ)) u := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using!
      (hasDerivAt_mul_const (x := u) (-(π : ℂ) * (t : ℂ)))
  have hexp :
      HasDerivAt (fun z : ℂ => Complex.exp (z * (-(π : ℂ) * (t : ℂ))))
        (Complex.exp (u * (-(π : ℂ) * (t : ℂ))) * (-(π : ℂ) * (t : ℂ))) u := by
    simpa using! (Complex.hasDerivAt_exp (u * (-(π : ℂ) * (t : ℂ)))).comp u hlin
  have h := hexp.const_mul c
  have hderiv :
      c * (Complex.exp (u * (-(π : ℂ) * (t : ℂ))) * (-(π : ℂ) * (t : ℂ))) =
        -((t : ℂ) * ((π : ℂ) * (c * Complex.exp (u * (-(π : ℂ) * (t : ℂ)))))) := by
    ring
  exact hderiv ▸ h

public lemma hasDerivAt_integral_of_dominated_ball {μ : Measure ℝ} {F F' : ℂ → ℝ → ℂ} {u0 : ℂ}
    {ε : ℝ} {bound : ℝ → ℝ} (hε : 0 < ε)
    (hF_meas : ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (fun t : ℝ => F u t) μ)
    (hF_int : Integrable (fun t : ℝ => F u0 t) μ)
    (hF'_meas : AEStronglyMeasurable (fun t : ℝ => F' u0 t) μ)
    (h_bound : ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε, ‖F' u t‖ ≤ bound t)
    (bound_integrable : Integrable bound μ)
    (h_diff :
      ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε,
        HasDerivAt (fun z : ℂ => F z t) (F' u t) u) :
    HasDerivAt (fun u : ℂ => ∫ t, F u t ∂μ) (∫ t, F' u0 t ∂μ) u0 := by
  simpa using!
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (α := ℝ) (E := ℂ)
      (μ := μ) (F := F) (x₀ := u0) (s := Metric.ball u0 ε)
      (hs := Metric.ball_mem_nhds u0 hε) (bound := bound) (F' := F')
      (hF_meas := hF_meas) (hF_int := hF_int) (hF'_meas := hF'_meas) (h_bound := h_bound)
      (bound_integrable := bound_integrable) (h_diff := h_diff)).2

namespace A

open scoped Topology

noncomputable def aTailIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  (2 * (Complex.I : ℂ)) * varphi.resToImagAxis t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

noncomputable def aTailIntegralC (u : ℂ) : ℂ :=
  ∫ t in Set.Ici (1 : ℝ), aTailIntegrandC u t

lemma I₆'_eq_aTailIntegralC (u : ℂ) : I₆' u = aTailIntegralC u := by
  unfold I₆' aTailIntegralC aTailIntegrandC
  have hEq :
      ∀ t ∈ Set.Ici (1 : ℝ),
        Φ₆ u t =
          (Complex.I : ℂ) * varphi.resToImagAxis t * Complex.exp (-(π : ℂ) * u * (t : ℂ)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have hz : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by
      simpa [mul_assoc] using! (MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t) ht)
    have him : 0 < (z₆' t).im := by
      simp [hz, Complex.mul_im, ht0]
    have hvar : varphi' (z₆' t) = varphi.resToImagAxis t := by
      simp [Function.resToImagAxis, ResToImagAxis, ht0, hz]
    have hexp : expU u (z₆' t) = Complex.exp (-(π : ℂ) * u * (t : ℂ)) :=
      expU_z₆'_eq (u := u) (t := t) ht
    simp [Φ₆, Φ₆', hvar, hexp, mul_assoc, mul_left_comm, mul_comm]
  have hInt :
      (∫ t in Set.Ici (1 : ℝ), Φ₆ u t) =
        ∫ t in Set.Ici (1 : ℝ),
          (Complex.I : ℂ) * varphi.resToImagAxis t * Complex.exp (-(π : ℂ) * u * (t : ℂ)) := by
    refine MeasureTheory.setIntegral_congr_fun (s := Set.Ici (1 : ℝ)) measurableSet_Ici ?_
    intro t ht
    exact hEq t ht
  -- Move the scalar `2` into the integrand and match `aTailIntegrandC`.
  calc
    (2 : ℂ) * ∫ t in Set.Ici (1 : ℝ), Φ₆ u t
        = (2 : ℂ) * ∫ t in Set.Ici (1 : ℝ),
            (Complex.I : ℂ) * varphi.resToImagAxis t * Complex.exp (-(π : ℂ) * u * (t : ℂ)) := by
              simp [hInt]
    _ = ∫ t in Set.Ici (1 : ℝ),
          (2 : ℂ) * ((Complex.I : ℂ) * varphi.resToImagAxis t *
            Complex.exp (-(π : ℂ) * u * (t : ℂ))) := by
            -- `∫ (2 * f) = 2 * ∫ f`, with `μ = volume.restrict (Set.Ici 1)`.
            exact
                Eq.symm
                  (MeasureTheory.integral_const_mul 2 fun a =>
                    I * Function.resToImagAxis varphi a * cexp (-↑π * u * ↑a))
    _ = ∫ t in Set.Ici (1 : ℝ), aTailIntegrandC u t := by
          simp [aTailIntegrandC, mul_assoc, mul_left_comm, mul_comm]

lemma aestronglyMeasurable_aTailIntegrandC (u : ℂ) (μ : Measure ℝ) :
    AEStronglyMeasurable (aTailIntegrandC u) μ := by
  have hmeas_axis : Measurable (varphi.resToImagAxis : ℝ → ℂ) := measurable_varphi_resToImagAxis
  have hmeas_exp : Measurable fun t : ℝ => Complex.exp (-(π : ℂ) * u * (t : ℂ)) := by
    fun_prop
  have hmeas_mul :
      Measurable fun t : ℝ =>
        (varphi.resToImagAxis t : ℂ) * Complex.exp (-(π : ℂ) * u * (t : ℂ)) :=
    hmeas_axis.mul hmeas_exp
  have hmeas_inner :
      Measurable fun t : ℝ =>
        (2 : ℂ) * ((Complex.I : ℂ) * ((varphi.resToImagAxis t : ℂ) *
          Complex.exp (-(π : ℂ) * u * (t : ℂ)))) :=
    measurable_const.mul (measurable_const.mul hmeas_mul)
  have hmeas : Measurable fun t : ℝ => aTailIntegrandC u t := by
    simpa [aTailIntegrandC, mul_assoc, mul_left_comm, mul_comm] using! hmeas_inner
  exact hmeas.aestronglyMeasurable

/-!
### Fixed exponential bound for `varphi.resToImagAxis`

We pick a single constant `Cφ` witnessing the exponential decay bound used in the dominated
differentiation arguments.
-/

/-- A fixed constant witnessing an exponential decay bound for `varphi.resToImagAxis` on
`Set.Ici 1`. -/
public noncomputable def Cφ : ℝ :=
  Classical.choose VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one

/-- The exponential decay bound for `varphi.resToImagAxis` on `Set.Ici 1` using the fixed constant
`Cφ`. -/
public lemma hCφ (t : ℝ) (ht : 1 ≤ t) :
    ‖varphi.resToImagAxis t‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) :=
  (Classical.choose_spec VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one) t ht

lemma Cφ_nonneg : 0 ≤ Cφ := by
  have h := hCφ (t := (1 : ℝ)) (le_rfl : (1 : ℝ) ≤ 1)
  have hexp_pos : 0 < Real.exp (-(2 * Real.pi) * (1 : ℝ)) := by positivity
  exact
    ForMathlib.nonneg_of_nonneg_le_mul (ha := norm_nonneg (varphi.resToImagAxis (1 : ℝ)))
      (hb := hexp_pos) (h := h)

/-- The measure `volume` restricted to `Set.Ici 1`, used for the tail integral `I₆'`. -/
@[expose] public noncomputable def μ : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))

attribute [irreducible] μ

lemma integrable_aTailIntegrandC {u0 : ℂ} (hu0 : u0 ∈ SpherePacking.rightHalfPlane) :
    Integrable (fun t : ℝ => aTailIntegrandC u0 t) μ := by
  have hu0_re : 0 < u0.re := by simpa [SpherePacking.rightHalfPlane] using! hu0
  let r : ℝ := u0.re / 2
  have hr : 0 < r := by simpa [r] using! (half_pos hu0_re)
  have hb : 0 < Real.pi * (r + 2) := mul_pos Real.pi_pos (by linarith)
  have hbound_int :
      Integrable (fun t : ℝ => (2 * Cφ) * Real.exp (-(Real.pi * (r + 2)) * t)) μ := by
    -- Bound by a constant multiple of `exp(-b*t)` on `Ici 1`.
    have :
        Integrable (fun t : ℝ => (2 * Cφ) * Real.exp (-(Real.pi * (r + 2)) * t)) (μ := μ) := by
      simpa [μ, mul_assoc, mul_left_comm, mul_comm] using!
        (integrable_bound_exp (C := (2 * Cφ)) (b := (Real.pi * (r + 2))) hb)
    exact this
  have hmeas : AEStronglyMeasurable (fun t : ℝ => aTailIntegrandC u0 t) μ := by
    simpa using! (aestronglyMeasurable_aTailIntegrandC (u := u0) μ)
  refine Integrable.mono' hbound_int hmeas ?_
  have h :
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))),
        ‖aTailIntegrandC u0 t‖ ≤ (2 * Cφ) * Real.exp (-(Real.pi * (r + 2)) * t) := by
    refine
      (ae_restrict_iff' (μ := (volume : Measure ℝ)) (s := Set.Ici (1 : ℝ)) measurableSet_Ici).2
        (.of_forall ?_)
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht1
    have hφ : ‖varphi.resToImagAxis t‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) := hCφ t ht1
    have hexp :
        ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ ≤ Real.exp (-(Real.pi * r) * t) := by
      have hre : u0.re - r = r := by
        dsimp [r]
        ring_nf
      have hu : (u0 : ℂ) ∈ Metric.ball u0 r := Metric.mem_ball_self hr
      simpa [hre, mul_assoc, mul_left_comm, mul_comm] using!
        (norm_exp_neg_pi_mul_le_of_mem_ball (u := u0) (u0 := u0) (r := r) hu (t := t) ht0)
    have hI : ‖(2 * (Complex.I : ℂ))‖ = 2 := by simp
    have hExp :
        Real.exp (-(2 * Real.pi) * t) * Real.exp (-(Real.pi * r) * t) =
          Real.exp (-(Real.pi * (r + 2)) * t) := by
      have hx :
          (-(Real.pi * (r + 2)) * t) = (-(2 * Real.pi) * t) + (-(Real.pi * r) * t) := by ring
      calc
        Real.exp (-(2 * Real.pi) * t) * Real.exp (-(Real.pi * r) * t) =
            Real.exp ((-(2 * Real.pi) * t) + (-(Real.pi * r) * t)) := by
              simp [Real.exp_add]
        _ = Real.exp (-(Real.pi * (r + 2)) * t) := by simp [hx]
    have hmain :
        ‖aTailIntegrandC u0 t‖ ≤ (2 * Cφ) * Real.exp (-(Real.pi * (r + 2)) * t) := by
      calc
        ‖aTailIntegrandC u0 t‖ =
            ‖(2 * (Complex.I : ℂ))‖ * ‖varphi.resToImagAxis t‖ *
              ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ := by
                simp [aTailIntegrandC, mul_left_comm, mul_comm]
        _ ≤ ‖(2 * (Complex.I : ℂ))‖ * (Cφ * Real.exp (-(2 * Real.pi) * t)) *
              Real.exp (-(Real.pi * r) * t) := by
                -- Bound `‖varphi‖` and `‖exp‖` separately, then multiply inequalities.
                have h2I0 : 0 ≤ ‖(2 * (Complex.I : ℂ))‖ := norm_nonneg _
                have hCexp0 : 0 ≤ Cφ * Real.exp (-(2 * Real.pi) * t) :=
                  mul_nonneg Cφ_nonneg (Real.exp_pos _).le
                have h2I_Cexp0 :
                    0 ≤ ‖(2 * (Complex.I : ℂ))‖ * (Cφ * Real.exp (-(2 * Real.pi) * t)) :=
                  mul_nonneg h2I0 hCexp0
                have h1 :
                    ‖(2 * (Complex.I : ℂ))‖ * ‖varphi.resToImagAxis t‖ ≤
                      ‖(2 * (Complex.I : ℂ))‖ * (Cφ * Real.exp (-(2 * Real.pi) * t)) :=
                  mul_le_mul_of_nonneg_left hφ h2I0
                have h2 :
                    (‖(2 * (Complex.I : ℂ))‖ * ‖varphi.resToImagAxis t‖) *
                        ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ ≤
                      (‖(2 * (Complex.I : ℂ))‖ * (Cφ * Real.exp (-(2 * Real.pi) * t))) *
                        ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ :=
                  mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
                exact le_mul_of_le_mul_of_nonneg_left h2 hexp h2I_Cexp0
        _ = (2 * Cφ) * (Real.exp (-(2 * Real.pi) * t) * Real.exp (-(Real.pi * r) * t)) := by
              rw [hI]
              ring_nf
        _ = (2 * Cφ) * Real.exp (-(Real.pi * (r + 2)) * t) := by
              simpa using! congrArg (fun x : ℝ => (2 * Cφ) * x) hExp
    simpa using! hmain
  simpa [μ] using! h

lemma ae_bound_aTailDeriv {u0 : ℂ} (hu0 : u0 ∈ SpherePacking.rightHalfPlane) :
    let r : ℝ := u0.re / 2
    let ε : ℝ := r
    let bound : ℝ → ℝ :=
      fun t : ℝ => (‖(π : ℂ)‖ * (2 * Cφ)) * (t * Real.exp (-(Real.pi * (r + 2)) * t))
    ∀ᵐ (t : ℝ) ∂μ, ∀ u ∈ Metric.ball u0 ε,
      ‖(-((t : ℂ) * ((π : ℂ) * aTailIntegrandC u t)))‖ ≤ bound t := by
  let r : ℝ := u0.re / 2
  let ε : ℝ := r
  have hu0_re : 0 < u0.re := by simpa [SpherePacking.rightHalfPlane] using! hu0
  have hr : 0 < r := by simpa [r] using! (half_pos hu0_re)
  have hb : 0 < Real.pi * (r + 2) := mul_pos Real.pi_pos (by linarith)
  let bound : ℝ → ℝ :=
    fun t : ℝ => (‖(π : ℂ)‖ * (2 * Cφ)) * (t * Real.exp (-(Real.pi * (r + 2)) * t))
  have h :
      ∀ᵐ (t : ℝ) ∂((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))),
        ∀ u ∈ Metric.ball u0 ε, ‖(-((t : ℂ) * ((π : ℂ) * aTailIntegrandC u t)))‖ ≤ bound t := by
    refine
      (ae_restrict_iff' (μ := (volume : Measure ℝ)) (s := Set.Ici (1 : ℝ)) measurableSet_Ici).2
        (.of_forall ?_)
    intro t ht u hu
    have ht1 : (1 : ℝ) ≤ t := ht
    have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht1
    have hφ : ‖varphi.resToImagAxis t‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) := hCφ t ht1
    have hexp :
        ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ Real.exp (-(Real.pi * r) * t) := by
      have hre : u0.re - ε = r := by dsimp [ε, r]; ring_nf
      have hle :=
        norm_exp_neg_pi_mul_le_of_mem_ball (u := u) (u0 := u0) (r := ε) hu (t := t) ht0
      simpa [hre, mul_assoc, mul_left_comm, mul_comm] using! hle
    have hI : ‖(2 * (Complex.I : ℂ))‖ = 2 := by simp
    have hExp :
        Real.exp (-(2 * Real.pi) * t) * Real.exp (-(Real.pi * r) * t) =
          Real.exp (-(Real.pi * (r + 2)) * t) := by
      have hx :
          (-(Real.pi * (r + 2)) * t) = (-(2 * Real.pi) * t) + (-(Real.pi * r) * t) := by ring
      calc
        Real.exp (-(2 * Real.pi) * t) * Real.exp (-(Real.pi * r) * t) =
            Real.exp ((-(2 * Real.pi) * t) + (-(Real.pi * r) * t)) := by
              simp [Real.exp_add]
        _ = Real.exp (-(Real.pi * (r + 2)) * t) := by simp [hx]
    have hF_le :
        ‖aTailIntegrandC u t‖ ≤ (2 * Cφ) * Real.exp (-(Real.pi * (r + 2)) * t) := by
      calc
        ‖aTailIntegrandC u t‖ =
            ‖(2 * (Complex.I : ℂ))‖ * ‖varphi.resToImagAxis t‖ *
              ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by
                simp [aTailIntegrandC, mul_left_comm, mul_comm]
        _ ≤ ‖(2 * (Complex.I : ℂ))‖ * (Cφ * Real.exp (-(2 * Real.pi) * t)) *
              Real.exp (-(Real.pi * r) * t) := by
                have h2I0 : 0 ≤ ‖(2 * (Complex.I : ℂ))‖ := norm_nonneg _
                have hCexp0 : 0 ≤ Cφ * Real.exp (-(2 * Real.pi) * t) :=
                  mul_nonneg Cφ_nonneg (Real.exp_pos _).le
                have h2I_Cexp0 :
                    0 ≤ ‖(2 * (Complex.I : ℂ))‖ * (Cφ * Real.exp (-(2 * Real.pi) * t)) :=
                  mul_nonneg h2I0 hCexp0
                have h1 :
                    ‖(2 * (Complex.I : ℂ))‖ * ‖varphi.resToImagAxis t‖ ≤
                      ‖(2 * (Complex.I : ℂ))‖ * (Cφ * Real.exp (-(2 * Real.pi) * t)) :=
                  mul_le_mul_of_nonneg_left hφ h2I0
                have h2 :
                    (‖(2 * (Complex.I : ℂ))‖ * ‖varphi.resToImagAxis t‖) *
                        ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤
                      (‖(2 * (Complex.I : ℂ))‖ * (Cφ * Real.exp (-(2 * Real.pi) * t))) *
                        ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ :=
                  mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
                exact le_mul_of_le_mul_of_nonneg_left h2 hexp h2I_Cexp0
        _ = (2 * Cφ) * (Real.exp (-(2 * Real.pi) * t) * Real.exp (-(Real.pi * r) * t)) := by
              rw [hI]
              ring_nf
        _ = (2 * Cφ) * Real.exp (-(Real.pi * (r + 2)) * t) := by
              simpa using! congrArg (fun x : ℝ => (2 * Cφ) * x) hExp
    have hpi : ‖(π : ℂ)‖ = Real.pi := by
      simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
    calc
      ‖(-((t : ℂ) * ((π : ℂ) * aTailIntegrandC u t)))‖ =
          ‖(π : ℂ)‖ * ‖(t : ℂ)‖ * ‖aTailIntegrandC u t‖ := by
            simp [mul_assoc, mul_comm, norm_neg]
      _ ≤ ‖(π : ℂ)‖ * ‖(t : ℂ)‖ * ((2 * Cφ) * Real.exp (-(Real.pi * (r + 2)) * t)) := by
            have hnonneg : 0 ≤ ‖(π : ℂ)‖ * ‖(t : ℂ)‖ :=
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
            simpa [mul_assoc] using! mul_le_mul_of_nonneg_left hF_le hnonneg
      _ = bound t := by
            have htC : ‖(t : ℂ)‖ = t := by simp [Complex.norm_real, abs_of_nonneg ht0]
            dsimp [bound]
            rw [htC]
            ring_nf
  simpa [μ, ε, r, bound] using! h

lemma hasDerivAt_aTailIntegrandC (u : ℂ) (t : ℝ) :
    HasDerivAt (fun z : ℂ => aTailIntegrandC z t)
      (-((t : ℂ) * ((π : ℂ) * aTailIntegrandC u t))) u := by
  simpa [aTailIntegrandC, mul_assoc, mul_left_comm, mul_comm] using!
    (ProfileComplex.hasDerivAt_const_mul_exp_neg_pi_mul
      (c := (2 * (Complex.I : ℂ)) * varphi.resToImagAxis t) (u := u) (t := t))

lemma differentiableAt_aTailIntegralC {u0 : ℂ} (hu0 : u0 ∈ SpherePacking.rightHalfPlane) :
    DifferentiableAt ℂ aTailIntegralC u0 := by
  have hu0_re : 0 < u0.re := by simpa [SpherePacking.rightHalfPlane] using! hu0
  let r : ℝ := u0.re / 2
  have hr : 0 < r := by simpa [r] using! (half_pos hu0_re)
  let ε : ℝ := r
  have hε : 0 < ε := by simpa [ε] using! hr
  have hb : 0 < Real.pi * (r + 2) := mul_pos Real.pi_pos (by linarith)
  let F (u : ℂ) (t : ℝ) : ℂ := aTailIntegrandC u t
  let F' (u : ℂ) (t : ℝ) : ℂ := -((t : ℂ) * ((π : ℂ) * F u t))
  let bound : ℝ → ℝ :=
    fun t : ℝ => (‖(π : ℂ)‖ * (2 * Cφ)) * (t * Real.exp (-(Real.pi * (r + 2)) * t))
  have hbound_int : Integrable bound μ := by
    simpa [μ, bound, mul_assoc, mul_left_comm, mul_comm] using!
      (integrable_bound_mul_exp (C := (‖(π : ℂ)‖ * (2 * Cφ))) (b := (Real.pi * (r + 2))) hb)
  have hF_meas :
      ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (fun t : ℝ => F u t) μ := by
    refine Filter.mem_of_superset (Filter.univ_mem : (Set.univ : Set ℂ) ∈ 𝓝 u0) ?_
    intro u _hu
    simpa [F] using! (aestronglyMeasurable_aTailIntegrandC (u := u) μ)
  have hF_int : Integrable (fun t : ℝ => F u0 t) μ := by
    simpa [F] using! (integrable_aTailIntegrandC (u0 := u0) hu0)
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => F' u0 t) μ := by
    have hFmeas : AEStronglyMeasurable (fun t : ℝ => F u0 t) μ := by
      simpa [F] using! (aestronglyMeasurable_aTailIntegrandC (u := u0) μ)
    have ht : AEStronglyMeasurable (fun t : ℝ => (t : ℂ)) μ :=
      (Complex.continuous_ofReal.measurable.aestronglyMeasurable)
    have hpiF : AEStronglyMeasurable (fun t : ℝ => (π : ℂ) * F u0 t) μ :=
      aestronglyMeasurable_const.mul hFmeas
    have hmul : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * ((π : ℂ) * F u0 t)) μ := ht.mul hpiF
    simpa [F'] using! hmul.neg
  have hbound :
      ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε, ‖F' u t‖ ≤ bound t := by
    -- Reuse the packaged tail estimate.
    simpa [F, F', bound, ε, r, μ, mul_assoc, mul_left_comm, mul_comm] using!
      (ae_bound_aTailDeriv (u0 := u0) hu0)
  have hdiff :
      ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε,
        HasDerivAt (fun z : ℂ => F z t) (F' u t) u := by
    refine Filter.Eventually.of_forall ?_
    exact fun x u a => hasDerivAt_aTailIntegrandC u x
  have hderiv :
      HasDerivAt (fun z : ℂ => ∫ t, F z t ∂μ) (∫ t, F' u0 t ∂μ) u0 := by
    -- Delegate the heavy dominated-differentiation step to a separate lemma
    -- (fresh heartbeat budget).
    exact
      (ProfileComplex.hasDerivAt_integral_of_dominated_ball (μ := μ) (F := F) (F' := F')
        (u0 := u0) (ε := ε) (bound := bound) hε hF_meas hF_int hF'_meas hbound hbound_int hdiff)
  have hEq : (fun z : ℂ => ∫ t, F z t ∂μ) = aTailIntegralC := by
    funext z
    simp [F, aTailIntegralC, μ]
  simpa [hEq] using! hderiv.differentiableAt

lemma differentiableAt_I₆' {u0 : ℂ} (hu0 : u0 ∈ SpherePacking.rightHalfPlane) :
    DifferentiableAt ℂ I₆' u0 := by
  have htail : I₆' = aTailIntegralC := by
    funext u
    simpa using! (I₆'_eq_aTailIntegralC (u := u))
  simpa [htail] using! (differentiableAt_aTailIntegralC (u0 := u0) hu0)

end ProfileComplex.A
end

end SpherePacking.Dim24
/-
Holomorphy of the complexified `a'` profile `ProfileComplex.A.aPrimeC` on the right half-plane.

This section assembles the differentiability results proved above in this file.
-/

open scoped Topology

open Complex

namespace SpherePacking.Dim24

noncomputable section

namespace ProfileComplex.A
lemma differentiableAt_aPrimeC {u0 : ℂ} (hu0 : u0 ∈ SpherePacking.rightHalfPlane) :
    DifferentiableAt ℂ aPrimeC u0 := by
  -- Expand into the sum of the six pieces and use the established differentiability of each.
  simpa [aPrimeC] using!
    (((((differentiableAt_I₁' u0).add (differentiableAt_I₂' u0)).add (differentiableAt_I₃' u0)).add
          (differentiableAt_I₄' u0)).add (differentiableAt_I₅' u0)).add
      (differentiableAt_I₆' (u0 := u0) hu0)

lemma differentiableOn_aPrimeC :
    DifferentiableOn ℂ aPrimeC SpherePacking.rightHalfPlane := by
  intro u hu
  exact (differentiableAt_aPrimeC (u0 := u) hu).differentiableWithinAt

/-- The complexified profile `aPrimeC` is holomorphic on `SpherePacking.rightHalfPlane`. -/
public lemma analyticOnNhd_aPrimeC :
    AnalyticOnNhd ℂ aPrimeC SpherePacking.rightHalfPlane := by
  -- On an open set, holomorphy is equivalent to complex differentiability.
  simpa [analyticOnNhd_iff_differentiableOn SpherePacking.rightHalfPlane_isOpen] using!
    differentiableOn_aPrimeC

end ProfileComplex.A
end

end SpherePacking.Dim24
