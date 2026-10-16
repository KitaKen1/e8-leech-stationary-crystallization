-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
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
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Continuation.Prelude
import SpherePacking.Dim24.ModularForms.Psi.ImagAxis


/-!
# Integrand setup for `laplaceBKernelC`

This file introduces the integrand `t ↦ BKernel0 t * exp (-(π : ℂ) * u * (t : ℂ))` and its
derivative with respect to `u`, together with the measurability and integrability lemmas used in
dominated convergence and differentiation under the integral sign.

It also packages the cusp-normalized combination `D` of `varphi₂` and `ψI` that appears in the
formula for `BKernel`.

## Main definitions
* `kernelIntegrand`
* `kernelIntegrandDeriv`
* `D`

## Main statements
* `hasDerivAt_kernelIntegrand`
* `integrableOn_kernelIntegrand_Ioc`
* `norm_varphi_it_le`, `norm_varphi₁_it_le`, `hCDq`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Topology

open Complex Filter MeasureTheory Real Set SchwartzMap
open UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The Laplace integrand `t ↦ BKernel0 t * exp (-(π : ℂ) * u * (t : ℂ))`. -/
@[expose] public def kernelIntegrand (u : ℂ) (t : ℝ) : ℂ :=
  BKernel0 t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

/-- Derivative of `kernelIntegrand` with respect to the complex parameter `u`. -/
@[expose] public def kernelIntegrandDeriv (u : ℂ) (t : ℝ) : ℂ :=
  BKernel0 t * (-(π : ℂ) * (t : ℂ)) * Complex.exp (-(π : ℂ) * u * (t : ℂ))


open SpecialValuesVarphi₁Limits SpecialValuesAux.Deriv

/-- Cusp-normalized combination of `varphi₂` and `ψI` appearing in the formula for `BKernel`. -/
@[expose] public def D (z : ℍ) : ℂ :=
  (-(π : ℂ) / (28304640 : ℂ)) * Dim24.varphi₂ z + (π : ℂ)⁻¹ * ((65520 : ℂ)⁻¹ * ψI z)

lemma qHalf_sq_eq_q (z : ℍ) : (qHalf z) ^ (2 : ℕ) = q (z : ℂ) := by
  -- `qHalf z = exp(w)` with `w = π * z * I`, so `qHalf z ^ 2 = exp(w + w) = exp(2π I z) = q(z)`.
  let w : ℂ := ((Real.pi : ℂ) * (z : ℂ)) * Complex.I
  have hw : w + w = 2 * Real.pi * Complex.I * (z : ℂ) := by
    dsimp [w]
    ring_nf
  calc
    (qHalf z) ^ (2 : ℕ) = Complex.exp w * Complex.exp w := by
          simp [qHalf, w, pow_two]
    _ = Complex.exp (w + w) := (Complex.exp_add w w).symm
    _ = q (z : ℂ) := by
          simp [q, hw, mul_comm]

lemma exp_four_pi_mul_I_eq_q_sq (z : ℍ) :
    Complex.exp (4 * Real.pi * Complex.I * (z : ℂ)) = (q (z : ℂ)) ^ (2 : ℕ) := by
  -- `q(z)^2 = exp(u) * exp(u) = exp(u+u) = exp(4π I z)`.
  let u : ℂ := 2 * Real.pi * Complex.I * (z : ℂ)
  have hu : u + u = 4 * Real.pi * Complex.I * (z : ℂ) := by
    dsimp [u]
    ring_nf
  calc
    Complex.exp (4 * Real.pi * Complex.I * (z : ℂ)) = Complex.exp (u + u) := by
          simp [u, hu]
    _ = Complex.exp u * Complex.exp u := Complex.exp_add u u
    _ = (q (z : ℂ)) ^ (2 : ℕ) := by
          simp [q, u, pow_two, mul_left_comm, mul_comm]

lemma tendsto_D_mul_q :
    Tendsto (fun z : ℍ => D z * q (z : ℂ)) atImInfty (𝓝 (-((10 : ℂ) / ((117 : ℂ) * π)))) := by
  -- `tendsto_q1_coeff` is the limit of a `q^{-1}`-normalized expression; it simplifies to `D z *
  -- q(z)`.
  let F : ℍ → ℂ := fun z =>
    (-(π : ℂ) / (28304640 : ℂ)) *
        ((Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ) - (864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) / q (z : ℂ)) +
      (π : ℂ)⁻¹ * ((65520 : ℂ)⁻¹ *
        ((ψI z * Complex.exp (4 * Real.pi * Complex.I * (z : ℂ)) - (2 : ℂ)) / (qHalf z) ^ (2 : ℕ)))
  have hF : Tendsto F atImInfty (𝓝 (-((10 : ℂ) / ((117 : ℂ) * π)))) := by
    simpa [
      F,
      div_eq_mul_inv,
      mul_assoc,
      mul_left_comm,
      mul_comm
    ] using! BKernelAsymptotics.tendsto_q1_coeff
  have hEq : ∀ z : ℍ, F z = D z * q (z : ℂ) := by
    intro z
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    -- Purely algebraic: clear denominators and normalize.
    -- First rewrite `qHalf^2 = q` and `exp(4π I z) = q^2`, then clear denominators.
    simp [F, D, qHalf_sq_eq_q, exp_four_pi_mul_I_eq_q_sq, sub_eq_add_neg, div_eq_mul_inv]
    field_simp [hzq, hπ]
    ring_nf
  refine Tendsto.congr' ?_ hF
  exact (Filter.Eventually.of_forall hEq)

/-! ### Differentiation under the Laplace integral -/

/-- `kernelIntegrandDeriv u t` is the derivative of `u ↦ kernelIntegrand u t`. -/
public lemma hasDerivAt_kernelIntegrand (u : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℂ => kernelIntegrand u t) (kernelIntegrandDeriv u t) u := by
  -- Differentiate `u ↦ exp (-(π:ℂ) * u * (t:ℂ))` and multiply by the constant `BKernel0 t`.
  have hlin :
      HasDerivAt (fun u : ℂ => (-(π : ℂ)) * u * (t : ℂ)) (-(π : ℂ) * (t : ℂ)) u := by
    simpa [mul_assoc] using!
      ((hasDerivAt_mul_const (t : ℂ) : HasDerivAt (fun u : ℂ => u * (t : ℂ)) (t : ℂ) u).const_mul
        (-(π : ℂ)))
  have hexp :
      HasDerivAt (fun u : ℂ => Complex.exp (-(π : ℂ) * u * (t : ℂ)))
        (Complex.exp (-(π : ℂ) * u * (t : ℂ)) * (-(π : ℂ) * (t : ℂ))) u :=
    (Complex.hasDerivAt_exp (-(π : ℂ) * u * (t : ℂ))).comp u hlin
  -- Multiply by `BKernel0 t` and rewrite into our `kernelIntegrandDeriv` definition.
  simpa [kernelIntegrand, kernelIntegrandDeriv, mul_assoc, mul_left_comm, mul_comm] using!
    (hexp.const_mul (BKernel0 t))

/-- Integrability of `BKernel0` on the finite interval `(0,1]`. -/
public lemma integrableOn_BKernel0_Ioc_zero_one :
    IntegrableOn (fun t : ℝ => BKernel0 t) (Set.Ioc (0 : ℝ) 1) volume := by
  have hV : IntegrableOn (LaplaceEqA.gV (u := (0 : ℝ))) (Set.Ioc (0 : ℝ) 1) volume :=
    LaplaceEqA.integrableOn_gV_Ioc (u := (0 : ℝ)) (by simp)
  have hψ : IntegrableOn (LaplaceEqA.gψ (u := (0 : ℝ))) (Set.Ioc (0 : ℝ) 1) volume :=
    LaplaceEqA.integrableOn_gψ_Ioc (u := (0 : ℝ)) (by simp)
  -- linear combination of two integrable functions
  have hV' :
      IntegrableOn (fun t : ℝ => ((π : ℂ) / (28304640 : ℂ)) * LaplaceEqA.gV 0 t) (Set.Ioc (0 : ℝ)
      1) volume :=
    hV.const_mul ((π : ℂ) / (28304640 : ℂ))
  have hψ' :
      IntegrableOn (fun t : ℝ => (1 / ((65520 : ℂ) * π)) * LaplaceEqA.gψ 0 t) (Set.Ioc (0 : ℝ)
      1) volume :=
    hψ.const_mul (1 / ((65520 : ℂ) * π))
  have hsum :
      IntegrableOn
          (fun t : ℝ =>
            ((π : ℂ) / (28304640 : ℂ)) * LaplaceEqA.gV 0 t +
              (1 / ((65520 : ℂ) * π)) * LaplaceEqA.gψ 0 t)
          (Set.Ioc (0 : ℝ) 1) volume := by
    simpa using! hV'.add hψ'
  -- identify the integrand with `BKernel0` on the restricted measure
  have hEq :
      (fun t : ℝ =>
            ((π : ℂ) / (28304640 : ℂ)) * LaplaceEqA.gV 0 t +
              (1 / ((65520 : ℂ) * π)) * LaplaceEqA.gψ 0 t) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
        fun t : ℝ => BKernel0 t := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    have hB : BKernel0 t = BKernel t ht0 := by simp [BKernel0, ht0]
    have hker : LaplaceProfiles.varphiKernel0 t = ((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht0) := by
      simp [LaplaceProfiles.varphiKernel0, ht0]
    have hψI : ψI' ((Complex.I : ℂ) * (t : ℂ)) = ψI (it t ht0) := by
      let z : ℂ := (Complex.I : ℂ) * (t : ℂ)
      have hz : 0 < z.im := by simpa [z, mul_assoc] using! ht0
      have hzEq : ψI' z = ψI (⟨z, hz⟩ : ℍ) := by simp [ψI', hz]
      assumption
    have hψI' : ψI' ((t : ℂ) * Complex.I) = ψI (it t ht0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using! hψI
    -- expand `BKernel` and the `gV`/`gψ` definitions and normalize scalars
    simp [LaplaceEqA.gV, LaplaceEqA.gψ, hB, BKernel, hker, hψI, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm]
  -- transport integrability across the ae-equality
  exact (integrableOn_congr_fun_ae hEq).mp hsum

/-- For `0 < t` and `0 ≤ Re u`, the exponential factor in the Laplace kernel has norm `≤ 1`. -/
public lemma norm_exp_neg_pi_mul_le_one {u : ℂ} {t : ℝ} (ht : 0 < t) (hu : 0 ≤ u.re) :
    ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ 1 := by
  -- `‖exp z‖ = exp(Re z)` and `Re (-(π*u*t)) = -π * Re u * t ≤ 0`.
  have hnonpos : -Real.pi * u.re * t ≤ 0 := by
    have hnonneg : 0 ≤ Real.pi * u.re * t := by
      have ht0 : 0 ≤ t := le_of_lt ht
      positivity [Real.pi_pos, hu, ht0]
    linarith
  have hexp : Real.exp (-Real.pi * u.re * t) ≤ 1 := by
    simpa [Real.exp_le_one_iff] using! hnonpos
  have hnorm :
      ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ = Real.exp (-Real.pi * u.re * t) := by
    simpa [mul_assoc] using! LaplaceBKernelAnalytic.norm_kernelExp (u := u) (t := t)
  rw [hnorm]
  exact hexp

/-- Integrability of `kernelIntegrand u` on `(0,1]` for `0 ≤ Re u`. -/
public lemma integrableOn_kernelIntegrand_Ioc {u : ℂ} (hu : 0 ≤ u.re) :
    IntegrableOn (kernelIntegrand u) (Set.Ioc (0 : ℝ) 1) volume := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hB : Integrable (fun t : ℝ => BKernel0 t) μ := by
    simpa [μ, MeasureTheory.IntegrableOn] using! integrableOn_BKernel0_Ioc_zero_one
  have hexp_meas : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(π : ℂ) * u * (t : ℂ))) μ := by
    -- continuity implies strong measurability
    have hcont : Continuous fun t : ℝ => Complex.exp (-(π : ℂ) * u * (t : ℂ)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  have hbound :
      ∀ᵐ t : ℝ ∂μ, ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ 1 := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    exact norm_exp_neg_pi_mul_le_one (u := u) (t := t) ht0 hu
  have hint0 :
      Integrable (fun t : ℝ => BKernel0 t * Complex.exp (-(π : ℂ) * u * (t : ℂ))) μ :=
    hB.mul_bdd hexp_meas hbound
  assumption

/-!
### Tail bounds for `BKernel0` on `t ≥ 1`

These are used to justify integrability and differentiation under the Laplace integral on
`Re u > 2`.
-/

open SpecialValuesVarphi₁Limits SpecialValuesAux.Deriv

lemma exists_bound_norm_resToImagAxis_Ici_one {F : ℍ → ℂ} {l : ℂ}
    (hF : Tendsto F atImInfty (𝓝 l)) (hcont : Continuous F) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖F.resToImagAxis t‖ ≤ C := by
  have hAxis : Tendsto F.resToImagAxis atTop (𝓝 l) :=
    Function.tendsto_resToImagAxis_atImInfty (F := F) (l := l) hF
  have hEv : ∀ᶠ t : ℝ in atTop, ‖F.resToImagAxis t - l‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      hAxis.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
  rcases (eventually_atTop.1 hEv) with ⟨A0, hA0⟩
  let A : ℝ := max A0 1
  have hA1 : 1 ≤ A := le_max_right _ _
  -- Bound on the compact interval `t ∈ [1,A]`.
  let h : Set.Icc (1 : ℝ) A → ℍ :=
    fun x =>
      ⟨(Complex.I : ℂ) * ((x : ℝ) : ℂ),
        by
          have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) x.property.1
          simpa [Complex.mul_im] using! hx0⟩
  have hcont_h : Continuous h := by
    fun_prop
  have hcont_comp : Continuous fun x : Set.Icc (1 : ℝ) A => F (h x) := hcont.comp hcont_h
  have hcomp : IsCompact (Set.range fun x : Set.Icc (1 : ℝ) A => F (h x)) :=
    isCompact_range hcont_comp
  have hbound : Bornology.IsBounded (Set.range fun x : Set.Icc (1 : ℝ) A => F (h x)) :=
    hcomp.isBounded
  rcases hbound.subset_closedBall (c := (0 : ℂ)) with ⟨C0, hC0ball⟩
  have hC0 : ∀ x : Set.Icc (1 : ℝ) A, ‖F (h x)‖ ≤ C0 := by
    intro x
    have hx : F (h x) ∈ Set.range (fun x : Set.Icc (1 : ℝ) A => F (h x)) := ⟨x, rfl⟩
    have hx' : F (h x) ∈ Metric.closedBall (0 : ℂ) C0 := hC0ball hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using! hx'
  refine ⟨max C0 (‖l‖ + 1), ?_⟩
  intro t ht1
  rcases le_total t A with htA | hAt
  · have htIcc : t ∈ Set.Icc (1 : ℝ) A := ⟨ht1, htA⟩
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
    have hbound : ‖F.resToImagAxis t‖ ≤ C0 := by
      simpa [Function.resToImagAxis, ResToImagAxis, ht0, h] using! hC0 ⟨t, htIcc⟩
    exact le_trans hbound (le_max_left _ _)
  · have hA0' : A0 ≤ t := le_trans (le_max_left _ _) hAt
    have hball : ‖F.resToImagAxis t - l‖ < 1 := hA0 t hA0'
    have htri : ‖F.resToImagAxis t‖ ≤ ‖F.resToImagAxis t - l‖ + ‖l‖ := by
      simpa [sub_eq_add_neg, add_assoc] using! norm_add_le (F.resToImagAxis t - l) l
    have hle : ‖F.resToImagAxis t‖ ≤ ‖l‖ + 1 := by
      have : ‖F.resToImagAxis t - l‖ + ‖l‖ < 1 + ‖l‖ := by linarith
      have : ‖F.resToImagAxis t - l‖ + ‖l‖ < ‖l‖ + 1 := by
        simpa [add_comm, add_left_comm, add_assoc] using! this
      exact le_of_lt (lt_of_le_of_lt htri this)
    exact le_trans hle (le_max_right _ _)

/-- A constant such that `‖varphi.resToImagAxis t‖ ≤ Cφ * exp (-(2 * π) * t)` for `t ≥ 1`. -/
public noncomputable def Cφ : ℝ :=
  Classical.choose VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one

/-- Exponential decay bound for `varphi.resToImagAxis` on `t ≥ 1`. -/
public lemma hCφ (t : ℝ) (ht : 1 ≤ t) :
    ‖varphi.resToImagAxis t‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) :=
  (Classical.choose_spec VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one) t ht

lemma continuous_qH : Continuous fun z : ℍ => q (z : ℂ) := by
  -- `q(z) = exp(2π i z)` is continuous.
  unfold q
  fun_prop

/-- A uniform bound for `‖varphi₁ z * q z‖` on the imaginary axis `t ≥ 1`. -/
public noncomputable def Cφ1q : ℝ :=
  Classical.choose
    (exists_bound_norm_resToImagAxis_Ici_one
      (F := fun z : ℍ => Dim24.varphi₁ z * q (z : ℂ))
      (l := (725760 : ℂ) * Complex.I / (π : ℂ))
      (hF := by
        simpa using! (SpecialValuesVarphi₁Limits.tendsto_varphi₁_mul_q))
      (hcont := by
        simpa using! (SpecialValuesAux.continuous_varphi₁.mul continuous_qH)))

/-- The bound defining `Cφ1q`, written as a lemma. -/
public lemma hCφ1q (t : ℝ) (ht : 1 ≤ t) :
    ‖(fun z : ℍ => Dim24.varphi₁ z * q (z : ℂ)).resToImagAxis t‖ ≤ Cφ1q :=
  (Classical.choose_spec
    (exists_bound_norm_resToImagAxis_Ici_one
      (F := fun z : ℍ => Dim24.varphi₁ z * q (z : ℂ))
      (l := (725760 : ℂ) * Complex.I / (π : ℂ))
      (hF := by simpa using! (SpecialValuesVarphi₁Limits.tendsto_varphi₁_mul_q))
      (hcont := by simpa using! (SpecialValuesAux.continuous_varphi₁.mul continuous_qH)))) t ht

lemma continuous_varphi₂ : Continuous (Dim24.varphi₂ : ℍ → ℂ) := by
  -- This is a rational combination of holomorphic modular forms; denominators are nonzero on `ℍ`.
  let f : ℍ → ℂ := fun z =>
    (-36 : ℂ) * ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) *
      ((π : ℂ) ^ (2 : ℕ) * (Δ z) ^ (2 : ℕ))⁻¹
  have hf : Continuous f := by
    have hE4 : Continuous (E₄ : ℍ → ℂ) := E₄.holo'.continuous
    have hE6 : Continuous (E₆ : ℍ → ℂ) := E₆.holo'.continuous
    have hΔ : Continuous (Δ : ℍ → ℂ) := SpecialValuesAux.continuous_Δ
    have hΔ2 : Continuous fun z : ℍ => (Δ z) ^ (2 : ℕ) := hΔ.pow 2
    have hden : Continuous fun z : ℍ => (π : ℂ) ^ (2 : ℕ) * (Δ z) ^ (2 : ℕ) :=
      continuous_const.mul hΔ2
    have hden_ne : ∀ z : ℍ, (π : ℂ) ^ (2 : ℕ) * (Δ z) ^ (2 : ℕ) ≠ 0 := by
      intro z
      refine mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)) (pow_ne_zero 2
      (Δ_ne_zero z))
    have hdenInv : Continuous fun z : ℍ => ((π : ℂ) ^ (2 : ℕ) * (Δ z) ^ (2 : ℕ))⁻¹ :=
      Continuous.inv₀ hden hden_ne
    have hpoly : Continuous fun z : ℍ =>
        (-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ) := by
      have h1 : Continuous fun z : ℍ => (-49 : ℂ) * (E₄ z) ^ (3 : ℕ) :=
        continuous_const.mul (hE4.pow 3)
      have h2 : Continuous fun z : ℍ => (25 : ℂ) * (E₆ z) ^ (2 : ℕ) :=
        continuous_const.mul (hE6.pow 2)
      simpa [add_assoc] using! h1.add h2
    have hnum : Continuous fun z : ℍ =>
        (-36 : ℂ) * ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) :=
      continuous_const.mul hpoly
    dsimp [f]; exact hnum.mul hdenInv
  assumption

lemma continuous_D : Continuous D := by
  have hψ : Continuous (ψI : ℍ → ℂ) :=
    SpherePacking.Dim24.continuous_ψI
  -- linear combination
  simpa [D, mul_assoc] using!
    (continuous_const.mul continuous_varphi₂).add (continuous_const.mul (continuous_const.mul hψ))

/-- A uniform bound for `‖D z * q z‖` on the imaginary axis `t ≥ 1`. -/
public noncomputable def CDq : ℝ :=
  Classical.choose
    (exists_bound_norm_resToImagAxis_Ici_one
      (F := fun z : ℍ => D z * q (z : ℂ))
      (l := (-((10 : ℂ) / ((117 : ℂ) * π))))
      (hF := by simpa using! tendsto_D_mul_q)
      (hcont := by simpa using! (continuous_D.mul continuous_qH)))

/-- The bound defining `CDq`, written as a lemma. -/
public lemma hCDq (t : ℝ) (ht : 1 ≤ t) :
    ‖(fun z : ℍ => D z * q (z : ℂ)).resToImagAxis t‖ ≤ CDq :=
  (Classical.choose_spec
    (exists_bound_norm_resToImagAxis_Ici_one
      (F := fun z : ℍ => D z * q (z : ℂ))
      (l := (-((10 : ℂ) / ((117 : ℂ) * π))))
      (hF := by simpa using! tendsto_D_mul_q)
      (hcont := by simpa using! (continuous_D.mul continuous_qH)))) t ht

/-- Norm of the modular parameter `q` on the imaginary-axis point `it t`. -/
public lemma norm_q_it (t : ℝ) (ht0 : 0 < t) :
    ‖q ((it t ht0 : ℍ) : ℂ)‖ = Real.exp (-2 * Real.pi * t) := by
  have him : (it t ht0).im = t := SpherePacking.Dim24.it_im t ht0
  simp [SpecialValuesVarphi₁Limits.norm_q, him]

/-- Exponential decay bound for `varphi (it t)` for `t ≥ 1`. -/
public lemma norm_varphi_it_le (t : ℝ) (ht : 1 ≤ t) :
    ‖varphi (it t (lt_of_lt_of_le (by norm_num) ht))‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  simpa [Function.resToImagAxis, ResToImagAxis, ht0] using! hCφ t ht

/-- Growth bound for `varphi₁ (it t)` for `t ≥ 1`. -/
public lemma norm_varphi₁_it_le (t : ℝ) (ht : 1 ≤ t) :
    ‖Dim24.varphi₁ (it t (lt_of_lt_of_le (by norm_num) ht))‖ ≤ Cφ1q * Real.exp (2 * Real.pi * t)
      := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  let zH : ℍ := it t ht0
  let z : ℂ := (zH : ℂ)
  have hzq : q z ≠ 0 := q_ne_zero z
  have hqInv : ‖(q z)⁻¹‖ = Real.exp (2 * Real.pi * t) := by
    have hq : ‖q z‖ = Real.exp (-2 * Real.pi * t) := by
      simpa [zH, z] using! norm_q_it t ht0
    -- `‖q⁻¹‖ = (‖q‖)⁻¹` and `exp (-a)⁻¹ = exp a`.
    calc
      ‖(q z)⁻¹‖ = (‖q z‖)⁻¹ := by simp
      _ = (Real.exp (-2 * Real.pi * t))⁻¹ := by simp [hq]
      _ = Real.exp (2 * Real.pi * t) := by
            -- invert `Real.exp_neg`
            simpa using! congrArg Inv.inv (Real.exp_neg (2 * Real.pi * t))
  have hphi1q : ‖Dim24.varphi₁ zH * q z‖ ≤ Cφ1q := by
    have haxis : ‖(fun z : ℍ => Dim24.varphi₁ z * q (z : ℂ)).resToImagAxis t‖ ≤ Cφ1q := hCφ1q t ht
    have hrepl :
        (fun z : ℍ => Dim24.varphi₁ z * q (z : ℂ)).resToImagAxis t = Dim24.varphi₁ zH * q z := by
      simpa [
        zH,
        z
      ] using! (
        resToImagAxis_eq_it (fun z => varphi₁ z * q ↑z) t ht0)
    simpa only [hrepl] using! haxis
  have hrew : Dim24.varphi₁ zH = (Dim24.varphi₁ zH * q z) * (q z)⁻¹ := by
    simp [hzq]
  calc
    ‖Dim24.varphi₁ zH‖ = ‖(Dim24.varphi₁ zH * q z) * (q z)⁻¹‖ := by
          simpa using! congrArg (fun w : ℂ => ‖w‖) hrew
    _ = ‖Dim24.varphi₁ zH * q z‖ * ‖(q z)⁻¹‖ := by simp []
    _ ≤ Cφ1q * Real.exp (2 * Real.pi * t) := by
      have := mul_le_mul_of_nonneg_right hphi1q (norm_nonneg ((q z)⁻¹))
      simpa [hqInv] using! this


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic
