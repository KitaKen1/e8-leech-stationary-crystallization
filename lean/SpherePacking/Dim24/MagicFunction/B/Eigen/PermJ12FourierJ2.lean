-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ12FourierJ1
import SpherePacking.Contour.PermJ12FourierCurveIntegral
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.Integration.FubiniIoc01
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.Dim24.ModularForms.Psi.Relations
import SpherePacking.Integration.UpperHalfPlaneComp


/-!
# Fourier transform of `J₂` as a curve integral

This file proves the curve-integral formula for the Fourier transform of the contour piece `J₂`.
As in the `J₁` case, we introduce an auxiliary kernel and use a Fubini argument to reduce to a
Gaussian Fourier transform computation.

## Main statements
* `fourier_J₂_eq_curveIntegral`
-/

open scoped FourierTransform
open scoped Real

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.BFourier
open MeasureTheory Set Filter
open SpherePacking.ForMathlib
open SpherePacking.Contour
open SpherePacking.Integration
open scoped Interval RealInnerProductSpace UpperHalfPlane

noncomputable section

open MagicFunction


section PermJ12

def permJ2Kernel (w : ℝ²⁴) : ℝ²⁴ × ℝ → ℂ :=
  fun p =>
    Complex.exp (↑(-2 * (π * ⟪p.1, w⟫)) * Complex.I) *
      (ψT' (z₂line p.2) *
        Complex.exp ((π : ℂ) * Complex.I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)))

lemma phase_mul_J₂'_eq_integral_permJ2Kernel (w x : ℝ²⁴) :
    Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) * RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ, permJ2Kernel w (x, t) ∂μIoc01 := by
  have hJ₂μ :
      RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) =
        ∫ t : ℝ,
          ψT' (z₂line t) *
            Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t)) ∂μIoc01 := by
    simpa [μIoc01] using! (J₂'_eq_integral_z₂line (r := (‖x‖ ^ (2 : ℕ))))
  calc
    Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) * RealIntegrals.J₂' (‖x‖ ^ (2 : ℕ)) =
        Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
          ∫ t : ℝ,
            ψT' (z₂line t) *
              Complex.exp
                  ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t))
                ∂μIoc01 := by
          simp [hJ₂μ, mul_assoc]
    _ =
        ∫ t : ℝ,
          Complex.exp (↑(-2 * (Real.pi * ⟪x, w⟫)) * Complex.I) *
            (ψT' (z₂line t) *
                Complex.exp
                  ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z₂line t))) ∂μIoc01 := by
          exact Eq.symm
            (integral_const_mul (Complex.exp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I)) fun a =>
              ψT' (z₂line a) * Complex.exp (↑π * Complex.I * ↑(‖x‖ ^ 2) * z₂line a))
    _ = ∫ t : ℝ, permJ2Kernel w (x, t) ∂μIoc01 := by
          simp [permJ2Kernel, mul_assoc]

lemma norm_permJ2Kernel (w x : ℝ²⁴) (t : ℝ) :
    ‖permJ2Kernel w (x, t)‖ = ‖ψT' (z₂line t)‖ * Real.exp (-(π * ‖x‖ ^ 2)) := by
  have hgauss :
      ‖Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t))‖ =
        Real.exp (-(π * ‖x‖ ^ 2)) := by
    simpa [z₂line, neg_mul, mul_assoc, mul_left_comm, mul_comm] using!
      (SpherePacking.ForMathlib.norm_cexp_pi_mul_I_mul_sq (V := ℝ²⁴) (z := z₂line t) (x := x))
  dsimp [permJ2Kernel]
  rw [norm_mul, norm_phase_eq_one (w := w) (x := x)]
  simp_all

lemma integrable_permJ2Kernel_slice (w : ℝ²⁴) (t : ℝ) :
    Integrable (fun x : ℝ²⁴ ↦ permJ2Kernel w (x, t)) (volume : Measure ℝ²⁴) := by
  have hz : 0 < (z₂line t).im := by simp [z₂line]
  have hgauss :
      Integrable (fun x : ℝ²⁴ ↦
          Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t)))
        (volume : Measure ℝ²⁴) :=
    SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul (z := z₂line t) hz
  have hgauss' :
      Integrable (fun x : ℝ²⁴ ↦
          ψT' (z₂line t) *
            Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t)))
        (volume : Measure ℝ²⁴) := by
    simpa [mul_assoc] using! hgauss.const_mul (ψT' (z₂line t))
  simpa [permJ2Kernel, mul_assoc] using!
    hgauss'.bdd_mul (aestronglyMeasurable_phase (w := w)) (ae_norm_phase_le_one (w := w))

lemma ae_integrable_permJ2Kernel_slice (w : ℝ²⁴) :
    ∀ᵐ t : ℝ ∂μIoc01, Integrable (fun x : ℝ²⁴ ↦ permJ2Kernel w (x, t)) (volume : Measure ℝ²⁴) := by
  exact Filter.Eventually.of_forall fun t => integrable_permJ2Kernel_slice (w := w) (t := t)

lemma integral_permJ2Kernel_x (w : ℝ²⁴) (t : ℝ) :
    (∫ x : ℝ²⁴, permJ2Kernel w (x, t)) = Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
  have hz : 0 < (z₂line t).im := by simp [z₂line]
  let c : ℂ := ψT' (z₂line t)
  have hfactor :
      (fun x : ℝ²⁴ ↦ permJ2Kernel w (x, t)) =
        fun x : ℝ²⁴ ↦
          c *
            (Complex.exp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I) *
              Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t))) := by
    funext x
    dsimp [permJ2Kernel, c]
    simp [mul_assoc, mul_left_comm, mul_comm]
  calc
    (∫ x : ℝ²⁴, permJ2Kernel w (x, t)) =
        ∫ x : ℝ²⁴,
          c *
            (Complex.exp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I) *
              Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₂line t))) := by
          simpa using!
            congrArg (fun F : ℝ²⁴ → ℂ => ∫ x : ℝ²⁴, F x) hfactor
    _ =
        c * ((((Complex.I : ℂ) / (z₂line t)) ^ (12 : ℕ)) *
          Complex.exp ((π : ℂ) * Complex.I * (‖w‖ ^ 2 : ℝ) * (-1 / (z₂line t)))) := by
          simpa using!
            (SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
              (k := 12) (w := w) (z := z₂line t) hz (c := c))
    _ = Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
          simp [c, Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm]

lemma continuous_ψT'_z₂line : Continuous fun t : ℝ => ψT' (z₂line t) := by
  have hz2 : Continuous z₂line :=
    continuous_z₂line
  refine
    SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
      (ψT := ψT) (ψT' := ψT') (SpherePacking.Dim24.continuous_ψT)
      (z := z₂line) hz2 (fun t => by simp [z₂line]) ?_
  intro t
  simp [ψT', z₂line]

lemma exists_bound_norm_ψT'_z₂line :
    ∃ M, ∀ t ∈ Ioc (0 : ℝ) 1, ‖ψT' (z₂line t)‖ ≤ M := by
  rcases
      SpherePacking.Integration.exists_bound_norm_uIoc_zero_one_of_continuous
        (f := fun t : ℝ => ψT' (z₂line t)) continuous_ψT'_z₂line with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  grind only [= uIoc_of_le]

lemma integrable_integral_norm_permJ2Kernel (w : ℝ²⁴) :
    Integrable (fun t : ℝ ↦ ∫ x : ℝ²⁴, ‖permJ2Kernel w (x, t)‖) μIoc01 := by
  rcases exists_bound_norm_ψT'_z₂line with ⟨Mψ, hMψ⟩
  let Cgauss : ℝ := ∫ x : ℝ²⁴, Real.exp (-(π * ‖x‖ ^ 2))
  have hCgauss : 0 ≤ Cgauss := by
    have : 0 ≤ fun x : ℝ²⁴ => Real.exp (-(π * ‖x‖ ^ 2)) := by
      intro x; positivity
    simpa [Cgauss] using! MeasureTheory.integral_nonneg this
  let g : ℝ → ℝ := fun t => ‖ψT' (z₂line t)‖ * Cgauss
  have hAE :
      (fun t : ℝ ↦ ∫ x : ℝ²⁴, ‖permJ2Kernel w (x, t)‖) =ᵐ[μIoc01] g := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
    intro t ht
    have hfun :
        (fun x : ℝ²⁴ => ‖permJ2Kernel w (x, t)‖) =
          fun x : ℝ²⁴ => ‖ψT' (z₂line t)‖ * Real.exp (-(π * ‖x‖ ^ 2)) := by
      funext x
      simpa [mul_assoc] using! (norm_permJ2Kernel (w := w) (x := x) (t := t))
    have hInt :
        (∫ x : ℝ²⁴, ‖permJ2Kernel w (x, t)‖) = ‖ψT' (z₂line t)‖ * Cgauss := by
      simpa [hfun, Cgauss, mul_assoc] using!
        (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ²⁴))
          (r := ‖ψT' (z₂line t)‖)
          (f := fun x : ℝ²⁴ => Real.exp (-(π * ‖x‖ ^ 2))))
    simpa [g] using! hInt
  have hmeas_g : AEStronglyMeasurable g μIoc01 := by
    have hmeas : Measurable g := (continuous_ψT'_z₂line.norm.mul continuous_const).measurable
    exact hmeas.aestronglyMeasurable
  have hg_bound : ∀ᵐ t : ℝ ∂μIoc01, ‖g t‖ ≤ (Mψ : ℝ) * Cgauss := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
    intro t ht
    have hψle : ‖ψT' (z₂line t)‖ ≤ Mψ := hMψ t ht
    have hgt0 : 0 ≤ g t := mul_nonneg (norm_nonneg _) hCgauss
    have hnorm_g : ‖g t‖ = g t := by simp [Real.norm_eq_abs, abs_of_nonneg hgt0]
    have : g t ≤ (Mψ : ℝ) * Cgauss := mul_le_mul_of_nonneg_right hψle hCgauss
    simpa [hnorm_g] using! this
  have hmajor : Integrable (fun _t : ℝ => (Mψ : ℝ) * Cgauss) μIoc01 := by
    simpa using! (integrable_const (α := ℝ) (μ := μIoc01) ((Mψ : ℝ) * Cgauss))
  have hg_int : Integrable g μIoc01 := Integrable.mono' hmajor hmeas_g hg_bound
  exact hg_int.congr hAE.symm

lemma integrable_permJ2Kernel (w : ℝ²⁴) :
    Integrable (permJ2Kernel w) ((volume : Measure ℝ²⁴).prod μIoc01) := by
  let sProd : Set (ℝ²⁴ × ℝ) := (Set.univ : Set ℝ²⁴) ×ˢ (Ioc (0 : ℝ) 1)
  have hsProd : MeasurableSet sProd := by
    simpa [sProd] using! (MeasurableSet.univ.prod measurableSet_Ioc)
  have hmeas : AEStronglyMeasurable (permJ2Kernel w) ((volume : Measure ℝ²⁴).prod μIoc01) := by
    let μProd : Measure (ℝ²⁴ × ℝ) := (volume : Measure ℝ²⁴).prod (volume : Measure ℝ)
    have hμ :
        ((volume : Measure ℝ²⁴).prod μIoc01) = μProd.restrict sProd := by
      simpa [μProd, sProd] using!
        (SpherePacking.Integration.prod_muIoc01_eq_restrict (μ := (volume : Measure ℝ²⁴)))
    have hcont : ContinuousOn (permJ2Kernel w) sProd := by
      have hphase :
          Continuous fun p : ℝ²⁴ × ℝ => Complex.exp (↑(-2 * π * ⟪p.1, w⟫) * Complex.I) := by
        have hinner : Continuous fun p : ℝ²⁴ × ℝ => (⟪p.1, w⟫ : ℝ) := by
          simpa using! (continuous_fst.inner continuous_const)
        have hreal : Continuous fun p : ℝ²⁴ × ℝ => (-2 * π) * (⟪p.1, w⟫ : ℝ) :=
          continuous_const.mul hinner
        have harg :
            Continuous fun p : ℝ²⁴ × ℝ =>
              (↑(((-2 * π) * (⟪p.1, w⟫ : ℝ))) : ℂ) * (Complex.I : ℂ) := by
          exact (Complex.continuous_ofReal.comp hreal).mul continuous_const
        simpa [mul_assoc] using! (Complex.continuous_exp.comp harg)
      have hψ :
          ContinuousOn (fun p : ℝ²⁴ × ℝ => ψT' (z₂line p.2)) sProd := by
        have hcont : Continuous fun p : ℝ²⁴ × ℝ => ψT' (z₂line p.2) :=
          continuous_ψT'_z₂line.comp continuous_snd
        exact hcont.continuousOn
      have hgauss :
          Continuous fun p : ℝ²⁴ × ℝ =>
            Complex.exp ((π : ℂ) * Complex.I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)) := by
        have hnormsq : Continuous fun p : ℝ²⁴ × ℝ => (‖p.1‖ ^ 2 : ℝ) :=
          (continuous_fst.norm.pow 2)
        have hz₂line : Continuous z₂line :=
          continuous_z₂line
        have hz : Continuous fun p : ℝ²⁴ × ℝ => z₂line p.2 := hz₂line.comp continuous_snd
        have harg' :
            Continuous fun p : ℝ²⁴ × ℝ =>
              (π : ℂ) * Complex.I * (((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2)) := by
          exact
            (continuous_const.mul continuous_const).mul
              ((Complex.continuous_ofReal.comp hnormsq).mul hz)
        simpa [mul_assoc] using! (Complex.continuous_exp.comp harg')
      have hmul :
          ContinuousOn
            (fun p : ℝ²⁴ × ℝ =>
              (ψT' (z₂line p.2)) *
                Complex.exp ((π : ℂ) * Complex.I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2))) sProd :=
        hψ.mul hgauss.continuousOn
      refine (hphase.continuousOn.mul hmul).congr ?_
      intro p _hp
      simp [permJ2Kernel, mul_assoc]
    have hker : AEStronglyMeasurable (permJ2Kernel w) (μProd.restrict sProd) := by
      simpa [μProd] using! (hcont.aestronglyMeasurable (μ := μProd) (s := sProd) hsProd)
    simpa [hμ] using! hker
  refine (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure ℝ²⁴)) (ν := μIoc01) hmeas).2 ?_
  exact ⟨ae_integrable_permJ2Kernel_slice (w := w), integrable_integral_norm_permJ2Kernel (w := w)⟩

private lemma integral_permJ2Kernel_x_ae (w : ℝ²⁴) :
    (fun t : ℝ => (∫ x : ℝ²⁴, permJ2Kernel w (x, t) ∂(volume : Measure _))) =ᵐ[μIoc01]
      fun t : ℝ => Ψ₁_fourier (‖w‖ ^ 2) (z₂line t) := by
  change
    (∀ᵐ t : ℝ ∂μIoc01,
      (∫ x : ℝ²⁴, permJ2Kernel w (x, t) ∂(volume : Measure _)) =
        Ψ₁_fourier (‖w‖ ^ 2) (z₂line t))
  refine Filter.Eventually.of_forall ?_
  intro t
  simpa using! (integral_permJ2Kernel_x (w := w) (t := t))

/-- Fourier transform of `J₂` as a curve integral along the segment from `-1 + i` to `i`. -/
public lemma fourier_J₂_eq_curveIntegral (w : ℝ²⁴) :
    (𝓕 (J₂ : ℝ²⁴ → ℂ)) w =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ 2)) z) := by
  simpa using! SpherePacking.Contour.fourier_J₂_eq_curveIntegral_of
    (fun x => by simpa using! (J₂_apply (x := x)))
    phase_mul_J₂'_eq_integral_permJ2Kernel integrable_permJ2Kernel integral_permJ2Kernel_x_ae
    (fun w' => by
      simpa using! (integral_muIoc01_z₂line (F := Ψ₁_fourier (‖w'‖ ^ 2)))) w


end PermJ12


end
end SpherePacking.Dim24.BFourier
