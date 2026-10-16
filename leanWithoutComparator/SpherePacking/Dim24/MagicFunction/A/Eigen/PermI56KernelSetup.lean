-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI56ChangeOfVariables
import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12Integrability
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.ForMathlib.FourierPhase
import SpherePacking.ForMathlib.ComplexI


/-!
# Kernel setup for the `I₅/I₆` permutation

This file defines the kernel used to rewrite the Fourier transform of `I₅` as an iterated
integral and supplies the measurability/integrability hypotheses needed for the Fubini swap.

We introduce irreducible aliases for the relevant volume measures to avoid timeouts during `whnf`.

## Main definitions
* `PermI56.permI5Kernel`
* `PermI56.μIciOne` (and the volume aliases `PermI56.μvol`, `PermI56.μvol24`)

## Main statement
* `PermI56.integrable_permI5Kernel`
-/

open Complex Real

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.AFourier
open MeasureTheory Set Complex Real Filter
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold

noncomputable section

namespace PermI56

open Complex Real Set MeasureTheory Filter intervalIntegral
open scoped Interval
open MagicFunction.Parametrisations

attribute [measurability] SpherePacking.Dim24.measurable_varphi'

/-- The kernel used for swapping integrals in the `perm_I₅` argument. -/
@[expose] public def permI5Kernel (w : ℝ²⁴) : ℝ²⁴ × ℝ → ℂ := fun p =>
  cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) * g (‖p.1‖ ^ 2) p.2

-- A measurability-friendly version of `permI5Kernel` (replace `s ^ (-12 : ℤ)` by `(s ^ 12)⁻¹`).
private def permI5KernelMeas (w : ℝ²⁴) : ℝ²⁴ × ℝ → ℂ := fun p =>
  cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I) *
    ((-I : ℂ) * varphi' (I * (p.2 : ℂ)) * ((p.2 : ℂ) ^ (12 : ℕ))⁻¹ *
      cexp ((-π : ℂ) * ((‖p.1‖ ^ (2 : ℕ) : ℝ) : ℂ) / (p.2 : ℂ)))

/-- Alias for the Lebesgue measure on `ℝ`, kept irreducible for performance. -/
@[expose] public def μvol : Measure ℝ := (volume : Measure ℝ)

/-- Unfolding lemma for `μvol`. -/
public lemma μvol_def : μvol = (volume : Measure ℝ) := by
  rfl

-- Prevent Lean from unfolding `volume` during `whnf`, which can cause timeouts.
attribute [irreducible] μvol

/-- Alias for the Lebesgue measure on `ℝ²⁴`, kept irreducible for performance. -/
@[expose] public def μvol24 : Measure ℝ²⁴ := (volume : Measure ℝ²⁴)

/-- Unfolding lemma for `μvol24`. -/
public lemma μvol24_def : μvol24 = (volume : Measure ℝ²⁴) := by
  rfl

-- Prevent Lean from unfolding `volume` during `whnf`, which can cause timeouts.
attribute [irreducible] μvol24

/--
The restriction of `μvol` to `Set.Ici 1`, used for the tail integrals in the `I₅/I₆` argument.
-/
@[expose] public def μIciOne : Measure ℝ :=
  μvol.restrict (Ici (1 : ℝ))

/-- Unfolding lemma for `μIciOne`. -/
public lemma μIciOne_def :
    μIciOne = μvol.restrict (Ici (1 : ℝ)) := rfl

-- Prevent Lean from unfolding the restriction during `whnf`.
attribute [irreducible] μIciOne

lemma hz_I_div (s : ℝ) (hs0 : 0 < s) : 0 < ((I : ℂ) / (s : ℂ)).im := by
  simp_all

lemma integrable_phase_mul_gaussian_I_div (w : ℝ²⁴) (s : ℝ) (hs0 : 0 < s) :
    Integrable
      (fun x : ℝ²⁴ =>
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
          cexp ((-π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ)))
      μvol24 := by
  have hz : 0 < ((I : ℂ) / (s : ℂ)).im := hz_I_div s hs0
  have h :=
    integrable_phase_mul_gaussian (w := w) (z := (I : ℂ) / (s : ℂ)) hz
  have hμ :
      Integrable
        (fun x : ℝ²⁴ =>
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            cexp ((π : ℂ) * I * (‖x‖ ^ 2 : ℝ) * ((I : ℂ) / (s : ℂ))))
        μvol24 := by
    simpa [μvol24_def] using! h
  -- Simplify the Gaussian exponent using `I * (I * z) = -z`.
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, I_mul_I_mul] using! hμ

lemma measurable_permI5KernelMeas (w : ℝ²⁴) : Measurable (permI5KernelMeas w) := by
  -- Phase factor depending on `p.1`.
  have h_inner : Measurable (fun p : ℝ²⁴ × ℝ => ⟪p.1, w⟫) :=
    (measurable_fst.inner measurable_const)
  have h_phaseReal : Measurable (fun p : ℝ²⁴ × ℝ => (-2 : ℝ) * (π * ⟪p.1, w⟫)) :=
    measurable_const.mul (measurable_const.mul h_inner)
  have h_phaseArg :
      Measurable (fun p : ℝ²⁴ × ℝ => (↑((-2 : ℝ) * (π * ⟪p.1, w⟫)) : ℂ) * I) :=
    (Complex.measurable_ofReal.comp h_phaseReal).mul_const I
  have h_phase :
      Measurable (fun p : ℝ²⁴ × ℝ => cexp ((↑((-2 : ℝ) * (π * ⟪p.1, w⟫)) : ℂ) * I)) :=
    h_phaseArg.cexp
  -- `s`-dependent pieces.
  have h_sC : Measurable (fun p : ℝ²⁴ × ℝ => (p.2 : ℂ)) :=
    Complex.measurable_ofReal.comp measurable_snd
  have h_varphiC : Measurable (fun p : ℝ²⁴ × ℝ => varphi' (I * (p.2 : ℂ))) :=
    measurable_varphi'.comp (measurable_const.mul h_sC)
  have h_invPow : Measurable (fun p : ℝ²⁴ × ℝ => ((p.2 : ℂ) ^ (12 : ℕ))⁻¹) :=
    (h_sC.pow_const (12 : ℕ)).inv
  -- Gaussian factor.
  have h_norm : Measurable (fun p : ℝ²⁴ × ℝ => ‖p.1‖) :=
    (measurable_fst : Measurable (fun p : ℝ²⁴ × ℝ => p.1)).norm
  have h_normPow : Measurable (fun p : ℝ²⁴ × ℝ => ‖p.1‖ ^ (2 : ℕ)) :=
    h_norm.pow_const (2 : ℕ)
  have h_rC : Measurable (fun p : ℝ²⁴ × ℝ => ((‖p.1‖ ^ (2 : ℕ) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp h_normPow
  have h_gaussArg :
      Measurable
        (fun p : ℝ²⁴ × ℝ => (-π : ℂ) * ((‖p.1‖ ^ (2 : ℕ) : ℝ) : ℂ) / (p.2 : ℂ)) :=
    (measurable_const.mul h_rC).div h_sC
  have h_gauss :
      Measurable
        (fun p : ℝ²⁴ × ℝ =>
          cexp ((-π : ℂ) * ((‖p.1‖ ^ (2 : ℕ) : ℝ) : ℂ) / (p.2 : ℂ))) :=
    h_gaussArg.cexp
  have h_rest :
      Measurable
        (fun p : ℝ²⁴ × ℝ =>
          (-I : ℂ) * varphi' (I * (p.2 : ℂ)) * ((p.2 : ℂ) ^ (12 : ℕ))⁻¹ *
            cexp ((-π : ℂ) * ((‖p.1‖ ^ (2 : ℕ) : ℝ) : ℂ) / (p.2 : ℂ))) := by
    -- build in the same left-associative order as the definition.
    simpa [mul_assoc] using! (((measurable_const.mul h_varphiC).mul h_invPow).mul h_gauss)
  -- This is exactly the product in `permI5KernelMeas`.
  exact h_phase.mul h_rest

lemma aestronglyMeasurable_permI5Kernel (w : ℝ²⁴) :
    AEStronglyMeasurable (permI5Kernel w) (μvol24.prod μIciOne) := by
  -- `Measurable` suffices as `ℂ` is second-countable.
  have hmeas' : Measurable (permI5KernelMeas w) := by
    -- Phase factor depending on `p.1`.
    exact measurable_permI5KernelMeas w
  have hEq : permI5Kernel w = permI5KernelMeas w := by
    ext p
    -- Use `zpow_neg` to rewrite the negative power in `g`.
    have hz : (p.2 : ℂ) ^ (-12 : ℤ) = ((p.2 : ℂ) ^ (12 : ℕ))⁻¹ := by
      simpa using! (zpow_negSucc (p.2 : ℂ) 11)
    dsimp [permI5Kernel, permI5KernelMeas, g]
    -- Rewrite the power term; the rest is definitional.
    rw [hz]
  have hmeas : Measurable (permI5Kernel w) := by
    simpa [hEq] using! hmeas'
  exact hmeas.aestronglyMeasurable

lemma ae_integrable_permI5Kernel_slice (w : ℝ²⁴) :
    ∀ s : ℝ, s ∈ Ici (1 : ℝ) → Integrable (fun x : ℝ²⁴ => permI5Kernel w (x, s)) μvol24 := by
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hphaseGauss := integrable_phase_mul_gaussian_I_div (w := w) (s := s) hs0
  -- Multiply by the `s`-dependent constant factor and identify the kernel.
  let c : ℂ := (-I : ℂ) * varphi' (I * (s : ℂ)) * (s ^ (-12 : ℤ))
  have hconst : Integrable (fun x : ℝ²⁴ => c * (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
        cexp ((-π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ)))) μvol24 :=
    hphaseGauss.const_mul c
  -- Reassociate/commute to match `permI5Kernel`.
  refine hconst.congr (Filter.Eventually.of_forall ?_)
  intro x
  dsimp [c, permI5Kernel, g]
  ac_rfl

lemma neg_mul_div (a b s : ℝ) : -(a * b) / s = -(a / s) * b := by
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

lemma integrable_integral_norm_permI5Kernel (w : ℝ²⁴) :
  Integrable (fun s : ℝ => ∫ x : ℝ²⁴, ‖permI5Kernel w (x, s)‖) μIciOne := by
  -- Bound the `x`-integral by a constant multiple of `‖varphi' (I*s)‖`,
  -- using the Gaussian integral.
  rcases Dim24.VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ, hCφ⟩
  have hCφ0 : 0 ≤ Cφ := by
    have h1 := hCφ 1 (le_rfl : (1 : ℝ) ≤ 1)
    have : 0 ≤ Cφ * Real.exp (-(2 * Real.pi) * (1 : ℝ)) := le_trans (norm_nonneg _) h1
    exact nonneg_of_mul_nonneg_left this (by positivity)
  let bound : ℝ → ℝ := fun s => Cφ * Real.exp (-(2 * Real.pi) * s)
  have hbound :
      ∀ᵐ s : ℝ ∂μIciOne, ‖∫ x : ℝ²⁴, ‖permI5Kernel w (x, s)‖‖ ≤ bound s := by
    -- Work with the restricted measure explicitly.
    rw [μIciOne_def]
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs0)
    -- `‖permI5Kernel‖` ignores the phase and is controlled by the Gaussian integral.
    have hnorm :
        (fun x : ℝ²⁴ => ‖permI5Kernel w (x, s)‖) =
          fun x : ℝ²⁴ =>
            ‖(-I : ℂ) * varphi' (I * (s : ℂ)) * (s ^ (-12 : ℤ))‖ *
              ‖cexp ((-π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ))‖ := by
      funext x
      -- Factor out the `x`-dependent phase (which has norm `1`).
      have hphase : ‖cexp (↑(-2 * (π * ⟪x, w⟫)) * I)‖ = (1 : ℝ) := by
        simpa using! (SpherePacking.ForMathlib.norm_phase_eq_one (w := w) (x := x))
      dsimp [permI5Kernel, g]
      -- Reassociate the products so `norm_mul` applies.
      simp_all
    have hgauss :
        (∫ x : ℝ²⁴,
              ‖cexp (- (↑π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ))‖) =
            (s ^ 12 : ℝ) := by
      -- Reduce to the real Gaussian integral.
      have hb : 0 < Real.pi / s := div_pos Real.pi_pos hs0
      have hreal :=
        (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℝ²⁴) (b := Real.pi / s) hb)
      have hnorm :
          (fun x : ℝ²⁴ => ‖cexp (- (↑π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ))‖) =
            fun x : ℝ²⁴ => rexp (-(Real.pi / s) * ‖x‖ ^ 2) := by
        funext x
        have hsR : s ≠ 0 := ne_of_gt hs0
        have hre :
            ((- (↑π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ))).re =
              (-(Real.pi / s) * ‖x‖ ^ 2) := by
          have hcoe :
              (- (↑π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ)) =
                (((-(Real.pi) * (‖x‖ ^ (2 : ℕ))) / s : ℝ) : ℂ) := by
            -- everything is `ofReal`, so division and multiplication commute with coercions
            calc
              (- (↑π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ)) =
                  (((-(Real.pi) * (‖x‖ ^ (2 : ℕ)) : ℝ) : ℂ) / (s : ℂ)) := by
                    simp
              _ = (((-(Real.pi) * (‖x‖ ^ (2 : ℕ)) / s : ℝ) : ℂ)) := by
                    simp
          -- now take real parts and finish the scalar algebra
          have hsR : s ≠ 0 := ne_of_gt hs0
          calc
            ((- (↑π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ))).re =
                (( (-(Real.pi) * (‖x‖ ^ (2 : ℕ)) / s : ℝ) : ℂ)).re := by
                  simp
            _ = (-(Real.pi) * (‖x‖ ^ (2 : ℕ)) / s) := by
                  rfl
            _ = (-(Real.pi / s) * ‖x‖ ^ 2) := by
                  -- rewrite `π / s * a` as `π * a / s` and move the negation across the division
                  simp [div_mul_eq_mul_div, neg_div, pow_two]
        -- `‖cexp z‖ = exp z.re`; keep the real part as `(_).re` and rewrite using `hre`.
        simp only [Complex.norm_exp]
        rw [hre]
      have hsR : s ≠ 0 := ne_of_gt hs0
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      have hpis : Real.pi / (Real.pi / s) = s := by
        field_simp [hpi, hsR]
      -- Put everything together.
      have hnorm_int :
          (∫ x : ℝ²⁴, ‖cexp (- (↑π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ))‖) =
            ∫ x : ℝ²⁴, rexp (-(Real.pi / s) * ‖x‖ ^ 2) :=
        congrArg (fun F : ℝ²⁴ → ℝ => ∫ x : ℝ²⁴, F x) hnorm
      -- Rewrite the Gaussian lemma with our normal form and simplify the exponent `24 / 2 = 12`.
      calc
        (∫ x : ℝ²⁴, ‖cexp (- (↑π : ℂ) * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) / (s : ℂ))‖) =
            ∫ x : ℝ²⁴, rexp (-(Real.pi / s) * ‖x‖ ^ 2) := by
              simpa using! hnorm_int
        _ = (Real.pi / (Real.pi / s)) ^ (↑(Module.finrank ℝ ℝ²⁴) / 2 : ℝ) := by
              simpa [mul_assoc] using! hreal
        _ = s ^ (↑(Module.finrank ℝ ℝ²⁴) / 2 : ℝ) := by
              simp [hpis]
        _ = s ^ (12 : ℝ) := by
              norm_num
        _ = (s ^ 12 : ℝ) :=
              Real.rpow_natCast s 12
    have hvarphi :
        ‖varphi' (I * (s : ℂ))‖ ≤ bound s := by
      -- Rewrite `varphi' (I*s)` as `varphi.resToImagAxis s` (since `s ≥ 1`).
      have : ‖varphi.resToImagAxis s‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * s) := hCφ s hs
      simpa [bound, varphi', Function.resToImagAxis, ResToImagAxis, hs0.le, mul_comm] using! this
    have : ‖∫ x : ℝ²⁴, ‖permI5Kernel w (x, s)‖‖ ≤ bound s := by
      -- crude bound: use `‖s^(-12)‖ * s^12 = 1` for `s > 0` and `‖-I‖ = 1`.
      -- The proof is not performance-critical; `simp` handles the algebra.
      have hnonneg : 0 ≤ ∫ x : ℝ²⁴, ‖permI5Kernel w (x, s)‖ := by
        exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
      -- Turn the estimate into a scalar one without `‖·‖` on the integral.
      have habs :
          ‖∫ x : ℝ²⁴, ‖permI5Kernel w (x, s)‖‖ = ∫ x : ℝ²⁴, ‖permI5Kernel w (x, s)‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      -- Use the explicit norm factorization.
      -- Reduce to an inequality without `‖·‖` (the integral is nonnegative).
      rw [habs]
      rw [hnorm]
      -- Pull out constants from the integral.
      have :
          (∫ x : ℝ²⁴,
              ‖(-I : ℂ) * varphi' (I * (s : ℂ)) * (s ^ (-12 : ℤ))‖ *
                ‖cexp (- (↑π : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ) / (s : ℂ))‖)
            =
            ‖(-I : ℂ) * varphi' (I * (s : ℂ)) * (s ^ (-12 : ℤ))‖ *
              ∫ x : ℝ²⁴, ‖cexp (- (↑π : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ) / (s : ℂ))‖ := by
        exact
          (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ²⁴))
            (r := ‖(-I : ℂ) * varphi' (I * (s : ℂ)) * (s ^ (-12 : ℤ))‖)
            (f := fun x : ℝ²⁴ => ‖cexp (- (↑π : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ) / (s : ℂ))‖))
      rw [this, hgauss]
      -- Cancel `s^(-12)` against `s^12` and apply the `varphi` bound.
      have hs_ne0 : (s : ℝ) ≠ 0 := ne_of_gt hs0
      have hcancel : ‖(s ^ (-12 : ℤ) : ℂ)‖ * (s ^ 12 : ℝ) = 1 := by
        have hs12_ne0 : (s ^ 12 : ℝ) ≠ 0 := pow_ne_zero 12 hs_ne0
        -- Simplify the goal to `(s ^ 12)⁻¹ * s ^ 12`, then close with `inv_mul_cancel₀`.
        simp only [Int.reduceNeg, zpow_neg, norm_inv, norm_zpow, norm_real, norm_eq_abs]
        simpa [abs_of_pos hs0] using! (inv_mul_cancel₀ hs12_ne0)
      -- Finish with `‖varphi'‖ ≤ bound`.
      -- (A lightweight bound; we only need integrability, not sharp constants.)
      have hbound' :
          ‖(-I : ℂ) * varphi' (I * (s : ℂ)) * (s ^ (-12 : ℤ))‖ * (s ^ 12 : ℝ) ≤ bound s := by
        calc
          ‖(-I : ℂ) * varphi' (I * (s : ℂ)) * (s ^ (-12 : ℤ))‖ * (s ^ 12 : ℝ)
              = ‖(-I : ℂ) * varphi' (I * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖ * (s ^ 12 : ℝ) := by
                  -- pull the `s`-dependent factor out of the norm
                  simp [mul_assoc]
          _ = ‖(-I : ℂ) * varphi' (I * (s : ℂ))‖ * (‖(s ^ (-12 : ℤ) : ℂ)‖ * (s ^ 12 : ℝ)) := by
                simp [mul_assoc]
          _ = ‖(-I : ℂ) * varphi' (I * (s : ℂ))‖ := by
                have h :=
                  congrArg (fun t : ℝ => ‖(-I : ℂ) * varphi' (I * (s : ℂ))‖ * t) hcancel
                simpa [mul_assoc] using! h
          _ = ‖varphi' (I * (s : ℂ))‖ := by
                -- `‖-I‖ = 1`
                simp
          _ ≤ bound s := hvarphi
      exact hbound'
    exact this
  -- Use `Integrable.mono` with the exponential majorant.
  have hmajor : Integrable bound μIciOne := by
    -- `bound` is integrable on `Ici 1` because it decays exponentially.
    have : IntegrableOn (fun s : ℝ => bound s) (Ici (1 : ℝ)) volume := by
      have h :
          IntegrableOn (fun s : ℝ => rexp ((-(2 * Real.pi)) * s)) (Ici (1 : ℝ)) volume := by
        refine (integrableOn_Ici_iff_integrableOn_Ioi).2 ?_
        simpa [mul_assoc, mul_left_comm, mul_comm] using!
          (integrableOn_exp_mul_Ioi (a := (-(2 * Real.pi) : ℝ))
            (ha := by linarith [Real.pi_pos]) (c := (1 : ℝ)))
      simpa [bound] using! (h.const_mul Cφ)
    simpa [μIciOne_def, μvol_def, IntegrableOn] using! this
  refine Integrable.mono' hmajor ?_ ?_
  · -- `s ↦ ∫ x, ‖permI5Kernel w (x, s)‖` is (ae-)strongly measurable, as it is the integral of a
    -- strongly measurable function on the product.
    have hEq : permI5Kernel w = permI5KernelMeas w := by
      ext p
      have hz : (p.2 : ℂ) ^ (-12 : ℤ) = ((p.2 : ℂ) ^ (12 : ℕ))⁻¹ := by
        simpa using! (zpow_negSucc (p.2 : ℂ) 11)
      dsimp [permI5Kernel, permI5KernelMeas, g]
      rw [hz]
    have hmeas : Measurable (fun p : ℝ²⁴ × ℝ => ‖permI5KernelMeas w p‖) := by
      dsimp [permI5KernelMeas]
      measurability
    have hsm : StronglyMeasurable (fun p : ℝ²⁴ × ℝ => ‖permI5KernelMeas w p‖) :=
      hmeas.stronglyMeasurable
    have hsm_int :
        StronglyMeasurable (fun s : ℝ => ∫ x : ℝ²⁴, ‖permI5KernelMeas w (x, s)‖) :=
      hsm.integral_prod_left' (μ := (volume : Measure ℝ²⁴))
    have hfun :
        (fun s : ℝ => ∫ x : ℝ²⁴, ‖permI5Kernel w (x, s)‖) =
          fun s : ℝ => ∫ x : ℝ²⁴, ‖permI5KernelMeas w (x, s)‖ := by
      funext s
      simp [hEq]
    simpa [hfun] using! hsm_int.aestronglyMeasurable
  · exact hbound

/-- Product integrability of `permI5Kernel w` on `ℝ²⁴ × Set.Ici 1`. -/
public lemma integrable_permI5Kernel (w : ℝ²⁴) :
    Integrable (permI5Kernel w) (μvol24.prod μIciOne) := by
  haveI : MeasureTheory.SFinite μvol24 := by
    -- unfold the volume measure alias for the instance search
    rw [μvol24_def]
    infer_instance
  haveI : MeasureTheory.SFinite μvol := by
    rw [μvol_def]
    infer_instance
  haveI : MeasureTheory.SFinite μIciOne := by
    -- unfold the restriction measure for the instance search
    rw [μIciOne_def]
    infer_instance
  have hmeas : AEStronglyMeasurable (permI5Kernel w) (μvol24.prod μIciOne) :=
    aestronglyMeasurable_permI5Kernel (w := w)
  refine (MeasureTheory.integrable_prod_iff' (μ := μvol24) (ν := μIciOne) hmeas).2 ?_
  refine ⟨?_, ?_⟩
  · -- Convert the pointwise slice integrability into an AE statement on the restricted measure.
    rw [μIciOne_def]
    refine (ae_restrict_iff' measurableSet_Ici).2 <| Filter.Eventually.of_forall ?_
    intro s hs
    exact ae_integrable_permI5Kernel_slice (w := w) s hs
  · simpa [μvol24_def] using! (integrable_integral_norm_permI5Kernel (w := w))


end PermI56

end

end SpherePacking.Dim24.AFourier
