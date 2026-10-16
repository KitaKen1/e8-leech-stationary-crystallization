-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSDecay
import SpherePacking.ForMathlib.ContDiffOnByDeriv
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.Integration.J6Integrable
import SpherePacking.Integration.SmoothIntegralIciOne
public import SpherePacking.Integration.Measure


/-!
# Differentiating under the `J₆'` tail integral

The tail term `J₆'` is an integral over `t ∈ [1,∞)` on the imaginary axis. We package the
parametrized integrand `gN n x t` and the integral functional `F n x := ∫ gN n x t dt` on the
domain `s := (-1, ∞)`, where differentiation under the integral is justified.

## Main definitions
* `Schwartz.J6Smooth.s`, `Schwartz.J6Smooth.coeff`, `Schwartz.J6Smooth.g`, `Schwartz.J6Smooth.gN`
* `Schwartz.J6Smooth.F`, `Schwartz.J6Smooth.G`

## Main statements
* `Schwartz.J6Smooth.hasDerivAt_F`
* `Schwartz.J6Smooth.deriv_G`
-/

noncomputable section

namespace SpherePacking.Dim24.Schwartz.J6Smooth

open scoped Topology

open Complex Real Set MeasureTheory Filter
open PsiExpBounds

open SpherePacking.Integration (μIciOne)

/-- Domain of differentiability for the tail integral, namely `(-1,∞)`. -/
@[expose] public def s : Set ℝ := Ioi (-1 : ℝ)

/-- The domain `s = (-1,∞)` is open. -/
public lemma isOpen_s : IsOpen s := by
  simpa [s] using! (isOpen_Ioi : IsOpen (Ioi (-1 : ℝ)))

/-- Coefficient in the exponential kernel for the parametrized `J₆'` integrand. -/
@[expose] public def coeff (t : ℝ) : ℂ := (-Real.pi * t : ℂ)

/-- The integrand defining `J₆'`, written in the variable `t ∈ [1,∞)`. -/
@[expose] public def g (x t : ℝ) : ℂ :=
  (Complex.I : ℂ) * (ψS.resToImagAxis t * cexp ((x : ℂ) * coeff t))

/-- The `n`th differentiated integrand for `J₆'`, used for differentiation under the integral. -/
@[expose] public def gN (n : ℕ) (x t : ℝ) : ℂ :=
  (coeff t) ^ n * g x t

/-! ## Measurability and integrability infrastructure -/

lemma g_continuousOn (x : ℝ) : ContinuousOn (g x) (Ici (1 : ℝ)) := by
  have hψS : Continuous ψS := SpherePacking.Dim24.PsiRewrites.continuous_ψS
  have hψ : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)) :=
    Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) hψS
  have hcoeff0 : Continuous fun t : ℝ ↦ coeff t := by
    have h :
        Continuous (fun t : ℝ ↦ (-Real.pi : ℂ) * (t : ℂ)) :=
      ((continuous_const : Continuous (fun _t : ℝ ↦ (-Real.pi : ℂ))).mul Complex.continuous_ofReal)
    simpa [coeff, mul_assoc] using! h
  have hcoeff : Continuous fun t : ℝ ↦ (x : ℂ) * coeff t :=
    (continuous_const.mul hcoeff0)
  have hexp : ContinuousOn (fun t : ℝ ↦ cexp ((x : ℂ) * coeff t)) (Ici (1 : ℝ)) :=
    (hcoeff.cexp).continuousOn
  have hψexp :
      ContinuousOn (fun t : ℝ ↦ ψS.resToImagAxis t * cexp ((x : ℂ) * coeff t)) (Ici (1 : ℝ)) :=
    hψ.mul hexp
  have hI : ContinuousOn (fun _t : ℝ ↦ (Complex.I : ℂ)) (Ici (1 : ℝ)) := continuousOn_const
  simpa [g, mul_assoc] using! hI.mul hψexp

lemma g_measurable (x : ℝ) :
    AEStronglyMeasurable (g x) μIciOne := by
  have hmeas :
      AEStronglyMeasurable (g x) ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ)) ?_ measurableSet_Ici
    simpa using! g_continuousOn x
  simpa [μIciOne] using! hmeas

/-! ### Measurability -/

/-- Measurability of the differentiated integrand `gN n x` on the tail domain `t ∈ [1,∞)`. -/
public lemma gN_measurable (n : ℕ) (x : ℝ) :
    AEStronglyMeasurable (gN n x) μIciOne := by
  have hcoeff0 : Continuous fun t : ℝ ↦ coeff t := by
    have h :
        Continuous (fun t : ℝ ↦ (-Real.pi : ℂ) * (t : ℂ)) :=
      ((continuous_const : Continuous (fun _t : ℝ ↦ (-Real.pi : ℂ))).mul Complex.continuous_ofReal)
    simpa [coeff, mul_assoc] using! h
  have hcoeff_on : ContinuousOn (fun t : ℝ ↦ (coeff t) ^ n) (Ici (1 : ℝ)) :=
    (hcoeff0.pow n).continuousOn
  have hg : ContinuousOn (g x) (Ici (1 : ℝ)) := g_continuousOn x
  have hmeas :
      AEStronglyMeasurable (gN n x) ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ)) ?_ measurableSet_Ici
    simpa [gN] using! hcoeff_on.mul hg
  simpa [μIciOne] using! hmeas

/-! ### Basic bounds -/

/-- Explicit norm identity for the kernel coefficient `coeff` on `t ∈ [1,∞)`. -/
public lemma coeff_norm (t : ℝ) (ht : t ∈ Ici (1 : ℝ)) : ‖coeff t‖ = Real.pi * t := by
  have ht0 : 0 ≤ t := le_trans (by simp : (0 : ℝ) ≤ 1) ht
  simp [coeff, Complex.norm_real, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht0, mul_comm]

/-! ### Kernel bound -/

/-- A basic bound on `‖g x t‖` by separating the `ψS` and exponential factors. -/
public lemma g_norm_bound (x : ℝ) (t : ℝ) :
    ‖g x t‖ ≤ ‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t) := by
  have hcexp : ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t) := by
    have harg : (x : ℂ) * coeff t = (-Real.pi * x * t : ℂ) := by
      simp [coeff, mul_left_comm, mul_comm]
    calc
      ‖cexp ((x : ℂ) * coeff t)‖ = ‖cexp (-Real.pi * x * t : ℂ)‖ := by simp [harg]
      _ = Real.exp ((-Real.pi * x * t : ℂ).re) := by
            simpa using! (Complex.norm_exp (-Real.pi * x * t : ℂ))
      _ = Real.exp (-Real.pi * x * t) := by simp
  have hEq : ‖g x t‖ = ‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t) := by
    simp [g, hcexp, mul_left_comm, mul_comm]
  exact le_of_eq hEq

lemma gN_integrable (n : ℕ) (x : ℝ) (hx : x ∈ s) : Integrable (gN n x) μIciOne := by
  have hx' : -1 < x := by simpa [s] using! hx
  have hmeas0 : AEStronglyMeasurable (gN n x) μIciOne := gN_measurable (n := n) (x := x)
  let f : ℝ → ℂ := SpherePacking.Integration.gN_J6_integrand ψS.resToImagAxis n x
  have hf : gN n x = f := by
    funext t
    simp [gN, g, coeff, f, SpherePacking.Integration.gN_J6_integrand, mul_left_comm, mul_comm]
  have hmeas : AEStronglyMeasurable f ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
    have hmeas0' :
        AEStronglyMeasurable (gN n x) ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
      simpa [μIciOne] using! hmeas0
    simpa [hf] using! hmeas0'
  have hInt :=
    (SpherePacking.Integration.integrable_gN_J6 (f := ψS.resToImagAxis)
      (hBound := PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one)
      (n := n) (x := x) hx' (hmeas := by simpa [f] using! hmeas))
  assumption

/-! ## Integral functionals -/

/-- The integral functional `F n x := ∫_{t∈[1,∞)} gN n x t dt`. -/
@[expose] public def F (n : ℕ) (x : ℝ) : ℂ := ∫ t in Ici (1 : ℝ), gN n x t

/--
Differentiating `F n` in `x` brings down a factor `coeff t`.
In particular, `F n` has derivative `F (n + 1)`.
-/
public lemma hasDerivAt_F (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    HasDerivAt (fun y : ℝ => F n y) (F (n + 1) x) x := by
  have hx' : (-1 : ℝ) < x := by simpa [s] using! hx
  have exists_bound :
      ∃ C, ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤
        C * Real.exp (-(Real.pi * (1 : ℝ)) * t) := by
    simpa [one_mul, mul_assoc] using! PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one
  have hInt : Integrable (gN n x) μIciOne := gN_integrable (n := n) (x := x) hx
  simpa [F, μIciOne, gN, g, coeff,
    SpherePacking.Integration.μIciOne,
    SpherePacking.Integration.SmoothIntegralIciOne.gN,
    SpherePacking.Integration.SmoothIntegralIciOne.g,
    SpherePacking.Integration.SmoothIntegralIciOne.coeff] using!
    (SpherePacking.Integration.SmoothIntegralIciOne.hasDerivAt_integral_gN
      (hf := ψS.resToImagAxis) (shift := (1 : ℝ)) (hshift := (by simp))
      (exists_bound_norm_hf := exists_bound)
      (gN_measurable := fun n x => by
        simpa [μIciOne, gN, g, coeff,
          SpherePacking.Integration.μIciOne,
          SpherePacking.Integration.SmoothIntegralIciOne.gN,
          SpherePacking.Integration.SmoothIntegralIciOne.g,
          SpherePacking.Integration.SmoothIntegralIciOne.coeff] using!
          (gN_measurable (n := n) (x := x)))
      (n := n) (x := x) hx' (hF_int := by
        assumption))

-- Incorporate the outer constant factor from the definition of `J₆'`.
/-- The rescaled tail integral functional `G n x := (-2) * F n x`, matching `RealIntegrals.J₆'`. -/
@[expose] public def G (n : ℕ) (x : ℝ) : ℂ := (-2 : ℂ) * F n x

/-- Derivative identity for `G`: `deriv (G n) = G (n+1)` on the domain `s`. -/
public lemma deriv_G (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    deriv (G n) x = G (n + 1) x := by
  have hF : HasDerivAt (fun y : ℝ ↦ F n y) (F (n + 1) x) x := hasDerivAt_F (n := n) (x := x) hx
  change deriv (fun y : ℝ ↦ G n y) x = G (n + 1) x
  simpa [G] using! (hF.const_mul (-2 : ℂ)).deriv

lemma iteratedDeriv_G_eq :
    ∀ n m : ℕ, Set.EqOn (iteratedDeriv n (G m)) (G (n + m)) s := by
  have hs : IsOpen s := by simpa [s] using! (isOpen_Ioi : IsOpen (Ioi (-1 : ℝ)))
  simpa using!
    (SpherePacking.ForMathlib.eqOn_iteratedDeriv_eq_of_deriv_eq (hs := hs) (G := G)
      (hderiv := fun n x hx => deriv_G (n := n) (x := x) hx))

end SpherePacking.Dim24.Schwartz.J6Smooth

end
