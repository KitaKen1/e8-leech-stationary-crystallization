-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
public import SpherePacking.Dim24.MagicFunction.B.Defs.J1Smooth
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.MagicFunction.PsiTPrimeZ1
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.ForMathlib.IteratedDeriv
public import SpherePacking.Integration.Measure

/-!
# Smoothness of `RealIntegrals.J₁'` via differentiation under the integral

We express `J₁'` as an integral over `t ∈ (0,1)` with integrand `gN n x t` and use differentiation
under the integral to identify iterated derivatives. In particular, `J₁'` is smooth on `ℝ`.

## Main definitions
* `Schwartz.J1Smooth.I`

## Main statements
* `Schwartz.J1Smooth.iteratedDeriv_J₁'_eq_integral_gN`
* `Schwartz.J1Smooth.contDiff_J₁'`
-/

noncomputable section


namespace SpherePacking.Dim24.Schwartz.J1Smooth

open Set
open MeasureTheory

open MagicFunction.Parametrisations
open intervalIntegral
open SpherePacking.Integration (μIoo01)

lemma J₁'_eq_integral_g_Ioo (x : ℝ) :
    RealIntegrals.J₁' x = ∫ t in Ioo (0 : ℝ) 1, g x t := by
  simp [J₁'_eq_integral, intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le,
    integral_Ioc_eq_integral_Ioo]

lemma continuous_coeff : Continuous coeff := by
  simpa [coeff, mul_assoc] using! (continuous_const.mul continuous_z₁')

lemma continuousOn_hf :
    ContinuousOn (fun t : ℝ => (Complex.I : ℂ) * ψT' (z₁' t)) (Ioo (0 : ℝ) 1) := by
  have hψS : Continuous ψS := SpherePacking.Dim24.PsiRewrites.continuous_ψS
  have hres : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)) :=
    Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) hψS
  have hψT : ContinuousOn (fun t : ℝ => ψT' (z₁' t)) (Ioo (0 : ℝ) 1) :=
    MagicFunction.continuousOn_ψT'_z₁'_of (k := 10) (ψS := ψS) (ψT' := ψT')
      hres ψT'_z₁'_eq
  simpa using! (continuousOn_const.mul hψT)

lemma exists_bound_norm_hf :
    ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖(Complex.I : ℂ) * ψT' (z₁' t)‖ ≤ M := by
  obtain ⟨Mψ, hMψ⟩ :=
    MagicFunction.exists_bound_norm_ψT'_z₁'_of (k := 10) (ψS := ψS) (ψT' := ψT')
      PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one ψT'_z₁'_eq
  refine ⟨Mψ, ?_⟩
  intro t ht
  simpa using! hMψ t ht

lemma continuousOn_g (x : ℝ) : ContinuousOn (g x) (Ioo (0 : ℝ) 1) := by
  simpa [g, SpherePacking.Integration.DifferentiationUnderIntegral.g] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.continuousOn_g_Ioo
      (coeff := coeff) (hf := fun t => (Complex.I : ℂ) * ψT' (z₁' t)) continuousOn_hf
      continuous_coeff x)

lemma continuousOn_gN (n : ℕ) (x : ℝ) : ContinuousOn (gN n x) (Ioo (0 : ℝ) 1) := by
  simpa [gN, g, SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g, mul_assoc, mul_comm] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.continuousOn_gN_Ioo
      (coeff := coeff) (hf := fun t => (Complex.I : ℂ) * ψT' (z₁' t))
      (continuousOn_hf := continuousOn_hf) continuous_coeff n x)

lemma ae_bound_gN_succ (n : ℕ) (x₀ : ℝ) :
    ∃ K : ℝ,
      (∀ᵐ t ∂μIoo01, ∀ x ∈ Metric.ball x₀ (1 : ℝ), ‖gN (n + 1) x t‖ ≤ K) ∧
        Integrable (fun _ : ℝ => K) μIoo01 := by
  simpa [SpherePacking.Integration.μIoo01, gN, g,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.ae_bound_gN_succ_Ioo
      (coeff := coeff) (hf := fun t : ℝ => (Complex.I : ℂ) * ψT' (z₁' t))
      (exists_bound_norm_h := exists_bound_norm_hf) (coeff_norm_le := fun t => coeff_norm_le t)
      n x₀)

lemma gN_integrable (n : ℕ) (x : ℝ) : Integrable (gN n x) μIoo01 := by
  simpa [SpherePacking.Integration.μIoo01, gN, g,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.integrable_gN_Ioo
      (coeff := coeff) (hf := fun t : ℝ => (Complex.I : ℂ) * ψT' (z₁' t))
      (continuousOn_hf := continuousOn_hf) continuous_coeff exists_bound_norm_hf
      (fun t => coeff_norm_le t) n x)

/-- The integral functional `I n x := ∫ gN n x t dt` on `t ∈ (0,1)`, used to compute derivatives. -/
@[expose] public def I (n : ℕ) (x : ℝ) : ℂ := ∫ t, gN n x t ∂μIoo01

lemma hasDerivAt_integral_gN (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ I n x) (I (n + 1) x₀) x₀ := by
  simpa [I, SpherePacking.Integration.μIoo01, gN, g,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.hasDerivAt_integral_gN_Ioo
      (coeff := coeff) (hf := fun t : ℝ => (Complex.I : ℂ) * ψT' (z₁' t))
      (continuousOn_hf := continuousOn_hf) continuous_coeff exists_bound_norm_hf
      (fun t => coeff_norm_le t) n x₀)

/-- The `n`th iterated derivative of `J₁'` is given by the integral functional `I n`. -/
public lemma iteratedDeriv_J₁'_eq_integral_gN (n : ℕ) :
    iteratedDeriv n RealIntegrals.J₁' = fun x : ℝ ↦ I n x := by
  have h0 : (fun x : ℝ => I 0 x) = RealIntegrals.J₁' := by
    funext x
    simpa [I, SpherePacking.Integration.μIoo01, gN] using! (J₁'_eq_integral_g_Ioo x).symm
  simpa [h0] using!
    (SpherePacking.ForMathlib.iteratedDeriv_eq_of_hasDerivAt_succ
      (I := I) (hI := fun n x => hasDerivAt_integral_gN (n := n) (x₀ := x)) n)

/-- The contour-integral term `J₁'` is smooth on `ℝ`. -/
public theorem contDiff_J₁' : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.J₁' := by
  have hI : ∀ n x, HasDerivAt (fun y : ℝ => I n y) (I (n + 1) x) x := by
    intro n x
    simpa using! (hasDerivAt_integral_gN (n := n) (x₀ := x))
  have h0 : (fun x : ℝ => I 0 x) = RealIntegrals.J₁' := by
    funext x
    simpa [I, SpherePacking.Integration.μIoo01, gN] using! (J₁'_eq_integral_g_Ioo x).symm
  simpa [h0] using! (SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I) hI)


end SpherePacking.Dim24.Schwartz.J1Smooth

end
