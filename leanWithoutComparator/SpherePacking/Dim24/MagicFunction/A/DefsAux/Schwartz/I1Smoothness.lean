/-
Smoothness of `I₁'`.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Prelude
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I1Prelude
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.ForMathlib.IteratedDeriv
public import SpherePacking.Integration.Measure


/-!
# Smoothness of `I₁'`

This file proves smoothness of the profile integral `RealIntegrals.I₁'` by differentiating under
the integral sign.

## Main definitions
* `I` (the integral of the differentiated kernel `gN`)

## Main statements
* `iteratedDeriv_I₁'_eq_integral_gN`
* `contDiff_I₁'`
-/

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

namespace Schwartz

open MeasureTheory Filter Topology

namespace I1Smooth

open RealIntegrals
open MagicFunction.Parametrisations
open Complex Real Set MeasureTheory Filter intervalIntegral
open scoped Interval

open SpherePacking.Integration (μIoo01)

private lemma I₁'_eq_integral_g_Ioo (x : ℝ) :
    RealIntegrals.I₁' x = ∫ t in Ioo (0 : ℝ) 1, g x t := by
  simp [I₁'_eq_integral, intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le,
    integral_Ioc_eq_integral_Ioo]

private lemma continuous_coeff : Continuous coeff := by
  simpa [coeff] using! (continuous_const.mul continuous_z₁')

private lemma continuousOn_varphi'_neg_one_div_z₁'_add_one :
    ContinuousOn (fun t : ℝ => varphi' (-1 / (z₁' t + 1))) (Ioo (0 : ℝ) 1) := by
  have hEq :
      EqOn
        (fun t : ℝ => varphi' (-1 / (z₁' t + 1)))
        (fun t : ℝ => varphi.resToImagAxis (1 / t))
        (Ioo (0 : ℝ) 1) := by
    intro t ht
    have htIoc : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    simpa using! (varphi'_neg_one_div_z₁'_add_one_eq (t := t) htIoc)
  have hdiv : ContinuousOn (fun t : ℝ => (1 / t : ℝ)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.div continuousOn_id fun _ ht => (ne_of_gt ht.1)
  have hdiv_maps : MapsTo (fun t : ℝ => (1 / t : ℝ)) (Ioo (0 : ℝ) 1) (Set.Ici (1 : ℝ)) := by
    intro t ht
    exact one_le_one_div ht.1 (le_of_lt ht.2)
  have hcont : ContinuousOn (fun t : ℝ => varphi.resToImagAxis (1 / t)) (Ioo (0 : ℝ) 1) := by
    simpa using!
      (VarphiExpBounds.continuousOn_varphi_resToImagAxis_Ici_one.comp hdiv hdiv_maps)
  exact hcont.congr hEq

private lemma continuousOn_h : ContinuousOn h (Ioo (0 : ℝ) 1) := by
  have hpow : ContinuousOn (fun t : ℝ => (z₁' t + 1) ^ (10 : ℕ)) (Ioo (0 : ℝ) 1) :=
    ((continuous_z₁'.add continuous_const).pow 10).continuousOn
  simpa [h, mul_assoc] using!
    (continuousOn_const.mul (continuousOn_varphi'_neg_one_div_z₁'_add_one.mul hpow))

private lemma continuous_g (x : ℝ) : Continuous fun t : ℝ => (x : ℂ) * coeff t :=
  continuous_const.mul (continuous_const.mul continuous_z₁')

private lemma continuousOn_g (x : ℝ) : ContinuousOn (g x) (Ioo (0 : ℝ) 1) := by
  simpa [g] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.continuousOn_g_Ioo
      (coeff := coeff) (hf := h) continuousOn_h continuous_coeff x)

private lemma continuousOn_gN (n : ℕ) (x : ℝ) : ContinuousOn (gN n x) (Ioo (0 : ℝ) 1) := by
  simpa [gN, g, SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.continuousOn_gN_Ioo
      (coeff := coeff) (hf := h) continuousOn_h continuous_coeff n x)

private lemma gN_integrable (n : ℕ) (x : ℝ) : Integrable (gN n x) μIoo01 := by
  simpa [μIoo01, gN, g, SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.integrable_gN_Ioo
      (coeff := coeff) (hf := h) continuousOn_h continuous_coeff
      exists_bound_norm_h (fun t => coeff_norm_le t) n x)

private lemma ae_bound_gN_succ (n : ℕ) (x₀ : ℝ) :
    ∃ K, (∀ᵐ t ∂μIoo01, ∀ x ∈ Metric.ball x₀ (1 : ℝ), ‖gN (n + 1) x t‖ ≤ K) ∧
      Integrable (fun _ : ℝ => K) μIoo01 := by
  simpa [μIoo01, gN, g, SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.ae_bound_gN_succ_Ioo
      (coeff := coeff) (hf := h) (exists_bound_norm_h := exists_bound_norm_h)
      (coeff_norm_le := fun t => coeff_norm_le t) n x₀)

/-- The integral of the differentiated kernel `gN` over `t ∈ (0, 1)`. -/
@[expose] public def I (n : ℕ) (x : ℝ) : ℂ := ∫ t, gN n x t ∂μIoo01

private lemma hasDerivAt_integral_gN (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ I n x) (I (n + 1) x₀) x₀ := by
  simpa [I, μIoo01, gN, g, SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.hasDerivAt_integral_gN_Ioo
      (coeff := coeff) (hf := h) continuousOn_h continuous_coeff exists_bound_norm_h
      (fun t => coeff_norm_le t) n x₀)

/-- Compute `iteratedDeriv n I₁'` as an integral of the differentiated kernel `gN`. -/
public lemma iteratedDeriv_I₁'_eq_integral_gN (n : ℕ) :
    iteratedDeriv n RealIntegrals.I₁' = fun x : ℝ ↦ I n x := by
  have h0 : (fun x : ℝ => I 0 x) = RealIntegrals.I₁' := by
    funext x
    simpa [I, SpherePacking.Integration.μIoo01, gN] using! (I₁'_eq_integral_g_Ioo x).symm
  simpa [h0] using!
    (SpherePacking.ForMathlib.iteratedDeriv_eq_of_hasDerivAt_succ
      (I := I) (hI := fun n x => hasDerivAt_integral_gN (n := n) (x₀ := x)) n)

/-- Smoothness of the profile integral `I₁'`. -/
public theorem contDiff_I₁' : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₁' := by
  have hI : ∀ n x, HasDerivAt (fun y : ℝ => I n y) (I (n + 1) x) x := by
    intro n x
    simpa using! (hasDerivAt_integral_gN (n := n) (x₀ := x))
  have h0 : (fun x : ℝ => I 0 x) = RealIntegrals.I₁' := by
    funext x
    simpa [I, SpherePacking.Integration.μIoo01, gN] using! (I₁'_eq_integral_g_Ioo x).symm
  simpa [h0] using! (SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I) hI)


end Schwartz.I1Smooth
end

end SpherePacking.Dim24
