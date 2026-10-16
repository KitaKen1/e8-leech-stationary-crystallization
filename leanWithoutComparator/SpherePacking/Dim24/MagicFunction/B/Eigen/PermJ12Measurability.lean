-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ12CurveIntegrals
public import SpherePacking.Integration.Measure
import SpherePacking.Integration.EndpointIntegrability
import SpherePacking.MagicFunction.PsiTPrimeZ1Integrability


/-!
# Measurability and integrability for the `permJ1Kernel` Fubini argument

This file collects measurability and integrability facts in the `t`-variable used to justify the
Fubini step in the `J₁` Fourier transform computation.

## Main statements
* `continuousOn_ψT'_z₁line`
* `ae_integrable_permJ1Kernel_slice`
* `integrable_integral_norm_permJ1Kernel`
-/

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.BFourier
open MeasureTheory Set Filter
open SpherePacking.Integration
open SpherePacking.Contour

noncomputable section


section PermJ12

/-- Continuity of `t ↦ ψT' (z₁line t)` on `Ioc (0,1)`. -/
public lemma continuousOn_ψT'_z₁line :
    ContinuousOn (fun t : ℝ => ψT' (z₁line t)) (Ioc (0 : ℝ) 1) := by
  have hψS : Continuous ψS := SpherePacking.Dim24.PsiRewrites.continuous_ψS
  have hres : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)) :=
    Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) hψS
  refine MagicFunction.continuousOn_ψT'_Ioc_of
      (k := 10) (ψS := ψS) (ψT' := ψT') (z := z₁line) hres ?_
  intro t ht
  simpa using! (ψT'_z₁line_eq (t := t) ht)

/-- Almost-everywhere integrability of the `x`-slice of `permJ1Kernel` for `t ∈ Ioc (0,1)`. -/
public lemma ae_integrable_permJ1Kernel_slice (w : ℝ²⁴) :
    (∀ᵐ t : ℝ ∂μIoc01,
        Integrable (fun x : ℝ²⁴ ↦ permJ1Kernel w (x, t)) (volume : Measure ℝ²⁴)) := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
  intro t ht
  exact integrable_permJ1Kernel_slice (w := w) (t := t) ht

/-- Integrability of `t ↦ ∫ ‖permJ1Kernel w (x,t)‖ dx` on `μIoc01`. -/
public lemma integrable_integral_norm_permJ1Kernel (w : ℝ²⁴) :
    Integrable (fun t : ℝ ↦ ∫ x : ℝ²⁴, ‖permJ1Kernel w (x, t)‖) μIoc01 := by
  rcases SpherePacking.Dim24.PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with
    ⟨Cψ, hCψ⟩
  let g : ℝ → ℝ := fun t => ‖ψT' (z₁line t)‖ * (1 / t) ^ (12 : ℕ)
  have hAE :
      (fun t : ℝ ↦ ∫ x : ℝ²⁴, ‖permJ1Kernel w (x, t)‖) =ᵐ[μIoc01] g := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
    intro t ht
    simpa [g] using! (integral_norm_permJ1Kernel (w := w) (t := t) ht)
  have hψTbound :
      ∀ t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
        ‖ψT' (z₁line t)‖ ≤ (Cψ : ℝ) * Real.exp (-Real.pi / t) * t ^ (10 : ℕ) := by
    intro t ht
    simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using!
      (MagicFunction.norm_modular_rewrite_Ioc_exp_bound (k := 10) (Cψ := Cψ) (ψS := ψS)
        (ψZ := ψT') (z := z₁line) (hCψ := hCψ)
        (hEq := fun s hs => ψT'_z₁line_eq (t := s) hs) (t := t) ht)
  have hg_int : Integrable g μIoc01 := by
    simpa [g] using!
      (MagicFunction.integrable_norm_ψT'_z₁line_mul_one_div_pow_add_two
        (ψT' := ψT') (k := 10) (Cψ := Cψ) continuousOn_ψT'_z₁line hψTbound)
  exact hg_int.congr hAE.symm


end PermJ12


end
end SpherePacking.Dim24.BFourier
