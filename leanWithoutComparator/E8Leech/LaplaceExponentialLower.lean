import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An exponential lower bound from a small-parameter Laplace kernel

On `[1/R, 2/R]`, the phase `1/t + R^2*t` is at most `5*R/2`.
Integrating a kernel lower bound `k*t^2*exp(-pi/t)` over this interval
gives `k/R^3 * exp(-5*pi*R/2)`. The kernel and integrability assumptions
are explicit; an application to the actual E8 kernel is supplied separately.
-/

namespace E8Leech

open MeasureTheory Set

theorem laplace_phase_le_on_reciprocal_interval {R t : ℝ} (hR : 0 < R)
    (htlo : 1 / R ≤ t) (hthi : t ≤ 2 / R) :
    1 / t + R ^ 2 * t ≤ 5 / 2 * R := by
  have ht : 0 < t := (one_div_pos.mpr hR).trans_le htlo
  have hxlo : 1 ≤ R * t := by nlinarith [(div_le_iff₀ hR).mp htlo]
  have hxhi : R * t ≤ 2 := by nlinarith [(le_div_iff₀ hR).mp hthi]
  have hp : (R * t - 1 / 2) * (R * t - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  apply le_of_mul_le_mul_right _ ht
  have heq : (1 / t + R ^ 2 * t) * t = 1 + (R * t) ^ 2 := by
    field_simp [ht.ne']
  rw [heq]
  nlinarith [hp]

theorem laplace_integrand_lower_on_reciprocal_interval {R t κ : ℝ}
    (hR : 0 < R) (hκ : 0 ≤ κ) (htlo : 1 / R ≤ t) (hthi : t ≤ 2 / R) :
    κ / R ^ 2 * Real.exp (-5 * Real.pi * R / 2) ≤
      (κ * t ^ 2 * Real.exp (-Real.pi / t)) * Real.exp (-Real.pi * R ^ 2 * t) := by
  have hsq : 1 / R ^ 2 ≤ t ^ 2 := by
    simpa only [div_pow, one_pow] using
      pow_le_pow_left₀ (one_div_nonneg.mpr hR.le) htlo 2
  have hphase := laplace_phase_le_on_reciprocal_interval hR htlo hthi
  have he : Real.exp (-5 * Real.pi * R / 2) ≤
      Real.exp (-Real.pi / t) * Real.exp (-Real.pi * R ^ 2 * t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_left hphase Real.pi_pos.le
    have heq : Real.pi * (1 / t + R ^ 2 * t) =
        Real.pi / t + Real.pi * R ^ 2 * t := by ring
    rw [heq] at hp
    calc
      _ = -(Real.pi * (5 / 2 * R)) := by ring
      _ ≤ -(Real.pi / t + Real.pi * R ^ 2 * t) := neg_le_neg hp
      _ = _ := by ring
  calc
    _ = κ * (1 / R ^ 2) * Real.exp (-5 * Real.pi * R / 2) := by ring
    _ ≤ κ * t ^ 2 * Real.exp (-5 * Real.pi * R / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hκ) (Real.exp_pos _).le
    _ ≤ κ * t ^ 2 *
        (Real.exp (-Real.pi / t) * Real.exp (-Real.pi * R ^ 2 * t)) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hκ (sq_nonneg t))
    _ = _ := by ring

/-- Restrict a nonnegative Laplace integral to a reciprocal interval. -/
theorem laplace_integral_exponential_lower {K : ℝ → ℝ} {κ t₀ R : ℝ}
    (hκ : 0 ≤ κ) (ht₀ : 0 < t₀) (hR : 0 < R) (hlarge : 2 / t₀ ≤ R)
    (hK : ∀ t : ℝ, 0 < t → 0 ≤ K t)
    (hlower : ∀ t : ℝ, 0 < t → t ≤ t₀ →
      κ * t ^ 2 * Real.exp (-Real.pi / t) ≤ K t)
    (hint : IntegrableOn (fun t : ℝ => K t * Real.exp (-Real.pi * R ^ 2 * t)) (Ioi 0)) :
    κ / R ^ 3 * Real.exp (-5 * Real.pi * R / 2) ≤
      ∫ t in Ioi (0 : ℝ), K t * Real.exp (-Real.pi * R ^ 2 * t) := by
  have hRt₀ : 2 / R ≤ t₀ := by
    apply (div_le_iff₀ hR).mpr
    nlinarith [(div_le_iff₀ ht₀).mp hlarge]
  have hsub : Icc (1 / R) (2 / R) ⊆ Ioi (0 : ℝ) :=
    fun t ht => (one_div_pos.mpr hR).trans_le ht.1
  have hpoint : ∀ t ∈ Icc (1 / R) (2 / R),
      κ / R ^ 2 * Real.exp (-5 * Real.pi * R / 2) ≤
        K t * Real.exp (-Real.pi * R ^ 2 * t) := by
    intro t ht
    exact (laplace_integrand_lower_on_reciprocal_interval hR hκ ht.1 ht.2).trans
      (mul_le_mul_of_nonneg_right
        (hlower t (hsub ht) (ht.2.trans hRt₀)) (Real.exp_pos _).le)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => K t * Real.exp (-Real.pi * R ^ 2 * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (hK t ht) (Real.exp_pos _).le
  have hconst : (∫ _ in Icc (1 / R) (2 / R),
      κ / R ^ 2 * Real.exp (-5 * Real.pi * R / 2)) =
        κ / R ^ 3 * Real.exp (-5 * Real.pi * R / 2) := by
    rw [setIntegral_const]
    have hvol : volume.real (Icc (1 / R) (2 / R)) = 1 / R := by
      have hwidth : 2 / R - 1 / R = 1 / R := by ring
      rw [measureReal_def, Real.volume_Icc, hwidth,
        ENNReal.toReal_ofReal (one_div_nonneg.mpr hR.le)]
    rw [hvol, smul_eq_mul]
    field_simp [hR.ne']
  rw [← hconst]
  have hcint : IntegrableOn
      (fun _ : ℝ => κ / R ^ 2 * Real.exp (-5 * Real.pi * R / 2)) (Icc (1 / R) (2 / R)) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply le_trans (setIntegral_mono_on hcint (hint.mono_set hsub)
    measurableSet_Icc hpoint)
  exact setIntegral_mono_set hint hnonneg (Filter.Eventually.of_forall hsub)

end E8Leech
