import E8Leech.EvenShellApproximation
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.IntegralA
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.IneqA
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.LaplaceA.Basic
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.LaplaceB.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Fixed-radius E8 magic-function shell approximation

The qualitative, fixed-radius part of BRR Lemma 2.2 is proved here for
Viazovska's actual magic function from Sphere-Packing-Lean. No magic-function
sign or representation is assumed: both are imported proved theorems.

The Laplace mass at an upper squared radius gives a common positive lower
bound for the sine-squared coefficient at every smaller squared radius above
two. The first shell is included separately. An exponential growth bound for
the constant, and the geometric periodic stability theorem, remain open.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Set
open MagicFunction.g.CohnElkies

/-- The positive Laplace mass of the actual E8 kernel, in the squared-radius parameter. -/
def e8MagicLaplaceMass (u : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), -A t * Real.exp (-Real.pi * u * t)

theorem integrable_e8MagicLaplace {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => -A t * Real.exp (-Real.pi * u * t)) (Ioi 0) := by
  have ha := (IntegralReps.aLaplaceIntegral_convergent hu).re
  have hb := (IntegralReps.bLaplaceIntegral_convergent hu).re
  refine (ha.add (hb.const_mul (36 / Real.pi ^ 2))).congr
    (Filter.Eventually.of_forall ?_)
  intro t
  change (IntegralReps.aLaplaceIntegrand u t).re +
    (36 / Real.pi ^ 2) * (IntegralReps.bLaplaceIntegrand u t).re =
      -A t * Real.exp (-Real.pi * u * t)
  simp only [IntegralReps.aLaplaceIntegrand, IntegralReps.bLaplaceIntegrand, A,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  ring

theorem e8MagicLaplaceMass_pos {u : ℝ} (hu : 2 < u) : 0 < e8MagicLaplaceMass u := by
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < -A t * Real.exp (-Real.pi * u * t) := by
    intro t ht
    exact mul_pos (neg_pos.mpr (A_neg ht)) (Real.exp_pos _)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => -A t * Real.exp (-Real.pi * u * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hpos t ht).le
  apply (integral_pos_iff_support_of_nonneg_ae hnonneg (integrable_e8MagicLaplace hu)).mpr
  have hs : Ioi (0 : ℝ) ⊆ Function.support
      (fun t : ℝ => -A t * Real.exp (-Real.pi * u * t)) := by
    intro t ht
    exact ne_of_gt (hpos t ht)
  have hv : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioi 0) := by simp
  exact hv.trans_le (measure_mono hs)

/-- A larger squared radius decreases the positive Laplace mass. -/
theorem e8MagicLaplaceMass_antitone {u U : ℝ} (hu : 2 < u) (huU : u ≤ U) :
    e8MagicLaplaceMass U ≤ e8MagicLaplaceMass u := by
  apply integral_mono_ae (integrable_e8MagicLaplace (hu.trans_le huU))
    (integrable_e8MagicLaplace hu)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply mul_le_mul_of_nonneg_left _ (neg_nonneg.mpr (A_neg ht).le)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr huU) (mul_nonneg Real.pi_pos.le ht.le)]

/-- The real magic profile equals a negative sine-squared factor times the positive mass. -/
theorem e8_gRadial_re_eq_laplaceMass {u : ℝ} (hu : 2 < u) :
    (gRadial u).re = -(Real.pi / 2160) *
      Real.sin (Real.pi * u / 2) ^ 2 * e8MagicLaplaceMass u := by
  have hInt :
      (∫ t in Ioi (0 : ℝ), (A t : ℂ) * Real.exp (-Real.pi * u * t)) =
        ((∫ t in Ioi (0 : ℝ), A t * Real.exp (-Real.pi * u * t) : ℝ) : ℂ) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), ((A t * Real.exp (-Real.pi * u * t) : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        exact (Complex.ofReal_mul _ _).symm
      _ = _ := integral_ofReal
  have hneg : (∫ t in Ioi (0 : ℝ), A t * Real.exp (-Real.pi * u * t)) =
      -e8MagicLaplaceMass u := by
    simp [e8MagicLaplaceMass, neg_mul, integral_neg]
  have h := gRadial_eq_integral_A hu
  rw [hInt, hneg] at h
  have hcoef : (Real.pi / 2160 : ℂ) = ((Real.pi / 2160 : ℝ) : ℂ) := by simp
  rw [hcoef, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul] at h
  have hre := congrArg Complex.re h
  simpa only [Complex.ofReal_re, mul_neg, neg_mul] using hre

/-- A common positive sine-squared coefficient on a fixed interval of squared radii. -/
theorem e8_gRadial_sine_squared_lower {u U : ℝ}
    (hu : 2 ≤ u) (huU : u ≤ U) :
    (Real.pi / 2160 * e8MagicLaplaceMass U) *
        Real.sin (Real.pi * u / 2) ^ 2 ≤ |(gRadial u).re| := by
  rcases hu.eq_or_lt with h | h
  · rw [← h]
    simp
  · have hn : (gRadial u).re ≤ 0 := by
      rw [e8_gRadial_re_eq_laplaceMass h]
      apply mul_nonpos_of_nonpos_of_nonneg _ (e8MagicLaplaceMass_pos h).le
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)
    rw [abs_of_nonpos hn, e8_gRadial_re_eq_laplaceMass h]
    have hm := e8MagicLaplaceMass_antitone h huU
    have hc : 0 ≤ Real.pi / 2160 * Real.sin (Real.pi * u / 2) ^ 2 := by positivity
    have hl := mul_le_mul_of_nonneg_left hm hc
    nlinarith [hl]

/-- BRR Lemma 2.2 for the actual E8 magic profile, with a fixed upper squared radius.
The constant is independent of `u`, including at the first shell. -/
theorem e8_gRadial_even_shell_bound {U : ℝ} (hU : 2 < U) :
    ∃ α : ℝ, 1 < α ∧ ∀ u : ℝ, 2 ≤ u → u ≤ U →
      ∃ k : ℤ, 1 ≤ k ∧ |u - 2 * k| ≤ α * Real.sqrt |(gRadial u).re| := by
  let C := (Real.pi / 2160 * e8MagicLaplaceMass U)⁻¹
  have hc : 0 < Real.pi / 2160 * e8MagicLaplaceMass U :=
    mul_pos (by positivity) (e8MagicLaplaceMass_pos hU)
  have hC : 0 < C := inv_pos.mpr hc
  refine ⟨max 2 (Real.sqrt C), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro u hu huU
  have hs : Real.sin (Real.pi * u / 2) ^ 2 ≤ C * |(gRadial u).re| := by
    have hl := e8_gRadial_sine_squared_lower hu huU
    dsimp only [C]
    rw [mul_comm _ |(gRadial u).re|, ← div_eq_mul_inv]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using hl
  obtain ⟨k, hk, hnear⟩ := exists_even_shell_of_sine_squared_bound (m := 1)
    (by simpa using hu) hC.le hs
  refine ⟨k, hk, hnear.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)

/-- Radius form of the fixed-radius E8 shell approximation. -/
theorem e8_magic_even_shell_bound {R : ℝ} (hR : 2 < R) :
    ∃ α : ℝ, 1 < α ∧ ∀ x : EuclideanSpace ℝ (Fin 8),
      Real.sqrt 2 ≤ ‖x‖ → ‖x‖ ≤ R →
      ∃ k : ℤ, 1 ≤ k ∧ |‖x‖ ^ 2 - 2 * k| ≤ α * Real.sqrt |(_root_.g x).re| := by
  have hU : 2 < R ^ 2 := by nlinarith [sq_nonneg (R - 2)]
  obtain ⟨α, hα, hbound⟩ := e8_gRadial_even_shell_bound hU
  refine ⟨α, hα, ?_⟩
  intro x hx hxR
  have hx2 : 2 ≤ ‖x‖ ^ 2 := by
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg 2) hx 2
    simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hs
  have hxU : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hxR 2
  simpa only [g_apply_eq_gRadial_norm_sq] using hbound (‖x‖ ^ 2) hx2 hxU

end E8Leech
