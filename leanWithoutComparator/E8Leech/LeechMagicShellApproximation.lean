import E8Leech.EvenShellApproximation
import E8Leech.LeechMagicKernelLower
import SpherePacking.Dim24.MagicFunction.F.Laplace.Equality.B
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Laplace mass of the Leech magic function

The magic function `f` of dimension 24 from Sphere-Packing-Lean has the Laplace representation
`f(x) = sin²(π|x|²/2) ∫₀^∞ A(t) exp(-π|x|²t) dt` for `|x| > 2`, with a kernel `A` whose real part
is negative. This file records the consequences used for the shell approximation (BRR,
Lemma 2.2), in the form of the `E8` file `E8MagicShellApproximation`:

* `leechMagicLaplaceMass u`: the positive Laplace mass `∫ (-Re A)(t) exp(-π u t) dt`; it is
  finite for `u > 4` (`integrable_leechMagicLaplace`), positive and antitone.
* `leech_f_re_eq_laplaceMass`: `Re f(x) = -sin²(π|x|²/2) · mass(|x|²)` for `|x| > 2`.
* `leech_f_sine_squared_lower`: `mass(U)·sin²(π|x|²/2) ≤ |Re f(x)|` for `2 ≤ |x|`, `|x|² ≤ U`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Set
open SpherePacking.Dim24
open SpherePacking.Dim24.LaplaceTmp
open SpherePacking.Dim24.LaplaceTmp.LaplaceEqA

local notation "ψI₂₄" => SpherePacking.Dim24.ψI

/-- The positive real kernel of the Laplace representation of the Leech magic function. -/
def leechKernel (t : ℝ) : ℝ := -(AKernel0 t).re

theorem leechKernel_eq {t : ℝ} (ht : 0 < t) : leechKernel t = -(AKernel t ht).re := by
  rw [leechKernel, AKernel0, dif_pos ht]

theorem leechKernel_pos {t : ℝ} (ht : 0 < t) : 0 < leechKernel t := by
  rw [leechKernel_eq ht]
  exact neg_pos.mpr (leech_AKernel_re_neg t ht)

/-- The positive Laplace mass of the Leech kernel, in the squared-radius parameter. -/
def leechMagicLaplaceMass (u : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), leechKernel t * Real.exp (-Real.pi * u * t)

/-- The complex Laplace integrand of the Leech kernel is integrable for `u > 4`. -/
theorem integrableOn_AKernel0_mul_exp {u : ℝ} (hu : 4 < u) :
    IntegrableOn (fun t : ℝ => AKernel0 t * (Real.exp (-Real.pi * u * t) : ℂ)) (Ioi 0) := by
  have hu0 : 0 ≤ u := by linarith
  have hIntV : IntegrableOn (gV u) (Ioi (0 : ℝ)) volume := by
    rw [Ioi_eq_Ioc_union_Ioi_one]
    exact integrableOn_union.2 ⟨integrableOn_gV_Ioc u hu0, integrableOn_gV_Ioi_one u hu⟩
  have hIntψ : IntegrableOn (gψ u) (Ioi (0 : ℝ)) volume := integrableOn_gψ_Ioi_zero u hu
  have hcomb : IntegrableOn (fun t : ℝ => ((Real.pi : ℂ) / (28304640 : ℂ)) * gV u t -
      (1 / ((65520 : ℂ) * (Real.pi : ℂ))) * gψ u t) (Ioi 0) :=
    (hIntV.const_mul _).sub (hIntψ.const_mul _)
  refine hcomb.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := ht
  have hz : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht0
  have hψ : SpherePacking.Dim24.ψI' ((t : ℂ) * Complex.I) = ψI₂₄ (it t ht0) := by
    rw [SpherePacking.Dim24.ψI', dif_pos hz]
    congr 1
    ext1
    simp [it, mul_comm]
  show ((Real.pi : ℂ) / (28304640 : ℂ)) * gV u t -
      (1 / ((65520 : ℂ) * (Real.pi : ℂ))) * gψ u t =
        AKernel0 t * (Real.exp (-Real.pi * u * t) : ℂ)
  rw [AKernel0, dif_pos ht0, AKernel, gV, gψ, LaplaceProfiles.varphiKernel0, dif_pos ht0, hψ]
  ring

theorem integrable_leechMagicLaplace {u : ℝ} (hu : 4 < u) :
    IntegrableOn (fun t : ℝ => leechKernel t * Real.exp (-Real.pi * u * t)) (Ioi 0) := by
  have h := (integrableOn_AKernel0_mul_exp hu).re.neg
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  change -((AKernel0 t * (Real.exp (-Real.pi * u * t) : ℂ)).re) =
    leechKernel t * Real.exp (-Real.pi * u * t)
  rw [Complex.re_mul_ofReal, leechKernel]
  ring

theorem leechMagicLaplaceMass_pos {u : ℝ} (hu : 4 < u) : 0 < leechMagicLaplaceMass u := by
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < leechKernel t * Real.exp (-Real.pi * u * t) := by
    intro t ht
    exact mul_pos (leechKernel_pos ht) (Real.exp_pos _)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => leechKernel t * Real.exp (-Real.pi * u * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hpos t ht).le
  apply (integral_pos_iff_support_of_nonneg_ae hnonneg (integrable_leechMagicLaplace hu)).mpr
  have hs : Ioi (0 : ℝ) ⊆ Function.support
      (fun t : ℝ => leechKernel t * Real.exp (-Real.pi * u * t)) := by
    intro t ht
    exact ne_of_gt (hpos t ht)
  have hv : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioi 0) := by simp
  exact hv.trans_le (measure_mono hs)

/-- A larger squared radius decreases the positive Laplace mass. -/
theorem leechMagicLaplaceMass_antitone {u U : ℝ} (hu : 4 < u) (huU : u ≤ U) :
    leechMagicLaplaceMass U ≤ leechMagicLaplaceMass u := by
  apply integral_mono_ae (integrable_leechMagicLaplace (hu.trans_le huU))
    (integrable_leechMagicLaplace hu)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply mul_le_mul_of_nonneg_left _ (leechKernel_pos ht).le
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr huU) (mul_nonneg Real.pi_pos.le ht.le)]

/-- The real part of the Leech magic function is a negative sine-squared factor times the
positive mass. -/
theorem leech_f_re_eq_laplaceMass {x : EuclideanSpace ℝ (Fin 24)} (hx : 2 < ‖x‖) :
    (f x).re =
      -(Real.sin (Real.pi * ‖x‖ ^ 2 / 2) ^ 2 * leechMagicLaplaceMass (‖x‖ ^ 2)) := by
  have hu : 4 < ‖x‖ ^ 2 := by nlinarith
  have h := f_eq_laplace_A x hx
  have hint := integrableOn_AKernel0_mul_exp hu
  have hre : (∫ t in Ioi (0 : ℝ), AKernel0 t * (Real.exp (-Real.pi * ‖x‖ ^ 2 * t) : ℂ)).re =
      -leechMagicLaplaceMass (‖x‖ ^ 2) := by
    have h1 : (∫ t in Ioi (0 : ℝ), AKernel0 t * (Real.exp (-Real.pi * ‖x‖ ^ 2 * t) : ℂ)).re =
        ∫ t in Ioi (0 : ℝ), (AKernel0 t * (Real.exp (-Real.pi * ‖x‖ ^ 2 * t) : ℂ)).re :=
      (integral_re hint).symm
    rw [h1, leechMagicLaplaceMass, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    change (AKernel0 t * (Real.exp (-Real.pi * ‖x‖ ^ 2 * t) : ℂ)).re =
      -(leechKernel t * Real.exp (-Real.pi * ‖x‖ ^ 2 * t))
    rw [Complex.re_mul_ofReal, leechKernel]
    ring
  rw [h, Complex.re_ofReal_mul, hre]
  ring

/-- A common positive sine-squared coefficient on a fixed range of squared radii. -/
theorem leech_f_sine_squared_lower {x : EuclideanSpace ℝ (Fin 24)} {U : ℝ}
    (hx : 2 ≤ ‖x‖) (hxU : ‖x‖ ^ 2 ≤ U) :
    leechMagicLaplaceMass U * Real.sin (Real.pi * ‖x‖ ^ 2 / 2) ^ 2 ≤ |(f x).re| := by
  rcases hx.eq_or_lt with h | h
  · have e : Real.sin (Real.pi * ‖x‖ ^ 2 / 2) = 0 := by
      rw [← h, show Real.pi * (2 : ℝ) ^ 2 / 2 = 2 * Real.pi by ring]
      exact Real.sin_two_pi
    rw [e]
    simp
  · have hu : 4 < ‖x‖ ^ 2 := by nlinarith
    have hmass := leechMagicLaplaceMass_pos hu
    rw [leech_f_re_eq_laplaceMass h, abs_neg, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) hmass.le)]
    have hm := leechMagicLaplaceMass_antitone hu hxU
    have hc : 0 ≤ Real.sin (Real.pi * ‖x‖ ^ 2 / 2) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hm hc]

end E8Leech
