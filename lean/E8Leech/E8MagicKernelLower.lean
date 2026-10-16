import SpherePacking.ModularForms.FG.Positivity
import SpherePacking.ModularForms.FG.AsymptoticsTools
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.IneqCommon
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.IneqA

/-!
# A quantitative small-parameter lower bound for the actual E8 magic kernel

Normalize the theta quotient `G / Delta` by its leading exponential. Its
limit is 20480. Positivity of `F` then gives a lower bound for `-A(t)` by a
positive constant times `t^2 * exp (-pi/t)` near zero. The threshold is
obtained from a proved limit; no numerical value for it is claimed.
-/

noncomputable section

namespace E8Leech

open Filter Complex UpperHalfPlane
open MagicFunction.g.CohnElkies
open scoped Topology

theorem e8_thetaTwo_normalized_tendsto :
    Tendsto (fun z : ℍ => H₂ z / Complex.exp (Real.pi * Complex.I * (z : ℂ)))
      atImInfty (𝓝 (16 : ℂ)) := by
  let h : ℍ → ℂ := fun z => jacobiTheta₂ (z / 2) z
  have hh : Tendsto h atImInfty (𝓝 (2 : ℂ)) :=
    jacobiTheta₂_half_mul_apply_tendsto_atImInfty
  have heq : (fun z : ℍ => H₂ z / Complex.exp (Real.pi * Complex.I * (z : ℂ))) =
      fun z => h z ^ 4 := by
    funext z
    have htheta : Θ₂ z = Complex.exp (Real.pi * Complex.I * (z : ℂ) / 4) * h z := by
      simpa only [h] using Θ₂_as_jacobiTheta₂ z
    have hexp : Complex.exp (Real.pi * Complex.I * (z : ℂ) / 4) ^ 4 =
        Complex.exp (Real.pi * Complex.I * (z : ℂ)) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    rw [show H₂ z = Θ₂ z ^ 4 by rfl, htheta, mul_pow, hexp]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  rw [heq]
  simpa only [show (2 : ℂ) ^ 4 = 16 by norm_num] using hh.pow 4

theorem e8_G_div_Delta_normalized_tendsto :
    Tendsto (fun z : ℍ => G z / Δ z / Complex.exp (Real.pi * Complex.I * (z : ℂ)))
      atImInfty (𝓝 (20480 : ℂ)) := by
  have heq : (fun z : ℍ => G z / Δ z / Complex.exp (Real.pi * Complex.I * (z : ℂ))) =
      fun z => 256 * (H₂ z / Complex.exp (Real.pi * Complex.I * (z : ℂ))) *
        (2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2) / (H₃ z * H₄ z) ^ 2 := by
    funext z
    have hd : Δ z = (H₂ z * H₃ z * H₄ z) ^ 2 / 256 := by
      simpa only [Delta_apply] using Delta_eq_H₂_H₃_H₄ z
    rw [hd]
    simp only [G, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Pi.ofNat_apply]
    field_simp [H₂_ne_zero z, H₃_ne_zero z, H₄_ne_zero z, Complex.exp_ne_zero]
  have hp : Tendsto (fun z : ℍ =>
      2 * H₂ z ^ 2 + 5 * H₂ z * H₄ z + 5 * H₄ z ^ 2) atImInfty (𝓝 (5 : ℂ)) := by
    have h2 : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 2) := tendsto_const_nhds
    have h5 : Tendsto (fun _ : ℍ => (5 : ℂ)) atImInfty (𝓝 5) := tendsto_const_nhds
    convert ((h2.mul (H₂_tendsto_atImInfty.pow 2)).add
      ((h5.mul H₂_tendsto_atImInfty).mul H₄_tendsto_atImInfty)).add
        (h5.mul (H₄_tendsto_atImInfty.pow 2)) using 1
    norm_num
  have hden : Tendsto (fun z : ℍ => (H₃ z * H₄ z) ^ 2) atImInfty (𝓝 (1 : ℂ)) := by
    simpa only [one_mul, one_pow] using (H₃_tendsto_atImInfty.mul H₄_tendsto_atImInfty).pow 2
  have h256 : Tendsto (fun _ : ℍ => (256 : ℂ)) atImInfty (𝓝 256) := tendsto_const_nhds
  rw [heq]
  convert ((h256.mul e8_thetaTwo_normalized_tendsto).mul hp).div hden
    (by norm_num) using 1 <;> first | rfl | norm_num

theorem e8_G_div_Delta_normalized_axis_tendsto :
    Tendsto (fun s : ℝ => (GReal s / (Δ.resToImagAxis s).re) /
      Real.exp (-Real.pi * s)) atTop (𝓝 (20480 : ℝ)) := by
  have h := (Complex.continuous_re.tendsto (20480 : ℂ)).comp
    (e8_G_div_Delta_normalized_tendsto.comp tendsto_ofComplex_I_mul_atTop_atImInfty)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hoff : ofComplex (Complex.I * s) = (⟨Complex.I * s, by simp [hs]⟩ : ℍ) :=
    ofComplex_apply_of_im_pos (by simpa using hs)
  have hz : (ofComplex (Complex.I * s) : ℂ) = Complex.I * s := by
    rw [hoff]
  have hG : G (ofComplex (Complex.I * s)) = (GReal s : ℂ) := by
    rw [hoff]
    simpa only [Function.resToImagAxis, ResToImagAxis, dif_pos hs] using G_eq_GReal hs
  have hD : Δ (ofComplex (Complex.I * s)) = ((Δ.resToImagAxis s).re : ℂ) := by
    apply Complex.ext
    · simp only [hoff, Function.resToImagAxis, ResToImagAxis, dif_pos hs, Complex.ofReal_re]
    · simpa only [hoff, Function.resToImagAxis, ResToImagAxis, dif_pos hs, Complex.ofReal_im] using
        Delta_imag_axis_real s hs
  have hE : Complex.exp (Real.pi * Complex.I * (ofComplex (Complex.I * s) : ℂ)) =
      (Real.exp (-Real.pi * s) : ℂ) := by
    rw [hz]
    have ha : Real.pi * Complex.I * (Complex.I * (s : ℂ)) =
        ((-Real.pi * s : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_neg]
      calc
        _ = (Real.pi : ℂ) * (Complex.I * Complex.I) * s := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [ha, ← Complex.ofReal_exp]
  simp only [Function.comp_apply, hG, hD, hE]
  rw [← Complex.ofReal_div, ← Complex.ofReal_div, Complex.ofReal_re]

/-- A common positive coefficient and threshold for the actual E8 kernel. -/
theorem e8_magic_kernel_small_parameter_lower :
    ∃ κ t₀ : ℝ, 0 < κ ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      κ * t ^ 2 * Real.exp (-Real.pi / t) ≤ -A t := by
  have he : ∀ᶠ s : ℝ in atTop,
      10240 ≤ (GReal s / (Δ.resToImagAxis s).re) / Real.exp (-Real.pi * s) :=
    e8_G_div_Delta_normalized_axis_tendsto.eventually
      (eventually_ge_nhds (by norm_num : (10240 : ℝ) < 20480))
  obtain ⟨T, hT⟩ := (eventually_atTop.1 he)
  let S := max 1 T
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c * 10240, 1 / S, by positivity, one_div_pos.mpr hS, ?_⟩
  intro t ht htS
  have hs : 0 < 1 / t := one_div_pos.mpr ht
  have hST : T ≤ 1 / t := by
    have hSt : S ≤ 1 / t := (le_div_iff₀ ht).mpr
      (by simpa only [mul_comm] using (le_div_iff₀ hS).mp htS)
    exact (le_max_right _ _).trans hSt
  have hratio : 10240 * Real.exp (-Real.pi / t) ≤ GReal (1 / t) /
      (Δ.resToImagAxis (1 / t)).re := by
    have h := (le_div_iff₀ (Real.exp_pos (-Real.pi * (1 / t)))).mp (hT (1 / t) hST)
    simpa only [mul_one_div] using h
  have hF : 0 ≤ FReal (1 / t) := (F_pos.2 (1 / t) hs).le
  have hD : 0 < (Δ.resToImagAxis (1 / t)).re := Delta_imag_axis_pos.2 (1 / t) hs
  rw [A_eq_neg_mul_FG_div_Delta t ht]
  have hnum : c * (GReal (1 / t) / (Δ.resToImagAxis (1 / t)).re) ≤
      (FReal (1 / t) + c * GReal (1 / t)) / (Δ.resToImagAxis (1 / t)).re := by
    rw [add_div, mul_div_assoc]
    exact le_add_of_nonneg_left (div_nonneg hF hD.le)
  have hl := (mul_le_mul_of_nonneg_left hratio hc.le).trans hnum
  have hb := mul_le_mul_of_nonneg_left hl (sq_nonneg t)
  nlinarith [hb]

end E8Leech
