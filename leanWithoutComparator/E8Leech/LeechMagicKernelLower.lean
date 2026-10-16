import E8Leech.E8MagicKernelLower
import SpherePacking.Dim24.MagicFunction.F.Sign.Auxiliary

/-!
# A quantitative small-parameter lower bound for the Leech magic kernel

The kernel `A(t)` of the Laplace representation of the magic function in dimension 24 is

`A(t) = (π/28304640) t¹⁰ φ(i/t) - (1/(65520π)) ψ_I(it)`,   `ψ_I(it) = -t¹⁰ ψ_S(i/t)`.

Both terms are nonpositive, the first one strictly (`leech_AKernel_re_neg`). The theta quotient
`ψ_S`, normalized by its leading exponential, has limit `-7·16⁵ = -7340032` at `i∞`
(`leech_psiS_normalized_tendsto`), so `-A(t)` is at least a positive constant times
`t¹⁰ exp(-π/t)` near zero (`leech_magic_kernel_small_parameter_lower`). The threshold comes from a
proved limit; no numerical value for it is claimed.
-/

noncomputable section

namespace E8Leech

open Filter Complex UpperHalfPlane
open SpherePacking.Dim24
open scoped Topology

local notation "ψS₂₄" => SpherePacking.Dim24.ψS
local notation "ψI₂₄" => SpherePacking.Dim24.ψI

theorem leech_psiS_normalized_tendsto :
    Tendsto (fun z : ℍ => ψS₂₄ z / Complex.exp (Real.pi * Complex.I * (z : ℂ)))
      atImInfty (𝓝 (-7340032 : ℂ)) := by
  have heq : (fun z : ℍ => ψS₂₄ z / Complex.exp (Real.pi * Complex.I * (z : ℂ))) =
      fun z => -(65536 * (H₂ z / Complex.exp (Real.pi * Complex.I * (z : ℂ))) *
        (7 * H₄ z ^ 2 + 7 * H₂ z * H₄ z + 2 * H₂ z ^ 2)) / (H₃ z * H₄ z) ^ 4 := by
    funext z
    have hd : Δ z = (H₂ z * H₃ z * H₄ z) ^ 2 / 256 := by
      simpa only [Delta_apply] using Delta_eq_H₂_H₃_H₄ z
    rw [SpherePacking.Dim24.ψS_apply, hd]
    field_simp [H₂_ne_zero z, H₃_ne_zero z, H₄_ne_zero z, Complex.exp_ne_zero]
    ring
  have hp : Tendsto (fun z : ℍ => 7 * H₄ z ^ 2 + 7 * H₂ z * H₄ z + 2 * H₂ z ^ 2)
      atImInfty (𝓝 (7 : ℂ)) := by
    have h7 : Tendsto (fun _ : ℍ => (7 : ℂ)) atImInfty (𝓝 7) := tendsto_const_nhds
    have h2 : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 2) := tendsto_const_nhds
    convert ((h7.mul (H₄_tendsto_atImInfty.pow 2)).add
      ((h7.mul H₂_tendsto_atImInfty).mul H₄_tendsto_atImInfty)).add
        (h2.mul (H₂_tendsto_atImInfty.pow 2)) using 1
    norm_num
  have hden : Tendsto (fun z : ℍ => (H₃ z * H₄ z) ^ 4) atImInfty (𝓝 (1 : ℂ)) := by
    simpa only [one_mul, one_pow] using (H₃_tendsto_atImInfty.mul H₄_tendsto_atImInfty).pow 4
  have hc : Tendsto (fun _ : ℍ => (65536 : ℂ)) atImInfty (𝓝 65536) := tendsto_const_nhds
  rw [heq]
  convert (((hc.mul e8_thetaTwo_normalized_tendsto).mul hp).neg).div hden
    (by norm_num) using 1 <;> first | rfl | norm_num

/-- On the imaginary axis, `-ψ_S(is)` is eventually at least `3670016·exp(-πs)`. -/
theorem leech_psiS_axis_eventually :
    ∀ᶠ s : ℝ in atTop, ∀ hs : 0 < s,
      3670016 * Real.exp (-Real.pi * s) ≤ -(ψS₂₄ (it s hs)).re := by
  have h := (Complex.continuous_re.tendsto (-7340032 : ℂ)).comp
    (leech_psiS_normalized_tendsto.comp tendsto_ofComplex_I_mul_atTop_atImInfty)
  have hlt : ((-7340032 : ℂ)).re < (-3670016 : ℝ) := by norm_num
  filter_upwards [h.eventually (eventually_le_nhds hlt)] with s hs' hs
  have hoff : ofComplex (Complex.I * s) = it s hs :=
    ofComplex_apply_of_im_pos (by simpa using hs)
  have hz : ((it s hs : ℍ) : ℂ) = Complex.I * s := rfl
  have hE : Complex.exp (Real.pi * Complex.I * ((it s hs : ℍ) : ℂ)) =
      (Real.exp (-Real.pi * s) : ℂ) := by
    rw [hz]
    have ha : Real.pi * Complex.I * (Complex.I * (s : ℂ)) = ((-Real.pi * s : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_neg]
      calc
        _ = (Real.pi : ℂ) * (Complex.I * Complex.I) * s := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [ha, ← Complex.ofReal_exp]
  simp only [Function.comp_apply, hoff, hE, Complex.div_ofReal_re] at hs'
  have hpos : 0 < Real.exp (-Real.pi * s) := Real.exp_pos _
  have h2 := (div_le_iff₀ hpos).mp hs'
  linarith

/-- The real part of the Leech kernel in terms of `φ` and `ψ_S` at `i/t`. -/
theorem leech_AKernel_re (t : ℝ) (ht : 0 < t) :
    (AKernel t ht).re = Real.pi / 28304640 * t ^ 10 * (varphi (iOverT t ht)).re +
      1 / (65520 * Real.pi) * t ^ 10 * (ψS₂₄ (iOverT t ht)).re := by
  have h1 : ((Real.pi : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) =
      ((Real.pi / 28304640 * t ^ 10 : ℝ) : ℂ) * varphi (iOverT t ht) := by
    push_cast
    ring
  have h2 : (1 / ((65520 : ℂ) * (Real.pi : ℂ))) * ψI₂₄ (it t ht) =
      ((-(1 / (65520 * Real.pi) * t ^ 10) : ℝ) : ℂ) * ψS₂₄ (iOverT t ht) := by
    rw [SignAux.ψI_it_eq_neg_t10_mul_ψS_iOverT t ht]
    push_cast
    ring
  unfold AKernel
  rw [h1, h2, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

/-- The Leech kernel is strictly negative on the positive axis. -/
theorem leech_AKernel_re_neg (t : ℝ) (ht : 0 < t) : (AKernel t ht).re < 0 := by
  have ht' : 0 < 1 / t := one_div_pos.mpr ht
  have hv : (varphi (iOverT t ht)).re < 0 := varphi_imagAxis_neg (1 / t) ht'
  have hψ : (ψS₂₄ (iOverT t ht)).re ≤ 0 := SpherePacking.Dim24.ψS_imagAxis_nonpos (1 / t) ht'
  rw [leech_AKernel_re]
  have h10 : 0 < t ^ 10 := pow_pos ht 10
  have h1 : Real.pi / 28304640 * t ^ 10 * (varphi (iOverT t ht)).re < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hv
  have h2 : 1 / (65520 * Real.pi) * t ^ 10 * (ψS₂₄ (iOverT t ht)).re ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hψ
  linarith

/-- A common positive coefficient and threshold for the Leech kernel. -/
theorem leech_magic_kernel_small_parameter_lower :
    ∃ κ t₀ : ℝ, 0 < κ ∧ 0 < t₀ ∧ ∀ t : ℝ, ∀ ht : 0 < t, t ≤ t₀ →
      κ * t ^ 10 * Real.exp (-Real.pi / t) ≤ -(AKernel t ht).re := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 leech_psiS_axis_eventually
  let S := max 1 T
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨3670016 / (65520 * Real.pi), 1 / S, by positivity, one_div_pos.mpr hS, ?_⟩
  intro t ht htS
  have hs : 0 < 1 / t := one_div_pos.mpr ht
  have hST : T ≤ 1 / t := by
    have hSt : S ≤ 1 / t := (le_div_iff₀ ht).mpr
      (by simpa only [mul_comm] using (le_div_iff₀ hS).mp htS)
    exact (le_max_right _ _).trans hSt
  have hψ : 3670016 * Real.exp (-Real.pi * (1 / t)) ≤ -(ψS₂₄ (iOverT t ht)).re :=
    hT (1 / t) hST hs
  have hv : (varphi (iOverT t ht)).re < 0 := varphi_imagAxis_neg (1 / t) hs
  have he : Real.exp (-Real.pi * (1 / t)) = Real.exp (-Real.pi / t) := by
    congr 1
    ring
  rw [he] at hψ
  rw [leech_AKernel_re]
  have h10 : 0 < t ^ 10 := pow_pos ht 10
  have h1 : Real.pi / 28304640 * t ^ 10 * (varphi (iOverT t ht)).re ≤ 0 :=
    (mul_neg_of_pos_of_neg (by positivity) hv).le
  have hc : 0 ≤ 1 / (65520 * Real.pi) * t ^ 10 := by positivity
  have h2 := mul_le_mul_of_nonneg_left hψ hc
  have e : 3670016 / (65520 * Real.pi) * t ^ 10 * Real.exp (-Real.pi / t) =
      1 / (65520 * Real.pi) * t ^ 10 * (3670016 * Real.exp (-Real.pi / t)) := by ring
  rw [e]
  linarith

end E8Leech
