import E8Leech.LeechMagicShellApproximation
import E8Leech.LaplaceExponentialLowerPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponential growth control for the Leech shell-approximation constant

The kernel lower bound `κ t¹⁰ exp(-π/t)` gives a reciprocal-interval Laplace estimate for large
radii; bounded radii are handled by positivity and monotonicity of the Laplace mass. So one
coefficient works for every `R > 2`:

`mass(R²) ≥ K R⁻¹¹ exp(-5πR/2)`  (`leechMagicLaplaceMass_exponential_lower`).

Taking square roots gives the growth rate of the constant of BRR Lemma 2.2 in dimension 24:
for `2 ≤ |x| ≤ R` there is `k ≥ 2` with `||x|² - 2k| ≤ α √|Re f(x)|`,
`α ≤ ρ R^(11/2) exp(5πR/4)` (`leech_magic_even_shell_exponential_bound`).

The absolute constants exist by proved theta limits and positive integrals; no numerical values
are computed for them.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Set
open SpherePacking.Dim24

theorem leechMagicLaplaceMass_exponential_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 2 < R →
      K / R ^ 11 * Real.exp (-5 * Real.pi * R / 2) ≤ leechMagicLaplaceMass (R ^ 2) := by
  obtain ⟨κ, t₀, hκ, ht₀, hlower⟩ := leech_magic_kernel_small_parameter_lower
  let R₀ := max 3 (2 / t₀)
  have hR₀ : 3 ≤ R₀ := le_max_left _ _
  have hR₀sq : 4 < R₀ ^ 2 := by nlinarith [sq_nonneg (R₀ - 3)]
  let K := min κ (2048 * leechMagicLaplaceMass (R₀ ^ 2))
  have hK : 0 < K := lt_min hκ (mul_pos (by norm_num) (leechMagicLaplaceMass_pos hR₀sq))
  refine ⟨K, hK, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  have hRsq : 4 < R ^ 2 := by nlinarith [sq_nonneg (R - 2)]
  by_cases hlarge : R₀ ≤ R
  · have hmain := laplace_integral_exponential_lower_pow 10 hκ.le ht₀ hRpos
      ((le_max_right _ _).trans hlarge)
      (K := leechKernel) (fun t ht => (leechKernel_pos ht).le)
      (fun t ht htt => by
        rw [leechKernel_eq ht]
        exact hlower t ht htt)
      (integrable_leechMagicLaplace hRsq)
    apply le_trans _ hmain
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) (Real.exp_pos _).le
  · have hsmall : R ≤ R₀ := (not_le.mp hlarge).le
    have hpow : (2048 : ℝ) ≤ R ^ 11 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hR.le 11
      norm_num at h
      exact h
    have he : Real.exp (-5 * Real.pi * R / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    calc
      _ ≤ K / R ^ 11 := mul_le_of_le_one_right (by positivity) he
      _ ≤ K / 2048 := div_le_div_of_nonneg_left hK.le (by norm_num) hpow
      _ ≤ leechMagicLaplaceMass (R₀ ^ 2) :=
        (div_le_iff₀ (by norm_num : (0 : ℝ) < 2048)).mpr
          (by simpa only [K, mul_comm] using
            min_le_right κ (2048 * leechMagicLaplaceMass (R₀ ^ 2)))
      _ ≤ leechMagicLaplaceMass (R ^ 2) := leechMagicLaplaceMass_antitone hRsq
        (pow_le_pow_left₀ hRpos.le hsmall 2)

theorem sqrt_leech_exponential_coefficient {D R : ℝ} (hD : 0 ≤ D) (hR : 0 < R) :
    Real.sqrt (D * R ^ 11 * Real.exp (5 * Real.pi * R / 2)) =
      Real.sqrt D * R ^ (11 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4) := by
  have he : Real.exp (5 * Real.pi * R / 2) = Real.exp (5 * Real.pi * R / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hs : Real.sqrt (R ^ 11) = R ^ (11 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  rw [Real.sqrt_mul (mul_nonneg hD (by positivity)), Real.sqrt_mul hD,
    hs, he, Real.sqrt_sq (Real.exp_pos _).le]

/-- **BRR's shell bound for the Leech magic function**, with one absolute coefficient
controlling its growth. -/
theorem leech_magic_even_shell_exponential_bound :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℝ, 2 < R →
      ∃ α : ℝ, 1 < α ∧ α ≤ ρ * R ^ (11 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4) ∧
        ∀ x : EuclideanSpace ℝ (Fin 24), 2 ≤ ‖x‖ → ‖x‖ ≤ R →
          ∃ k : ℤ, 2 ≤ k ∧ |‖x‖ ^ 2 - 2 * k| ≤ α * Real.sqrt |(f x).re| := by
  obtain ⟨K, hK, hmass⟩ := leechMagicLaplaceMass_exponential_lower
  let D := 1 / K
  have hD : 0 < D := by dsimp [D]; positivity
  let ρ := max 2 (Real.sqrt D)
  have hρ : 0 < ρ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨ρ, hρ, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  have hRsq : 4 < R ^ 2 := by nlinarith [sq_nonneg (R - 2)]
  let B := D * R ^ 11 * Real.exp (5 * Real.pi * R / 2)
  have hB : 0 < B := by dsimp [B]; positivity
  let α := max 2 (Real.sqrt B)
  refine ⟨α, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_, ?_⟩
  · have hfactor : 1 ≤ R ^ (11 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4) :=
      one_le_mul_of_one_le_of_one_le
        (Real.one_le_rpow (by linarith) (by norm_num))
        (Real.one_le_exp_iff.mpr (by positivity))
    have hsqrt := sqrt_leech_exponential_coefficient hD.le hRpos
    change max 2 (Real.sqrt B) ≤ _
    apply max_le
    · calc
        (2 : ℝ) ≤ ρ := le_max_left _ _
        _ ≤ ρ * (R ^ (11 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4)) :=
          le_mul_of_one_le_right hρ.le hfactor
        _ = _ := by ring
    · dsimp only [B] at hsqrt ⊢
      rw [hsqrt]
      gcongr
      exact le_max_right _ _
  · intro x hx hxR
    have hxU : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hxR 2
    have hx4 : 2 * ((2 : ℤ) : ℝ) ≤ ‖x‖ ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 2
      norm_num at h ⊢
      linarith
    have hc : 0 < leechMagicLaplaceMass (R ^ 2) := leechMagicLaplaceMass_pos hRsq
    have hs : Real.sin (Real.pi * ‖x‖ ^ 2 / 2) ^ 2 ≤
        (leechMagicLaplaceMass (R ^ 2))⁻¹ * |(f x).re| := by
      rw [mul_comm _ |(f x).re|, ← div_eq_mul_inv]
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using leech_f_sine_squared_lower hx hxU
    have hL : 0 < K / R ^ 11 * Real.exp (-5 * Real.pi * R / 2) := by positivity
    have hi := (inv_le_inv₀ hc hL).mpr (hmass R hR)
    have heq : (K / R ^ 11 * Real.exp (-5 * Real.pi * R / 2))⁻¹ = B := by
      dsimp [B, D]
      rw [show -5 * Real.pi * R / 2 = -(5 * Real.pi * R / 2) by ring, Real.exp_neg]
      field_simp [hK.ne', hRpos.ne', Real.exp_ne_zero]
    rw [heq] at hi
    have hsB := hs.trans (mul_le_mul_of_nonneg_right hi (abs_nonneg (f x).re))
    obtain ⟨k, hk, hnear⟩ := exists_even_shell_of_sine_squared_bound (m := 2) hx4 hB.le hsB
    exact ⟨k, hk, hnear.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))⟩

end E8Leech
