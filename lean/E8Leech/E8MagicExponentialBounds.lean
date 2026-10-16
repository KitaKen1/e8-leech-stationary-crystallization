import E8Leech.E8MagicShellApproximation
import E8Leech.E8MagicKernelLower
import E8Leech.LaplaceExponentialLower
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponential growth control for the E8 shell-approximation constant

The actual kernel lower bound supplies a reciprocal-interval Laplace estimate
for large radii. The remaining bounded radii are handled by positivity and
monotonicity of the same actual Laplace mass. Thus one coefficient works for
every `R > 2`. Taking square roots gives the E8 growth rate in BRR Lemma 2.2.

The absolute constants exist by proved theta limits and positive integrals;
this file does not compute numerical values for them. Periodic packing
geometry and the Leech counterpart remain separate work.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Set
open MagicFunction.g.CohnElkies

theorem e8MagicLaplaceMass_exponential_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 2 < R →
      K / R ^ 3 * Real.exp (-5 * Real.pi * R / 2) ≤ e8MagicLaplaceMass (R ^ 2) := by
  obtain ⟨κ, t₀, hκ, ht₀, hlower⟩ := e8_magic_kernel_small_parameter_lower
  let R₀ := max 3 (2 / t₀)
  have hR₀ : 3 ≤ R₀ := le_max_left _ _
  have hR₀sq : 2 < R₀ ^ 2 := by nlinarith [sq_nonneg (R₀ - 3)]
  let K := min κ (8 * e8MagicLaplaceMass (R₀ ^ 2))
  have hK : 0 < K := lt_min hκ (mul_pos (by norm_num) (e8MagicLaplaceMass_pos hR₀sq))
  refine ⟨K, hK, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  have hRsq : 2 < R ^ 2 := by nlinarith [sq_nonneg (R - 2)]
  by_cases hlarge : R₀ ≤ R
  · have hmain := laplace_integral_exponential_lower hκ.le ht₀ hRpos
      ((le_max_right _ _).trans hlarge)
      (K := fun t => -A t) (fun t ht => (neg_pos.mpr (A_neg ht)).le)
      hlower (integrable_e8MagicLaplace hRsq)
    apply le_trans _ hmain
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) (Real.exp_pos _).le
  · have hsmall : R ≤ R₀ := (not_le.mp hlarge).le
    have hcube : (8 : ℝ) ≤ R ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hR.le 3
      norm_num at h
      exact h
    have he : Real.exp (-5 * Real.pi * R / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    calc
      _ ≤ K / R ^ 3 := mul_le_of_le_one_right (by positivity) he
      _ ≤ K / 8 := div_le_div_of_nonneg_left hK.le (by norm_num) hcube
      _ ≤ e8MagicLaplaceMass (R₀ ^ 2) :=
        (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
          (by simpa only [K, mul_comm] using min_le_right κ (8 * e8MagicLaplaceMass (R₀ ^ 2)))
      _ ≤ e8MagicLaplaceMass (R ^ 2) := e8MagicLaplaceMass_antitone hRsq
        (pow_le_pow_left₀ hRpos.le hsmall 2)

theorem sqrt_e8_exponential_coefficient {K R : ℝ} (hK : 0 < K) (hR : 0 < R) :
    Real.sqrt ((2160 / (Real.pi * K)) * R ^ 3 * Real.exp (5 * Real.pi * R / 2)) =
      Real.sqrt (2160 / (Real.pi * K)) * R ^ (3 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4) := by
  have hc : 0 ≤ 2160 / (Real.pi * K) := by positivity
  have he : Real.exp (5 * Real.pi * R / 2) = Real.exp (5 * Real.pi * R / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hs : Real.sqrt (R ^ 3) = R ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  rw [Real.sqrt_mul (mul_nonneg hc (by positivity)), Real.sqrt_mul hc,
    hs, he, Real.sqrt_sq (Real.exp_pos _).le]

/-- BRR's E8 shell bound with one absolute coefficient controlling its growth. -/
theorem e8_gRadial_even_shell_exponential_bound :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℝ, 2 < R →
      ∃ α : ℝ, 1 < α ∧ α ≤ ρ * R ^ (3 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4) ∧
        ∀ u : ℝ, 2 ≤ u → u ≤ R ^ 2 →
          ∃ k : ℤ, 1 ≤ k ∧ |u - 2 * k| ≤ α * Real.sqrt |(gRadial u).re| := by
  obtain ⟨K, hK, hmass⟩ := e8MagicLaplaceMass_exponential_lower
  let D := 2160 / (Real.pi * K)
  have hD : 0 < D := by dsimp [D]; positivity
  let ρ := max 2 (Real.sqrt D)
  have hρ : 0 < ρ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨ρ, hρ, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  have hRsq : 2 < R ^ 2 := by nlinarith [sq_nonneg (R - 2)]
  let B := D * R ^ 3 * Real.exp (5 * Real.pi * R / 2)
  have hB : 0 < B := by dsimp [B]; positivity
  let α := max 2 (Real.sqrt B)
  refine ⟨α, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_, ?_⟩
  · have hfactor : 1 ≤ R ^ (3 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4) :=
      one_le_mul_of_one_le_of_one_le
        (Real.one_le_rpow (by linarith) (by norm_num))
        (Real.one_le_exp_iff.mpr (by positivity))
    have hsqrt := sqrt_e8_exponential_coefficient hK hRpos
    change max 2 (Real.sqrt B) ≤ _
    apply max_le
    · calc
        (2 : ℝ) ≤ ρ := le_max_left _ _
        _ ≤ ρ * (R ^ (3 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4)) :=
          le_mul_of_one_le_right hρ.le hfactor
        _ = _ := by ring
    · dsimp only [B, D] at hsqrt ⊢
      rw [hsqrt]
      gcongr
      exact le_max_right _ _
  · intro u hu huR
    let C := (Real.pi / 2160 * e8MagicLaplaceMass (R ^ 2))⁻¹
    have hc : 0 < Real.pi / 2160 * e8MagicLaplaceMass (R ^ 2) :=
      mul_pos (by positivity) (e8MagicLaplaceMass_pos hRsq)
    have hs : Real.sin (Real.pi * u / 2) ^ 2 ≤ C * |(gRadial u).re| := by
      dsimp only [C]
      rw [mul_comm _ |(gRadial u).re|, ← div_eq_mul_inv]
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using e8_gRadial_sine_squared_lower hu huR
    have hL : 0 < Real.pi / 2160 *
        (K / R ^ 3 * Real.exp (-5 * Real.pi * R / 2)) := by positivity
    have hi := (inv_le_inv₀ hc hL).mpr
      (mul_le_mul_of_nonneg_left (hmass R hR) (by positivity : 0 ≤ Real.pi / 2160))
    have heq : (Real.pi / 2160 *
        (K / R ^ 3 * Real.exp (-5 * Real.pi * R / 2)))⁻¹ = B := by
      dsimp [B, D]
      rw [show -5 * Real.pi * R / 2 = -(5 * Real.pi * R / 2) by ring, Real.exp_neg]
      field_simp [Real.pi_ne_zero, hK.ne', hRpos.ne', Real.exp_ne_zero]
    rw [heq] at hi
    have hsB := hs.trans (mul_le_mul_of_nonneg_right hi (abs_nonneg (gRadial u).re))
    obtain ⟨k, hk, hnear⟩ := exists_even_shell_of_sine_squared_bound (m := 1)
      (by simpa using hu) hB.le hsB
    exact ⟨k, hk, hnear.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))⟩

theorem e8_magic_even_shell_exponential_bound :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℝ, 2 < R →
      ∃ α : ℝ, 1 < α ∧ α ≤ ρ * R ^ (3 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4) ∧
        ∀ x : EuclideanSpace ℝ (Fin 8), Real.sqrt 2 ≤ ‖x‖ → ‖x‖ ≤ R →
          ∃ k : ℤ, 1 ≤ k ∧ |‖x‖ ^ 2 - 2 * k| ≤ α * Real.sqrt |(_root_.g x).re| := by
  obtain ⟨ρ, hρ, hbound⟩ := e8_gRadial_even_shell_exponential_bound
  refine ⟨ρ, hρ, ?_⟩
  intro R hR
  obtain ⟨α, hα, hαbound, hnear⟩ := hbound R hR
  refine ⟨α, hα, hαbound, ?_⟩
  intro x hx hxR
  have hx2 : 2 ≤ ‖x‖ ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg 2) hx 2
    simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using h
  have hxU : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hxR 2
  simpa only [g_apply_eq_gRadial_norm_sq] using hnear (‖x‖ ^ 2) hx2 hxU

end E8Leech
