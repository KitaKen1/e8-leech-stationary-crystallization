import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantitative approximation by even squared lengths

The elementary part of BRR Lemma 2.2: rounding `u / 2` chooses an even
integer at distance at most one, and the sine chord bound controls that
distance. The lower bound on the shell index is retained, including at the
first shell. This file has no premise about a magic function or a packing.
-/

namespace E8Leech

theorem sine_squared_lower_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    x ^ 2 ≤ Real.sin (Real.pi * x / 2) ^ 2 := by
  have hpos : ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
      y ^ 2 ≤ Real.sin (Real.pi * y / 2) ^ 2 := by
    intro y hy hy1
    have hphase : Real.pi * y / 2 ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin (by positivity : 0 ≤ Real.pi * y / 2) hphase
    have hcancel : 2 / Real.pi * (Real.pi * y / 2) = y := by field_simp
    rw [hcancel] at hs
    exact pow_le_pow_left₀ hy hs 2
  by_cases hx0 : 0 ≤ x
  · exact hpos x hx0 (by simpa only [abs_of_nonneg hx0] using hx)
  · have hn : 0 ≤ -x := by linarith
    have hs := hpos (-x) hn (by simpa only [abs_of_neg (lt_of_not_ge hx0)] using hx)
    simpa only [neg_sq, mul_neg, neg_div, Real.sin_neg] using hs

theorem sine_squared_even_shift (u : ℝ) (k : ℤ) :
    Real.sin (Real.pi * (u - 2 * k) / 2) ^ 2 =
      Real.sin (Real.pi * u / 2) ^ 2 := by
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  have hphase : 2 * (Real.pi * (u - 2 * k) / 2) =
      2 * (Real.pi * u / 2) - k * (2 * Real.pi) := by ring
  rw [hphase, Real.cos_sub_int_mul_two_pi]

/-- A nearest even shell, with its lower index bound and a quantitative sine estimate. -/
theorem exists_even_shell_sine_squared {u : ℝ} {m : ℤ} (hu : 2 * (m : ℝ) ≤ u) :
    ∃ k : ℤ, m ≤ k ∧ |u - 2 * k| ≤ 1 ∧
      (u - 2 * k) ^ 2 ≤ Real.sin (Real.pi * u / 2) ^ 2 := by
  let k := round (u / 2)
  have hknear : |u - 2 * k| ≤ 1 := by
    have h := abs_sub_round (u / 2)
    have heq : |u - 2 * k| = 2 * |u / 2 - k| := by
      rw [← abs_of_pos (by norm_num : (0 : ℝ) < 2), ← abs_mul]
      congr 1
      ring
    rw [heq]
    linarith
  have hklower : m ≤ k := by
    have h := sub_half_lt_round (u / 2)
    have hm : ((m - 1 : ℤ) : ℝ) < k := by
      push_cast
      dsimp [k]
      linarith
    have hm' : m - 1 < k := by exact_mod_cast hm
    omega
  refine ⟨k, hklower, hknear, ?_⟩
  exact (sine_squared_lower_of_abs_le_one hknear).trans_eq (sine_squared_even_shift u k)

/-- Transfer a sine-squared bound to a square-root bound for an even shell. -/
theorem exists_even_shell_of_sine_squared_bound {u C y : ℝ} {m : ℤ}
    (hu : 2 * (m : ℝ) ≤ u) (hC : 0 ≤ C)
    (hs : Real.sin (Real.pi * u / 2) ^ 2 ≤ C * |y|) :
    ∃ k : ℤ, m ≤ k ∧ |u - 2 * k| ≤ Real.sqrt C * Real.sqrt |y| := by
  obtain ⟨k, hk, _, hsq⟩ := exists_even_shell_sine_squared hu
  refine ⟨k, hk, ?_⟩
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hC, Real.sq_sqrt (abs_nonneg y)]
  exact hsq.trans hs

end E8Leech
