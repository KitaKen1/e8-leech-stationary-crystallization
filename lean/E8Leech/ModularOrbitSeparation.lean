import E8Leech.GaussianParameterNormalization

/-!
# An elementary modular-orbit exclusion for the positive kernel block

For integral a,b,c,d with ad-bc=1, the imaginary part of the actual Mobius
image of I*v is v/(d^2+c^2*v^2). If 1 <= v <= 2 it is at most 2.
Thus I*q, with 3 <= q <= 4, cannot be in that modular orbit.

This proves the geometric exclusion. Identifying equality of modular
j-values with orbit equivalence is a separate analytic input.
-/

noncomputable section

namespace E8Leech

open Set

theorem integer_mobius_pure_imaginary_im (a b c d : ℤ)
    (hdet : a * d - b * c = 1) (v : ℝ) :
    (((a : ℂ) * (Complex.I * v) + b) /
      ((c : ℂ) * (Complex.I * v) + d)).im =
      v / ((d : ℝ) ^ 2 + (c : ℝ) ^ 2 * v ^ 2) := by
  have hd : (a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ) = 1 := by exact_mod_cast hdet
  have hn : (a : ℝ) * v * (d : ℝ) - (b : ℝ) * ((c : ℝ) * v) = v := by
    calc
      _ = ((a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ)) * v := by ring
      _ = v := by rw [hd]; ring
  simp only [Complex.div_im, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [zero_mul, mul_zero, zero_add, add_zero, sub_zero, one_mul]
  rw [← sub_div, hn]
  congr 1
  ring

theorem integer_mobius_pure_imaginary_im_le_two (a b c d : ℤ)
    (hdet : a * d - b * c = 1) {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 2) :
    (((a : ℂ) * (Complex.I * v) + b) /
      ((c : ℂ) * (Complex.I * v) + d)).im ≤ 2 := by
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_cases hc : c = 0
    · right
      intro hd
      simp [hc, hd] at hdet
    · exact Or.inl hc
  have hsq (n : ℤ) (hn : n ≠ 0) : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hn' : n ≤ -1 ∨ 1 ≤ n := by omega
    rcases hn' with hn' | hn'
    · have h : (n : ℝ) ≤ -1 := by exact_mod_cast hn'
      nlinarith only [h, sq_nonneg ((n : ℝ) + 1)]
    · have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      nlinarith only [h, sq_nonneg ((n : ℝ) - 1)]
  have hden : 1 ≤ (d : ℝ) ^ 2 + (c : ℝ) ^ 2 * v ^ 2 := by
    rcases hcd with hc | hd
    · have h := hsq c hc
      have hv_sq : (1 : ℝ) ≤ v ^ 2 := by
        nlinarith only [hv.1, sq_nonneg (v - 1)]
      have hprod : (1 : ℝ) ≤ (c : ℝ) ^ 2 * v ^ 2 :=
        by simpa using mul_le_mul h hv_sq (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (c : ℝ))
      exact hprod.trans (le_add_of_nonneg_left (sq_nonneg (d : ℝ)))
    · have h := hsq d hd
      exact h.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg (c : ℝ)) (sq_nonneg v)))
  rw [integer_mobius_pure_imaginary_im a b c d hdet]
  apply (div_le_iff₀ (by linarith : 0 < (d : ℝ) ^ 2 + (c : ℝ) ^ 2 * v ^ 2)).mpr
  linarith only [hv.2, hden]

theorem gaussian_dual_not_integer_mobius_image (a b c d : ℤ)
    (hdet : a * d - b * c = 1) {α v : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3)) (hv : v ∈ Icc (1 : ℝ) 2) :
    Complex.I * (Real.pi / α : ℝ) ≠
      ((a : ℂ) * (Complex.I * v) + b) / ((c : ℂ) * (Complex.I * v) + d) := by
  intro h
  have him := congrArg Complex.im h
  have hle := integer_mobius_pure_imaginary_im_le_two a b c d hdet hv
  have hq := gaussian_dual_compact_interval hα
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add] at him
  linarith only [hq.1, him, hle]

end E8Leech
