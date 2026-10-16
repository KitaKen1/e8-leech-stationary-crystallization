import E8Leech.LaplaceExponentialLower

/-!
# An exponential lower bound from a small-parameter Laplace kernel, general power

The version of `laplace_integral_exponential_lower` for a kernel lower bound
`k * t ^ m * exp (-pi / t)` with an arbitrary power `m`: integrating over `[1/R, 2/R]` gives
`k / R ^ (m + 1) * exp (-5 * pi * R / 2)`. The case `m = 2` is the `E8` kernel; the Leech kernel
has `m = 10`.
-/

namespace E8Leech

open MeasureTheory Set

theorem laplace_integrand_lower_on_reciprocal_interval_pow {R t κ : ℝ} (m : ℕ)
    (hR : 0 < R) (hκ : 0 ≤ κ) (htlo : 1 / R ≤ t) (hthi : t ≤ 2 / R) :
    κ / R ^ m * Real.exp (-5 * Real.pi * R / 2) ≤
      (κ * t ^ m * Real.exp (-Real.pi / t)) * Real.exp (-Real.pi * R ^ 2 * t) := by
  have ht : 0 < t := (one_div_pos.mpr hR).trans_le htlo
  have hpow : 1 / R ^ m ≤ t ^ m := by
    simpa only [div_pow, one_pow] using
      pow_le_pow_left₀ (one_div_nonneg.mpr hR.le) htlo m
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
    _ = κ * (1 / R ^ m) * Real.exp (-5 * Real.pi * R / 2) := by ring
    _ ≤ κ * t ^ m * Real.exp (-5 * Real.pi * R / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hκ) (Real.exp_pos _).le
    _ ≤ κ * t ^ m *
        (Real.exp (-Real.pi / t) * Real.exp (-Real.pi * R ^ 2 * t)) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hκ (pow_nonneg ht.le m))
    _ = _ := by ring

/-- Restrict a nonnegative Laplace integral to a reciprocal interval, for a kernel bounded below
by `κ * t ^ m * exp (-π / t)` near zero. -/
theorem laplace_integral_exponential_lower_pow {K : ℝ → ℝ} {κ t₀ R : ℝ} (m : ℕ)
    (hκ : 0 ≤ κ) (ht₀ : 0 < t₀) (hR : 0 < R) (hlarge : 2 / t₀ ≤ R)
    (hK : ∀ t : ℝ, 0 < t → 0 ≤ K t)
    (hlower : ∀ t : ℝ, 0 < t → t ≤ t₀ →
      κ * t ^ m * Real.exp (-Real.pi / t) ≤ K t)
    (hint : IntegrableOn (fun t : ℝ => K t * Real.exp (-Real.pi * R ^ 2 * t)) (Ioi 0)) :
    κ / R ^ (m + 1) * Real.exp (-5 * Real.pi * R / 2) ≤
      ∫ t in Ioi (0 : ℝ), K t * Real.exp (-Real.pi * R ^ 2 * t) := by
  have hRt₀ : 2 / R ≤ t₀ := by
    apply (div_le_iff₀ hR).mpr
    nlinarith [(div_le_iff₀ ht₀).mp hlarge]
  have hsub : Icc (1 / R) (2 / R) ⊆ Ioi (0 : ℝ) :=
    fun t ht => (one_div_pos.mpr hR).trans_le ht.1
  have hpoint : ∀ t ∈ Icc (1 / R) (2 / R),
      κ / R ^ m * Real.exp (-5 * Real.pi * R / 2) ≤
        K t * Real.exp (-Real.pi * R ^ 2 * t) := by
    intro t ht
    exact (laplace_integrand_lower_on_reciprocal_interval_pow m hR hκ ht.1 ht.2).trans
      (mul_le_mul_of_nonneg_right
        (hlower t (hsub ht) (ht.2.trans hRt₀)) (Real.exp_pos _).le)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => K t * Real.exp (-Real.pi * R ^ 2 * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (hK t ht) (Real.exp_pos _).le
  have hconst : (∫ _ in Icc (1 / R) (2 / R),
      κ / R ^ m * Real.exp (-5 * Real.pi * R / 2)) =
        κ / R ^ (m + 1) * Real.exp (-5 * Real.pi * R / 2) := by
    rw [setIntegral_const]
    have hvol : volume.real (Icc (1 / R) (2 / R)) = 1 / R := by
      have hwidth : 2 / R - 1 / R = 1 / R := by ring
      rw [measureReal_def, Real.volume_Icc, hwidth,
        ENNReal.toReal_ofReal (one_div_nonneg.mpr hR.le)]
    rw [hvol, smul_eq_mul, pow_succ]
    field_simp [hR.ne']
  rw [← hconst]
  have hcint : IntegrableOn
      (fun _ : ℝ => κ / R ^ m * Real.exp (-5 * Real.pi * R / 2)) (Icc (1 / R) (2 / R)) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply le_trans (setIntegral_mono_on hcint (hint.mono_set hsub)
    measurableSet_Icc hpoint)
  exact setIntegral_mono_set hint hnonneg (Filter.Eventually.of_forall hsub)

end E8Leech
