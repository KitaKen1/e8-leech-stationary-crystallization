import E8Leech.CompactQuadraticSlack

/-!
# A separated Laplace block for every compact positive Gaussian interval

Keep the unit-length block [V,V+1] instead of [1,2]. The explicit choice
V = max(1, pi/a, b/pi) + 2 avoids both q=v and q=1/v for
alpha in [a,b], q=pi/alpha. Compact positivity on this block gives full-radius
quadratic slack without differentiating the improper integral.
Actual CKMRV kernels, signs, integrability and representations remain inputs.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Classical

def gaussianSeparatedBlockStart (a b : ℝ) : ℝ :=
  max 1 (max (Real.pi / a) (b / Real.pi)) + 2

theorem gaussian_dual_interval {a b α : ℝ} (ha : 0 < a) (hα : α ∈ Icc a b) :
    Real.pi / α ∈ Icc (Real.pi / b) (Real.pi / a) := by
  have hα0 : 0 < α := ha.trans_le hα.1
  have hb : 0 < b := hα0.trans_le hα.2
  constructor
  · exact div_le_div_of_nonneg_left Real.pi_pos.le hα0 hα.2
  · exact div_le_div_of_nonneg_left Real.pi_pos.le ha hα.1

theorem gaussianSeparatedBlockStart_pos (a b : ℝ) :
    0 < gaussianSeparatedBlockStart a b := by
  have h := le_max_left (1 : ℝ) (max (Real.pi / a) (b / Real.pi))
  dsimp [gaussianSeparatedBlockStart]
  linarith

theorem gaussian_separated_block_above_dual {a b α v : ℝ}
    (ha : 0 < a) (hα : α ∈ Icc a b)
    (hv : v ∈ Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1)) :
    2 ≤ v - Real.pi / α := by
  have hq := (gaussian_dual_interval ha hα).2
  have hmax := (le_max_left (Real.pi / a) (b / Real.pi)).trans
    (le_max_right (1 : ℝ) (max (Real.pi / a) (b / Real.pi)))
  dsimp [gaussianSeparatedBlockStart] at hv
  linarith only [hv.1, hq, hmax]

theorem gaussian_separated_block_below_inverse_dual {a b α v : ℝ}
    (ha : 0 < a) (hα : α ∈ Icc a b)
    (hv : v ∈ Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1)) :
    1 / v < Real.pi / α := by
  have hα0 : 0 < α := ha.trans_le hα.1
  have hb : 0 < b := hα0.trans_le hα.2
  have hv0 : 0 < v := (gaussianSeparatedBlockStart_pos a b).trans_le hv.1
  have hmax := (le_max_right (Real.pi / a) (b / Real.pi)).trans
    (le_max_right (1 : ℝ) (max (Real.pi / a) (b / Real.pi)))
  have hbv : b / Real.pi < v := by
    dsimp [gaussianSeparatedBlockStart] at hv
    linarith only [hv.1, hmax]
  have hprod : b < v * Real.pi := (div_lt_iff₀ Real.pi_pos).mp hbv
  have hrec : 1 / v < Real.pi / b := by
    apply (div_lt_div_iff₀ hv0 hb).mpr
    simpa only [one_mul, mul_one, mul_comm] using hprod
  exact hrec.trans_le (gaussian_dual_interval ha hα).1

theorem gaussian_separated_block_avoids_diagonals {a b α v : ℝ}
    (ha : 0 < a) (hα : α ∈ Icc a b)
    (hv : v ∈ Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1)) :
    Real.pi / α ≠ v ∧ Real.pi / α ≠ 1 / v := by
  constructor
  · have h := gaussian_separated_block_above_dual ha hα hv
    intro heq
    rw [heq, sub_self] at h
    norm_num at h
  · exact (gaussian_separated_block_below_inverse_dual ha hα hv).ne'

theorem laplace_factor_lower_from_shifted_block {K : ℝ → ℝ} {B V u : ℝ}
    (hV : 0 < V) (hu : u ^ 2 ≤ 4)
    (hK : ∀ t : ℝ, 0 < t → 0 ≤ K t)
    (hblock : ∀ t ∈ Icc V (V + 1), B ≤ K t)
    (hint : IntegrableOn (fun t => K t * Real.exp (-Real.pi * u ^ 2 * t))
      (Ioi (0 : ℝ)) volume) :
    B * Real.exp (-4 * Real.pi * (V + 1)) ≤
      ∫ t in Ioi (0 : ℝ), K t * Real.exp (-Real.pi * u ^ 2 * t) := by
  have hsub : Icc V (V + 1) ⊆ Ioi (0 : ℝ) := fun _ ht => hV.trans_le ht.1
  have hlow : ∀ t ∈ Icc V (V + 1), B * Real.exp (-4 * Real.pi * (V + 1)) ≤
      K t * Real.exp (-Real.pi * u ^ 2 * t) := by
    intro t ht
    have hproduct : u ^ 2 * t ≤ 4 * (V + 1) :=
      (mul_le_mul_of_nonneg_right hu (hsub ht).le).trans
        (mul_le_mul_of_nonneg_left ht.2 (by norm_num))
    have hexp : Real.exp (-4 * Real.pi * (V + 1)) ≤
        Real.exp (-Real.pi * u ^ 2 * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hproduct)]
    exact mul_le_mul (hblock t ht) hexp (Real.exp_pos _).le (hK t (hsub ht))
  have hlower := setIntegral_ge_of_const_le_real (μ := volume) measurableSet_Icc
    (by simp : volume (Icc V (V + 1)) ≠ ∞) hlow (hint.mono_set hsub)
  have hmass : volume.real (Icc V (V + 1)) = 1 := by
    simp [Measure.real, Real.volume_Icc]
  rw [hmass, mul_one] at hlower
  refine hlower.trans (setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall hsub))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (hK t ht) (Real.exp_pos _).le

theorem gaussian_normalized_shifted_laplace_block_lower (m : ℕ) (K : ℝ × ℝ → ℝ)
    {a b B V α u : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (hV : 0 < V)
    (hα : α ∈ Icc a b) (hu : u ^ 2 ≤ 4)
    (hnonneg : ∀ v : ℝ, 0 < v → 0 ≤ K (Real.pi / α, v))
    (hblock : ∀ v ∈ Icc V (V + 1), B ≤ K (Real.pi / α, v))
    (hint : IntegrableOn (fun v => K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))
      (Ioi (0 : ℝ)) volume) :
    (Real.pi / b) ^ m * B * Real.exp (-4 * Real.pi * (V + 1)) ≤
      (Real.pi / α) ^ m * ∫ v in Ioi (0 : ℝ),
        K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v) := by
  have hq := gaussian_dual_interval ha hα
  have hb : 0 < b := (ha.trans_le hα.1).trans_le hα.2
  have hq0 : 0 < Real.pi / b := div_pos Real.pi_pos hb
  have hpow := pow_le_pow_left₀ hq0.le hq.1 m
  rw [← integral_gaussianDualLaplaceKernel]
  apply laplace_factor_lower_from_shifted_block hV hu ?_ ?_
    (integrableOn_gaussianDualLaplaceKernel m K α u hint)
  · intro v hv
    exact mul_nonneg (pow_nonneg (hq0.le.trans hq.1) m) (hnonneg v hv)
  · intro v hv
    exact mul_le_mul hpow (hblock v hv) hB (pow_nonneg (hq0.le.trans hq.1) m)

theorem uniform_full_quadratic_slack_of_shifted_laplace_kernel
    (m : ℕ) {a b r V : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4) (hV : 0 < V)
    (φ K : ℝ × ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc a b ×ˢ Icc 0 (7 / 8 * r)))
    (horigin : ∀ α ∈ Icc a b, 0 < φ (α, 0))
    (hinterior : ∀ α ∈ Icc a b, ∀ u : ℝ, 0 < u → u < r → 0 < φ (α, u))
    (hK : ContinuousOn K (Icc (Real.pi / b) (Real.pi / a) ×ˢ Icc V (V + 1)))
    (hKpos : ∀ p ∈ Icc (Real.pi / b) (Real.pi / a) ×ˢ Icc V (V + 1), 0 < K p)
    (hKnonneg : ∀ q ∈ Icc (Real.pi / b) (Real.pi / a), ∀ v : ℝ, 0 < v → 0 ≤ K (q, v))
    (hint : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      IntegrableOn (fun v => K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))
        (Ioi (0 : ℝ)) volume)
    (hfactor : ∀ α ∈ Icc a b, ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = (Real.pi / α) ^ m * (4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ v in Ioi (0 : ℝ), K (Real.pi / α, v) * Real.exp (-Real.pi * u ^ 2 * v))) :
    ∃ c : ℝ, 0 < c ∧ ∀ α ∈ Icc a b, ∀ u ∈ Icc (0 : ℝ) r,
      c * (r - u) ^ 2 ≤ φ (α, u) := by
  obtain ⟨A, hA, hlA⟩ := compact_rectangle_positive_lower hφ
    (compact_far_positive_of_origin_and_interior hr φ horigin hinterior)
  obtain ⟨B, hB, hlB⟩ := compact_rectangle_positive_lower hK hKpos
  let c := 4 * (Real.pi / b) ^ m * B * Real.exp (-4 * Real.pi * (V + 1)) * r ^ 2
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨min (A / r ^ 2) c, lt_min (div_pos hA (pow_pos hr 2)) hc, ?_⟩
  intro α hα u hu
  apply full_quadratic_slack_of_two_regions hA hr hu (hlA α hα)
  intro v hv
  have hv0 : 0 ≤ v := by linarith only [hv.1, hr]
  have hvsq := pow_le_pow_left₀ hv0 hv.2 2
  have hfour : v ^ 2 ≤ 4 := by rcases hroot with h | h <;> linarith only [hvsq, h]
  have hq := gaussian_dual_interval ha hα
  have hJ := gaussian_normalized_shifted_laplace_block_lower m K ha hB.le hV hα hfour
    (hKnonneg _ hq) (hlB _ hq) (hint α hα v hv)
  have hsin := sine_squared_even_root_lower hr hroot hv.1 hv.2
  rw [hfactor α hα v hv]
  calc
    c * (r - v) ^ 2 = 4 * (r ^ 2 * (r - v) ^ 2) *
        ((Real.pi / b) ^ m * B * Real.exp (-4 * Real.pi * (V + 1))) := by dsimp [c]; ring
    _ ≤ 4 * Real.sin (Real.pi * v ^ 2 / 2) ^ 2 *
        ((Real.pi / b) ^ m * B * Real.exp (-4 * Real.pi * (V + 1))) := by gcongr
    _ ≤ 4 * Real.sin (Real.pi * v ^ 2 / 2) ^ 2 *
        ((Real.pi / α) ^ m * ∫ w in Ioi (0 : ℝ),
          K (Real.pi / α, w) * Real.exp (-Real.pi * v ^ 2 * w)) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = _ := by ring

end E8Leech
