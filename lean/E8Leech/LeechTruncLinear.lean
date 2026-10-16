import E8Leech.KronLeechH2Lin
import E8Leech.E8KernelLinearGrowth
import E8Leech.LeechUnitCost

/-!
# Linear growth of the truncated Leech kernel on the block `q ∈ [3, 4]`

The fourth bound of `LeechBlockBounds`:
`𝒦̂⁽²⁴⁾(iq, it) − e^{2πt}(a₁(q) t + a₀(q)) ≥ c₁ t` for `q ∈ [3, 4]` and `t ≥ T`.

It follows from the quantitative form `Kron.LeechTruncMargin` of the truncated inequality on the
strip `q ∈ [3, 4]`, `t ≥ T₀`,

`b² t̂ a⁵ μ < 21743271936 Λ π û t̂² Δ(it) (𝒩/(b − a)) · (𝒦̂ − e^{2πt}(a₁ t + a₀))`,

and three elementary bounds: `Δ(it) ≤ D e^{−2πt}` for large `t` (`Δ = O(q)` at the cusp),
`E₄(it) ≤ 2` for large `t` (`E₄ → 1`), and `Δ(iq) ≤ M` on `[3, 4]` (continuity). With them
`0 < 𝒩/(b − a) ≤ 16 M / a` for `t ≥ q + 1`, and the left side divided by the bounds of the factors
is `≥ c₁ t` with `c₁ = 3π e^{−24π} μ / (16 · 21743271936 Λ D M)`.

* `exists_axDelta_le`, `exists_axE4_le`: the two bounds at the cusp.
* `linear_of_margin_core`: the real-number core.
* `leech_trunc_linear_of_margin`: the linear growth from the quantitative form on the strip.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set Asymptotics
open UpperHalfPlane hiding I
open scoped Real

/-- The discriminant on the axis is at most a multiple of `e^{−2πt}` for large `t`. -/
theorem exists_axDelta_le : ∃ D Y : ℝ, 0 < D ∧ ∀ t : ℝ, 0 < t → Y ≤ t →
    axDelta (axV t) (axW t) ≤ D * Real.exp (-π * t) ^ 2 := by
  obtain ⟨C, hC⟩ := isBigO_discriminant.bound
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hC
  refine ⟨max C 1, Y, lt_of_lt_of_le one_pos (le_max_right _ _), fun t ht hYt => ?_⟩
  have h : ‖ModularForm.discriminant (imagPt t)‖ ≤
      C * ‖Real.exp (-2 * π * (imagPt t).im)‖ := hY (imagPt t) (by rw [im_imagPt ht]; exact hYt)
  have hexp : Real.exp (-2 * π * t) = Real.exp (-π * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [discriminant_imagPt_eq_ax ht, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (axDelta_pos ht), im_imagPt ht, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    hexp] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

/-- `E₄` on the axis is at most `2` for large `t`. -/
theorem exists_axE4_le : ∃ Y : ℝ, ∀ t : ℝ, 0 < t → Y ≤ t → axE4 (axV t) (axW t) ≤ 2 := by
  have hev : ∀ᶠ τ : ℍ in atImInfty, ModularForm.E₄ τ ∈ Metric.ball (1 : ℂ) 1 :=
    tendsto_eisensteinFour_atImInfty.eventually (Metric.ball_mem_nhds (1 : ℂ) one_pos)
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hev
  refine ⟨Y, fun t ht hYt => ?_⟩
  have h : ModularForm.E₄ (imagPt t) ∈ Metric.ball (1 : ℂ) 1 :=
    hY (imagPt t) (by rw [im_imagPt ht]; exact hYt)
  rw [Metric.mem_ball, dist_eq_norm, E4_imagPt_eq_ax ht] at h
  have e : ((axE4 (axV t) (axW t) : ℝ) : ℂ) - 1 = ((axE4 (axV t) (axW t) - 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h
  linarith [(abs_lt.mp h).2]

/-- `E₄ = V² + VW + W²` is nonnegative. -/
theorem axE4_nonneg (V W : ℝ) : 0 ≤ axE4 V W := by
  rw [axE4]
  nlinarith [sq_nonneg (V + W / 2), sq_nonneg W]

/-- The real-number core of the linear growth: the bounds `Δ ≤ D b²` and `R a ≤ 16 M` of the
two positive factors turn the quantitative form into a lower bound of `x`. -/
theorem linear_of_margin_core {a b th μ P Δ R x D M : ℝ} (ha : 0 < a) (hb : 0 < b) (hth : 0 < th)
    (hμ : 0 < μ) (hP : 0 < P) (hΔ : 0 < Δ) (hR : 0 < R) (hΔle : Δ ≤ D * b ^ 2)
    (hRa : R * a ≤ 16 * M) (hD : 0 < D)
    (h : b ^ 2 * (th * (a ^ 5 * μ)) < P * Δ * R * x) : th * (a ^ 6 * μ) < 16 * P * D * M * x := by
  have hL : 0 < b ^ 2 * (th * (a ^ 5 * μ)) := by positivity
  have hx0 : 0 < x := by
    by_contra hneg
    rw [not_lt] at hneg
    have hnp : P * Δ * R * x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hP.le hΔ.le) hR.le) hneg
    linarith
  have h8 := mul_lt_mul_of_pos_right h ha
  have h10 : Δ * (R * a) ≤ D * b ^ 2 * (16 * M) :=
    mul_le_mul hΔle hRa (mul_nonneg hR.le ha.le) (by positivity)
  have h11 := mul_le_mul_of_nonneg_left h10 (mul_nonneg hP.le hx0.le)
  have h7 : b ^ 2 * (th * (a ^ 6 * μ)) < b ^ 2 * (16 * P * D * M * x) := by
    calc b ^ 2 * (th * (a ^ 6 * μ)) = b ^ 2 * (th * (a ^ 5 * μ)) * a := by ring
      _ < P * Δ * R * x * a := h8
      _ = P * x * (Δ * (R * a)) := by ring
      _ ≤ P * x * (D * b ^ 2 * (16 * M)) := h11
      _ = b ^ 2 * (16 * P * D * M * x) := by ring
  exact lt_of_mul_lt_mul_left h7 (pow_pos hb 2).le

/-- The constants of the quantitative form in terms of `q` and `t`. -/
theorem linear_const_core {C q t A D M x : ℝ} (hq : 0 < q) (ht : 0 < t)
    (h : 1 / (π * t) * A < 16 * (C * π * (1 / (π * q)) * (1 / (π * t)) ^ 2) * D * M * x) :
    A * (q * (π * t)) < 16 * C * D * M * x := by
  have hπ := Real.pi_pos
  have e : 16 * (C * π * (1 / (π * q)) * (1 / (π * t)) ^ 2) * D * M * x =
      1 / (π * t) * (16 * C * D * M * x / (q * (π * t))) := by
    field_simp
  rw [e] at h
  have h1 := lt_of_mul_lt_mul_left h (by positivity : (0 : ℝ) ≤ 1 / (π * t))
  rwa [lt_div_iff₀ (by positivity)] at h1

/-- `𝒩 ≥ −8M` when `Δ(iq) ≤ M` and `0 ≤ E₄(it) ≤ 2`. -/
theorem axNu_ge_core {Δq Δt Eq Et M : ℝ} (hΔq : Δq ≤ M) (hM : 0 < M) (hEt0 : 0 ≤ Et)
    (hEt : Et ≤ 2) (hΔt : 0 ≤ Δt) (hEq : 0 ≤ Eq) : -(8 * M) ≤ Δt * Eq ^ 3 - Δq * Et ^ 3 := by
  have hEt3 : Et ^ 3 ≤ 8 := (pow_le_pow_left₀ hEt0 hEt 3).trans (by norm_num)
  have h1 : Δq * Et ^ 3 ≤ M * 8 := mul_le_mul hΔq hEt3 (pow_nonneg hEt0 3) hM.le
  have h2 : 0 ≤ Δt * Eq ^ 3 := mul_nonneg hΔt (pow_nonneg hEq 3)
  linarith

/-- The divided denominator times `a` is at most `16 M` when `b ≤ a/2`. -/
theorem divided_mul_le_core {a b R N M : ℝ} (hR : 0 < R) (hba : b ≤ a / 2)
    (hRδ : R * (b - a) = N) (hN : -(8 * M) ≤ N) : R * a ≤ 16 * M := by
  have h1 : a ≤ 2 * (a - b) := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hR.le
  have h3 : R * (2 * (a - b)) = -2 * (R * (b - a)) := by ring
  rw [hRδ] at h3
  linarith

theorem exp_neg_pi_le_half : Real.exp (-π) ≤ 1 / 2 := by
  have h4 : 2 ≤ Real.exp π := by linarith [Real.add_one_le_exp π, Real.pi_gt_three]
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-- `e^{−πt} ≤ e^{−πq}/2` for `t ≥ q + 1`. -/
theorem exp_neg_pi_le_half_of_add_one_le {q t : ℝ} (h : q + 1 ≤ t) :
    Real.exp (-π * t) ≤ Real.exp (-π * q) / 2 := by
  have hπ := Real.pi_pos
  have h0 : π * (q + 1) ≤ π * t := mul_le_mul_of_nonneg_left h hπ.le
  have h1 : Real.exp (-π * t) ≤ Real.exp (-π * (q + 1)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-π * (q + 1)) = Real.exp (-π * q) * Real.exp (-π) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 := mul_le_mul_of_nonneg_left exp_neg_pi_le_half (Real.exp_pos (-π * q)).le
  rw [h2] at h1
  linarith

/-- The divided denominator `𝒩/(b − a)` times `a` is at most `16 M` on the strip. -/
theorem axNu_div_mul_le {q t M : ℝ} (hq0 : 0 < q) (ht0 : 0 < t) (hqt : q + 1 ≤ t)
    (hprod : 1 < q * t) (hM : 0 < M) (hΔqle : axDelta (axV q) (axW q) ≤ M)
    (hEtle : axE4 (axV t) (axW t) ≤ 2) :
    axNu (axV q) (axW q) (axV t) (axW t) / (Real.exp (-π * t) - Real.exp (-π * q)) *
      Real.exp (-π * q) ≤ 16 * M := by
  have hba := exp_neg_pi_le_half_of_add_one_le hqt
  have ha : 0 < Real.exp (-π * q) := Real.exp_pos _
  have hN := ckmrvAxisDividedDenominator_pos hq0 ht0 (by linarith : q ≠ t) hprod
  have hδ : Real.exp (-π * t) - Real.exp (-π * q) ≠ 0 := by
    have h : Real.exp (-π * t) - Real.exp (-π * q) < 0 := by linarith
    exact h.ne
  have hNge : -(8 * M) ≤ axNu (axV q) (axW q) (axV t) (axW t) :=
    axNu_ge_core hΔqle hM (axE4_nonneg _ _) hEtle (axDelta_pos ht0).le (axE4_nonneg _ _)
  exact divided_mul_le_core hN hba (div_mul_cancel₀ _ hδ) hNge

/-- **The linear lower bound at a point of the strip** from the quantitative form and the three
bounds of the generators. -/
theorem leech_trunc_linear_point {Λ : ℕ} (hΛ : 0 < Λ) {μ : ℚ} (hμ : 0 < μ) {D M q t : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hq : q ∈ Icc (3 : ℝ) 4) (ht5 : 5 ≤ t)
    (hΔtle : axDelta (axV t) (axW t) ≤ D * Real.exp (-π * t) ^ 2)
    (hEtle : axE4 (axV t) (axW t) ≤ 2) (hΔqle : axDelta (axV q) (axW q) ≤ M)
    (hm : Kron.LeechTruncMargin Λ μ q t) :
    Real.exp (-(24 * π)) * μ * (3 * π) / (16 * 21743271936 * Λ * D * M) * t ≤
      leechDualKernel (q, t) -
        ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
          Real.exp (2 * π * t) := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have hμ' : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hq0 : 0 < q := by linarith [hq.1]
  have ht0 : 0 < t := by linarith
  have hF : 0 < 16 * 21743271936 * (Λ : ℝ) * D * M := by positivity
  have hprod : 1 < q * t :=
    calc (1 : ℝ) < 3 * 5 := by norm_num
      _ ≤ q * t := mul_le_mul hq.1 ht5 (by norm_num) hq0.le
  have hqt : q + 1 ≤ t := by linarith [hq.2]
  have hN := ckmrvAxisDividedDenominator_pos hq0 ht0 (by linarith : q ≠ t) hprod
  have hRa := axNu_div_mul_le hq0 ht0 hqt hprod hM hΔqle hEtle
  have hth : 0 < 1 / (π * t) := by positivity
  have hP : 0 < 21743271936 * (Λ : ℝ) * π * (1 / (π * q)) * (1 / (π * t)) ^ 2 := by positivity
  have h6 := linear_of_margin_core (Real.exp_pos (-π * q)) (Real.exp_pos (-π * t)) hth hμ' hP
    (axDelta_pos ht0) hN hΔtle hRa hD hm
  have h13 := linear_const_core hq0 ht0 h6
  have ha6 : Real.exp (-(24 * π)) ≤ Real.exp (-π * q) ^ 6 := by
    rw [← Real.exp_nat_mul]
    have h0 : π * q ≤ π * 4 := mul_le_mul_of_nonneg_left hq.2 hπ.le
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have h14 : Real.exp (-(24 * π)) * μ * (3 * π) * t ≤
      Real.exp (-π * q) ^ 6 * μ * (q * (π * t)) := by
    have h15 : Real.exp (-(24 * π)) * μ ≤ Real.exp (-π * q) ^ 6 * μ :=
      mul_le_mul_of_nonneg_right ha6 hμ'.le
    have h16 : 3 * (π * t) ≤ q * (π * t) := mul_le_mul_of_nonneg_right hq.1 (by positivity)
    calc Real.exp (-(24 * π)) * μ * (3 * π) * t =
          Real.exp (-(24 * π)) * μ * (3 * (π * t)) := by ring
      _ ≤ Real.exp (-π * q) ^ 6 * μ * (q * (π * t)) :=
          mul_le_mul h15 h16 (by positivity) (by positivity)
  have hkernel : leechDualKernel (q, t) = (ckmrvLeechHatKernel (imagPt q) (imagPt t)).re := rfl
  rw [hkernel, div_mul_eq_mul_div, div_le_iff₀ hF]
  calc Real.exp (-(24 * π)) * μ * (3 * π) * t ≤
        Real.exp (-π * q) ^ 6 * μ * (q * (π * t)) := h14
    _ ≤ 16 * (21743271936 * Λ) * D * M *
        ((ckmrvLeechHatKernel (imagPt q) (imagPt t)).re -
          Real.exp (2 * π * t) *
            ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re)) := h13.le
    _ = ((ckmrvLeechHatKernel (imagPt q) (imagPt t)).re -
          ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
            Real.exp (2 * π * t)) * (16 * 21743271936 * Λ * D * M) := by ring

/-- **Linear growth of the truncated Leech kernel on the block** from the quantitative form of the
truncated inequality on the strip `q ∈ [3, 4]`, `t ≥ T₀`. -/
theorem leech_trunc_linear_of_margin {Λ : ℕ} (hΛ : 0 < Λ) {μ : ℚ} (hμ : 0 < μ) {T₀ : ℝ}
    (h : ∀ q ∈ Icc (3 : ℝ) 4, ∀ t : ℝ, T₀ ≤ t → Kron.LeechTruncMargin Λ μ q t) :
    ∃ c₁ T : ℝ, 0 < c₁ ∧ 4 < T ∧ ∀ q ∈ Icc (3 : ℝ) 4, ∀ t : ℝ, T ≤ t →
      c₁ * t ≤ leechDualKernel (q, t) -
        ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
          Real.exp (2 * π * t) := by
  have hπ := Real.pi_pos
  have hΛ' : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have hμ' : (0 : ℝ) < μ := by exact_mod_cast hμ
  obtain ⟨D, Y₁, hD, hΔle⟩ := exists_axDelta_le
  obtain ⟨Y₂, hE4le⟩ := exists_axE4_le
  obtain ⟨M₀, hM₀⟩ := exists_bound_axis34 mdifferentiable_modularDiscriminant.continuous
  have hM : 0 < max M₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨Real.exp (-(24 * π)) * μ * (3 * π) / (16 * 21743271936 * Λ * D * max M₀ 1),
    max (max T₀ 5) (max Y₁ Y₂), by positivity, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (4 : ℝ) < 5)
      (le_trans (le_max_right T₀ 5) (le_max_left _ _))
  intro q hq t ht
  have hq0 : 0 < q := by linarith [hq.1]
  have ht5 : 5 ≤ t := le_trans (le_trans (le_max_right T₀ 5) (le_max_left _ _)) ht
  have hT₀ : T₀ ≤ t := le_trans (le_trans (le_max_left T₀ 5) (le_max_left _ _)) ht
  have hY₁ : Y₁ ≤ t := le_trans (le_trans (le_max_left Y₁ Y₂) (le_max_right _ _)) ht
  have hY₂ : Y₂ ≤ t := le_trans (le_trans (le_max_right Y₁ Y₂) (le_max_right _ _)) ht
  have ht0 : 0 < t := by linarith
  have hΔqle : axDelta (axV q) (axW q) ≤ max M₀ 1 := by
    have h1 := hM₀ (imagPt q) ⟨q, hq, rfl⟩
    rw [discriminant_imagPt_eq_ax hq0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (axDelta_pos hq0)] at h1
    exact le_trans h1 (le_max_left _ _)
  exact leech_trunc_linear_point hΛ hμ hD hM hq ht5 (hΔle t ht0 hY₁) (hE4le t ht0 hY₂) hΔqle
    (h q hq t hT₀)

end E8Leech
