import E8Leech.GaussianMixtureCrystallization

/-!
# Uniform linear growth of the E8 dual kernel near the self-dual parameter

The existing uniform cusp estimates apply on every compact positive imaginary
interval. The cusp slope is continuous and positive at q=1, hence bounded
below on a left neighborhood. This supplies the uniform small-radius cost
needed when Gaussian parameters decrease to π from the right.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Set Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold

theorem exists_bound_imaginary_interval {a b : ℝ} (ha : 0 < a)
    {g : ℍ → ℂ} (hg : Continuous g) :
    ∃ M : ℝ, ∀ τ ∈ imagPt '' Icc a b, ‖g τ‖ ≤ M := by
  have hc : ContinuousOn (fun q : ℝ => g (imagPt q)) (Icc a b) :=
    (hg.comp_continuousOn continuousOn_ofComplex_I_mul).mono
      (fun q hq => ha.trans_le hq.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨M, by rintro _ ⟨q, hq, rfl⟩; exact hM q hq⟩

def e8KernelSlope (q : ℝ) : ℝ := π * q / 6 *
  (EisensteinSeries.E2 (imagPt q) * ModularForm.E₄ (imagPt q) - ModularForm.E₆ (imagPt q)).re

theorem e8KernelSlope_eq {q : ℝ} (hq : 0 < q) :
    e8KernelSlope q = π * q / 6 * (eisensteinTwoQ (imaginaryNome q) *
      eisensteinFourQ (imaginaryNome q) - eisensteinSixQ (imaginaryNome q)) := by
  rw [e8KernelSlope, axis_E2E4E6_eq hq, Complex.ofReal_re]

theorem continuousOn_e8KernelSlope : ContinuousOn e8KernelSlope (Ioi 0) := by
  have hc := continuousOn_re_imagPt
    ((E2_mdifferentiable.continuous.mul (ModularFormClass.continuous ModularForm.E₄)).sub
      (ModularFormClass.continuous ModularForm.E₆))
  exact ((continuousOn_const.mul continuousOn_id).div_const 6).mul hc

theorem e8KernelSlope_one_pos : 0 < e8KernelSlope 1 := by
  rw [e8KernelSlope_eq (by norm_num : (0 : ℝ) < 1)]
  have h := eisenstein_two_four_six_lower (imaginaryNome_pos 1).le
    (imaginaryNome_small (by norm_num : (1 : ℝ) ≤ 1))
  exact mul_pos (by positivity)
    ((mul_pos (by norm_num : (0 : ℝ) < 700) (imaginaryNome_pos 1)).trans_le h)

theorem exists_e8KernelSlope_left_lower :
    ∃ a m : ℝ, 0 < a ∧ a < 1 ∧ 0 < m ∧ ∀ q ∈ Icc a 1, m ≤ e8KernelSlope q := by
  have hc : ContinuousAt e8KernelSlope 1 :=
    continuousOn_e8KernelSlope.continuousAt (isOpen_Ioi.mem_nhds (by norm_num))
  have hpos := e8KernelSlope_one_pos
  have hev : ∀ᶠ q : ℝ in 𝓝 1, e8KernelSlope 1 / 2 < e8KernelSlope q :=
    hc.tendsto.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hev
  let η := min (1 / 2 : ℝ) (ε / 2)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hηε : η < ε := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨1 - η, e8KernelSlope 1 / 2, by linarith, by linarith, by positivity, ?_⟩
  intro q hq
  apply (he ?_).le
  rw [Real.dist_eq, abs_of_nonpos (by linarith only [hq.2])]
  linarith only [hq.1, hηε]

theorem e8_kernel_linear_growth_of_slope_lower {a b s₀ : ℝ} (ha : 0 < a)
    (hs₀pos : 0 < s₀)
    (hslower : ∀ q ∈ Icc a b, s₀ ≤ π * q / 6 *
      (eisensteinTwoQ (imaginaryNome q) * eisensteinFourQ (imaginaryNome q) -
        eisensteinSixQ (imaginaryNome q))) :
    ∃ c₁ T : ℝ, 0 < c₁ ∧ 1 ≤ T ∧ ∀ q ∈ Icc a b, ∀ t : ℝ, T ≤ t →
      c₁ * t ≤ e8DualKernel (q, t) := by
  have hE4 : Continuous (fun τ : ℍ => ModularForm.E₄ τ) :=
    ModularFormClass.continuous ModularForm.E₄
  have hE6 : Continuous (fun τ : ℍ => ModularForm.E₆ τ) :=
    ModularFormClass.continuous ModularForm.E₆
  have hc : ∀ j : Fin 3, Continuous (fun τ : ℍ => eightMinusTauCoeff j τ) := fun j =>
    (mdifferentiable_eightMinusTauCoeff j).continuous
  have hphi : ∀ i : Fin 3, Continuous (fun τ : ℍ => ckmrvPhiBasis τ i) := fun i =>
    (mdifferentiable_ckmrvPhiBasis i).continuous
  have hmf2 : Continuous (fun τ : ℍ => ckmrvModularFactor τ 2) :=
    (mdifferentiable_ckmrvModularFactor 2).continuous
  obtain ⟨Mj, hMj⟩ := exists_bound_imaginary_interval ha continuous_kleinModularJ
  obtain ⟨M0, hM0⟩ := exists_bound_imaginary_interval ha (hc 0)
  obtain ⟨M1, hM1⟩ := exists_bound_imaginary_interval ha (hc 1)
  obtain ⟨M2, hM2⟩ := exists_bound_imaginary_interval ha (hc 2)
  obtain ⟨Ma, hMa⟩ := exists_bound_imaginary_interval ha ((hphi 1).mul hE4)
  obtain ⟨Mb, hMb⟩ := exists_bound_imaginary_interval ha ((hphi 0).mul hE6)
  obtain ⟨MF, hMF⟩ := exists_bound_imaginary_interval ha ((hphi 2).mul hmf2)
  obtain ⟨Cm, Ym, hm⟩ := exists_bound_of_isBigO_prod
    (isBigO_ckmrvEightMinusKernel_sub_G_unif hMj hM0 hM1 hM2)
  obtain ⟨Cp, Yp, hp⟩ := exists_bound_of_isBigO_prod
    (isBigO_ckmrvEightPlusKernel_sub_G_unif hMj hMa hMb hMF)
  have hG0c : Continuous ckmrvEightHatG0 := by
    unfold ckmrvEightHatG0
    exact ((continuous_const.mul (continuous_const.mul ((hphi 0).mul hE6))).sub
      (continuous_const.mul ((((hc 0).mul continuous_const).add (hc 1)).add (hc 2)))).div_const 2
  obtain ⟨MD, hMD⟩ := exists_bound_imaginary_interval ha hG0c
  have hπ := Real.pi_pos
  set E := MD + (|Cp| + |Cm|) / 2 with hE
  refine ⟨s₀ / 2, max 1 (max (max Yp Ym) (2 * E / s₀)), by positivity, le_max_left _ _, ?_⟩
  intro q hq t ht
  have hq0 : 0 < q := ha.trans_le hq.1
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  have htY : max Yp Ym ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htE : 2 * E / s₀ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have hτ : imagPt q ∈ imagPt '' Icc a b := ⟨q, hq, rfl⟩
  have him := im_imagPt ht0
  have hnorm := norm_coe_imagPt ht0
  -- the remainders
  have hRm := hm (imagPt q) hτ (imagPt t) (by rw [him]; exact le_trans (le_max_right _ _) htY)
  have hRp := hp (imagPt q) hτ (imagPt t) (by rw [him]; exact le_trans (le_max_left _ _) htY)
  simp only [him, hnorm] at hRm hRp
  have hte := mul_exp_neg_pi_le_one ht0.le
  have hte0 : 0 ≤ t * Real.exp (-π * t) := by positivity
  have hte2 : t ^ 2 * Real.exp (-2 * π * t) ≤ 1 := by
    have : t ^ 2 * Real.exp (-2 * π * t) = (t * Real.exp (-π * t)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    rw [this]
    exact pow_le_one₀ hte0 hte
  have hRm' : ‖ckmrvEightMinusKernel (imagPt q) (imagPt t) -
      ckmrvEightMinusG (imagPt q) (imagPt t)‖ ≤ |Cm| := by
    refine hRm.trans ?_
    rw [Real.norm_of_nonneg hte0]
    calc Cm * (t * Real.exp (-π * t)) ≤ |Cm| * (t * Real.exp (-π * t)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hte0
      _ ≤ |Cm| * 1 := mul_le_mul_of_nonneg_left hte (abs_nonneg _)
      _ = |Cm| := mul_one _
  have hRp' : ‖ckmrvEightPlusKernel (imagPt q) (imagPt t) -
      ckmrvEightPlusG (imagPt q) (imagPt t)‖ ≤ |Cp| := by
    refine hRp.trans ?_
    have h0 : 0 ≤ t ^ 2 * Real.exp (-2 * π * t) := by positivity
    rw [Real.norm_of_nonneg h0]
    calc Cp * (t ^ 2 * Real.exp (-2 * π * t)) ≤ |Cp| * (t ^ 2 * Real.exp (-2 * π * t)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |Cp| * 1 := mul_le_mul_of_nonneg_left hte2 (abs_nonneg _)
      _ = |Cp| := mul_one _
  -- decomposition
  have hdec : ckmrvEightHatKernel (imagPt q) (imagPt t) =
      (ckmrvEightPlusG (imagPt q) (imagPt t) - ckmrvEightMinusG (imagPt q) (imagPt t)) / 2 +
      ((ckmrvEightPlusKernel (imagPt q) (imagPt t) - ckmrvEightPlusG (imagPt q) (imagPt t)) -
        (ckmrvEightMinusKernel (imagPt q) (imagPt t) -
          ckmrvEightMinusG (imagPt q) (imagPt t))) / 2 := by
    simp only [ckmrvEightHatKernel]; ring
  rw [ckmrvEightG_hat_imagPt hq0 ht0] at hdec
  -- the slope
  set X := eisensteinTwoQ (imaginaryNome q) * eisensteinFourQ (imaginaryNome q) -
    eisensteinSixQ (imaginaryNome q) with hX
  have hslope : s₀ ≤ π * q / 6 * X := hslower q hq
  -- real parts
  have hD := hMD (imagPt q) hτ
  have hreD : -MD ≤ (ckmrvEightHatG0 (imagPt q)).re :=
    le_trans (neg_le_neg hD) (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  set R := ((ckmrvEightPlusKernel (imagPt q) (imagPt t) - ckmrvEightPlusG (imagPt q) (imagPt t)) -
    (ckmrvEightMinusKernel (imagPt q) (imagPt t) - ckmrvEightMinusG (imagPt q) (imagPt t))) / 2
    with hR
  have hRn : ‖R‖ ≤ (|Cp| + |Cm|) / 2 := by
    rw [hR, norm_div, Complex.norm_ofNat]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add hRp' hRm')
  have hreR : -((|Cp| + |Cm|) / 2) ≤ R.re :=
    le_trans (neg_le_neg hRn) (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  have hval : e8DualKernel (q, t) = π * q / 6 * X * t + (ckmrvEightHatG0 (imagPt q)).re + R.re := by
    simp only [e8DualKernel]
    rw [hdec, Complex.add_re, Complex.add_re, Complex.ofReal_re]
  rw [hval]
  have hmain : s₀ * t ≤ π * q / 6 * X * t := mul_le_mul_of_nonneg_right hslope ht0.le
  have hEt : E ≤ s₀ / 2 * t := by
    rw [div_le_iff₀ hs₀pos] at htE
    linarith
  linarith


theorem e8_kernel_linear_growth_left_of_one :
    ∃ a c₁ T : ℝ, 0 < a ∧ a < 1 ∧ 0 < c₁ ∧ 1 ≤ T ∧
      ∀ q ∈ Icc a 1, ∀ t : ℝ, T ≤ t → c₁ * t ≤ e8DualKernel (q, t) := by
  obtain ⟨a, m, ha, ha1, hm, hlower⟩ := exists_e8KernelSlope_left_lower
  obtain ⟨c₁, T, hc₁, hT, hbound⟩ := e8_kernel_linear_growth_of_slope_lower ha hm
    (fun q hq => by
      have h := hlower q hq
      rw [e8KernelSlope_eq (ha.trans_le hq.1)] at h
      exact h)
  exact ⟨a, c₁, T, ha, ha1, hc₁, hT, hbound⟩

end E8Leech
