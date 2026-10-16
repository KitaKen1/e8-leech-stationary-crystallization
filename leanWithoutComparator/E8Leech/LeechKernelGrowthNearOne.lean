import E8Leech.LeechKernelUniform

/-!
# Uniform linear growth of the truncated Leech kernel near q=1

Uniform cusp remainders and the positive nongrowing slope give a common
linear lower bound after subtracting the exponentially growing cusp terms.
The result holds on every compact positive interval, including q=1.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Set Asymptotics
open UpperHalfPlane hiding I
open scoped Real

/-- The combined cusp term is precisely the cusp profile on the imaginary axis. -/
theorem leechHatG_imagPt (q : ℝ) {t : ℝ} (ht : 0 < t) :
    (ckmrvLeechPlusG (imagPt q) (imagPt t) -
      ckmrvLeechMinusG (imagPt q) (imagPt t)) / 2 = leechAxisProfile (-1) q t := by
  rw [ckmrvLeechPlusG_imagPt _ ht, ckmrvLeechMinusG_imagPt _ ht]
  change (cuspProfile (leechPlusCusp (imagPt q) 0) (leechPlusCusp (imagPt q) 1)
      (leechPlusCusp (imagPt q) 2) (leechPlusCusp (imagPt q) 3) (2 * π) t -
    cuspProfile (leechMinusCusp (imagPt q) 0) (leechMinusCusp (imagPt q) 1)
      (leechMinusCusp (imagPt q) 2) (leechMinusCusp (imagPt q) 3) (2 * π) t) / 2 = _
  simp only [leechAxisProfile, leechAxisCusp, cuspProfile]
  ring

theorem leechAxisProfile_re (q t : ℝ) :
    (leechAxisProfile (-1) q t).re =
      ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
        Real.exp (2 * π * t) + (leechAxisCusp (-1) q 2).re * t +
        (leechAxisCusp (-1) q 3).re := by
  simp only [leechAxisProfile, cuspProfile, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, mul_zero, sub_zero, zero_mul, zero_add]
  ring

/-- A common positive linear bound on any compact positive parameter interval. -/
theorem leech_trunc_linear_on_compact {a b : ℝ} (ha : 0 < a) :
    ∃ c₁ T : ℝ, 0 < c₁ ∧ 1 ≤ T ∧ ∀ q ∈ Icc a b, ∀ t : ℝ, T ≤ t →
      c₁ * t ≤ leechDualKernel (q, t) -
        ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
          Real.exp (2 * π * t) := by
  have hK : IsCompact (imagPt '' Icc a b) := isCompact_Icc.image_of_continuousOn
    (continuousOn_ofComplex_I_mul.mono (fun q hq => ha.trans_le hq.1))
  obtain ⟨Cm, Ym, hm⟩ := exists_bound_of_isBigO_prod
    (isBigO_ckmrvLeechMinusKernel_sub_G_uniform hK)
  obtain ⟨Cp, Yp, hp⟩ := exists_bound_of_isBigO_prod
    (isBigO_ckmrvLeechPlusKernel_sub_G_uniform hK)
  obtain ⟨M, hM⟩ := exists_leechAxisCusp_compact_bound (-1) ha (b := b)
  let m := Real.exp (-4 * π * b)
  have hmpos : 0 < m := Real.exp_pos _
  let E := M + (|Cp| * (2 / π ^ 2) + |Cm|) / 2
  refine ⟨m / 2, max 1 (max (max Yp Ym) (2 * E / m)), by positivity, le_max_left _ _, ?_⟩
  intro q hq t ht
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith only [ht1]
  have htY : max Yp Ym ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htE : 2 * E / m ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have hτ : imagPt q ∈ imagPt '' Icc a b := ⟨q, hq, rfl⟩
  have him := im_imagPt ht0
  have hnorm := norm_coe_imagPt ht0
  have hRm := hm (imagPt q) hτ (imagPt t) (by rw [him]; exact le_trans (le_max_right _ _) htY)
  have hRp := hp (imagPt q) hτ (imagPt t) (by rw [him]; exact le_trans (le_max_left _ _) htY)
  simp only [him, hnorm] at hRm hRp
  have hte := mul_exp_neg_pi_le_one ht0.le
  have hte0 : 0 ≤ t * Real.exp (-π * t) := by positivity
  have hte2 : t ^ 2 * Real.exp (-π * t) ≤ 2 / π ^ 2 := by
    convert pow_mul_exp_neg_le_factorial_div Real.pi_pos ht0.le 2 using 1
    norm_num
  have hRm' : ‖ckmrvLeechMinusKernel (imagPt q) (imagPt t) -
      ckmrvLeechMinusG (imagPt q) (imagPt t)‖ ≤ |Cm| := by
    refine hRm.trans ?_
    rw [Real.norm_of_nonneg hte0]
    calc Cm * (t * Real.exp (-π * t)) ≤ |Cm| * (t * Real.exp (-π * t)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hte0
      _ ≤ |Cm| * 1 := mul_le_mul_of_nonneg_left hte (abs_nonneg _)
      _ = |Cm| := mul_one _
  have hRp' : ‖ckmrvLeechPlusKernel (imagPt q) (imagPt t) -
      ckmrvLeechPlusG (imagPt q) (imagPt t)‖ ≤ |Cp| * (2 / π ^ 2) := by
    refine hRp.trans ?_
    have h0 : 0 ≤ t ^ 2 * Real.exp (-π * t) := by positivity
    rw [Real.norm_of_nonneg h0]
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) h0).trans
      (mul_le_mul_of_nonneg_left hte2 (abs_nonneg _))
  let R := ((ckmrvLeechPlusKernel (imagPt q) (imagPt t) -
      ckmrvLeechPlusG (imagPt q) (imagPt t)) -
    (ckmrvLeechMinusKernel (imagPt q) (imagPt t) -
      ckmrvLeechMinusG (imagPt q) (imagPt t))) / 2
  have hRn : ‖R‖ ≤ (|Cp| * (2 / π ^ 2) + |Cm|) / 2 := by
    dsimp only [R]
    rw [norm_div, Complex.norm_ofNat]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add hRp' hRm')
  have hreR : -((|Cp| * (2 / π ^ 2) + |Cm|) / 2) ≤ R.re :=
    le_trans (neg_le_neg hRn) (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  have hD : -M ≤ (leechAxisCusp (-1) q 3).re :=
    le_trans (neg_le_neg (hM q hq 3)) (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  have hdec : ckmrvLeechHatKernel (imagPt q) (imagPt t) =
      leechAxisProfile (-1) q t + R := by
    rw [← leechHatG_imagPt q ht0]
    simp only [ckmrvLeechHatKernel, R]
    ring
  have hval : leechDualKernel (q, t) = (leechAxisProfile (-1) q t).re + R.re := by
    simp only [leechDualKernel]
    rw [hdec, Complex.add_re]
  have hslope : m ≤ (leechAxisCusp (-1) q 2).re := leechAxisCusp_two_compact_lower ha hq
  have hmain := mul_le_mul_of_nonneg_right hslope ht0.le
  have hEt : E ≤ m / 2 * t := by
    rw [div_le_iff₀ hmpos] at htE
    linarith only [htE]
  rw [hval, leechAxisProfile_re]
  dsimp only [E] at hEt
  linarith only [hmain, hEt, hD, hreR]

/-- The self-dual parameter is included in the common left-neighborhood bound. -/
theorem leech_trunc_linear_left_of_one :
    ∃ c₁ T : ℝ, 0 < c₁ ∧ 2 < T ∧ ∀ q ∈ Icc (1 / 2 : ℝ) 1,
      ∀ t : ℝ, T ≤ t → c₁ * t ≤ leechDualKernel (q, t) -
        ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
          Real.exp (2 * π * t) := by
  obtain ⟨c₁, T, hc₁, -, hbound⟩ := leech_trunc_linear_on_compact
    (a := 1 / 2) (b := 1) (by norm_num)
  exact ⟨c₁, max 3 T, hc₁, lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    fun q hq t ht => hbound q hq t ((le_max_right _ _).trans ht)⟩


/-- The growing slope has a common positive lower bound on any nonempty positive compact interval. -/
theorem leech_lead_lower_on_compact {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ m : ℝ, 0 < m ∧ ∀ q ∈ Icc a b, m ≤ (leechAxisCusp (-1) q 0).re := by
  have hc : ContinuousOn (fun q : ℝ => (leechAxisCusp (-1) q 0).re) (Icc a b) :=
    (continuousOn_leechAxisCusp_re (-1) 0).mono (fun q hq => ha.trans_le hq.1)
  obtain ⟨q₀, hq₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc
  exact ⟨_, leechAxisCusp_lead_pos_all (ha.trans_le hq₀.1), fun q hq => hmin hq⟩

/-- A common later truncation makes the growing cusp's constant term nonnegative.
This replaces the special fixed-block ratio bound in the large-radius part of the profile. -/
theorem exists_leech_cusp_uniform_cut {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ m p : ℝ, 0 < m ∧ 1 ≤ p ∧ ∀ q ∈ Icc a b,
      m ≤ (leechAxisCusp (-1) q 0).re ∧
      0 ≤ (leechAxisCusp (-1) q 1).re + p * (leechAxisCusp (-1) q 0).re := by
  obtain ⟨m, hm, hlead⟩ := leech_lead_lower_on_compact ha hab
  obtain ⟨M, hM⟩ := exists_leechAxisCusp_compact_bound (-1) ha (b := b)
  let p := 1 + |M| / m
  have hp : 1 ≤ p := le_add_of_nonneg_right (div_nonneg (abs_nonneg M) hm.le)
  refine ⟨m, p, hm, hp, fun q hq => ⟨hlead q hq, ?_⟩⟩
  have hconst : -M ≤ (leechAxisCusp (-1) q 1).re :=
    le_trans (neg_le_neg (hM q hq 1)) (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  have hmul := mul_le_mul_of_nonneg_left (hlead q hq) (zero_le_one.trans hp)
  have hpm : p * m = m + |M| := by dsimp only [p]; field_simp
  rw [hpm] at hmul
  linarith only [hm, hconst, hmul, le_abs_self M]

end E8Leech
