import E8Leech.GaussianBaseline

/-!
# Strict positivity of the Leech leading cusp coefficient for every q > 0

If the already nonnegative leading coefficient vanished, the next coefficient
would be negative by the strict cusp-sum inequality. The positive kernel would
then have a negative exponential leading term, contradicting its cusp bound.
At q = 1 the existing modular estimate supplies strict positivity directly.
-/

noncomputable section
namespace E8Leech
open Complex Filter Asymptotics Topology
open scoped Real

theorem leechAxisCusp_lead_pos_all {q : ℝ} (hq : 0 < q) :
    0 < (leechAxisCusp (-1) q 0).re := by
  by_cases hq1 : q = 1
  · exact leechAxisCusp_lead_pos hq1.ge
  have hnonneg := leechAxisCusp_lead_nonneg hq hq1
  by_contra h
  have ha : (leechAxisCusp (-1) q 0).re = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hbneg : (leechAxisCusp (-1) q 1).re < 0 := by
    simpa only [ha, add_zero] using leechAxisCusp_sum_neg hq
  obtain ⟨g, -, hgK, -, -, -, hsub⟩ := exists_leechAxis (-1) hq hq1
  obtain ⟨C, hC, hbound⟩ := hsub.exists_pos
  set b := (leechAxisCusp (-1) q 1).re
  set c := (leechAxisCusp (-1) q 2).re
  set d := (leechAxisCusp (-1) q 3).re
  have hb : 0 < -b := neg_pos.mpr hbneg
  obtain ⟨t, hbt, hT⟩ := (hbound.bound.and (eventually_ge_atTop
    (max (max q q⁻¹ + 1) ((|c| + |d| + C + 1) / (-b))))).exists
  have ht1 : max q q⁻¹ + 1 ≤ t := le_trans (le_max_left _ _) hT
  have ht2 : (|c| + |d| + C + 1) / (-b) ≤ t := le_trans (le_max_right _ _) hT
  have hqt : q < t := by linarith [le_max_left q q⁻¹]
  have hqt' : q⁻¹ < t := by linarith [le_max_right q q⁻¹]
  have ht0 : 0 < t := lt_trans hq hqt
  have ht1' : 1 ≤ t := by linarith [lt_of_lt_of_le hq (le_max_left q q⁻¹)]
  have hg : 0 ≤ (g t).re := by
    rw [hgK t hqt.ne' hqt'.ne', leechAxisKernel_neg_one]
    exact ckmrvLeechHatKernel_nonneg hq ht0 hqt.ne' hqt'.ne'
  have hexp : t * Real.exp ((-π + π / 4) * t) ≤ 1 := by
    have h1 := Real.add_one_le_exp ((π - π / 4) * t)
    have h2 : t ≤ Real.exp ((π - π / 4) * t) := by nlinarith [Real.pi_gt_three]
    have h3 : Real.exp ((-π + π / 4) * t) = (Real.exp ((π - π / 4) * t))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [h3, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h2
  have hdiff : ‖g t - leechAxisProfile (-1) q t‖ ≤ C := by
    refine hbt.trans ?_
    rw [Real.norm_of_nonneg (mul_nonneg ht0.le (Real.exp_pos _).le)]
    exact (mul_le_mul_of_nonneg_left hexp hC.le).trans_eq (mul_one C)
  have hPlow : -C ≤ (leechAxisProfile (-1) q t).re := by
    have h1 := (Complex.abs_re_le_norm (g t - leechAxisProfile (-1) q t)).trans hdiff
    rw [Complex.sub_re] at h1
    linarith [(abs_le.mp h1).2]
  have hre : (leechAxisProfile (-1) q t).re =
      b * Real.exp (2 * π * t) + c * t + d := by
    simp only [leechAxisProfile, cuspProfile]
    rw [← Complex.ofReal_mul, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.re_mul_ofReal, Complex.re_mul_ofReal, Complex.re_mul_ofReal, ha]
    dsimp [b, c, d]
    ring
  have hexp1 : t ≤ Real.exp (π * t) := by
    have h1 := Real.add_one_le_exp (π * t)
    nlinarith [Real.pi_gt_three]
  have hexp2 : t ^ 2 ≤ Real.exp (2 * π * t) := by
    calc t ^ 2 ≤ Real.exp (π * t) ^ 2 := pow_le_pow_left₀ ht0.le hexp1 2
      _ = Real.exp (2 * π * t) := by rw [sq, ← Real.exp_add]; congr 1; ring
  have hbt' : |c| + |d| + C + 1 ≤ -b * t := by
    rw [div_le_iff₀ hb] at ht2
    linarith only [ht2]
  have hneg : b * Real.exp (2 * π * t) ≤ b * t ^ 2 :=
    mul_le_mul_of_nonpos_left hexp2 hbneg.le
  have hc : c * t ≤ |c| * t := mul_le_mul_of_nonneg_right (le_abs_self c) ht0.le
  have hd : d ≤ |d| * t := by nlinarith [le_abs_self d, abs_nonneg d]
  have htprod := mul_le_mul_of_nonneg_right hbt' ht0.le
  rw [hre] at hPlow
  nlinarith [mul_nonneg hC.le (sub_nonneg.mpr ht1')]

end E8Leech
