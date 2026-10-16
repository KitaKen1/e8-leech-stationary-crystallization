import E8Leech.LeechUniformTruncatedProfile
import E8Leech.E8UniformSlackNearPi

/-!
# One full-radius Leech quadratic slack on the right of π

The truncated profile covers small radii and the Laplace boundary. Above a
fixed neighborhood of that boundary, a positive separated block and a
compact sine minimum give the far-radius bound. Spatial continuity fills
the origin; the same block controls the shortest-vector endpoint.
-/

noncomputable section
set_option maxHeartbeats 600000
namespace E8Leech
open Set MeasureTheory Filter Topology
open scoped ENNReal Real

theorem leech_gaussian_separated_block_lower_reg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℝ, 0 < B ∧ ∀ q ∈ Icc (π / b) (π / a),
      ∀ t ∈ Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1),
        B ≤ leechDualKernelReg (q, t) := by
  obtain ⟨B, hB, hblock⟩ := leech_gaussian_separated_block_lower ha hab
  refine ⟨B, hB, fun q hq t ht => ?_⟩
  have hq0 : 0 < q := (div_pos Real.pi_pos (ha.trans_le hab)).trans_le hq.1
  have hreg : ckmrvImaginaryPair (q, t) ∈ ckmrvRegularLocus :=
    gaussian_separated_rectangle_regular (a := a) (b := b) ha hab ⟨hq, ht⟩
  rw [leechDualKernelReg_eq_of_regular (q := q) (t := t) hq0 hreg]
  exact hblock q hq t ht

theorem exists_sin_sq_lower_above_two_pi {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π / 2) :
    ∃ s : ℝ, 0 < s ∧ ∀ b ∈ Icc (2 * π + δ) (49 * π / 16),
      s ≤ 4 * Real.sin (b / 2) ^ 2 := by
  have hc : Continuous (fun b : ℝ => 4 * Real.sin (b / 2) ^ 2) := by fun_prop
  have hab : 2 * π + δ ≤ 49 * π / 16 := by linarith only [hδπ, Real.pi_pos]
  obtain ⟨b₀, hb₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc.continuousOn
  have hs := Real.sin_pos_of_pos_of_lt_pi
    (by linarith only [hb₀.1, hδ] : 0 < b₀ / 2 - π)
    (by linarith only [hb₀.2, Real.pi_pos] : b₀ / 2 - π < π)
  rw [Real.sin_sub_pi] at hs
  have hne : Real.sin (b₀ / 2) ≠ 0 := (neg_pos.mp hs).ne
  exact ⟨_, by positivity, fun b hb => hmin hb⟩

theorem leech_uniform_far_slack_right_pi :
    ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Ioc π (2 * π), ∀ u ∈ Icc (0 : ℝ) (7 / 4),
      A ≤ leechSlackProfile (α, u) := by
  obtain ⟨As, hAs, hsmall⟩ := leechHatProfile_re_lower_small_left_of_one
  obtain ⟨δ, Am, hδ, hδπ, hAm, hmiddle⟩ := leechHatProfile_re_lower_boundary_left_of_one
  obtain ⟨s, hs, hsine⟩ := exists_sin_sq_lower_above_two_pi hδ hδπ
  have hπ2 : π ≤ 2 * π := by linarith [Real.pi_pos]
  obtain ⟨B, hB, hblock⟩ := leech_gaussian_separated_block_lower_reg Real.pi_pos hπ2
  let V := gaussianSeparatedBlockStart π (2 * π)
  have hV : 0 < V := gaussianSeparatedBlockStart_pos _ _
  let C := (π / (2 * π)) ^ 12 * B * Real.exp (-4 * π * (V + 1))
  have hC : 0 < C := by dsimp only [C]; positivity
  let A := min ((1 / 2 : ℝ) ^ 12 * min As Am) (s * C)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hq : ∀ α ∈ Ioc π (2 * π), π / α ∈ Icc (1 / 2 : ℝ) 1 := by
    intro α hα
    have h := gaussian_dual_interval Real.pi_pos ⟨hα.1.le, hα.2⟩
    simpa only [div_self Real.pi_ne_zero,
      show π / (2 * π) = (1 / 2 : ℝ) by field_simp] using h
  have hgood : ∀ α ∈ Ioc π (2 * π), 0 < α ∧ α ≠ π := fun α hα =>
    ⟨Real.pi_pos.trans hα.1, hα.1.ne'⟩
  have hfarpos : ∀ α ∈ Ioc π (2 * π), ∀ u : ℝ, 0 < u → u ≤ 7 / 4 →
      A ≤ leechSlackProfile (α, u) := by
    intro α hα u hu humax
    obtain ⟨hα0, hαπ⟩ := hgood α hα
    have hqa := hq α hα
    have hq0 : 0 < π / α := div_pos Real.pi_pos hα0
    have hq1 : π / α ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq hα0.ne').mp h).symm
    have hu2 : u ^ 2 ≤ 49 / 16 := by
      have h := pow_le_pow_left₀ hu.le humax 2
      norm_num at h
      exact h
    have hb : 0 < π * u ^ 2 := mul_pos Real.pi_pos (pow_pos hu 2)
    by_cases hmid : π * u ^ 2 ≤ 2 * π + δ
    · have hprof : min As Am ≤ (leechAxisRadialProfile (-1) (π / α) (π * u ^ 2)).re := by
        rcases le_or_gt π (π * u ^ 2) with hbig | hlt
        · exact (min_le_right _ _).trans (hmiddle _ hqa hq1 _ ⟨hbig, hmid⟩)
        · exact (min_le_left _ _).trans (hsmall _ hqa hq1 _ hb hlt)
      rw [leechSlackProfile_eq hα0 hαπ hu.le]
      exact (min_le_left _ _).trans
        (mul_le_mul (pow_le_pow_left₀ (by norm_num) hqa.1 12) hprof
          (lt_min hAs hAm).le (pow_nonneg hq0.le 12))
    · have huLap : 2 < u ^ 2 := by
        have hmul : 2 * π < π * u ^ 2 := by linarith only [hmid, hδ]
        nlinarith only [hmul, Real.pi_pos]
      have hJ := gaussian_normalized_shifted_laplace_block_lower 12 leechDualKernelReg
        Real.pi_pos hB.le hV ⟨hα.1.le, hα.2⟩ (show u ^ 2 ≤ 4 by linarith only [hu2])
        (fun t ht => leechDualKernelReg_nonneg leechKernelInequalities hq0 ht)
        (hblock (π / α) (gaussian_dual_interval Real.pi_pos ⟨hα.1.le, hα.2⟩))
        (integrableOn_leechDualKernelReg hq0 hq1 huLap)
      change C ≤ _ at hJ
      have hsin := hsine (π * u ^ 2) ⟨(lt_of_not_ge hmid).le, by nlinarith only [hu2, Real.pi_pos]⟩
      apply (min_le_right _ _).trans
      rw [leechSlackProfile_eq_laplace_reg hα0 hαπ hu.le huLap]
      calc
        s * C ≤ (4 * Real.sin (π * u ^ 2 / 2) ^ 2) * C :=
          mul_le_mul_of_nonneg_right hsin hC.le
        _ ≤ (4 * Real.sin (π * u ^ 2 / 2) ^ 2) *
            ((π / α) ^ 12 * ∫ t in Ioi (0 : ℝ),
              leechDualKernelReg (π / α, t) * Real.exp (-π * u ^ 2 * t)) :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
        _ = _ := by ring
  refine ⟨A, hA, fun α hα u hu => ?_⟩
  rcases eq_or_lt_of_le hu.1 with hzero | hpos
  · subst u
    refine ge_of_tendsto
      ((continuous_leechSlackProfile_radius α).continuousAt.continuousWithinAt (s := Ioi 0)) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 7 / 4 by norm_num)] with v hv
    exact hfarpos α hα v hv.1 hv.2.le
  · exact hfarpos α hα u hpos hu.2

/-- The common quadratic coefficient is independent of α on the whole interval (π,2π]. -/
theorem leech_uniform_quadratic_slack_right_pi :
    ∃ b k : ℝ, π < b ∧ 0 < k ∧ ∀ α ∈ Ioc π b, ∀ u ∈ Icc (0 : ℝ) 2,
      k * (2 - u) ^ 2 ≤ leechSlackProfile (α, u) := by
  have hb : π < 2 * π := by linarith [Real.pi_pos]
  obtain ⟨A, hA, hfar⟩ := leech_uniform_far_slack_right_pi
  obtain ⟨B, hB, hblock⟩ := leech_gaussian_separated_block_lower_reg Real.pi_pos hb.le
  have hgood : ∀ α ∈ Ioc π (2 * π), 0 < α ∧ α ≠ π := fun α hα =>
    ⟨Real.pi_pos.trans hα.1, hα.1.ne'⟩
  have hq0 : ∀ α ∈ Ioc π (2 * π), 0 < π / α := fun α hα =>
    div_pos Real.pi_pos (hgood α hα).1
  have hq1 : ∀ α ∈ Ioc π (2 * π), π / α ≠ 1 := fun α hα h =>
    (hgood α hα).2 ((div_eq_one_iff_eq (hgood α hα).1.ne').mp h).symm
  obtain ⟨k, hk, hlower⟩ := uniform_quadratic_slack_of_far_and_shifted_block 12
    leechSlackProfile leechDualKernelReg Real.pi_pos hb.le (by norm_num : (0 : ℝ) < 2)
    (Or.inr (by norm_num : (2 : ℝ) ^ 2 = 4)) hA hB (gaussianSeparatedBlockStart_pos π (2 * π))
    (Ioc π (2 * π)) (fun _ hα => ⟨hα.1.le, hα.2⟩)
    (fun α hα u hu => hfar α hα u (by norm_num at hu ⊢; exact hu))
    (fun α hα t ht => leechDualKernelReg_nonneg leechKernelInequalities (hq0 α hα) ht)
    (fun α hα => hblock _ (gaussian_dual_interval Real.pi_pos ⟨hα.1.le, hα.2⟩))
    (fun α hα u hu => integrableOn_leechDualKernelReg (hq0 α hα) (hq1 α hα)
      (by nlinarith only [hu.1]))
    (fun α hα u hu => leechSlackProfile_eq_laplace_reg (hgood α hα).1 (hgood α hα).2
      (by linarith only [hu.1]) (by nlinarith only [hu.1]))
  exact ⟨2 * π, k, hb, hk, hlower⟩

end E8Leech
