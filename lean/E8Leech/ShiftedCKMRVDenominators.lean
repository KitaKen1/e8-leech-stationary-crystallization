import E8Leech.CKMRVDenominatorBounds
import E8Leech.ShiftedLaplaceSlack

/-!
# Actual CKMRV denominator separation on arbitrary positive parameter intervals

Compact continuity bounds the actual j-function on the dual parameter interval.
Its q-product lower bound at large imaginary height dominates that bound.
The explicit large-height candidate yields a pole-free unit block for both
actual CKMRV denominators. No global j-orbit classification or derivative is used.
This proves denominator separation, not numerator or kernel positivity.
-/

noncomputable section
namespace E8Leech
open Set

theorem kleinImaginaryJ_exp_lower {v : ℝ} (hv : 1 ≤ v) :
    Real.exp (2 * Real.pi * v) ≤ (kleinImaginaryJ v).re := by
  rw [kleinImaginaryJ_eq_q (by linarith only [hv]), Complex.ofReal_re]
  have h := kleinJQ_lower (imaginaryNome_pos v) (imaginaryNome_small hv)
  rwa [imaginaryNome_reciprocal] at h

theorem exists_shifted_klein_gap {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ V : ℝ, 0 < V ∧ gaussianSeparatedBlockStart a b ≤ V ∧
      ∀ q ∈ Icc (Real.pi / b) (Real.pi / a), ∀ v ∈ Icc V (V + 1),
        1 ≤ (kleinImaginaryJ v - kleinImaginaryJ q).re := by
  have hb : 0 < b := ha.trans_le hab
  have hq0 : 0 < Real.pi / b := div_pos Real.pi_pos hb
  have hcont : ContinuousOn (fun q => ‖kleinImaginaryJ q‖)
      (Icc (Real.pi / b) (Real.pi / a)) :=
    (continuousOn_kleinImaginaryJ.mono (fun _ h => hq0.trans_le h.1)).norm
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hcont
  let V := max (gaussianSeparatedBlockStart a b) (M + 2)
  have hV : 0 < V := (gaussianSeparatedBlockStart_pos a b).trans_le (le_max_left _ _)
  refine ⟨V, hV, le_max_left _ _, ?_⟩
  intro q hq v hv
  have hbound : (kleinImaginaryJ q).re ≤ M :=
    (Complex.re_le_norm _).trans (hM ⟨q, hq, rfl⟩)
  have hstart : 1 ≤ gaussianSeparatedBlockStart a b := by
    dsimp [gaussianSeparatedBlockStart]
    have := le_max_left (1 : ℝ) (max (Real.pi / a) (b / Real.pi))
    linarith
  have hv1 : 1 ≤ v := (hstart.trans (le_max_left _ _)).trans hv.1
  have hvM : M + 2 ≤ v := (le_max_right _ _).trans hv.1
  have hexp := Real.add_one_le_exp (2 * Real.pi * v)
  have hlinear : v + 1 ≤ Real.exp (2 * Real.pi * v) := by
    nlinarith only [hexp, hv1, Real.pi_gt_three]
  have hlarge := kleinImaginaryJ_exp_lower hv1
  simp only [Complex.sub_re]
  linarith only [hbound, hvM, hlinear, hlarge]

theorem ckmrvImaginaryDenominator_ne_zero_of_j_gap {q v : ℝ}
    (hgap : 0 < (kleinImaginaryJ v - kleinImaginaryJ q).re) :
    ckmrvImaginaryDenominator (q, v) ≠ 0 := by
  have hdiff : kleinImaginaryJ q - kleinImaginaryJ v ≠ 0 := by
    intro heq
    have hreal := congrArg Complex.re heq
    simp only [Complex.sub_re, Complex.zero_re] at hreal
    simp only [Complex.sub_re] at hgap
    linarith
  exact mul_ne_zero (mul_ne_zero (ModularForm.discriminant_ne_zero _)
    (ModularForm.discriminant_ne_zero _)) hdiff

theorem ckmrvLeechImaginaryDenominator_ne_zero_of_j_gap {q v : ℝ}
    (hgap : 0 < (kleinImaginaryJ v - kleinImaginaryJ q).re) :
    ckmrvLeechImaginaryDenominator (q, v) ≠ 0 :=
  mul_ne_zero (ckmrvImaginaryDenominator_ne_zero_of_j_gap hgap)
    (ModularForm.discriminant_ne_zero _)

theorem continuousOn_ckmrvLeechImaginaryDenominator_positive :
    ContinuousOn ckmrvLeechImaginaryDenominator (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  have hD : Continuous ModularForm.discriminant := by
    simpa only [CuspForm.coe_discriminant] using ModularFormClass.continuous CuspForm.discriminant
  exact continuousOn_ckmrvImaginaryDenominator_positive.mul
    ((hD.comp_continuousOn UpperHalfPlane.continuousOn_ofComplex_I_mul).comp
      continuousOn_snd (fun _ h => h.2))

theorem exists_shifted_ckmrv_denominator_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ V D D24 : ℝ, 0 < V ∧ gaussianSeparatedBlockStart a b ≤ V ∧ 0 < D ∧ 0 < D24 ∧
      ∀ q ∈ Icc (Real.pi / b) (Real.pi / a), ∀ v ∈ Icc V (V + 1),
        D ≤ ‖ckmrvImaginaryDenominator (q, v)‖ ∧
        D24 ≤ ‖ckmrvLeechImaginaryDenominator (q, v)‖ := by
  obtain ⟨V, hV, hstart, hgap⟩ := exists_shifted_klein_gap ha hab
  have hb : 0 < b := ha.trans_le hab
  have hq0 := div_pos Real.pi_pos hb
  have hsub : Icc (Real.pi / b) (Real.pi / a) ×ˢ Icc V (V + 1) ⊆
      Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) :=
    fun _ h => ⟨hq0.trans_le h.1.1, hV.trans_le h.2.1⟩
  have hpos : ∀ p ∈ Icc (Real.pi / b) (Real.pi / a) ×ˢ Icc V (V + 1),
      0 < ‖ckmrvImaginaryDenominator p‖ := by
    intro p hp
    exact norm_pos_iff.mpr (ckmrvImaginaryDenominator_ne_zero_of_j_gap
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hgap _ hp.1 _ hp.2)))
  have hpos24 : ∀ p ∈ Icc (Real.pi / b) (Real.pi / a) ×ˢ Icc V (V + 1),
      0 < ‖ckmrvLeechImaginaryDenominator p‖ := by
    intro p hp
    exact norm_pos_iff.mpr (ckmrvLeechImaginaryDenominator_ne_zero_of_j_gap
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hgap _ hp.1 _ hp.2)))
  obtain ⟨D, hD, hlD⟩ := compact_rectangle_positive_lower
    (continuousOn_ckmrvImaginaryDenominator_positive.mono hsub).norm hpos
  obtain ⟨D24, hD24, hlD24⟩ := compact_rectangle_positive_lower
    (continuousOn_ckmrvLeechImaginaryDenominator_positive.mono hsub).norm hpos24
  exact ⟨V, D, D24, hV, hstart, hD, hD24, fun q hq v hv => ⟨hlD q hq v hv, hlD24 q hq v hv⟩⟩

theorem exists_shifted_gaussian_ckmrv_inverse_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ V D D24 : ℝ, 0 < V ∧ gaussianSeparatedBlockStart a b ≤ V ∧ 0 < D ∧ 0 < D24 ∧
      ∀ α ∈ Icc a b, ∀ v ∈ Icc V (V + 1),
        ckmrvImaginaryDenominator (Real.pi / α, v) ≠ 0 ∧
        ckmrvLeechImaginaryDenominator (Real.pi / α, v) ≠ 0 ∧
        ‖(ckmrvImaginaryDenominator (Real.pi / α, v))⁻¹‖ ≤ D⁻¹ ∧
        ‖(ckmrvLeechImaginaryDenominator (Real.pi / α, v))⁻¹‖ ≤ D24⁻¹ := by
  obtain ⟨V, D, D24, hV, hstart, hD, hD24, hl⟩ := exists_shifted_ckmrv_denominator_bounds ha hab
  refine ⟨V, D, D24, hV, hstart, hD, hD24, ?_⟩
  intro α hα v hv
  obtain ⟨h8, h24⟩ := hl _ (gaussian_dual_interval ha hα) v hv
  exact ⟨norm_pos_iff.mp (hD.trans_le h8), norm_pos_iff.mp (hD24.trans_le h24),
    by rw [norm_inv]; exact (inv_le_inv₀ (hD.trans_le h8) hD).mpr h8,
    by rw [norm_inv]; exact (inv_le_inv₀ (hD24.trans_le h24) hD24).mpr h24⟩

end E8Leech
