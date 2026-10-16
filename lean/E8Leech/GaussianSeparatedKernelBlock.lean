import E8Leech.GaussianBaseline
import E8Leech.ShiftedLaplaceSlack

/-!
# Positive blocks for the actual kernels on every positive parameter interval

The block moves above both singular curves. Its compact positive lower bound
therefore remains valid even when the Gaussian parameter interval contains π.
This is a statement about the kernels on the separated block, not a definition
of a Schwartz certificate at the exceptional parameter.
-/

noncomputable section
namespace E8Leech
open Set

theorem continuousOn_ckmrvImaginaryPair_positive {S : Set (ℝ × ℝ)}
    (hS : ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2) : ContinuousOn ckmrvImaginaryPair S :=
  (UpperHalfPlane.continuousOn_ofComplex_I_mul.comp continuous_fst.continuousOn
    (fun p hp => (hS p hp).1)).prodMk
      (UpperHalfPlane.continuousOn_ofComplex_I_mul.comp continuous_snd.continuousOn
        (fun p hp => (hS p hp).2))

theorem gaussian_separated_rectangle_regular {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MapsTo ckmrvImaginaryPair
      (Icc (Real.pi / b) (Real.pi / a) ×ˢ
        Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1))
      ckmrvRegularLocus := by
  have hb : 0 < b := ha.trans_le hab
  rintro ⟨q, t⟩ ⟨hq, ht⟩
  have hq0 : 0 < q := (div_pos Real.pi_pos hb).trans_le hq.1
  have ht0 : 0 < t := (gaussianSeparatedBlockStart_pos a b).trans_le ht.1
  have hmaxq := (le_max_left (Real.pi / a) (b / Real.pi)).trans
    (le_max_right (1 : ℝ) (max (Real.pi / a) (b / Real.pi)))
  have hmaxi := (le_max_right (Real.pi / a) (b / Real.pi)).trans
    (le_max_right (1 : ℝ) (max (Real.pi / a) (b / Real.pi)))
  have hqt : q < t := by
    dsimp [gaussianSeparatedBlockStart] at ht
    linarith only [hq.2, ht.1, hmaxq]
  have hbt : b / Real.pi < t := by
    dsimp [gaussianSeparatedBlockStart] at ht
    linarith only [ht.1, hmaxi]
  have hqi : q⁻¹ ≤ b / Real.pi := by
    calc q⁻¹ ≤ (Real.pi / b)⁻¹ := inv_anti₀ (div_pos Real.pi_pos hb) hq.1
      _ = b / Real.pi := inv_div _ _
  exact sub_ne_zero.mpr (kleinModularJ_imagPt_ne hq0 ht0 hqt.ne' (hqi.trans_lt hbt).ne')

theorem continuousOn_e8DualKernel_separated {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn e8DualKernel
      (Icc (Real.pi / b) (Real.pi / a) ×ˢ
        Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1)) := by
  have hc := continuousOn_ckmrvImaginaryPair_positive (S :=
    Icc (Real.pi / b) (Real.pi / a) ×ˢ
      Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1))
    (fun p hp => ⟨(div_pos Real.pi_pos (ha.trans_le hab)).trans_le hp.1.1,
      (gaussianSeparatedBlockStart_pos a b).trans_le hp.2.1⟩)
  have hmaps := gaussian_separated_rectangle_regular ha hab
  have hp := continuousOn_ckmrvEightPlusKernel_regular.comp hc hmaps
  have hm := continuousOn_ckmrvEightMinusKernel_regular.comp hc hmaps
  exact (Complex.continuous_re.comp_continuousOn ((hp.sub hm).div_const 2)).congr
    (fun _ _ => rfl)

theorem continuousOn_leechDualKernel_separated {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn leechDualKernel
      (Icc (Real.pi / b) (Real.pi / a) ×ˢ
        Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1)) := by
  have hc := continuousOn_ckmrvImaginaryPair_positive (S :=
    Icc (Real.pi / b) (Real.pi / a) ×ˢ
      Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1))
    (fun p hp => ⟨(div_pos Real.pi_pos (ha.trans_le hab)).trans_le hp.1.1,
      (gaussianSeparatedBlockStart_pos a b).trans_le hp.2.1⟩)
  have hmaps := gaussian_separated_rectangle_regular ha hab
  have hp := continuousOn_ckmrvLeechPlusKernel_regular.comp hc hmaps
  have hm := continuousOn_ckmrvLeechMinusKernel_regular.comp hc hmaps
  exact (Complex.continuous_re.comp_continuousOn ((hp.sub hm).div_const 2)).congr
    (fun _ _ => rfl)

theorem e8_gaussian_separated_block_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℝ, 0 < B ∧ ∀ q ∈ Icc (Real.pi / b) (Real.pi / a),
      ∀ t ∈ Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1),
        B ≤ e8DualKernel (q, t) := by
  apply compact_rectangle_positive_lower (continuousOn_e8DualKernel_separated ha hab)
  intro p hp
  have hreg := gaussian_separated_rectangle_regular ha hab hp
  exact ckmrvEightHatKernel_pos
    ((div_pos Real.pi_pos (ha.trans_le hab)).trans_le hp.1.1)
    ((gaussianSeparatedBlockStart_pos a b).trans_le hp.2.1) (sub_ne_zero.mp hreg)

theorem leech_gaussian_separated_block_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℝ, 0 < B ∧ ∀ q ∈ Icc (Real.pi / b) (Real.pi / a),
      ∀ t ∈ Icc (gaussianSeparatedBlockStart a b) (gaussianSeparatedBlockStart a b + 1),
        B ≤ leechDualKernel (q, t) := by
  apply compact_rectangle_positive_lower (continuousOn_leechDualKernel_separated ha hab)
  intro p hp
  have hreg := gaussian_separated_rectangle_regular ha hab hp
  exact ckmrvLeechHatKernel_pos
    ((div_pos Real.pi_pos (ha.trans_le hab)).trans_le hp.1.1)
    ((gaussianSeparatedBlockStart_pos a b).trans_le hp.2.1) (sub_ne_zero.mp hreg)

end E8Leech
