import E8Leech.CKMRVKernelSLP
import E8Leech.KernelBoxEndpoints

/-! The first checked box contains an explicit real rectangle of positive E8 kernel values. -/

namespace E8Leech.Taylor

open scoped Real

theorem firstKernelBox_mem_axis {u t : ℝ}
    (hu : (49999 / 10000 : ℝ) ≤ u ∧ u ≤ 50001 / 10000)
    (ht : (39999 / 10000 : ℝ) ≤ t ∧ t ≤ 40001 / 10000) :
    firstKernelBox.Mem (axisEnv u t) := by
  have ha := kernel_candidate_nome_u hu.1 hu.2
  have hb := kernel_candidate_nome_t ht.1 ht.2
  have hl := kernel_candidate_log_two
  have hpL := Real.pi_gt_d6
  have hpH := Real.pi_lt_d6
  norm_num [Box.Mem, firstKernelBox, axisEnv] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith [ha.1, ha.2, hb.1, hb.2, hu.1, hu.2, ht.1, ht.2, hl.1, hl.2]

/-- Positivity on an explicit two-dimensional rectangle, with no kernel-sign premise. -/
theorem ckmrvEightHatKernel_pos_first_rectangle {u t : ℝ}
    (hu : (49999 / 10000 : ℝ) ≤ u ∧ u ≤ 50001 / 10000)
    (ht : (39999 / 10000 : ℝ) ≤ t ∧ t ≤ 40001 / 10000) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have hu0 : 0 < u := by linarith [hu.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have h1 : t ≠ u := by intro h; linarith [hu.1, ht.2]
  have h2 : t ≠ u⁻¹ := by
    intro h
    have hmul := inv_mul_cancel₀ hu0.ne'
    rw [← h] at hmul
    nlinarith [hu.1, ht.1]
  exact ckmrvEightHatKernel_pos_of_checked_slp_box firstKernelBox_checked hu0 ht0
    (kleinModularJ_imagPt_ne hu0 ht0 h1 h2) (firstKernelBox_mem_axis hu ht)

/-- The certified rectangle contains an actual axis pair. -/
theorem firstKernelBox_nonempty : firstKernelBox.Mem (axisEnv 5 4) :=
  firstKernelBox_mem_axis (by norm_num) (by norm_num)

theorem ckmrvEightHatKernel_pos_five_four :
    0 < (ckmrvEightHatKernel (imagPt 5) (imagPt 4)).re :=
  ckmrvEightHatKernel_pos_first_rectangle (by norm_num) (by norm_num)

end E8Leech.Taylor
