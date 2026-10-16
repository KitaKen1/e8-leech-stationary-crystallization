import E8Leech.CKMRVKernelMixedPhiNegative
import E8Leech.CKMRVKernelMixedPhiPositive

/-!
# Quantitative kernel bounds with independent theta and E2 orders

For ut < 1 use the divided numerator upper and denominator lower; for ut > 1
use the divided numerator lower and denominator upper. Both branches exclude the
diagonal for a positive margin. Soundness alone does not assert a concrete margin
or certify the entire regular locus.
-/

namespace E8Leech.Taylor

def kernelMixedPhiNegativeLowerBoundChecks (NE : ℕ) (C : KernelRectangleCandidate) (ε : ℚ) : Prop :=
  let regs := kernelMixedProgramModels C.box C.M C.N NE C.D C.n C.K
  0 ≤ ε ∧ TM.upper C.box (regs.getD kernelPhiRegister SLP.dd0).D ≤
    2 * ε * TM.lower C.box (regs.getD kernelNuRegister SLP.dd0).D

instance (NE : ℕ) (C : KernelRectangleCandidate) (ε : ℚ) :
    Decidable (kernelMixedPhiNegativeLowerBoundChecks NE C ε) := by
  unfold kernelMixedPhiNegativeLowerBoundChecks
  infer_instance

def checkKernelMixedPhiNegativeLowerBound (NE : ℕ) (C : KernelRectangleCandidate) (ε : ℚ) : Bool :=
  checkKernelMixedPhiNegativeRectangle NE C && decide (kernelMixedPhiNegativeLowerBoundChecks NE C ε)

/-- The inequality direction reverses because the exact denominator is negative. -/
theorem ckmrvEightHatKernel_lower_bound_of_checked_mixed_negative_phi_rectangle
    {C : KernelRectangleCandidate} {NE : ℕ} {ε : ℚ}
    (hc : checkKernelMixedPhiNegativeLowerBound NE C ε = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) (hut : u ≠ t) :
    (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  obtain ⟨hr, he⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hε, hn⟩ := (of_decide_eq_true he : kernelMixedPhiNegativeLowerBoundChecks NE C ε)
  obtain ⟨hep, hk⟩ := Bool.and_eq_true_iff.mp hr
  have hC := kernelMixedPhiNegativeCertificate_of_check hk
  have hb := hC.nome.valid
  have hu0 : 0 < u := lt_of_lt_of_le (by exact_mod_cast hb.2.2.1) hu.1
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast hb.2.2.2.1) ht.1
  have hprod : u * t < 1 := by
    have hhi : C.box.uhi * C.box.thi < 1 :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hep).2
    have hhir : (C.box.uhi : ℝ) * C.box.thi < 1 := by exact_mod_cast hhi
    exact (mul_le_mul hu.2 ht.2 ht0.le (hu0.le.trans hu.2)).trans_lt hhir
  have hj : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t) := by
    apply kleinModularJ_imagPt_ne hu0 ht0 hut.symm
    intro h
    have hz : u * t = 1 := by rw [h]; exact mul_inv_cancel₀ hu0.ne'
    linarith
  have hab : (axisEnv u t).a ≠ (axisEnv u t).b := by
    intro h
    have h' := Real.exp_injective h
    apply hut
    change -Real.pi * u = -Real.pi * t at h'
    nlinarith [Real.pi_pos]
  have he' := kernelMixedPhiNegativeRectangle_mem_axis hr hu ht
  have hP := approx_kernelMixedProgram_phi hC.nome hC.e2Tail C.N NE C.D C.n C.K
    hC.logarithms (S := fun _ => True)
  have hQ := approx_kernelMixedProgram_nu hC.nome hC.e2Tail C.N NE C.D C.n C.K
    hC.logarithms (S := fun _ => True)
  have hp := TM.le_upper hb hP.2.2 he' ⟨trivial, hab⟩
  have hql := TM.lower_le hb hQ.2.2 he' ⟨trivial, hab⟩
  have hqn := ckmrvAxisDividedDenominator_neg hu0 ht0 hut hprod
  rw [kernelPhiExpr_evalA_zero _ rfl ht0.ne', sub_zero,
    kernelPhiExpr_eval_axis hu0 ht0, ← ckmrvEightHatKernel_axis hu0 ht0 hj] at hp
  rw [kernelNuExpr_evalA_zero, sub_zero, kernelNuExpr_eval_axis hu0 ht0] at hql
  have hp' : 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re *
      (axNu (axV u) (axW u) (axV t) (axW t) / ((axisEnv u t).b - (axisEnv u t).a)) ≤
      (TM.upper C.box
        ((kernelMixedProgramModels C.box C.M C.N NE C.D C.n C.K).getD kernelPhiRegister SLP.dd0).D : ℝ) := by
    convert hp using 1
    ring
  have hεr : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hnr : (TM.upper C.box
      ((kernelMixedProgramModels C.box C.M C.N NE C.D C.n C.K).getD kernelPhiRegister SLP.dd0).D : ℝ) ≤
      2 * (ε : ℝ) * (TM.lower C.box
        ((kernelMixedProgramModels C.box C.M C.N NE C.D C.n C.K).getD kernelNuRegister SLP.dd0).D : ℝ) := by
    exact_mod_cast hn
  have hm := hp'.trans (hnr.trans
    (mul_le_mul_of_nonneg_left hql (show (0 : ℝ) ≤ 2 * ε by positivity)))
  by_contra h
  have hlt : (ckmrvEightHatKernel (imagPt u) (imagPt t)).re < (ε : ℝ) := lt_of_not_ge h
  have hlt' := mul_lt_mul_of_neg_right
    (show 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re < 2 * (ε : ℝ) by linarith) hqn
  exact (not_lt_of_ge hm) hlt'

def checkKernelMixedPhiNegativeLowerBoundCover (NE : ℕ) (ε : ℚ) : KernelRectangleCover → AxisTile → Bool :=
  checkKernelRectangleCoverWith (fun C => checkKernelMixedPhiNegativeLowerBound NE C ε)

theorem ckmrvEightHatKernel_lower_bound_of_checked_mixed_negative_phi_cover {NE : ℕ} {ε : ℚ}
    (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelMixedPhiNegativeLowerBoundCover NE ε cover R = true)
    {u t : ℝ} (hm : R.Mem u t) (hut : u ≠ t) :
    (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have h := kernelRectangleCoverWith_sound (fun C => checkKernelMixedPhiNegativeLowerBound NE C ε)
    (fun u t => u ≠ t → (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re)
    (fun _ h _ _ hu ht hut =>
      ckmrvEightHatKernel_lower_bound_of_checked_mixed_negative_phi_rectangle h hu ht hut)
    cover R hc hm
  exact h hut


def kernelMixedPhiPositiveLowerBoundChecks (NE : ℕ) (C : KernelRectangleCandidate) (ε : ℚ) : Prop :=
  let regs := kernelMixedProgramModels C.box C.M C.N NE C.D C.n C.K
  0 ≤ ε ∧ 2 * ε * TM.upper C.box (regs.getD kernelNuRegister SLP.dd0).D ≤
    TM.lower C.box (regs.getD kernelPhiRegister SLP.dd0).D

instance (NE : ℕ) (C : KernelRectangleCandidate) (ε : ℚ) :
    Decidable (kernelMixedPhiPositiveLowerBoundChecks NE C ε) := by
  unfold kernelMixedPhiPositiveLowerBoundChecks
  infer_instance

def checkKernelMixedPhiPositiveLowerBound (NE : ℕ) (C : KernelRectangleCandidate) (ε : ℚ) : Bool :=
  checkKernelMixedPhiPositiveRectangle NE C && decide (kernelMixedPhiPositiveLowerBoundChecks NE C ε)

/-- A positive divided denominator permits a numerator lower / denominator upper estimate. -/
theorem ckmrvEightHatKernel_lower_bound_of_checked_mixed_positive_phi_rectangle
    {C : KernelRectangleCandidate} {NE : ℕ} {ε : ℚ}
    (hc : checkKernelMixedPhiPositiveLowerBound NE C ε = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) (hut : u ≠ t) :
    (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  obtain ⟨hr, he⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hε, hn⟩ := (of_decide_eq_true he : kernelMixedPhiPositiveLowerBoundChecks NE C ε)
  obtain ⟨hep, hk⟩ := Bool.and_eq_true_iff.mp hr
  have hC := kernelMixedPhiPositiveCertificate_of_check hk
  have hb := hC.nome.valid
  have hu0 : 0 < u := lt_of_lt_of_le (by exact_mod_cast hb.2.2.1) hu.1
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast hb.2.2.2.1) ht.1
  have hprod : 1 < u * t := by
    have hlo : 1 < C.box.ulo * C.box.tlo :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hep).2
    have hlor : (1 : ℝ) < (C.box.ulo : ℝ) * C.box.tlo := by exact_mod_cast hlo
    exact hlor.trans_le (mul_le_mul hu.1 ht.1 (by exact_mod_cast hb.2.2.2.1.le) hu0.le)
  have hj : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t) := by
    apply kleinModularJ_imagPt_ne hu0 ht0 hut.symm
    intro h
    have hz : u * t = 1 := by rw [h]; exact mul_inv_cancel₀ hu0.ne'
    linarith
  have hab : (axisEnv u t).a ≠ (axisEnv u t).b := by
    intro h
    have h' := Real.exp_injective h
    apply hut
    change -Real.pi * u = -Real.pi * t at h'
    nlinarith [Real.pi_pos]
  have he' := kernelMixedPhiPositiveRectangle_mem_axis hr hu ht
  have hP := approx_kernelMixedProgram_phi hC.nome hC.e2Tail C.N NE C.D C.n C.K
    hC.logarithms (S := fun _ => True)
  have hQ := approx_kernelMixedProgram_nu hC.nome hC.e2Tail C.N NE C.D C.n C.K
    hC.logarithms (S := fun _ => True)
  have hp := TM.lower_le hb hP.2.2 he' ⟨trivial, hab⟩
  have hqu := TM.le_upper hb hQ.2.2 he' ⟨trivial, hab⟩
  have hqp := ckmrvAxisDividedDenominator_pos hu0 ht0 hut hprod
  rw [kernelPhiExpr_evalA_zero _ rfl ht0.ne', sub_zero,
    kernelPhiExpr_eval_axis hu0 ht0, ← ckmrvEightHatKernel_axis hu0 ht0 hj] at hp
  rw [kernelNuExpr_evalA_zero, sub_zero, kernelNuExpr_eval_axis hu0 ht0] at hqu
  have hp' : (TM.lower C.box
      ((kernelMixedProgramModels C.box C.M C.N NE C.D C.n C.K).getD kernelPhiRegister SLP.dd0).D : ℝ) ≤
      2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re *
        (axNu (axV u) (axW u) (axV t) (axW t) / ((axisEnv u t).b - (axisEnv u t).a)) := by
    convert hp using 1
    ring
  have hεr : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hnr : 2 * (ε : ℝ) * (TM.upper C.box
      ((kernelMixedProgramModels C.box C.M C.N NE C.D C.n C.K).getD kernelNuRegister SLP.dd0).D : ℝ) ≤
      (TM.lower C.box
        ((kernelMixedProgramModels C.box C.M C.N NE C.D C.n C.K).getD kernelPhiRegister SLP.dd0).D : ℝ) := by
    exact_mod_cast hn
  have hm := (mul_le_mul_of_nonneg_left hqu (show (0 : ℝ) ≤ 2 * ε by positivity)).trans
    (hnr.trans hp')
  by_contra h
  have hlt : (ckmrvEightHatKernel (imagPt u) (imagPt t)).re < (ε : ℝ) := lt_of_not_ge h
  have hlt' := mul_lt_mul_of_pos_right
    (show 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re < 2 * (ε : ℝ) by linarith) hqp
  exact (not_lt_of_ge hm) hlt'

def checkKernelMixedPhiPositiveLowerBoundCover (NE : ℕ) (ε : ℚ) : KernelRectangleCover → AxisTile → Bool :=
  checkKernelRectangleCoverWith (fun C => checkKernelMixedPhiPositiveLowerBound NE C ε)

theorem ckmrvEightHatKernel_lower_bound_of_checked_mixed_positive_phi_cover {NE : ℕ} {ε : ℚ}
    (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelMixedPhiPositiveLowerBoundCover NE ε cover R = true)
    {u t : ℝ} (hm : R.Mem u t) (hut : u ≠ t) :
    (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have h := kernelRectangleCoverWith_sound (fun C => checkKernelMixedPhiPositiveLowerBound NE C ε)
    (fun u t => u ≠ t → (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re)
    (fun _ h _ _ hu ht hut =>
      ckmrvEightHatKernel_lower_bound_of_checked_mixed_positive_phi_rectangle h hu ht hut)
    cover R hc hm
  exact h hut


end E8Leech.Taylor
