import E8Leech.CKMRVKernelRectangles

/-! Explicit rational lower bounds for the actual kernel on checked real rectangles. -/

namespace E8Leech.Taylor

def kernelRectangleLowerBoundChecks (C : KernelRectangleCandidate) (ε : ℚ) : Prop :=
  let regs := kernelProgramModels C.box C.M C.N C.D C.n C.K
  0 ≤ ε ∧ 2 * ε * TM.upper C.box (regs.getD kernelNuRegister SLP.dd0).D ≤
    TM.lower C.box (regs.getD kernelPhiRegister SLP.dd0).D

instance (C : KernelRectangleCandidate) (ε : ℚ) :
    Decidable (kernelRectangleLowerBoundChecks C ε) := by
  unfold kernelRectangleLowerBoundChecks
  infer_instance

def checkKernelRectangleLowerBound (C : KernelRectangleCandidate) (ε : ℚ) : Bool :=
  checkKernelRectangle C && decide (kernelRectangleLowerBoundChecks C ε)

/-- A rational numerator lower bound and denominator upper bound give a quantitative bound.
No division by an interval containing zero is used. -/
theorem ckmrvEightHatKernel_lower_bound_of_checked_rectangle
    {C : KernelRectangleCandidate} {ε : ℚ}
    (hc : checkKernelRectangleLowerBound C ε = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) :
    (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  obtain ⟨hr, he⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hε, hn⟩ := (of_decide_eq_true he : kernelRectangleLowerBoundChecks C ε)
  have hC := kernelSLPBoxCertificate_of_check ((Bool.and_eq_true_iff.mp hr).2)
  have hb := hC.nome.valid
  have hu0 : 0 < u := lt_of_lt_of_le (by exact_mod_cast hb.2.2.1) hu.1
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast hb.2.2.2.1) ht.1
  have hj := kernelRectangle_regular hr hu ht
  have he' := kernelRectangle_mem_axis hr hu ht
  have hut : u ≠ t := by intro h; subst t; exact hj rfl
  have hab : (axisEnv u t).a ≠ (axisEnv u t).b := by
    intro h
    have h' := Real.exp_injective h
    apply hut
    change -Real.pi * u = -Real.pi * t at h'
    nlinarith [Real.pi_pos]
  have hP := approx_kernelProgram_phi hC.nome hC.e2Tail C.N C.D C.n C.K
    hC.logarithms (S := fun _ => True)
  have hQ := approx_kernelProgram_nu hC.nome hC.e2Tail C.N C.D C.n C.K
    hC.logarithms (S := fun _ => True)
  have hp := TM.lower_le hb hP.2.2 he' ⟨trivial, hab⟩
  have hqu := TM.le_upper hb hQ.2.2 he' ⟨trivial, hab⟩
  have hqp := TM.pos_of_lower_pos hb hQ.2.2 hC.denominator he' ⟨trivial, hab⟩
  rw [kernelPhiExpr_evalA_zero _ rfl ht0.ne', sub_zero, kernelPhiExpr_eval_axis hu0 ht0] at hp
  rw [kernelNuExpr_evalA_zero, sub_zero, kernelNuExpr_eval_axis hu0 ht0] at hqu hqp
  rw [← ckmrvEightHatKernel_axis hu0 ht0 hj] at hp
  have hp' : (TM.lower C.box
      ((kernelProgramModels C.box C.M C.N C.D C.n C.K).getD kernelPhiRegister SLP.dd0).D : ℝ) ≤
      2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re *
        (axNu (axV u) (axW u) (axV t) (axW t) / ((axisEnv u t).b - (axisEnv u t).a)) := by
    convert hp using 1
    ring
  have hεr : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hnr : 2 * (ε : ℝ) * (TM.upper C.box
      ((kernelProgramModels C.box C.M C.N C.D C.n C.K).getD kernelNuRegister SLP.dd0).D : ℝ) ≤
      (TM.lower C.box
        ((kernelProgramModels C.box C.M C.N C.D C.n C.K).getD kernelPhiRegister SLP.dd0).D : ℝ) := by
    exact_mod_cast hn
  have hm := (mul_le_mul_of_nonneg_left hqu (show (0 : ℝ) ≤ 2 * ε by positivity)).trans
    (hnr.trans hp')
  by_contra h
  have hlt : (ckmrvEightHatKernel (imagPt u) (imagPt t)).re < (ε : ℝ) := lt_of_not_ge h
  have hlt' := mul_lt_mul_of_pos_right
    (show 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re < 2 * (ε : ℝ) by linarith) hqp
  linarith

end E8Leech.Taylor
