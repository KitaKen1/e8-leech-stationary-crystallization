import E8Leech.CKMRVKernelPhiNegative

/-! Quantitative bounds below ut = 1, using a numerator upper and denominator lower. -/

namespace E8Leech.Taylor

def kernelPhiNegativeLowerBoundChecks (C : KernelRectangleCandidate) (ε : ℚ) : Prop :=
  let regs := kernelProgramModels C.box C.M C.N C.D C.n C.K
  0 ≤ ε ∧ TM.upper C.box (regs.getD kernelPhiRegister SLP.dd0).D ≤
    2 * ε * TM.lower C.box (regs.getD kernelNuRegister SLP.dd0).D

instance (C : KernelRectangleCandidate) (ε : ℚ) :
    Decidable (kernelPhiNegativeLowerBoundChecks C ε) := by
  unfold kernelPhiNegativeLowerBoundChecks
  infer_instance

def checkKernelPhiNegativeLowerBound (C : KernelRectangleCandidate) (ε : ℚ) : Bool :=
  checkKernelPhiNegativeRectangle C && decide (kernelPhiNegativeLowerBoundChecks C ε)

/-- The inequality direction reverses because the exact denominator is negative. -/
theorem ckmrvEightHatKernel_lower_bound_of_checked_negative_phi_rectangle
    {C : KernelRectangleCandidate} {ε : ℚ}
    (hc : checkKernelPhiNegativeLowerBound C ε = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) (hut : u ≠ t) :
    (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  obtain ⟨hr, he⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hε, hn⟩ := (of_decide_eq_true he : kernelPhiNegativeLowerBoundChecks C ε)
  obtain ⟨hep, hk⟩ := Bool.and_eq_true_iff.mp hr
  have hC := kernelSLPPhiNegativeCertificate_of_check hk
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
  have he' := kernelPhiNegativeRectangle_mem_axis hr hu ht
  have hP := approx_kernelProgram_phi hC.nome hC.e2Tail C.N C.D C.n C.K
    hC.logarithms (S := fun _ => True)
  have hQ := approx_kernelProgram_nu hC.nome hC.e2Tail C.N C.D C.n C.K
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
        ((kernelProgramModels C.box C.M C.N C.D C.n C.K).getD kernelPhiRegister SLP.dd0).D : ℝ) := by
    convert hp using 1
    ring
  have hεr : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hnr : (TM.upper C.box
      ((kernelProgramModels C.box C.M C.N C.D C.n C.K).getD kernelPhiRegister SLP.dd0).D : ℝ) ≤
      2 * (ε : ℝ) * (TM.lower C.box
        ((kernelProgramModels C.box C.M C.N C.D C.n C.K).getD kernelNuRegister SLP.dd0).D : ℝ) := by
    exact_mod_cast hn
  have hm := hp'.trans (hnr.trans
    (mul_le_mul_of_nonneg_left hql (show (0 : ℝ) ≤ 2 * ε by positivity)))
  by_contra h
  have hlt : (ckmrvEightHatKernel (imagPt u) (imagPt t)).re < (ε : ℝ) := lt_of_not_ge h
  have hlt' := mul_lt_mul_of_neg_right
    (show 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re < 2 * (ε : ℝ) by linarith) hqn
  exact (not_lt_of_ge hm) hlt'

def checkKernelPhiNegativeLowerBoundCover (ε : ℚ) : KernelRectangleCover → AxisTile → Bool :=
  checkKernelRectangleCoverWith (fun C => checkKernelPhiNegativeLowerBound C ε)

theorem ckmrvEightHatKernel_lower_bound_of_checked_negative_phi_cover {ε : ℚ}
    (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelPhiNegativeLowerBoundCover ε cover R = true)
    {u t : ℝ} (hm : R.Mem u t) (hut : u ≠ t) :
    (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have h := kernelRectangleCoverWith_sound (fun C => checkKernelPhiNegativeLowerBound C ε)
    (fun u t => u ≠ t → (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re)
    (fun _ h _ _ hu ht hut =>
      ckmrvEightHatKernel_lower_bound_of_checked_negative_phi_rectangle h hu ht hut)
    cover R hc hm
  exact h hut

end E8Leech.Taylor
