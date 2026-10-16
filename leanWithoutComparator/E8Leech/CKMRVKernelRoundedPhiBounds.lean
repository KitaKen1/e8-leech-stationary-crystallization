import E8Leech.CKMRVKernelRoundedPhiNegative

/-!
# Quantitative rounded kernel bounds below the inverse curve

For ut < 1 use the divided numerator upper and denominator lower.
The branch excludes the diagonal for a positive margin. Soundness alone does not assert a concrete margin
or certify the entire regular locus.

This module uses the outward-rounded evaluator at precision p.
-/

namespace E8Leech.Taylor

def kernelRoundedMixedPhiNegativeLowerBoundChecks (NE p : ℕ) (C : KernelRectangleCandidate) (ε : ℚ) : Prop :=
  let regs := kernelRoundedMixedProgramModels C.box C.M C.N NE C.D C.n C.K p
  0 ≤ ε ∧ TM.upper C.box (regs.getD kernelPhiRegister SLP.dd0).D ≤
    2 * ε * TM.lower C.box (regs.getD kernelNuRegister SLP.dd0).D

instance (NE p : ℕ) (C : KernelRectangleCandidate) (ε : ℚ) :
    Decidable (kernelRoundedMixedPhiNegativeLowerBoundChecks NE p C ε) := by
  unfold kernelRoundedMixedPhiNegativeLowerBoundChecks
  infer_instance

def checkKernelRoundedMixedPhiNegativeLowerBound (NE p : ℕ) (C : KernelRectangleCandidate) (ε : ℚ) : Bool :=
  checkKernelRoundedMixedPhiNegativeRectangle NE p C && decide (kernelRoundedMixedPhiNegativeLowerBoundChecks NE p C ε)

/-- The inequality direction reverses because the exact denominator is negative. -/
theorem ckmrvEightHatKernel_lower_bound_of_checked_rounded_mixed_negative_phi_rectangle
    {C : KernelRectangleCandidate} {NE p : ℕ} {ε : ℚ}
    (hc : checkKernelRoundedMixedPhiNegativeLowerBound NE p C ε = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) (hut : u ≠ t) :
    (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  obtain ⟨hr, he⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hε, hn⟩ := (of_decide_eq_true he : kernelRoundedMixedPhiNegativeLowerBoundChecks NE p C ε)
  obtain ⟨hep, hk⟩ := Bool.and_eq_true_iff.mp hr
  have hC := kernelRoundedMixedPhiNegativeCertificate_of_check hk
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
  have he' := kernelRoundedMixedPhiNegativeRectangle_mem_axis hr hu ht
  have hP := approx_kernelRoundedMixedProgram_phi hC.nome hC.e2Tail C.N NE C.D C.n C.K p
    hC.logarithms (S := fun _ => True)
  have hQ := approx_kernelRoundedMixedProgram_nu hC.nome hC.e2Tail C.N NE C.D C.n C.K p
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
        ((kernelRoundedMixedProgramModels C.box C.M C.N NE C.D C.n C.K p).getD kernelPhiRegister SLP.dd0).D : ℝ) := by
    convert hp using 1
    ring
  have hεr : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hnr : (TM.upper C.box
      ((kernelRoundedMixedProgramModels C.box C.M C.N NE C.D C.n C.K p).getD kernelPhiRegister SLP.dd0).D : ℝ) ≤
      2 * (ε : ℝ) * (TM.lower C.box
        ((kernelRoundedMixedProgramModels C.box C.M C.N NE C.D C.n C.K p).getD kernelNuRegister SLP.dd0).D : ℝ) := by
    exact_mod_cast hn
  have hm := hp'.trans (hnr.trans
    (mul_le_mul_of_nonneg_left hql (show (0 : ℝ) ≤ 2 * ε by positivity)))
  by_contra h
  have hlt : (ckmrvEightHatKernel (imagPt u) (imagPt t)).re < (ε : ℝ) := lt_of_not_ge h
  have hlt' := mul_lt_mul_of_neg_right
    (show 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re < 2 * (ε : ℝ) by linarith) hqn
  exact (not_lt_of_ge hm) hlt'

def checkKernelRoundedMixedPhiNegativeLowerBoundCover (NE p : ℕ) (ε : ℚ) : KernelRectangleCover → AxisTile → Bool :=
  checkKernelRectangleCoverWith (fun C => checkKernelRoundedMixedPhiNegativeLowerBound NE p C ε)

theorem ckmrvEightHatKernel_lower_bound_of_checked_rounded_mixed_negative_phi_cover {NE p : ℕ} {ε : ℚ}
    (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelRoundedMixedPhiNegativeLowerBoundCover NE p ε cover R = true)
    {u t : ℝ} (hm : R.Mem u t) (hut : u ≠ t) :
    (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have h := kernelRectangleCoverWith_sound (fun C => checkKernelRoundedMixedPhiNegativeLowerBound NE p C ε)
    (fun u t => u ≠ t → (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re)
    (fun _ h _ _ hu ht hut =>
      ckmrvEightHatKernel_lower_bound_of_checked_rounded_mixed_negative_phi_rectangle h hu ht hut)
    cover R hc hm
  exact h hut


end E8Leech.Taylor
