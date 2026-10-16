import E8Leech.CKMRVKernelPhiRectangles

/-!
# Numerator-only certificates below the inverse curve

For ut < 1 the exact divided denominator is negative. A negative upper bound for the
divided numerator therefore proves a positive kernel. This module provides the checker
and its soundness, without claiming that every point has a successful certificate.
-/

namespace E8Leech.Taylor

structure KernelSLPPhiNegativeCertificate (B : Box) (M : ℚ) (N D n K : ℕ) : Prop where
  nome : NomeOK B M
  e2Tail : 4 * M < 1
  logarithms : LogarithmOK B M N D K
  numerator : TM.upper B ((kernelProgramModels B M N D n K).getD kernelPhiRegister SLP.dd0).D < 0

def kernelSLPPhiNegativeBoxChecks (B : Box) (M : ℚ) (N D n K : ℕ) : Prop :=
  B.Valid ∧ B.ahi ≤ M ∧ B.bhi ≤ M ∧ M ≤ 1 / 2 ∧ 4 * M < 1 ∧
    (∀ j : Fin 3,
      TM.absBound B ((generatorDD B M N (logarithmIndex j)).A.sub (TM.const 1)) < 1 ∧
      TM.absBound B ((generatorDD B M N (logarithmIndex j)).B.sub (TM.const 1)) < 1 ∧
      TM.absBound B (DD.logZ B D K (generatorDD B M N (logarithmIndex j))) < 1) ∧
    TM.upper B ((kernelProgramModels B M N D n K).getD kernelPhiRegister SLP.dd0).D < 0

instance (B : Box) (M : ℚ) (N D n K : ℕ) :
    Decidable (kernelSLPPhiNegativeBoxChecks B M N D n K) := by
  unfold kernelSLPPhiNegativeBoxChecks Box.Valid
  infer_instance

def checkKernelSLPPhiNegativeBox (B : Box) (M : ℚ) (N D n K : ℕ) : Bool :=
  decide (kernelSLPPhiNegativeBoxChecks B M N D n K)

theorem kernelSLPPhiNegativeCertificate_of_check {B : Box} {M : ℚ} {N D n K : ℕ}
    (h : checkKernelSLPPhiNegativeBox B M N D n K = true) :
    KernelSLPPhiNegativeCertificate B M N D n K := by
  have hc : kernelSLPPhiNegativeBoxChecks B M N D n K := of_decide_eq_true h
  obtain ⟨hv, ha, hb, hm, he, hl, hp⟩ := hc
  exact ⟨⟨hv, ha, hb, hm⟩, he, ⟨fun j => (hl j).1, fun j => (hl j).2.1,
    fun j => (hl j).2.2⟩, hp⟩

theorem ckmrvEightHatKernel_pos_of_checked_negative_phi_box {B : Box} {M : ℚ}
    {N D n K : ℕ} (h : checkKernelSLPPhiNegativeBox B M N D n K = true)
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (hut : u ≠ t) (hprod : u * t < 1)
    (he : B.Mem (axisEnv u t)) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have hC := kernelSLPPhiNegativeCertificate_of_check h
  have hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t) := by
    apply kleinModularJ_imagPt_ne hu ht hut.symm
    intro hti
    have hzero : u * t = 1 := by rw [hti]; exact mul_inv_cancel₀ hu.ne'
    linarith
  have hab : (axisEnv u t).a ≠ (axisEnv u t).b := by
    intro h
    have h' := Real.exp_injective h
    apply hut
    change -Real.pi * u = -Real.pi * t at h'
    nlinarith [Real.pi_pos]
  have hP := approx_kernelProgram_phi hC.nome hC.e2Tail N D n K hC.logarithms
    (S := fun _ => True)
  have hp := TM.neg_of_upper_neg hC.nome.valid hP.2.2 hC.numerator he ⟨trivial, hab⟩
  rw [kernelPhiExpr_evalA_zero _ rfl ht.ne', sub_zero, kernelPhiExpr_eval_axis hu ht,
    ← ckmrvEightHatKernel_axis hu ht hJ] at hp
  have hmul : 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re *
      (axNu (axV u) (axW u) (axV t) (axW t) /
        (Real.exp (-Real.pi * t) - Real.exp (-Real.pi * u))) < 0 := by
    change (2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re *
      axNu (axV u) (axW u) (axV t) (axW t)) /
        (Real.exp (-Real.pi * t) - Real.exp (-Real.pi * u)) < 0 at hp
    convert hp using 1
    ring
  have hq := ckmrvAxisDividedDenominator_neg hu ht hut hprod
  have hk : 0 < 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
    by_contra hn
    have hnonneg := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hn) hq.le
    linarith
  linarith

def checkKernelPhiNegativeRectangle (C : KernelRectangleCandidate) : Bool :=
  decide (kernelPhiRectangleEndpointChecks C) && decide (C.box.uhi * C.box.thi < 1) &&
    checkKernelSLPPhiNegativeBox C.box C.M C.N C.D C.n C.K

theorem kernelPhiNegativeRectangle_mem_axis {C : KernelRectangleCandidate}
    (hc : checkKernelPhiNegativeRectangle C = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) : C.box.Mem (axisEnv u t) := by
  obtain ⟨he, hk⟩ := Bool.and_eq_true_iff.mp hc
  exact (of_decide_eq_true (Bool.and_eq_true_iff.mp he).1 :
    kernelPhiRectangleEndpointChecks C).mem_axis
      (kernelSLPPhiNegativeCertificate_of_check hk).nome.valid hu ht

theorem ckmrvEightHatKernel_pos_of_checked_negative_phi_rectangle
    {C : KernelRectangleCandidate} (hc : checkKernelPhiNegativeRectangle C = true)
    {u t : ℝ} (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) (hut : u ≠ t) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  obtain ⟨he, hk⟩ := Bool.and_eq_true_iff.mp hc
  have hb := (kernelSLPPhiNegativeCertificate_of_check hk).nome.valid
  have hu0 : 0 < u := lt_of_lt_of_le (by exact_mod_cast hb.2.2.1) hu.1
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast hb.2.2.2.1) ht.1
  have hp : C.box.uhi * C.box.thi < 1 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp he).2
  have hpr : (C.box.uhi : ℝ) * C.box.thi < 1 := by exact_mod_cast hp
  have hm := mul_le_mul hu.2 ht.2 ht0.le (hu0.le.trans hu.2)
  exact ckmrvEightHatKernel_pos_of_checked_negative_phi_box hk hu0 ht0 hut
    (hm.trans_lt hpr) (kernelPhiNegativeRectangle_mem_axis hc hu ht)

theorem ckmrvEightHatKernel_nonneg_of_checked_negative_phi_rectangle
    {C : KernelRectangleCandidate} (hc : checkKernelPhiNegativeRectangle C = true)
    {u t : ℝ} (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) :
    0 ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  by_cases h : u = t
  · subst t
    rw [ckmrvEightHatKernel_eq_zero_of_kleinJ_eq rfl]
    simp
  · exact (ckmrvEightHatKernel_pos_of_checked_negative_phi_rectangle hc hu ht h).le

def checkKernelPhiNegativeRectangleCover : KernelRectangleCover → AxisTile → Bool :=
  checkKernelRectangleCoverWith checkKernelPhiNegativeRectangle

theorem ckmrvEightHatKernel_pos_of_checked_negative_phi_cover
    (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelPhiNegativeRectangleCover cover R = true)
    {u t : ℝ} (hm : R.Mem u t) (hut : u ≠ t) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have h := kernelRectangleCoverWith_sound checkKernelPhiNegativeRectangle
    (fun u t => u ≠ t → 0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re)
    (fun _ h _ _ hu ht hut =>
      ckmrvEightHatKernel_pos_of_checked_negative_phi_rectangle h hu ht hut)
    cover R hc hm
  exact h hut

theorem ckmrvEightHatKernel_nonneg_of_checked_negative_phi_cover
    (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelPhiNegativeRectangleCover cover R = true) {u t : ℝ} (hm : R.Mem u t) :
    0 ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  exact kernelRectangleCoverWith_sound _ _
    (fun _ h _ _ hu ht => ckmrvEightHatKernel_nonneg_of_checked_negative_phi_rectangle h hu ht)
    cover R hc hm

end E8Leech.Taylor
