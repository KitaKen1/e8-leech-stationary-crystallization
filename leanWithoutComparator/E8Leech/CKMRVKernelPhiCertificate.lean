import E8Leech.CKMRVAxisDenominatorSign
import E8Leech.CKMRVKernelSLP

/-!
# Numerator-only certificates above the inverse curve

The shared program is checked against the same source expression as before.
Only its numerator lower bound is required: the denominator sign follows
from the exact imaginary-axis theorem, for every positive pair with ut > 1.
-/

namespace E8Leech.Taylor

structure KernelSLPPhiCertificate (B : Box) (M : ℚ) (N D n K : ℕ) : Prop where
  nome : NomeOK B M
  e2Tail : 4 * M < 1
  logarithms : LogarithmOK B M N D K
  numerator : 0 < TM.lower B ((kernelProgramModels B M N D n K).getD kernelPhiRegister SLP.dd0).D

def kernelSLPPhiBoxChecks (B : Box) (M : ℚ) (N D n K : ℕ) : Prop :=
  B.Valid ∧ B.ahi ≤ M ∧ B.bhi ≤ M ∧ M ≤ 1 / 2 ∧ 4 * M < 1 ∧
    (∀ j : Fin 3,
      TM.absBound B ((generatorDD B M N (logarithmIndex j)).A.sub (TM.const 1)) < 1 ∧
      TM.absBound B ((generatorDD B M N (logarithmIndex j)).B.sub (TM.const 1)) < 1 ∧
      TM.absBound B (DD.logZ B D K (generatorDD B M N (logarithmIndex j))) < 1) ∧
    0 < TM.lower B ((kernelProgramModels B M N D n K).getD kernelPhiRegister SLP.dd0).D

instance (B : Box) (M : ℚ) (N D n K : ℕ) :
    Decidable (kernelSLPPhiBoxChecks B M N D n K) := by
  unfold kernelSLPPhiBoxChecks Box.Valid
  infer_instance

def checkKernelSLPPhiBox (B : Box) (M : ℚ) (N D n K : ℕ) : Bool :=
  decide (kernelSLPPhiBoxChecks B M N D n K)

theorem kernelSLPPhiCertificate_of_check {B : Box} {M : ℚ} {N D n K : ℕ}
    (h : checkKernelSLPPhiBox B M N D n K = true) : KernelSLPPhiCertificate B M N D n K := by
  have hc : kernelSLPPhiBoxChecks B M N D n K := of_decide_eq_true h
  obtain ⟨hv, ha, hb, hm, he, hl, hp⟩ := hc
  exact ⟨⟨hv, ha, hb, hm⟩, he, ⟨fun j => (hl j).1, fun j => (hl j).2.1,
    fun j => (hl j).2.2⟩, hp⟩

theorem kernelSLPPhiCertificate_of_full {B : Box} {M : ℚ} {N D n K : ℕ}
    (h : KernelSLPBoxCertificate B M N D n K) : KernelSLPPhiCertificate B M N D n K :=
  ⟨h.nome, h.e2Tail, h.logarithms, h.numerator⟩

theorem checkKernelSLPPhiBox_eq_true_of_full {B : Box} {M : ℚ} {N D n K : ℕ}
    (h : checkKernelSLPBox B M N D n K = true) :
    checkKernelSLPPhiBox B M N D n K = true := by
  apply decide_eq_true
  have hc : kernelSLPBoxChecks B M N D n K := of_decide_eq_true h
  obtain ⟨hv, ha, hb, hm, he, hl, hp, _⟩ := hc
  exact ⟨hv, ha, hb, hm, he, hl, hp⟩

/-- No numerical lower bound for the divided denominator is assumed here. -/
theorem ckmrvEightHatKernel_pos_of_checked_phi_box {B : Box} {M : ℚ} {N D n K : ℕ}
    (h : checkKernelSLPPhiBox B M N D n K = true) {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hut : u ≠ t) (hprod : 1 < u * t) (he : B.Mem (axisEnv u t)) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have hC := kernelSLPPhiCertificate_of_check h
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
  have hp := TM.pos_of_lower_pos hC.nome.valid hP.2.2 hC.numerator he ⟨trivial, hab⟩
  rw [kernelPhiExpr_evalA_zero _ rfl ht.ne', sub_zero, kernelPhiExpr_eval_axis hu ht,
    ← ckmrvEightHatKernel_axis hu ht hJ] at hp
  have hmul : 0 < 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re *
      (axNu (axV u) (axW u) (axV t) (axW t) /
        (Real.exp (-Real.pi * t) - Real.exp (-Real.pi * u))) := by
    change 0 < (2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re *
      axNu (axV u) (axW u) (axV t) (axW t)) /
        (Real.exp (-Real.pi * t) - Real.exp (-Real.pi * u)) at hp
    convert hp using 1
    ring
  have hq := ckmrvAxisDividedDenominator_pos hu ht hut hprod
  have hk : 0 < 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re :=
    (mul_pos_iff_of_pos_right hq).mp hmul
  linarith

end E8Leech.Taylor
