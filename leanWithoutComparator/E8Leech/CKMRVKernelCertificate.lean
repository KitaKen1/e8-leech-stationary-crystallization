import E8Leech.CKMRVKernelExpr
import E8Leech.TaylorModelEnclosure

/-!
# Soundness of rational box certificates for the actual E8 hat kernel

A `KernelBoxCertificate` contains only the rational bounds needed by the generator models and
positive lower bounds for the divided differences of the numerator and denominator. Its
soundness theorem gives strict positivity of the actual CKMRV kernel on the certified box,
off the two singular curves. No positivity assumption about the real kernel is an input.

This is the certificate interface, not yet a cover of the whole positive quadrant.
-/

namespace E8Leech.Taylor

open UpperHalfPlane hiding I
open scoped Real

def kernelExprModel (B : Box) (M : ℚ) (N D n K : ℕ) (x : KExpr) : DD :=
  KExpr.dd B D (generatorDD B M N) (logarithmDD B M N D n K) x

theorem approx_kernelExprModel {B : Box} {M : ℚ} (hB : NomeOK B M) (hM : 4 * M < 1)
    (N D n K : ℕ) (hL : LogarithmOK B M N D K) (x : KExpr) {S : Env → Prop} :
    (kernelExprModel B M N D n K x).Approx B S (KExpr.evalA x) (KExpr.evalB x) :=
  KExpr.approx_dd hB.valid D (approx_generatorDD hB hM N)
    (approx_logarithmDD hB hM N D n K hL) x

/-- All certificate fields are rational inequalities or finite rational computations. -/
structure KernelBoxCertificate (B : Box) (M : ℚ) (N D n K : ℕ) : Prop where
  nome : NomeOK B M
  e2Tail : 4 * M < 1
  logarithms : LogarithmOK B M N D K
  numerator : 0 < TM.lower B (kernelExprModel B M N D n K kernelPhiExpr).D
  denominator : 0 < TM.lower B (kernelExprModel B M N D n K kernelNuExpr).D

/-- The finite rational checks in a form with a computable decision procedure. -/
def kernelBoxChecks (B : Box) (M : ℚ) (N D n K : ℕ) : Prop :=
  B.Valid ∧ B.ahi ≤ M ∧ B.bhi ≤ M ∧ M ≤ 1 / 2 ∧ 4 * M < 1 ∧
    (∀ j : Fin 3,
      TM.absBound B ((generatorDD B M N (logarithmIndex j)).A.sub (TM.const 1)) < 1 ∧
      TM.absBound B ((generatorDD B M N (logarithmIndex j)).B.sub (TM.const 1)) < 1 ∧
      TM.absBound B (DD.logZ B D K (generatorDD B M N (logarithmIndex j))) < 1) ∧
    0 < TM.lower B (kernelExprModel B M N D n K kernelPhiExpr).D ∧
    0 < TM.lower B (kernelExprModel B M N D n K kernelNuExpr).D

instance instDecidableKernelBoxChecks (B : Box) (M : ℚ) (N D n K : ℕ) :
    Decidable (kernelBoxChecks B M N D n K) := by
  unfold kernelBoxChecks Box.Valid
  infer_instance

def checkKernelBox (B : Box) (M : ℚ) (N D n K : ℕ) : Bool :=
  decide (kernelBoxChecks B M N D n K)

theorem kernelBoxCertificate_of_check {B : Box} {M : ℚ} {N D n K : ℕ}
    (h : checkKernelBox B M N D n K = true) : KernelBoxCertificate B M N D n K := by
  have hc : kernelBoxChecks B M N D n K := of_decide_eq_true h
  obtain ⟨hvalid, ha, hb, hM, hE, hL, hP, hQ⟩ := hc
  exact ⟨⟨hvalid, ha, hb, hM⟩, hE, ⟨fun j => (hL j).1, fun j => (hL j).2.1,
    fun j => (hL j).2.2⟩, hP, hQ⟩

/-- A rational box certificate proves strict positivity of the actual kernel there. -/
theorem ckmrvEightHatKernel_pos_of_box_certificate {B : Box} {M : ℚ} {N D n K : ℕ}
    (hC : KernelBoxCertificate B M N D n K) {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) (he : B.Mem (axisEnv u t)) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have hut : u ≠ t := by
    intro h
    subst t
    exact hJ rfl
  have hab : (axisEnv u t).a ≠ (axisEnv u t).b := by
    intro h
    have h' := Real.exp_injective h
    apply hut
    change -π * u = -π * t at h'
    nlinarith [Real.pi_pos]
  have hP := approx_kernelExprModel hC.nome hC.e2Tail N D n K hC.logarithms kernelPhiExpr
    (S := fun _ => True)
  have hQ := approx_kernelExprModel hC.nome hC.e2Tail N D n K hC.logarithms kernelNuExpr
    (S := fun _ => True)
  have hp := TM.pos_of_lower_pos hC.nome.valid hP.2.2 hC.numerator he ⟨trivial, hab⟩
  have hq := TM.pos_of_lower_pos hC.nome.valid hQ.2.2 hC.denominator he ⟨trivial, hab⟩
  rw [kernelPhiExpr_evalA_zero _ rfl ht.ne', sub_zero, kernelPhiExpr_eval_axis hu ht] at hp
  rw [kernelNuExpr_evalA_zero, sub_zero, kernelNuExpr_eval_axis hu ht] at hq
  rw [← ckmrvEightHatKernel_axis hu ht hJ] at hp
  have hmul : 0 < 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re *
      (axNu (axV u) (axW u) (axV t) (axW t) / ((axisEnv u t).b - (axisEnv u t).a)) := by
    convert hp using 1; ring
  by_contra h
  have hnonpos : 2 * (ckmrvEightHatKernel (imagPt u) (imagPt t)).re ≤ 0 := by
    linarith [not_lt.mp h]
  have := mul_nonpos_of_nonpos_of_nonneg hnonpos hq.le
  linarith

/-- A successful finite computation gives positivity of the real kernel. -/
theorem ckmrvEightHatKernel_pos_of_checked_box {B : Box} {M : ℚ} {N D n K : ℕ}
    (h : checkKernelBox B M N D n K = true) {u t : ℝ} (hu : 0 < u) (ht : 0 < t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) (he : B.Mem (axisEnv u t)) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re :=
  ckmrvEightHatKernel_pos_of_box_certificate (kernelBoxCertificate_of_check h) hu ht hJ he

end E8Leech.Taylor
