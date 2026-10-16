import E8Leech.CKMRVKernelCover
import E8Leech.CKMRVKernelPhiCertificate

/-!
# Numerator-only real rectangles

These endpoint checks allow the diagonal to cross a leaf. Off the diagonal the exact
denominator theorem gives strict positivity. On the diagonal the existing Lean kernel
is zero because its definition uses totalized division; this is not a continuation value.
-/

namespace E8Leech.Taylor

open scoped Real

def kernelPhiRectangleEndpointChecks (C : KernelRectangleCandidate) : Prop :=
  let B := C.box
  B.ulo ≤ B.uhi ∧ B.tlo ≤ B.thi ∧ 0 < C.expTerms ∧
    (3141593 / 1000000 : ℚ) * B.uhi ≤ 2 ^ C.expScale ∧
    (3141593 / 1000000 : ℚ) * B.thi ≤ 2 ^ C.expScale ∧
    B.alo ≤ expNegLo ((3141593 / 1000000) * B.uhi) C.expScale C.expTerms ∧
    expNegHi ((3141592 / 1000000) * B.ulo) C.expScale C.expTerms ≤ B.ahi ∧
    B.blo ≤ expNegLo ((3141593 / 1000000) * B.thi) C.expScale C.expTerms ∧
    expNegHi ((3141592 / 1000000) * B.tlo) C.expScale C.expTerms ≤ B.bhi ∧
    B.plo ≤ 3141592 / 1000000 ∧ 3141593 / 1000000 ≤ B.phi ∧
    B.llo ≤ 69 / 100 ∧ 7 / 10 ≤ B.lhi

instance (C : KernelRectangleCandidate) : Decidable (kernelPhiRectangleEndpointChecks C) := by
  unfold kernelPhiRectangleEndpointChecks
  infer_instance

theorem kernelPhiRectangleEndpointChecks_of_full {C : KernelRectangleCandidate}
    (he : kernelRectangleEndpointChecks C) : kernelPhiRectangleEndpointChecks C := by
  obtain ⟨hu, ht, hn, _, _, he⟩ := he
  exact ⟨hu, ht, hn, he⟩

theorem kernelPhiRectangleEndpointChecks.mem_axis {C : KernelRectangleCandidate}
    (he : kernelPhiRectangleEndpointChecks C) (hb : C.box.Valid) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) : C.box.Mem (axisEnv u t) := by
  obtain ⟨_, _, hn, hku, hkt, hal, hah, hbl, hbh, hpl, hph, hll, hlh⟩ := he
  have ha := exp_neg_pi_mul_bounds hb.2.2.1.le hu.1 hu.2 hku hn
  have hbb := exp_neg_pi_mul_bounds hb.2.2.2.1.le ht.1 ht.2 hkt hn
  have hpl' : (3141592 / 1000000 : ℝ) ≤ π := by
    have h := Real.pi_gt_d6
    norm_num at h ⊢
    exact h.le
  have hph' : π ≤ (3141593 / 1000000 : ℝ) := by
    have h := Real.pi_lt_d6
    norm_num at h ⊢
    exact h.le
  have hplr := (Rat.cast_le (K := ℝ)).mpr hpl
  have hphr := (Rat.cast_le (K := ℝ)).mpr hph
  have hllr := (Rat.cast_le (K := ℝ)).mpr hll
  have hlhr := (Rat.cast_le (K := ℝ)).mpr hlh
  push_cast at hplr hphr hllr hlhr
  exact ⟨(Rat.cast_le.mpr hal).trans ha.1, ha.2.trans (Rat.cast_le.mpr hah),
    (Rat.cast_le.mpr hbl).trans hbb.1, hbb.2.trans (Rat.cast_le.mpr hbh),
    hu.1, hu.2, ht.1, ht.2, hplr.trans hpl', hph'.trans hphr,
    hllr.trans kernel_candidate_log_two.1, kernel_candidate_log_two.2.trans hlhr⟩

def checkKernelPhiRectangle (C : KernelRectangleCandidate) : Bool :=
  decide (kernelPhiRectangleEndpointChecks C) && decide (1 < C.box.ulo * C.box.tlo) &&
    checkKernelSLPPhiBox C.box C.M C.N C.D C.n C.K

theorem checkKernelPhiRectangle_eq_true_of_full {C : KernelRectangleCandidate}
    (hc : checkKernelRectangle C = true) (hp : 1 < C.box.ulo * C.box.tlo) :
    checkKernelPhiRectangle C = true := by
  obtain ⟨he, hk⟩ := Bool.and_eq_true_iff.mp hc
  have he' := kernelPhiRectangleEndpointChecks_of_full (of_decide_eq_true he)
  simp only [checkKernelPhiRectangle, decide_eq_true he', decide_eq_true hp,
    Bool.true_and, checkKernelSLPPhiBox_eq_true_of_full hk]

theorem kernelPhiRectangle_mem_axis {C : KernelRectangleCandidate}
    (hc : checkKernelPhiRectangle C = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) : C.box.Mem (axisEnv u t) := by
  obtain ⟨he, hk⟩ := Bool.and_eq_true_iff.mp hc
  exact (of_decide_eq_true (Bool.and_eq_true_iff.mp he).1 :
    kernelPhiRectangleEndpointChecks C).mem_axis
      (kernelSLPPhiCertificate_of_check hk).nome.valid hu ht

theorem ckmrvEightHatKernel_pos_of_checked_phi_rectangle {C : KernelRectangleCandidate}
    (hc : checkKernelPhiRectangle C = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) (hut : u ≠ t) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  obtain ⟨he, hk⟩ := Bool.and_eq_true_iff.mp hc
  have hb := (kernelSLPPhiCertificate_of_check hk).nome.valid
  have hu0 : 0 < u := lt_of_lt_of_le (by exact_mod_cast hb.2.2.1) hu.1
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast hb.2.2.2.1) ht.1
  have hp : 1 < C.box.ulo * C.box.tlo :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp he).2
  have hpr : (1 : ℝ) < (C.box.ulo : ℝ) * C.box.tlo := by exact_mod_cast hp
  have hm := mul_le_mul hu.1 ht.1 (by exact_mod_cast hb.2.2.2.1.le) hu0.le
  exact ckmrvEightHatKernel_pos_of_checked_phi_box hk hu0 ht0 hut
    (hpr.trans_le hm) (kernelPhiRectangle_mem_axis hc hu ht)

theorem ckmrvEightHatKernel_nonneg_of_checked_phi_rectangle {C : KernelRectangleCandidate}
    (hc : checkKernelPhiRectangle C = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) :
    0 ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  by_cases h : u = t
  · subst t
    rw [ckmrvEightHatKernel_eq_zero_of_kleinJ_eq rfl]
    simp
  · exact (ckmrvEightHatKernel_pos_of_checked_phi_rectangle hc hu ht h).le

def checkKernelPhiRectangleCover : KernelRectangleCover → AxisTile → Bool :=
  checkKernelRectangleCoverWith checkKernelPhiRectangle

theorem ckmrvEightHatKernel_pos_of_checked_phi_cover
    (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelPhiRectangleCover cover R = true)
    {u t : ℝ} (hm : R.Mem u t) (hut : u ≠ t) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have h := kernelRectangleCoverWith_sound checkKernelPhiRectangle
    (fun u t => u ≠ t → 0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re)
    (fun _ h _ _ hu ht hut => ckmrvEightHatKernel_pos_of_checked_phi_rectangle h hu ht hut)
    cover R hc hm
  exact h hut

theorem ckmrvEightHatKernel_nonneg_of_checked_phi_cover
    (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelPhiRectangleCover cover R = true) {u t : ℝ} (hm : R.Mem u t) :
    0 ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  exact kernelRectangleCoverWith_sound _ _
    (fun _ h _ _ hu ht => ckmrvEightHatKernel_nonneg_of_checked_phi_rectangle h hu ht)
    cover R hc hm

end E8Leech.Taylor
