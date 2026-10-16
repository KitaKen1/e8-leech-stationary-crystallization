import E8Leech.CKMRVKernelSLP
import E8Leech.KernelBoxEndpoints

/-!
# Certified real rectangles and recursive covers

Rational endpoint checks connect a shared-program certificate to the whole real rectangle.
A cover tree checks every leaf and every split; no unverified grid or coverage assumption is used.
These positive divided-difference certificates do not yet cover the whole regular locus.
-/

namespace E8Leech.Taylor

open scoped Real

structure KernelRectangleCandidate where
  box : Box
  M : ℚ
  N : ℕ
  D : ℕ
  n : ℕ
  K : ℕ
  expScale : ℕ
  expTerms : ℕ

def kernelRectangleEndpointChecks (C : KernelRectangleCandidate) : Prop :=
  let B := C.box
  B.ulo ≤ B.uhi ∧ B.tlo ≤ B.thi ∧ 0 < C.expTerms ∧
    (B.thi < B.ulo ∨ B.uhi < B.tlo) ∧
    (1 < B.ulo * B.tlo ∨ B.uhi * B.thi < 1) ∧
    (3141593 / 1000000 : ℚ) * B.uhi ≤ 2 ^ C.expScale ∧
    (3141593 / 1000000 : ℚ) * B.thi ≤ 2 ^ C.expScale ∧
    B.alo ≤ expNegLo ((3141593 / 1000000) * B.uhi) C.expScale C.expTerms ∧
    expNegHi ((3141592 / 1000000) * B.ulo) C.expScale C.expTerms ≤ B.ahi ∧
    B.blo ≤ expNegLo ((3141593 / 1000000) * B.thi) C.expScale C.expTerms ∧
    expNegHi ((3141592 / 1000000) * B.tlo) C.expScale C.expTerms ≤ B.bhi ∧
    B.plo ≤ 3141592 / 1000000 ∧ 3141593 / 1000000 ≤ B.phi ∧
    B.llo ≤ 69 / 100 ∧ 7 / 10 ≤ B.lhi

instance (C : KernelRectangleCandidate) : Decidable (kernelRectangleEndpointChecks C) := by
  unfold kernelRectangleEndpointChecks
  infer_instance

def checkKernelRectangle (C : KernelRectangleCandidate) : Bool :=
  decide (kernelRectangleEndpointChecks C) &&
    checkKernelSLPBox C.box C.M C.N C.D C.n C.K

theorem kernelRectangle_mem_axis {C : KernelRectangleCandidate}
    (hc : checkKernelRectangle C = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) : C.box.Mem (axisEnv u t) := by
  obtain ⟨he, hk⟩ := Bool.and_eq_true_iff.mp hc
  have hC := kernelSLPBoxCertificate_of_check hk
  have hb := hC.nome.valid
  obtain ⟨_, _, hn, _, _, hku, hkt, hal, hah, hbl, hbh, hpl, hph, hll, hlh⟩ :=
    (of_decide_eq_true he : kernelRectangleEndpointChecks C)
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

theorem kernelRectangle_regular {C : KernelRectangleCandidate}
    (hc : checkKernelRectangle C = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) :
    kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t) := by
  obtain ⟨he, hk⟩ := Bool.and_eq_true_iff.mp hc
  have hb := (kernelSLPBoxCertificate_of_check hk).nome.valid
  have hu0 : 0 < u := lt_of_lt_of_le (by exact_mod_cast hb.2.2.1) hu.1
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast hb.2.2.2.1) ht.1
  have hhiU : (0 : ℝ) ≤ C.box.uhi := hu0.le.trans hu.2
  obtain ⟨_, _, _, hd, hp, _⟩ := (of_decide_eq_true he : kernelRectangleEndpointChecks C)
  have hne : t ≠ u := by
    intro h
    rcases hd with hd | hd
    · have hdr : (C.box.thi : ℝ) < C.box.ulo := by exact_mod_cast hd
      linarith [hu.1, ht.2]
    · have hdr : (C.box.uhi : ℝ) < C.box.tlo := by exact_mod_cast hd
      linarith [hu.2, ht.1]
  have hinv : t ≠ u⁻¹ := by
    intro h
    have hut : u * t = 1 := by rw [h, mul_inv_cancel₀ hu0.ne']
    rcases hp with hp | hp
    · have hpr : (1 : ℝ) < (C.box.ulo : ℝ) * C.box.tlo := by exact_mod_cast hp
      have hm := mul_le_mul hu.1 ht.1 (by exact_mod_cast hb.2.2.2.1.le) hu0.le
      linarith
    · have hpr : (C.box.uhi : ℝ) * C.box.thi < 1 := by exact_mod_cast hp
      have hm := mul_le_mul hu.2 ht.2 ht0.le hhiU
      linarith
  exact kleinModularJ_imagPt_ne hu0 ht0 hne hinv

theorem ckmrvEightHatKernel_pos_of_checked_rectangle {C : KernelRectangleCandidate}
    (hc : checkKernelRectangle C = true) {u t : ℝ}
    (hu : (C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi)
    (ht : (C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  have hk := (Bool.and_eq_true_iff.mp hc).2
  have hb := (kernelSLPBoxCertificate_of_check hk).nome.valid
  exact ckmrvEightHatKernel_pos_of_checked_slp_box hk
    (lt_of_lt_of_le (by exact_mod_cast hb.2.2.1) hu.1)
    (lt_of_lt_of_le (by exact_mod_cast hb.2.2.2.1) ht.1)
    (kernelRectangle_regular hc hu ht) (kernelRectangle_mem_axis hc hu ht)

structure AxisTile where
  ulo : ℚ
  uhi : ℚ
  tlo : ℚ
  thi : ℚ

def AxisTile.Mem (R : AxisTile) (u t : ℝ) : Prop :=
  (R.ulo : ℝ) ≤ u ∧ u ≤ R.uhi ∧ (R.tlo : ℝ) ≤ t ∧ t ≤ R.thi

def AxisTile.CoveredBy (R : AxisTile) (C : KernelRectangleCandidate) : Prop :=
  R.ulo ≤ R.uhi ∧ R.tlo ≤ R.thi ∧ C.box.ulo ≤ R.ulo ∧ R.uhi ≤ C.box.uhi ∧
    C.box.tlo ≤ R.tlo ∧ R.thi ≤ C.box.thi

instance (R : AxisTile) (C : KernelRectangleCandidate) : Decidable (R.CoveredBy C) := by
  unfold AxisTile.CoveredBy
  infer_instance

inductive KernelRectangleCover where
  | leaf (candidate : KernelRectangleCandidate)
  | splitU (cut : ℚ) (left right : KernelRectangleCover)
  | splitT (cut : ℚ) (lower upper : KernelRectangleCover)

def checkKernelRectangleCover : KernelRectangleCover → AxisTile → Bool
  | .leaf C, R => decide (R.CoveredBy C) && checkKernelRectangle C
  | .splitU q l r, R => decide (R.ulo ≤ q ∧ q ≤ R.uhi) &&
      checkKernelRectangleCover l ⟨R.ulo, q, R.tlo, R.thi⟩ &&
      checkKernelRectangleCover r ⟨q, R.uhi, R.tlo, R.thi⟩
  | .splitT q l r, R => decide (R.tlo ≤ q ∧ q ≤ R.thi) &&
      checkKernelRectangleCover l ⟨R.ulo, R.uhi, R.tlo, q⟩ &&
      checkKernelRectangleCover r ⟨R.ulo, R.uhi, q, R.thi⟩

/-- Every point of the target rectangle is covered, including the split boundaries. -/
theorem ckmrvEightHatKernel_pos_of_checked_cover (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelRectangleCover cover R = true) {u t : ℝ} (hm : R.Mem u t) :
    0 < (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  induction cover generalizing R with
  | leaf C =>
    obtain ⟨hcov, hC⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨_, _, h1, h2, h3, h4⟩ := (of_decide_eq_true hcov : R.CoveredBy C)
    exact ckmrvEightHatKernel_pos_of_checked_rectangle hC
      ⟨(Rat.cast_le.mpr h1).trans hm.1, hm.2.1.trans (Rat.cast_le.mpr h2)⟩
      ⟨(Rat.cast_le.mpr h3).trans hm.2.2.1, hm.2.2.2.trans (Rat.cast_le.mpr h4)⟩
  | splitU q l r ihl ihr =>
    obtain ⟨hleft, hright⟩ := Bool.and_eq_true_iff.mp hc
    have hleft := (Bool.and_eq_true_iff.mp hleft).2
    by_cases hq : u ≤ (q : ℝ)
    · exact ihl _ hleft ⟨hm.1, hq, hm.2.2.1, hm.2.2.2⟩
    · exact ihr _ hright ⟨(not_le.mp hq).le, hm.2.1, hm.2.2.1, hm.2.2.2⟩
  | splitT q l r ihl ihr =>
    obtain ⟨hlower, hupper⟩ := Bool.and_eq_true_iff.mp hc
    have hlower := (Bool.and_eq_true_iff.mp hlower).2
    by_cases hq : t ≤ (q : ℝ)
    · exact ihl _ hlower ⟨hm.1, hm.2.1, hm.2.2.1, hq⟩
    · exact ihr _ hupper ⟨hm.1, hm.2.1, (not_le.mp hq).le, hm.2.2.2⟩

end E8Leech.Taylor
