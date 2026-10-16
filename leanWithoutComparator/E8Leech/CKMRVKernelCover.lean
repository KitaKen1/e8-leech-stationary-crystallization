import E8Leech.CKMRVKernelRectangleBounds

/-! A common closed-cover checker for positivity, numerator checks and quantitative bounds. -/

namespace E8Leech.Taylor

def checkKernelRectangleCoverWith (checkLeaf : KernelRectangleCandidate → Bool) :
    KernelRectangleCover → AxisTile → Bool
  | .leaf C, R => decide (R.CoveredBy C) && checkLeaf C
  | .splitU q l r, R => decide (R.ulo ≤ q ∧ q ≤ R.uhi) &&
      checkKernelRectangleCoverWith checkLeaf l ⟨R.ulo, q, R.tlo, R.thi⟩ &&
      checkKernelRectangleCoverWith checkLeaf r ⟨q, R.uhi, R.tlo, R.thi⟩
  | .splitT q l r, R => decide (R.tlo ≤ q ∧ q ≤ R.thi) &&
      checkKernelRectangleCoverWith checkLeaf l ⟨R.ulo, R.uhi, R.tlo, q⟩ &&
      checkKernelRectangleCoverWith checkLeaf r ⟨R.ulo, R.uhi, q, R.thi⟩

theorem AxisTile.CoveredBy.mem {R : AxisTile} {C : KernelRectangleCandidate}
    (hc : R.CoveredBy C) {u t : ℝ} (hm : R.Mem u t) :
    ((C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi) ∧
      ((C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) := by
  obtain ⟨_, _, h1, h2, h3, h4⟩ := hc
  exact ⟨⟨(Rat.cast_le.mpr h1).trans hm.1, hm.2.1.trans (Rat.cast_le.mpr h2)⟩,
    ⟨(Rat.cast_le.mpr h3).trans hm.2.2.1, hm.2.2.2.trans (Rat.cast_le.mpr h4)⟩⟩

/-- A successful recursive certificate proves the leaf property at every target point. -/
theorem kernelRectangleCoverWith_sound (checkLeaf : KernelRectangleCandidate → Bool)
    (P : ℝ → ℝ → Prop)
    (hLeaf : ∀ C, checkLeaf C = true → ∀ {u t : ℝ},
      ((C.box.ulo : ℝ) ≤ u ∧ u ≤ C.box.uhi) →
      ((C.box.tlo : ℝ) ≤ t ∧ t ≤ C.box.thi) → P u t)
    (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelRectangleCoverWith checkLeaf cover R = true)
    {u t : ℝ} (hm : R.Mem u t) : P u t := by
  induction cover generalizing R with
  | leaf C =>
    obtain ⟨hcov, hC⟩ := Bool.and_eq_true_iff.mp hc
    have hmem := (of_decide_eq_true hcov : R.CoveredBy C).mem hm
    exact hLeaf C hC hmem.1 hmem.2
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

def checkKernelRectangleLowerBoundCover (ε : ℚ) : KernelRectangleCover → AxisTile → Bool :=
  checkKernelRectangleCoverWith (fun C => checkKernelRectangleLowerBound C ε)

/-- Every leaf must certify the same numerical lower bound, including at split boundaries. -/
theorem ckmrvEightHatKernel_lower_bound_of_checked_cover {ε : ℚ}
    (cover : KernelRectangleCover) (R : AxisTile)
    (hc : checkKernelRectangleLowerBoundCover ε cover R = true)
    {u t : ℝ} (hm : R.Mem u t) :
    (ε : ℝ) ≤ (ckmrvEightHatKernel (imagPt u) (imagPt t)).re := by
  exact kernelRectangleCoverWith_sound _ _
    (fun _ h _ _ hu ht => ckmrvEightHatKernel_lower_bound_of_checked_rectangle h hu ht)
    cover R hc hm

end E8Leech.Taylor
