import E8Leech.CKMRVKernelMixedPhiBounds
import E8Leech.CKMRVKernelPhiNegativeBounds
import E8Leech.CKMRVKernelRectangleBounds

/-! Exact proof reuse when the independent orders coincide. -/

namespace E8Leech.Taylor

theorem checkKernelMixedPhiPositiveRectangle_eq_uniform (C : KernelRectangleCandidate) :
    checkKernelMixedPhiPositiveRectangle C.N C = checkKernelPhiRectangle C := by
  have hc : kernelMixedPhiPositiveBoxChecks C.box C.M C.N C.N C.D C.n C.K ↔
      kernelSLPPhiBoxChecks C.box C.M C.N C.D C.n C.K := by
    unfold kernelMixedPhiPositiveBoxChecks kernelSLPPhiBoxChecks
    rw [kernelMixedProgramModels_eq_uniform]
  simp only [checkKernelMixedPhiPositiveRectangle, checkKernelPhiRectangle,
    checkKernelMixedPhiPositiveBox, checkKernelSLPPhiBox]
  rw [Bool.decide_congr hc]

theorem checkKernelMixedPhiNegativeRectangle_eq_uniform (C : KernelRectangleCandidate) :
    checkKernelMixedPhiNegativeRectangle C.N C = checkKernelPhiNegativeRectangle C := by
  have hc : kernelMixedPhiNegativeBoxChecks C.box C.M C.N C.N C.D C.n C.K ↔
      kernelSLPPhiNegativeBoxChecks C.box C.M C.N C.D C.n C.K := by
    unfold kernelMixedPhiNegativeBoxChecks kernelSLPPhiNegativeBoxChecks
    rw [kernelMixedProgramModels_eq_uniform]
  simp only [checkKernelMixedPhiNegativeRectangle, checkKernelPhiNegativeRectangle,
    checkKernelMixedPhiNegativeBox, checkKernelSLPPhiNegativeBox]
  rw [Bool.decide_congr hc]

theorem checkKernelMixedPhiNegativeLowerBound_eq_uniform (C : KernelRectangleCandidate) (ε : ℚ) :
    checkKernelMixedPhiNegativeLowerBound C.N C ε = checkKernelPhiNegativeLowerBound C ε := by
  have hc : kernelMixedPhiNegativeLowerBoundChecks C.N C ε ↔
      kernelPhiNegativeLowerBoundChecks C ε := by
    unfold kernelMixedPhiNegativeLowerBoundChecks kernelPhiNegativeLowerBoundChecks
    rw [kernelMixedProgramModels_eq_uniform]
  simp only [checkKernelMixedPhiNegativeLowerBound, checkKernelPhiNegativeLowerBound,
    checkKernelMixedPhiNegativeRectangle_eq_uniform]
  rw [Bool.decide_congr hc]

/-- Reuse an existing quantitative certificate after verifying its inverse-curve branch. -/
theorem checkKernelMixedPhiPositiveLowerBound_eq_true_of_full
    {C : KernelRectangleCandidate} {ε : ℚ}
    (hc : checkKernelRectangleLowerBound C ε = true) (hp : 1 < C.box.ulo * C.box.tlo) :
    checkKernelMixedPhiPositiveLowerBound C.N C ε = true := by
  obtain ⟨hr, he⟩ := Bool.and_eq_true_iff.mp hc
  apply Bool.and_eq_true_iff.mpr
  constructor
  · rw [checkKernelMixedPhiPositiveRectangle_eq_uniform]
    exact checkKernelPhiRectangle_eq_true_of_full hr hp
  · apply decide_eq_true
    have h : kernelRectangleLowerBoundChecks C ε := of_decide_eq_true he
    simpa only [kernelMixedPhiPositiveLowerBoundChecks, kernelRectangleLowerBoundChecks,
      kernelMixedProgramModels_eq_uniform] using h

end E8Leech.Taylor
