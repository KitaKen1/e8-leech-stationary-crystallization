import E8Leech.CKMRVSLPTrace
import E8Leech.CKMRVKernelRoundedPhiBounds

/-! Transfer a completely checked register trace into the existing rectangle checkers.
The final sign and numerical margin are separate hypotheses, never native assumptions. -/

namespace E8Leech.Taylor

theorem kernelRoundedMixedProgramModels_eq_of_trace {B : Box} {M : ℚ} {N NE D n K p : ℕ}
    {ws : List DD}
    (ht : SLP.checkRoundedTrace B D p (mixedGeneratorDD B M N NE)
      (logarithmDD B M N D n K) kernelProgram ws [] = true) :
    ws = kernelRoundedMixedProgramModels B M N NE D n K p := by
  simpa only [List.nil_append, kernelRoundedMixedProgramModels] using SLP.checkRoundedTrace_eq_run ht

theorem checkKernelRoundedMixedPhiNegativeRectangle_of_trace {C : KernelRectangleCandidate}
    {NE p : ℕ} {ws : List DD}
    (hn : NomeOK C.box C.M) (hm : 4 * C.M < 1)
    (hl : LogarithmOK C.box C.M C.N C.D C.K)
    (he : kernelPhiRectangleEndpointChecks C) (hp : C.box.uhi * C.box.thi < 1)
    (ht : SLP.checkRoundedTrace C.box C.D p (mixedGeneratorDD C.box C.M C.N NE)
      (logarithmDD C.box C.M C.N C.D C.n C.K) kernelProgram ws [] = true)
    (hu : TM.upper C.box (ws.getD kernelPhiRegister SLP.dd0).D < 0) :
    checkKernelRoundedMixedPhiNegativeRectangle NE p C = true := by
  have hr := kernelRoundedMixedProgramModels_eq_of_trace ht
  have hc : kernelRoundedMixedPhiNegativeBoxChecks C.box C.M C.N NE C.D C.n C.K p := by
    refine ⟨hn.valid, hn.ahi_le, hn.bhi_le, hn.M_le, hm, ?_, ?_⟩
    · intro j
      exact ⟨hl.left j, hl.right j, hl.difference j⟩
    · rw [← hr]
      exact hu
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨decide_eq_true he, decide_eq_true hp⟩, decide_eq_true hc⟩

theorem checkKernelRoundedMixedPhiNegativeLowerBound_of_trace {C : KernelRectangleCandidate}
    {NE p : ℕ} {ws : List DD} {ε : ℚ}
    (hc : checkKernelRoundedMixedPhiNegativeRectangle NE p C = true)
    (ht : SLP.checkRoundedTrace C.box C.D p (mixedGeneratorDD C.box C.M C.N NE)
      (logarithmDD C.box C.M C.N C.D C.n C.K) kernelProgram ws [] = true)
    (he : 0 ≤ ε)
    (hb : TM.upper C.box (ws.getD kernelPhiRegister SLP.dd0).D ≤
      2 * ε * TM.lower C.box (ws.getD kernelNuRegister SLP.dd0).D) :
    checkKernelRoundedMixedPhiNegativeLowerBound NE p C ε = true := by
  have hr := kernelRoundedMixedProgramModels_eq_of_trace ht
  have hbound : kernelRoundedMixedPhiNegativeLowerBoundChecks NE p C ε := by
    unfold kernelRoundedMixedPhiNegativeLowerBoundChecks
    rw [← hr]
    exact ⟨he, hb⟩
  exact Bool.and_eq_true_iff.mpr ⟨hc, decide_eq_true hbound⟩

end E8Leech.Taylor
