import E8Leech.CKMRVSLPRound
import E8Leech.CKMRVKernelMixedOrders

/-! Rounded shared models still enclose the exact two CKMRV numerator expressions. -/

namespace E8Leech.Taylor

def kernelRoundedMixedProgramModels (B : Box) (M : ℚ) (N NE D n K p : ℕ) : List DD :=
  SLP.runDDRounded B D p (mixedGeneratorDD B M N NE)
    (logarithmDD B M N D n K) kernelProgram []

theorem approx_kernelRoundedMixedProgram_phi {B : Box} {M : ℚ} (hB : NomeOK B M)
    (hM : 4 * M < 1) (N NE D n K p : ℕ) (hL : LogarithmOK B M N D K)
    {S : Env → Prop} :
    ((kernelRoundedMixedProgramModels B M N NE D n K p).getD kernelPhiRegister SLP.dd0).Approx B S
      (KExpr.evalA kernelPhiExpr) (KExpr.evalB kernelPhiExpr) :=
  SLP.approx_checkedRounded hB.valid D p (approx_mixedGeneratorDD hB hM N NE)
    (approx_logarithmDD hB hM N D n K hL) kernelProgram kernelPhiRegister
    kernelPhiExpr kernelProgram_phi_checked

theorem approx_kernelRoundedMixedProgram_nu {B : Box} {M : ℚ} (hB : NomeOK B M)
    (hM : 4 * M < 1) (N NE D n K p : ℕ) (hL : LogarithmOK B M N D K)
    {S : Env → Prop} :
    ((kernelRoundedMixedProgramModels B M N NE D n K p).getD kernelNuRegister SLP.dd0).Approx B S
      (KExpr.evalA kernelNuExpr) (KExpr.evalB kernelNuExpr) :=
  SLP.approx_checkedRounded hB.valid D p (approx_mixedGeneratorDD hB hM N NE)
    (approx_logarithmDD hB hM N D n K hL) kernelProgram kernelNuRegister
    kernelNuExpr kernelProgram_nu_checked

end E8Leech.Taylor
