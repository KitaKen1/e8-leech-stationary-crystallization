import E8Leech.CKMRVKernelSLP

/-!
# Different truncation orders for theta generators and E2

The theta series have sparse quadratic exponents, while E2 needs a geometric tail.
Each order is independently sound. The same checked shared program therefore permits
smaller theta orders without changing its source expression or the E2 precision.
-/

namespace E8Leech.Taylor

def mixedGeneratorDD (B : Box) (M : ℚ) (Nθ NE : ℕ) (i : Fin 5) : DD :=
  generatorDD B M (if i = 4 then NE else Nθ) i

theorem approx_mixedGeneratorDD {B : Box} {M : ℚ} (hB : NomeOK B M)
    (hM : 4 * M < 1) (Nθ NE : ℕ) {S : Env → Prop} (i : Fin 5) :
    (mixedGeneratorDD B M Nθ NE i).Approx B S
      (fun e => genFun i e.a) (fun e => genFun i e.b) :=
  approx_generatorDD hB hM (if i = 4 then NE else Nθ) i

def kernelMixedProgramModels (B : Box) (M : ℚ) (Nθ NE D n K : ℕ) : List DD :=
  SLP.runDD B D (mixedGeneratorDD B M Nθ NE)
    (logarithmDD B M Nθ D n K) kernelProgram []

theorem kernelMixedProgramModels_eq_uniform (B : Box) (M : ℚ) (N D n K : ℕ) :
    kernelMixedProgramModels B M N N D n K = kernelProgramModels B M N D n K := by
  have h : mixedGeneratorDD B M N N = generatorDD B M N := by
    funext i
    simp only [mixedGeneratorDD, ite_self]
  simp only [kernelMixedProgramModels, kernelProgramModels, h]

theorem approx_kernelMixedProgram_phi {B : Box} {M : ℚ} (hB : NomeOK B M)
    (hM : 4 * M < 1) (Nθ NE D n K : ℕ) (hL : LogarithmOK B M Nθ D K)
    {S : Env → Prop} :
    ((kernelMixedProgramModels B M Nθ NE D n K).getD kernelPhiRegister SLP.dd0).Approx B S
      (KExpr.evalA kernelPhiExpr) (KExpr.evalB kernelPhiExpr) :=
  SLP.approx_checked hB.valid D (approx_mixedGeneratorDD hB hM Nθ NE)
    (approx_logarithmDD hB hM Nθ D n K hL) kernelProgram kernelPhiRegister
    kernelPhiExpr kernelProgram_phi_checked

theorem approx_kernelMixedProgram_nu {B : Box} {M : ℚ} (hB : NomeOK B M)
    (hM : 4 * M < 1) (Nθ NE D n K : ℕ) (hL : LogarithmOK B M Nθ D K)
    {S : Env → Prop} :
    ((kernelMixedProgramModels B M Nθ NE D n K).getD kernelNuRegister SLP.dd0).Approx B S
      (KExpr.evalA kernelNuExpr) (KExpr.evalB kernelNuExpr) :=
  SLP.approx_checked hB.valid D (approx_mixedGeneratorDD hB hM Nθ NE)
    (approx_logarithmDD hB hM Nθ D n K hL) kernelProgram kernelNuRegister
    kernelNuExpr kernelProgram_nu_checked

end E8Leech.Taylor
