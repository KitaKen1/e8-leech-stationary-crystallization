import E8Leech.LeechCrystallization
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Joint measurability of the explicit CKMRV kernels

The totalized rational formulas are measurable, including their values on the
equal-j locus. This is a measurability statement, not a continuous extension at
that locus. Parameter integrals are consequently measurable even before their
integrability and sign estimates are supplied.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped Manifold BigOperators

@[fun_prop] theorem measurable_imagPt : Measurable imagPt := by
  have hc : ContinuousOn imagPt (Ioi 0) := UpperHalfPlane.continuousOn_ofComplex_I_mul
  have h : Measurable ((Ioi (0 : ℝ)).piecewise imagPt (fun _ => imagPt 0)) :=
    hc.measurable_piecewise continuous_const.continuousOn
      measurableSet_Ioi
  have heq : (Ioi (0 : ℝ)).piecewise imagPt (fun _ => imagPt 0) = imagPt := by
    funext t
    by_cases ht : 0 < t
    · simp [Set.piecewise, ht]
    · simp only [Set.piecewise, mem_Ioi, if_neg ht, imagPt]
      exact UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos
        (by simp) (by simpa using le_of_not_gt ht)
  rwa [heq] at h

@[fun_prop] theorem measurable_ckmrvModularFactor (i : Fin 9) :
    Measurable (fun τ => ckmrvModularFactor τ i) :=
  (mdifferentiable_ckmrvModularFactor i).continuous.measurable

@[fun_prop] theorem measurable_ckmrvPhiBasis (i : Fin 3) :
    Measurable (fun τ => ckmrvPhiBasis τ i) :=
  (mdifferentiable_ckmrvPhiBasis i).continuous.measurable

@[fun_prop] theorem measurable_ckmrvTildePhiBasis (i : Fin 3) :
    Measurable (fun τ => ckmrvTildePhiBasis τ i) :=
  (mdifferentiable_ckmrvTildePhiBasis i).continuous.measurable

@[fun_prop] theorem measurable_ckmrvPsiBasis (i : Fin 3) :
    Measurable (fun τ => ckmrvPsiBasis τ i) :=
  (mdifferentiable_ckmrvPsiBasis i).continuous.measurable

@[fun_prop] theorem measurable_ckmrvTildePsiBasis (i : Fin 3) :
    Measurable (fun τ => ckmrvTildePsiBasis τ i) := by
  fin_cases i
  · exact mdifferentiable_ckmrvL.continuous.measurable
  · exact mdifferentiable_thetaW.continuous.measurable
  · have hu := mdifferentiable_thetaU.continuous.measurable
    have hv := mdifferentiable_thetaV.continuous.measurable
    change Measurable (fun τ => thetaU τ ^ 2 - thetaV τ ^ 2)
    fun_prop

@[fun_prop] theorem measurable_kleinModularJ : Measurable kleinModularJ :=
  continuous_kleinModularJ.measurable

@[fun_prop] theorem measurable_modularDiscriminant : Measurable ModularForm.discriminant :=
  mdifferentiable_modularDiscriminant.continuous.measurable

@[fun_prop] theorem measurable_ckmrvEightPlusCoefficientMatrix (i j : Fin 3) :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvEightPlusCoefficientMatrix p.1 p.2 i j) := by
  simp only [ckmrvEightPlusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul,
    ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply]
  fin_cases i <;> fin_cases j <;> simp [ckmrvEightPlusCore] <;> fun_prop

@[fun_prop] theorem measurable_ckmrvEightMinusCoefficientMatrix (i j : Fin 3) :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvEightMinusCoefficientMatrix p.1 p.2 i j) := by
  simp only [ckmrvEightMinusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul,
    ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply]
  fin_cases i <;> fin_cases j <;> simp [ckmrvEightMinusCore] <;> fun_prop

@[fun_prop] theorem measurable_ckmrvLeechPlusCoefficientMatrix (i j : Fin 3) :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvLeechPlusCoefficientMatrix p.1 p.2 i j) := by
  simp only [ckmrvLeechPlusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul,
    ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply]
  fin_cases i <;> fin_cases j <;> simp [ckmrvLeechPlusCore] <;> fun_prop

@[fun_prop] theorem measurable_ckmrvLeechMinusCoefficientMatrix (i j : Fin 3) :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane =>
      ckmrvLeechMinusCoefficientMatrix p.1 p.2 i j) := by
  simp only [ckmrvLeechMinusCoefficientMatrix, Matrix.smul_apply, smul_eq_mul,
    ckmrvModularCoreMatrix, ckmrvDiagonalCore_apply]
  fin_cases i <;> fin_cases j <;> simp [ckmrvLeechMinusCore] <;> fun_prop

@[fun_prop] theorem measurable_ckmrvEightPlusKernel :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvEightPlusKernel p.1 p.2) := by
  simp only [ckmrvEightPlusKernel, ckmrvCoreContraction, Fin.sum_univ_three]
  fun_prop

@[fun_prop] theorem measurable_ckmrvEightMinusKernel :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvEightMinusKernel p.1 p.2) := by
  simp only [ckmrvEightMinusKernel, ckmrvCoreContraction, Fin.sum_univ_three]
  fun_prop

@[fun_prop] theorem measurable_ckmrvLeechPlusKernel :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvLeechPlusKernel p.1 p.2) := by
  simp only [ckmrvLeechPlusKernel, ckmrvCoreContraction, Fin.sum_univ_three]
  fun_prop

@[fun_prop] theorem measurable_ckmrvLeechMinusKernel :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvLeechMinusKernel p.1 p.2) := by
  simp only [ckmrvLeechMinusKernel, ckmrvCoreContraction, Fin.sum_univ_three]
  fun_prop

@[fun_prop] theorem measurable_ckmrvEightKernel :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvEightKernel p.1 p.2) := by
  unfold ckmrvEightKernel
  fun_prop

@[fun_prop] theorem measurable_ckmrvLeechKernel :
    Measurable (fun p : UpperHalfPlane × UpperHalfPlane => ckmrvLeechKernel p.1 p.2) := by
  unfold ckmrvLeechKernel
  fun_prop

end E8Leech
