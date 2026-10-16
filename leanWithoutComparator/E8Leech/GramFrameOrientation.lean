import E8Leech.GeneralOrientationClassification
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Measurable orthogonal orientations reconstructed from exact Gram frames -/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Classical

variable {d : ℕ} (b : Module.Basis (Fin d) ℝ (Ambient d))

def frameOperator (v : Fin d → Ambient d) : Ambient d →L[ℝ] Ambient d :=
  ∑ i, ((b.coord i).toContinuousLinearMap).smulRight (v i)

@[simp] theorem frameOperator_basis (v : Fin d → Ambient d) (i : Fin d) :
    frameOperator b v (b i) = v i := by
  simp [frameOperator, Module.Basis.coord_apply, Finsupp.single_apply]

theorem continuous_frameOperator : Continuous (frameOperator b) := by
  apply continuous_finsetSum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ (Ambient d) (Ambient d)
    (b.coord i).toContinuousLinearMap).continuous.comp (continuous_apply i)

def FrameGram (v : Fin d → Ambient d) : Prop :=
  ∀ i j, ⟪v i, v j⟫_ℝ = ⟪b i, b j⟫_ℝ

theorem measurableSet_frameGram : MeasurableSet {v | FrameGram b v} := by
  simp only [FrameGram, ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    measurableSet_eq_fun ((measurable_pi_apply i).inner (measurable_pi_apply j)) measurable_const

theorem frameOperator_inner (v : Fin d → Ambient d) (hv : FrameGram b v) (x y : Ambient d) :
    ⟪frameOperator b v x, frameOperator b v y⟫_ℝ = ⟪x, y⟫_ℝ := by
  have hv' (i j : Fin d) : ⟪v i, v j⟫_ℝ = ⟪b i, b j⟫_ℝ := hv i j
  calc
    _ = ⟪frameOperator b v (∑ i, b.repr x i • b i),
        frameOperator b v (∑ j, b.repr y j • b j)⟫_ℝ := by rw [b.sum_repr, b.sum_repr]
    _ = ⟪∑ i, b.repr x i • v i, ∑ j, b.repr y j • v j⟫_ℝ := by
      simp only [map_sum, map_smul, frameOperator_basis]
    _ = ⟪∑ i, b.repr x i • b i, ∑ j, b.repr y j • b j⟫_ℝ := by
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      simp_rw [hv']
    _ = _ := by rw [b.sum_repr, b.sum_repr]

def frameIsometry (v : Fin d → Ambient d) (hv : FrameGram b v) : Ambient d ≃ₗᵢ[ℝ] Ambient d :=
  let L := (frameOperator b v).toLinearMap.isometryOfInner (frameOperator_inner b v hv)
  LinearIsometryEquiv.ofSurjective L (LinearMap.surjective_of_injective (f := L.toLinearMap) L.injective)

@[simp] theorem frameIsometry_apply (v : Fin d → Ambient d) (hv : FrameGram b v) (x : Ambient d) :
    frameIsometry b v hv x = frameOperator b v x := rfl

@[simp] theorem frameIsometry_basis (v : Fin d → Ambient d) (hv : FrameGram b v) (i : Fin d) :
    frameIsometry b v hv (b i) = v i := frameOperator_basis b v i

theorem frameGram_of_orientation (Q : LatticeOrientation d) : FrameGram b (fun i => Q.isometry (b i)) :=
  fun i j => Q.isometry.inner_map_map (b i) (b j)

def orientationOfFrame (v : Fin d → Ambient d) : LatticeOrientation d :=
  if h : FrameGram b v then ⟨frameIsometry b v h⟩ else ⟨LinearIsometryEquiv.refl ℝ (Ambient d)⟩

theorem orientationOfFrame_basis (v : Fin d → Ambient d) (hv : FrameGram b v) (i : Fin d) :
    (orientationOfFrame b v).isometry (b i) = v i := by
  simp only [orientationOfFrame, dif_pos hv, frameIsometry_basis]

theorem orientationOfFrame_eq (Q : LatticeOrientation d) :
    orientationOfFrame b (fun i => Q.isometry (b i)) = Q := by
  have hL : (orientationOfFrame b (fun i => Q.isometry (b i))).isometry = Q.isometry := by
    have hm : (orientationOfFrame b (fun i => Q.isometry (b i))).isometry.toLinearMap =
        Q.isometry.toLinearMap := b.ext fun i =>
      orientationOfFrame_basis b _ (frameGram_of_orientation b Q) i
    exact LinearIsometryEquiv.ext fun x => congrArg (fun f : Ambient d →ₗ[ℝ] Ambient d => f x) hm
  cases Q
  exact congrArg LatticeOrientation.mk hL


theorem measurable_orientation_of_clm {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → LatticeOrientation d)
    (hf : Measurable (fun ω => (f ω).isometry.toContinuousLinearMap)) : Measurable f := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap f (borel (LatticeOrientation d)) ≤ _
  rw [borel_comap, MeasurableSpace.comap_comp]
  exact hf.comap_le

theorem measurable_orientationOfFrame : Measurable (orientationOfFrame b) := by
  apply measurable_orientation_of_clm
  have he : (fun v => (orientationOfFrame b v).isometry.toContinuousLinearMap) =
      fun v => if FrameGram b v then frameOperator b v else ContinuousLinearMap.id ℝ (Ambient d) := by
    funext v
    by_cases hv : FrameGram b v
    · simp only [orientationOfFrame, dif_pos hv, if_pos hv]
      ext x
      rfl
    · simp only [orientationOfFrame, dif_neg hv, if_neg hv]
      ext x
      rfl
  rw [he]
  exact Measurable.ite (measurableSet_frameGram b) (continuous_frameOperator b).measurable measurable_const

end E8Leech
