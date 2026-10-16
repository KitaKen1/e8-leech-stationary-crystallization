import E8Leech.GramFrameOrientation
import E8Leech.FinitePiKernel
import E8Leech.JointTranslation
import Mathlib.Probability.Kernel.Composition.MapComap

/-! # A measurable finite kernel of orientations from an anchored configuration

The kernel uses finite counting windows and exact Gram frames. No point or
orientation is selected measurably. Each compatible orientation has mass one.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory Metric
open scoped ENNReal InnerProductSpace Classical

variable {d : ℕ}

theorem orientation_clm_injective : Function.Injective
    (fun Q : LatticeOrientation d => Q.isometry.toContinuousLinearMap) := by
  intro Q R h
  have he : Q.isometry = R.isometry := LinearIsometryEquiv.ext fun x =>
    congrArg (fun f : Ambient d →L[ℝ] Ambient d => f x) h
  cases Q
  cases R
  exact congrArg LatticeOrientation.mk he

instance : MeasurableSingletonClass (LatticeOrientation d) where
  measurableSet_singleton Q := by
    have hm : Measurable (fun Q : LatticeOrientation d => Q.isometry.toContinuousLinearMap) :=
      (continuous_induced_dom : Continuous (fun Q : LatticeOrientation d =>
        Q.isometry.toContinuousLinearMap)).measurable
    have he : {Q} = (fun R : LatticeOrientation d => R.isometry.toContinuousLinearMap) ⁻¹'
        {Q.isometry.toContinuousLinearMap} := by
      ext R
      simp only [mem_singleton_iff, mem_preimage]
      exact orientation_clm_injective.eq_iff.symm
    rw [he]
    exact hm (measurableSet_singleton _)

def relativeWindowPoints (r : ℝ) (c : Configuration (Ambient d)) (x : Ambient d) :
    Finset (Ambient d) :=
  windowPointFinset (translate (-x) c) (closedBall 0 r) isBounded_closedBall

@[simp] theorem mem_relativeWindowPoints (r : ℝ) (c : Configuration (Ambient d))
    (x v : Ambient d) :
    v ∈ relativeWindowPoints r c x ↔ x + v ∈ c.support ∧ ‖v‖ ≤ r := by
  simp only [relativeWindowPoints, mem_windowPointFinset, mem_closedBall, dist_zero_right]
  change (v ∈ (fun y => -x + y) '' c.support ∧ ‖v‖ ≤ r) ↔ _
  have he : v ∈ (fun y => -x + y) '' c.support ↔ x + v ∈ c.support := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hv
      exact ⟨x + v, hv, by abel⟩
  rw [he]

def relativePointKernel (d : ℕ) (r : ℝ) :
    Kernel (Configuration (Ambient d) × Ambient d) (Ambient d) :=
  (boundedCountingKernel d r).comap (fun p => translate (-p.2) p.1)
    measurable_translate_negative_center

theorem relativePointKernel_eq_count (r : ℝ) (c : Configuration (Ambient d)) (x : Ambient d) :
    relativePointKernel d r (c, x) =
      Measure.count.restrict (relativeWindowPoints r c x : Set (Ambient d)) := by
  rw [relativePointKernel, Kernel.comap_apply, boundedCountingKernel, Kernel.restrict_apply,
    countingKernel_restrict_window _ measurableSet_closedBall isBounded_closedBall]
  rfl

theorem relativePointKernel_finite (r : ℝ) (p : Configuration (Ambient d) × Ambient d) :
    IsFiniteMeasure (relativePointKernel d r p) := boundedCountingKernel_finite r _

theorem relativePointKernel_singleton (r : ℝ) (c : Configuration (Ambient d)) (x v : Ambient d) :
    relativePointKernel d r (c, x) {v} =
      if v ∈ relativeWindowPoints r c x then 1 else 0 := by
  rw [relativePointKernel_eq_count, Measure.restrict_apply (measurableSet_singleton v)]
  by_cases hv : v ∈ relativeWindowPoints r c x
  · simp [hv, Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hv)]
  · have he : {v} ∩ (relativeWindowPoints r c x : Set (Ambient d)) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_singleton_iff, Finset.mem_coe, mem_empty_iff_false, iff_false]
      rintro ⟨rfl, hy⟩
      exact hv hy
    simp [hv, he]

theorem relativePointKernel_compl_eq_zero (r : ℝ) (c : Configuration (Ambient d)) (x : Ambient d) :
    relativePointKernel d r (c, x) (relativeWindowPoints r c x : Set (Ambient d))ᶜ = 0 := by
  rw [relativePointKernel_eq_count, Measure.restrict_apply (Finset.measurableSet _).compl]
  simp

variable (b : Module.Basis (Fin d) ℝ (Ambient d))

def relativeFrameKernel : Kernel (Configuration (Ambient d) × Ambient d) (Fin d → Ambient d) :=
  finitePiKernel (fun i => relativePointKernel d ‖b i‖)
    (fun i p => relativePointKernel_finite ‖b i‖ p)

theorem relativeFrameKernel_finite (p : Configuration (Ambient d) × Ambient d) :
    IsFiniteMeasure (relativeFrameKernel b p) := finitePiKernel_finite _ _ p

def orientationCandidatePoints (c : Configuration (Ambient d)) (x : Ambient d) :
    Finset (LatticeOrientation d) :=
  ((Fintype.piFinset (fun i => relativeWindowPoints ‖b i‖ c x)).filter (FrameGram b)).image
    (orientationOfFrame b)

def BasisOrientationCandidate (c : Configuration (Ambient d)) (x : Ambient d)
    (Q : LatticeOrientation d) : Prop := ∀ i, x + Q.isometry (b i) ∈ c.support

@[simp] theorem mem_orientationCandidatePoints (c : Configuration (Ambient d)) (x : Ambient d)
    (Q : LatticeOrientation d) :
    Q ∈ orientationCandidatePoints b c x ↔ BasisOrientationCandidate b c x Q := by
  constructor
  · intro hQ
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨hv, hg⟩ := Finset.mem_filter.mp hv
    intro i
    rw [orientationOfFrame_basis b v hg]
    exact (mem_relativeWindowPoints _ _ _ _).mp ((Fintype.mem_piFinset.mp hv) i) |>.1
  · intro hQ
    refine Finset.mem_image.mpr ⟨fun i => Q.isometry (b i), ?_, orientationOfFrame_eq b Q⟩
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr fun i => ?_, frameGram_of_orientation b Q⟩
    exact (mem_relativeWindowPoints _ _ _ _).mpr ⟨hQ i, by simp⟩

def anchoredOrientationKernel :
    Kernel (Configuration (Ambient d) × Ambient d) (LatticeOrientation d) :=
  ((relativeFrameKernel b).restrict (measurableSet_frameGram b)).map (orientationOfFrame b)

theorem anchoredOrientationKernel_finite (p : Configuration (Ambient d) × Ambient d) :
    IsFiniteMeasure (anchoredOrientationKernel b p) := by
  let := relativeFrameKernel_finite b p
  rw [anchoredOrientationKernel, Kernel.map_apply _ (measurable_orientationOfFrame b),
    Kernel.restrict_apply]
  infer_instance

theorem frame_orientation_fiber (Q : LatticeOrientation d) :
    (orientationOfFrame b ⁻¹' {Q}) ∩ {v | FrameGram b v} =
      {fun i => Q.isometry (b i)} := by
  ext v
  constructor
  · rintro ⟨hv, hg⟩
    have hQ : orientationOfFrame b v = Q := hv
    apply Set.mem_singleton_iff.mpr
    funext i
    rw [← hQ, orientationOfFrame_basis b v hg]
  · rintro rfl
    exact ⟨orientationOfFrame_eq b Q, frameGram_of_orientation b Q⟩

theorem anchoredOrientationKernel_singleton (c : Configuration (Ambient d)) (x : Ambient d)
    (Q : LatticeOrientation d) :
    anchoredOrientationKernel b (c, x) {Q} =
      if BasisOrientationCandidate b c x Q then 1 else 0 := by
  rw [anchoredOrientationKernel, Kernel.map_apply' _ (measurable_orientationOfFrame b) _
    (measurableSet_singleton Q), Kernel.restrict_apply, Measure.restrict_apply
      ((measurable_orientationOfFrame b) (measurableSet_singleton Q)), frame_orientation_fiber]
  change finitePiKernel _ _ _ _ = _
  rw [finitePiKernel_singleton]
  simp_rw [relativePointKernel_singleton, mem_relativeWindowPoints, LinearIsometryEquiv.norm_map,
    le_refl, and_true]
  by_cases hQ : BasisOrientationCandidate b c x Q
  · rw [if_pos hQ]
    exact Finset.prod_eq_one fun i _ => if_pos (hQ i)
  · rw [if_neg hQ]
    obtain ⟨i, hi⟩ := not_forall.mp hQ
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem anchoredOrientationKernel_compl_eq_zero (c : Configuration (Ambient d)) (x : Ambient d) :
    anchoredOrientationKernel b (c, x) (orientationCandidatePoints b c x : Set _)ᶜ = 0 := by
  have hz := finitePiKernel_compl_pi_eq_zero
    (fun i => relativePointKernel d ‖b i‖) (fun i p => relativePointKernel_finite ‖b i‖ p)
    (c, x) (fun i => (relativeWindowPoints ‖b i‖ c x : Set (Ambient d)))
    (fun i => Finset.measurableSet _) (fun i => relativePointKernel_compl_eq_zero ‖b i‖ c x)
  rw [anchoredOrientationKernel, Kernel.map_apply' _ (measurable_orientationOfFrame b) _
    (Finset.measurableSet _).compl, Kernel.restrict_apply,
    Measure.restrict_apply ((measurable_orientationOfFrame b) (Finset.measurableSet _).compl)]
  apply measure_mono_null _ hz
  rintro v ⟨hv, hg⟩ hbox
  apply hv
  apply Finset.mem_image.mpr
  refine ⟨v, Finset.mem_filter.mpr ⟨?_, hg⟩, rfl⟩
  exact Fintype.mem_piFinset.mpr fun i => hbox i (mem_univ i)

theorem anchoredOrientationKernel_eq_sum (c : Configuration (Ambient d)) (x : Ambient d) :
    anchoredOrientationKernel b (c, x) =
      ∑ Q ∈ orientationCandidatePoints b c x, Measure.dirac Q := by
  have hae : ∀ᵐ Q ∂anchoredOrientationKernel b (c, x), Q ∈ orientationCandidatePoints b c x := by
    rw [ae_iff]
    exact anchoredOrientationKernel_compl_eq_zero b c x
  rw [Measure.ae_mem_finset_iff.mp hae]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [anchoredOrientationKernel_singleton, if_pos ((mem_orientationCandidatePoints b c x Q).mp hQ),
    one_smul]

end E8Leech
