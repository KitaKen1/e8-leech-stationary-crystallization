import E8Leech.FiniteAtomicSupport
import E8Leech.FinitePairForms
import E8Leech.TernaryLatticeReconstruction

/-! # Measurable distinct counts in finite ternary images -/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory Metric
open scoped ENNReal Classical

def ternaryWindowPoints {d : ℕ} (n : ℕ) (c : Configuration (Ambient d)) : Finset (Ambient d) :=
  windowPointFinset c (closedBall 0 (n : ℝ)) (isBounded_closedBall)

@[simp] theorem mem_ternaryWindowPoints {d : ℕ} (n : ℕ)
    (c : Configuration (Ambient d)) (x : Ambient d) :
    x ∈ ternaryWindowPoints n c ↔ x ∈ c.support ∧ dist x 0 ≤ n := by
  simp [ternaryWindowPoints]

def ternaryWindowImage {d : ℕ} (n : ℕ) (c : Configuration (Ambient d)) : Finset (Ambient d) :=
  ((ternaryWindowPoints n c).product
    ((ternaryWindowPoints n c).product (ternaryWindowPoints n c))).image
      (fun p => p.1 - p.2.1 + p.2.2)

@[simp] theorem mem_ternaryWindowImage {d : ℕ} (n : ℕ)
    (c : Configuration (Ambient d)) (x : Ambient d) :
    x ∈ ternaryWindowImage n c ↔ ∃ u ∈ ternaryWindowPoints n c,
      ∃ v ∈ ternaryWindowPoints n c, ∃ w ∈ ternaryWindowPoints n c, u - v + w = x := by
  constructor
  · intro hx
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hx
    obtain ⟨hu, hvw⟩ := Finset.mem_product.mp hp
    obtain ⟨hv, hw⟩ := Finset.mem_product.mp hvw
    exact ⟨p.1, hu, p.2.1, hv, p.2.2, hw, he⟩
  · rintro ⟨u, hu, v, hv, w, hw, he⟩
    exact Finset.mem_image.mpr ⟨(u, (v, w)),
      Finset.mem_product.mpr ⟨hu, Finset.mem_product.mpr ⟨hv, hw⟩⟩, he⟩

theorem boundedCountingKernel_lintegral_eq_sum {d : ℕ} (n : ℕ)
    (c : Configuration (Ambient d)) (f : Ambient d → ℝ≥0∞) :
    (∫⁻ x, f x ∂boundedCountingKernel d (n : ℝ) c) = ∑ x ∈ ternaryWindowPoints n c, f x := by
  rw [boundedCountingKernel, Kernel.restrict_apply,
    countingKernel_restrict_window c measurableSet_closedBall isBounded_closedBall]
  simpa only [Measure.count_singleton, mul_one, ternaryWindowPoints] using
    (lintegral_finset (ternaryWindowPoints n c) f (μ := Measure.count))

theorem measurable_ternaryWindow_sum {d : ℕ} (n : ℕ) (F : Ambient d → Ambient d → Ambient d → ℝ≥0∞)
    (hF : Measurable (fun p : (Ambient d × Ambient d) × Ambient d => F p.1.1 p.1.2 p.2)) :
    Measurable (fun c : Configuration (Ambient d) => ∑ u ∈ ternaryWindowPoints n c,
      ∑ v ∈ ternaryWindowPoints n c, ∑ w ∈ ternaryWindowPoints n c, F u v w) := by
  let κ := boundedCountingKernel d (n : ℝ)
  have hk : ∀ c, IsFiniteMeasure (κ c) := boundedCountingKernel_finite (n : ℝ)
  have hi : Measurable (fun p : (Configuration (Ambient d) × Ambient d) × Ambient d =>
      ∫⁻ w, F p.1.2 p.2 w ∂κ p.1.1) :=
    measurable_lintegral_finite_fibers_param κ hk (fun p => p.1.1) measurable_fst.fst
      (hF.comp ((measurable_fst.fst.snd.prodMk measurable_fst.snd).prodMk measurable_snd))
  have hj : Measurable (fun p : Configuration (Ambient d) × Ambient d =>
      ∫⁻ v, ∫⁻ w, F p.2 v w ∂κ p.1 ∂κ p.1) :=
    measurable_lintegral_finite_fibers_param κ hk (fun p => p.1) measurable_fst hi
  have hm : Measurable (fun c : Configuration (Ambient d) =>
      ∫⁻ u, ∫⁻ v, ∫⁻ w, F u v w ∂κ c ∂κ c ∂κ c) :=
    measurable_lintegral_of_finite_fibers κ hk hj
  simpa only [κ, boundedCountingKernel_lintegral_eq_sum] using hm

def ternaryWindowKernel (d : ℕ) (n : ℕ) : Kernel (Configuration (Ambient d)) (Ambient d) where
  toFun c := ∑ u ∈ ternaryWindowPoints n c, ∑ v ∈ ternaryWindowPoints n c,
    ∑ w ∈ ternaryWindowPoints n c, Measure.dirac (u - v + w)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun W hW => ?_
    simp only [Measure.finsetSum_apply, Measure.dirac_apply' _ hW]
    exact measurable_ternaryWindow_sum n (fun u v w => if u - v + w ∈ W then 1 else 0)
      (Measurable.ite (hW.preimage ((measurable_fst.fst.sub measurable_fst.snd).add
        measurable_snd)) measurable_const measurable_const)

theorem ternaryWindowKernel_finite (d : ℕ) (n : ℕ) (c : Configuration (Ambient d)) :
    IsFiniteMeasure (ternaryWindowKernel d n c) := by
  change IsFiniteMeasure (∑ u ∈ ternaryWindowPoints n c, ∑ v ∈ ternaryWindowPoints n c,
    ∑ w ∈ ternaryWindowPoints n c, Measure.dirac (u - v + w))
  infer_instance

theorem ternaryWindowKernel_compl_image {d : ℕ} (n : ℕ) (c : Configuration (Ambient d)) :
    ternaryWindowKernel d n c (ternaryWindowImage n c : Set (Ambient d))ᶜ = 0 := by
  change (∑ u ∈ ternaryWindowPoints n c, ∑ v ∈ ternaryWindowPoints n c,
    ∑ w ∈ ternaryWindowPoints n c, Measure.dirac (u - v + w)) _ = 0
  simp only [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  apply Finset.sum_eq_zero
  intro w hw
  have hm : u - v + w ∈ ternaryWindowImage n c :=
    mem_ternaryWindowImage n c _ |>.mpr ⟨u, hu, v, hv, w, hw, rfl⟩
  simp [Measure.dirac_apply' _ (ternaryWindowImage n c).measurableSet.compl, hm]

theorem ternaryWindowKernel_atom_pos {d : ℕ} (n : ℕ) (c : Configuration (Ambient d))
    {x : Ambient d} (hx : x ∈ ternaryWindowImage n c) :
    ternaryWindowKernel d n c {x} ≠ 0 := by
  obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := (mem_ternaryWindowImage n c x).mp hx
  have hh : 1 ≤ ternaryWindowKernel d n c {u - v + w} := by
    change 1 ≤ (∑ u' ∈ ternaryWindowPoints n c, ∑ v' ∈ ternaryWindowPoints n c,
      ∑ w' ∈ ternaryWindowPoints n c, Measure.dirac (u' - v' + w')) {u - v + w}
    simp only [Measure.finsetSum_apply]
    calc
      1 = Measure.dirac (u - v + w) {u - v + w} := by simp
      _ ≤ ∑ w' ∈ ternaryWindowPoints n c, Measure.dirac (u - v + w') {u - v + w} :=
        Finset.single_le_sum (f := fun w' => Measure.dirac (u - v + w') {u - v + w})
          (fun _ _ => bot_le) hw
      _ ≤ ∑ v' ∈ ternaryWindowPoints n c, ∑ w' ∈ ternaryWindowPoints n c,
          Measure.dirac (u - v' + w') {u - v + w} :=
        Finset.single_le_sum (f := fun v' => ∑ w' ∈ ternaryWindowPoints n c,
          Measure.dirac (u - v' + w') {u - v + w}) (fun _ _ => bot_le) hv
      _ ≤ ∑ u' ∈ ternaryWindowPoints n c, ∑ v' ∈ ternaryWindowPoints n c,
          ∑ w' ∈ ternaryWindowPoints n c, Measure.dirac (u' - v' + w') {u - v + w} :=
        Finset.single_le_sum (f := fun u' => ∑ v' ∈ ternaryWindowPoints n c,
          ∑ w' ∈ ternaryWindowPoints n c, Measure.dirac (u' - v' + w') {u - v + w})
          (fun _ _ => bot_le) hu
  exact (zero_lt_one.trans_le hh).ne'

theorem measurable_ternaryWindow_count {d : ℕ} (n : ℕ) {W : Set (Ambient d)}
    (hW : MeasurableSet W) :
    Measurable (fun c : Configuration (Ambient d) =>
      Measure.count ((ternaryWindowImage n c : Set (Ambient d)) ∩ W)) :=
  measurable_count_finite_atomic_support (ternaryWindowKernel d n) (ternaryWindowKernel_finite d n)
    (isClosed_eq continuous_fst continuous_snd).measurableSet (ternaryWindowImage n)
    (ternaryWindowKernel_compl_image n) (fun c _ hx => ternaryWindowKernel_atom_pos n c hx) hW

end E8Leech
