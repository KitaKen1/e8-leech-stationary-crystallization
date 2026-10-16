import E8Leech.TernaryWindowCounts
import E8Leech.JointTranslation

/-!
# A measurable translation-equivariant ternary reconstruction

Take `c - c + c` when it is locally finite, and the empty configuration otherwise.
Both the local-finiteness test and every output count are measurable. This gives
a total configuration map, without a measurable enumeration of the input points.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Metric
open scoped ENNReal Classical

theorem ternaryWindowImage_mono {d : ℕ} (c : Configuration (Ambient d)) :
    Monotone (fun n => (ternaryWindowImage n c : Set (Ambient d))) := by
  intro n m hnm x hx
  obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := (mem_ternaryWindowImage n c x).mp hx
  have hb : ∀ y, y ∈ ternaryWindowPoints n c → y ∈ ternaryWindowPoints m c := by
    intro y hy
    obtain ⟨hy, hd⟩ := (mem_ternaryWindowPoints n c y).mp hy
    exact (mem_ternaryWindowPoints m c y).mpr ⟨hy, hd.trans (by exact_mod_cast hnm)⟩
  exact (mem_ternaryWindowImage m c _).mpr ⟨u, hb u hu, v, hb v hv, w, hb w hw, rfl⟩

theorem iUnion_ternaryWindowImage {d : ℕ} (c : Configuration (Ambient d)) :
    (⋃ n : ℕ, (ternaryWindowImage n c : Set (Ambient d))) = ternarySupport c := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨u, hu, v, hv, w, hw, he⟩ := (mem_ternaryWindowImage n c x).mp hn
    exact ⟨u, (mem_ternaryWindowPoints n c u).mp hu |>.1,
      v, (mem_ternaryWindowPoints n c v).mp hv |>.1,
      w, (mem_ternaryWindowPoints n c w).mp hw |>.1, he⟩
  · rintro ⟨u, hu, v, hv, w, hw, rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (max (dist u 0) (max (dist v 0) (dist w 0)))
    apply mem_iUnion.mpr
    refine ⟨n, (mem_ternaryWindowImage n c _).mpr ⟨u, ?_, v, ?_, w, ?_, rfl⟩⟩
    · exact (mem_ternaryWindowPoints n c u).mpr ⟨hu, (le_max_left _ _).trans hn.le⟩
    · exact (mem_ternaryWindowPoints n c v).mpr
        ⟨hv, ((le_max_left _ _).trans (le_max_right _ _)).trans hn.le⟩
    · exact (mem_ternaryWindowPoints n c w).mpr
        ⟨hw, ((le_max_right _ _).trans (le_max_right _ _)).trans hn.le⟩

def ternaryCount {d : ℕ} (c : Configuration (Ambient d)) (W : Set (Ambient d)) : ℝ≥0∞ :=
  Measure.count (ternarySupport c ∩ W)

theorem ternaryCount_eq_iSup {d : ℕ} (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    ternaryCount c W = ⨆ n : ℕ, Measure.count ((ternaryWindowImage n c : Set (Ambient d)) ∩ W) := by
  rw [ternaryCount, ← iUnion_ternaryWindowImage, iUnion_inter]
  exact (show Monotone (fun n => (ternaryWindowImage n c : Set (Ambient d)) ∩ W) from
    fun _ _ h => inter_subset_inter_left W (ternaryWindowImage_mono c h)).measure_iUnion

theorem measurable_ternaryCount {d : ℕ} {W : Set (Ambient d)} (hW : MeasurableSet W) :
    Measurable (fun c : Configuration (Ambient d) => ternaryCount c W) := by
  simp_rw [ternaryCount_eq_iSup]
  exact Measurable.iSup fun n => measurable_ternaryWindow_count n hW

def TernaryLocallyFinite {d : ℕ} (c : Configuration (Ambient d)) : Prop :=
  ∀ K : Set (Ambient d), IsCompact K → (ternarySupport c ∩ K).Finite

theorem ternaryLocallyFinite_iff_counts {d : ℕ} (c : Configuration (Ambient d)) :
    TernaryLocallyFinite c ↔ ∀ n : ℕ, ternaryCount c (closedBall 0 (n : ℝ)) < ∞ := by
  constructor
  · intro h n
    exact Measure.count_apply_lt_top.mpr (h _ (isCompact_closedBall _ _))
  · intro h K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Ambient d)
    obtain ⟨n, hn⟩ := exists_nat_ge r
    exact (Measure.count_apply_lt_top.mp (h n)).subset
      (fun _ hx => ⟨hx.1, closedBall_subset_closedBall hn (hr hx.2)⟩)

theorem measurableSet_ternaryLocallyFinite {d : ℕ} :
    MeasurableSet {c : Configuration (Ambient d) | TernaryLocallyFinite c} := by
  have he : {c : Configuration (Ambient d) | TernaryLocallyFinite c} =
      ⋂ n : ℕ, {c | ternaryCount c (closedBall 0 (n : ℝ)) < ∞} := by
    ext c
    simp only [mem_iInter, mem_ofPred_eq, ternaryLocallyFinite_iff_counts]
  rw [he]
  exact MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_ternaryCount measurableSet_closedBall) measurable_const

def ternaryReconstruction {d : ℕ} (c : Configuration (Ambient d)) : Configuration (Ambient d) :=
  if h : TernaryLocallyFinite c then ⟨ternarySupport c, h⟩ else
    ⟨∅, fun K _ => by simp⟩

theorem ternaryReconstruction_support {d : ℕ} (c : Configuration (Ambient d)) :
    (ternaryReconstruction c).support = if TernaryLocallyFinite c then ternarySupport c else ∅ := by
  by_cases h : TernaryLocallyFinite c <;> simp [ternaryReconstruction, h]

theorem measurable_ternaryReconstruction {d : ℕ} :
    Measurable (ternaryReconstruction : Configuration (Ambient d) → Configuration (Ambient d)) := by
  apply Configuration.measurable_of_counts
  intro W hW
  have he : (fun c : Configuration (Ambient d) => (ternaryReconstruction c).count W) =
      fun c => if TernaryLocallyFinite c then ternaryCount c W else 0 := by
    funext c
    by_cases h : TernaryLocallyFinite c <;>
      simp [Configuration.count, ternaryReconstruction_support, ternaryCount, h]
  rw [he]
  exact Measurable.ite measurableSet_ternaryLocallyFinite (measurable_ternaryCount hW) measurable_const

theorem ternaryLocallyFinite_translate_of {d : ℕ} (a : Ambient d)
    (c : Configuration (Ambient d)) (hc : TernaryLocallyFinite c) :
    TernaryLocallyFinite (translate a c) := by
  let k : Configuration (Ambient d) := ⟨ternarySupport c, hc⟩
  intro K hK
  rw [ternarySupport_translate]
  exact (translate a k).finite_on_compacts K hK

theorem ternaryLocallyFinite_translate_iff {d : ℕ} (a : Ambient d) (c : Configuration (Ambient d)) :
    TernaryLocallyFinite (translate a c) ↔ TernaryLocallyFinite c := by
  refine ⟨fun h => ?_, ternaryLocallyFinite_translate_of a c⟩
  have hh := ternaryLocallyFinite_translate_of (-a) (translate a c) h
  simpa only [translate_negative_cancel] using hh

theorem ternaryReconstruction_translate {d : ℕ} (a : Ambient d) (c : Configuration (Ambient d)) :
    ternaryReconstruction (translate a c) = translate a (ternaryReconstruction c) := by
  apply Configuration.ext
  change (ternaryReconstruction (translate a c)).support =
    (fun x => a + x) '' (ternaryReconstruction c).support
  rw [ternaryReconstruction_support, ternaryReconstruction_support,
    ternaryLocallyFinite_translate_iff]
  by_cases h : TernaryLocallyFinite c <;> simp [h, ternarySupport_translate]

end E8Leech
