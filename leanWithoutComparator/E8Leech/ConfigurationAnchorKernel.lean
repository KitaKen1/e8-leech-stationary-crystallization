import E8Leech.FiniteKernelNormalization
import E8Leech.TernaryWindowCounts

/-! # Measurable probability averaging over anchors in the first occupied window

Only a natural-number window is selected. No configuration point is selected.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory Metric
open scoped ENNReal Classical

variable {d : ℕ}

def AnchorWindowCondition (c : Configuration (Ambient d)) (n : ℕ) : Prop :=
  boundedCountingKernel d (n : ℝ) c univ ≠ 0 ∨
    (n = 0 ∧ ∀ m : ℕ, boundedCountingKernel d (m : ℝ) c univ = 0)

theorem anchorWindowCondition_exists (c : Configuration (Ambient d)) :
    ∃ n : ℕ, AnchorWindowCondition c n := by
  by_cases h : ∃ n : ℕ, boundedCountingKernel d (n : ℝ) c univ ≠ 0
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · push Not at h
    exact ⟨0, Or.inr ⟨rfl, h⟩⟩

theorem measurableSet_anchorWindowCondition (n : ℕ) :
    MeasurableSet {c : Configuration (Ambient d) | AnchorWindowCondition c n} := by
  have hm (m : ℕ) : MeasurableSet {c : Configuration (Ambient d) |
      boundedCountingKernel d (m : ℝ) c univ = 0} :=
    measurableSet_eq_fun ((boundedCountingKernel d (m : ℝ)).measurable_coe MeasurableSet.univ)
      measurable_const
  have hall : MeasurableSet {c : Configuration (Ambient d) |
      ∀ m : ℕ, boundedCountingKernel d (m : ℝ) c univ = 0} := by
    have he : {c : Configuration (Ambient d) | ∀ m : ℕ,
        boundedCountingKernel d (m : ℝ) c univ = 0} =
        ⋂ m : ℕ, {c | boundedCountingKernel d (m : ℝ) c univ = 0} := by
      ext c
      simp only [mem_ofPred_eq, mem_iInter]
    rw [he]
    exact MeasurableSet.iInter hm
  exact (hm n).compl.union ((MeasurableSet.const (n = 0)).inter hall)

def anchorWindowRadius (c : Configuration (Ambient d)) : ℕ := Nat.find (anchorWindowCondition_exists c)

theorem measurable_anchorWindowRadius : Measurable (anchorWindowRadius (d := d)) :=
  measurable_find anchorWindowCondition_exists measurableSet_anchorWindowCondition

def occupiedWindowKernel (d : ℕ) : Kernel (Configuration (Ambient d)) (Ambient d) where
  toFun c := boundedCountingKernel d (anchorWindowRadius c : ℝ) c
  measurable' := Measurable.find (fun n => (boundedCountingKernel d (n : ℝ)).measurable)
    measurableSet_anchorWindowCondition anchorWindowCondition_exists

theorem occupiedWindowKernel_finite (c : Configuration (Ambient d)) :
    IsFiniteMeasure (occupiedWindowKernel d c) := boundedCountingKernel_finite _ c

theorem boundedCountingKernel_univ_eq_card (n : ℕ) (c : Configuration (Ambient d)) :
    boundedCountingKernel d (n : ℝ) c univ = (ternaryWindowPoints n c).card := by
  calc
    _ = ∫⁻ _ : Ambient d, (1 : ℝ≥0∞) ∂boundedCountingKernel d (n : ℝ) c := (lintegral_one).symm
    _ = ∑ _ ∈ ternaryWindowPoints n c, (1 : ℝ≥0∞) := boundedCountingKernel_lintegral_eq_sum n c _
    _ = _ := by simp

theorem exists_occupied_window_of_nonempty (c : Configuration (Ambient d))
    (hc : c.support.Nonempty) : ∃ n : ℕ, boundedCountingKernel d (n : ℝ) c univ ≠ 0 := by
  obtain ⟨x, hx⟩ := hc
  obtain ⟨n, hn⟩ := exists_nat_ge (dist x 0)
  refine ⟨n, ?_⟩
  rw [boundedCountingKernel_univ_eq_card]
  exact_mod_cast Finset.card_ne_zero.mpr ⟨x, (mem_ternaryWindowPoints n c x).mpr ⟨hx, hn⟩⟩

theorem occupiedWindowKernel_univ_ne_zero (c : Configuration (Ambient d))
    (hc : c.support.Nonempty) : occupiedWindowKernel d c univ ≠ 0 := by
  have h := Nat.find_spec (anchorWindowCondition_exists c)
  rcases h with h | ⟨_, h⟩
  · exact h
  · obtain ⟨n, hn⟩ := exists_occupied_window_of_nonempty c hc
    exact (hn (h n)).elim

def configurationAnchorKernel (d : ℕ) : Kernel (Configuration (Ambient d)) (Ambient d) :=
  normalizedFiniteKernel (occupiedWindowKernel d) 0

instance : IsMarkovKernel (configurationAnchorKernel d) :=
  normalizedFiniteKernel_isMarkov (occupiedWindowKernel d) occupiedWindowKernel_finite 0

theorem occupiedWindowKernel_compl_window_eq_zero (c : Configuration (Ambient d)) :
    occupiedWindowKernel d c (ternaryWindowPoints (anchorWindowRadius c) c : Set _)ᶜ = 0 := by
  change boundedCountingKernel d (anchorWindowRadius c : ℝ) c _ = 0
  rw [boundedCountingKernel, Kernel.restrict_apply,
    countingKernel_restrict_window _ measurableSet_closedBall isBounded_closedBall,
    Measure.restrict_apply (Finset.measurableSet _).compl]
  simp only [ternaryWindowPoints, compl_inter_self, measure_empty]

theorem configurationAnchorKernel_ae_mem_window (c : Configuration (Ambient d))
    (hc : c.support.Nonempty) :
    ∀ᵐ x ∂configurationAnchorKernel d c, x ∈ ternaryWindowPoints (anchorWindowRadius c) c := by
  rw [ae_iff]
  exact normalizedFiniteKernel_null_of_ne (occupiedWindowKernel d) 0 c
    (occupiedWindowKernel_univ_ne_zero c hc) (occupiedWindowKernel_compl_window_eq_zero c)

theorem configurationAnchorKernel_ae_mem_support (c : Configuration (Ambient d))
    (hc : c.support.Nonempty) : ∀ᵐ x ∂configurationAnchorKernel d c, x ∈ c.support :=
  (configurationAnchorKernel_ae_mem_window c hc).mono fun x hx =>
    ((mem_ternaryWindowPoints _ c x).mp hx).1

end E8Leech
