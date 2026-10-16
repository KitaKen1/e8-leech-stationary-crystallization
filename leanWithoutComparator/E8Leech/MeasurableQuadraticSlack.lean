import E8Leech.GaussianMixtureAtomCrystallization
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# A measurable positive-mass set with a common quadratic slack

Quantize the positive coefficient and test the inequality on countably many
clamped rational radii. Spatial continuity extends these tests to every radius.
Thus separately measurable families with a positive coefficient at each good
parameter supply a common coefficient on a measurable set of positive mass.
No atom, density, or parameter continuity is required.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

def slackRadiusClamp (r u : ℝ) : ℝ := max 0 (min r u)

theorem continuous_slackRadiusClamp (r : ℝ) : Continuous (slackRadiusClamp r) := by
  unfold slackRadiusClamp
  fun_prop

theorem slackRadiusClamp_mem {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    slackRadiusClamp r u ∈ Icc 0 r :=
  ⟨le_max_left _ _, max_le hr (min_le_left _ _)⟩

theorem slackRadiusClamp_of_mem {r u : ℝ} (hu : u ∈ Icc 0 r) :
    slackRadiusClamp r u = u := by
  simp only [slackRadiusClamp, min_eq_right hu.2, max_eq_right hu.1]

def quadraticSlackLevelSet (φ : ℝ × ℝ → ℝ) (r : ℝ) (n : ℕ) : Set ℝ :=
  {α | ∀ q : ℚ, (1 / ((n : ℝ) + 1)) * (r - slackRadiusClamp r q) ^ 2 ≤
    φ (α, slackRadiusClamp r q)}

theorem measurableSet_quadraticSlackLevelSet (φ : ℝ × ℝ → ℝ) (r : ℝ)
    (hm : ∀ u : ℝ, Measurable (fun α => φ (α, u))) (n : ℕ) :
    MeasurableSet (quadraticSlackLevelSet φ r n) := by
  simp only [quadraticSlackLevelSet, ofPred_forall]
  exact MeasurableSet.iInter (fun q => measurableSet_le measurable_const (hm _))

theorem quadraticSlackLevelSet_lower {φ : ℝ × ℝ → ℝ} {r α : ℝ} {n : ℕ}
    (hc : Continuous (fun u => φ (α, u))) (hα : α ∈ quadraticSlackLevelSet φ r n)
    {u : ℝ} (hu : u ∈ Icc 0 r) :
    (1 / ((n : ℝ) + 1)) * (r - u) ^ 2 ≤ φ (α, u) := by
  have hclosed : IsClosed {v : ℝ |
      (1 / ((n : ℝ) + 1)) * (r - slackRadiusClamp r v) ^ 2 ≤
        φ (α, slackRadiusClamp r v)} :=
    isClosed_le (continuous_const.mul
      ((continuous_const.sub (continuous_slackRadiusClamp r)).pow 2))
      (hc.comp (continuous_slackRadiusClamp r))
  have hsub : range (fun q : ℚ => (q : ℝ)) ⊆ {v : ℝ |
      (1 / ((n : ℝ) + 1)) * (r - slackRadiusClamp r v) ^ 2 ≤
        φ (α, slackRadiusClamp r v)} := by
    rintro _ ⟨q, rfl⟩
    exact hα q
  have h := hclosed.closure_subset_iff.mpr hsub
  rw [(Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))).closure_range] at h
  have hpoint := h (mem_univ u)
  change (1 / ((n : ℝ) + 1)) * (r - slackRadiusClamp r u) ^ 2 ≤
    φ (α, slackRadiusClamp r u) at hpoint
  simpa only [slackRadiusClamp_of_mem hu] using hpoint

theorem exists_positive_mass_uniform_quadratic_slack
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S) (hmass : ν S ≠ 0)
    (φ : ℝ × ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hm : ∀ u : ℝ, Measurable (fun α => φ (α, u)))
    (hc : ∀ α ∈ S, Continuous (fun u => φ (α, u)))
    (hq : ∀ α ∈ S, ∃ k : ℝ, 0 < k ∧ ∀ u ∈ Icc 0 r,
      k * (r - u) ^ 2 ≤ φ (α, u)) :
    ∃ k : ℝ, 0 < k ∧ ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ S ∧ ν A ≠ 0 ∧
      ∀ α ∈ A, ∀ u ∈ Icc 0 r, k * (r - u) ^ 2 ≤ φ (α, u) := by
  let A : ℕ → Set ℝ := fun n => S ∩ quadraticSlackLevelSet φ r n
  have hcover : S ⊆ ⋃ n, A n := by
    intro α hα
    obtain ⟨k, hk, hlower⟩ := hq α hα
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hk
    refine mem_iUnion.mpr ⟨n, hα, ?_⟩
    intro q
    exact (mul_le_mul_of_nonneg_right hn.le (sq_nonneg _)).trans
      (hlower _ (slackRadiusClamp_mem hr _))
  have hunion : ν (⋃ n, A n) ≠ 0 := by
    intro hz
    exact hmass (le_zero_iff.mp ((measure_mono hcover).trans (le_of_eq hz)))
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion
  refine ⟨1 / ((n : ℝ) + 1), by positivity, A n,
    hS.inter (measurableSet_quadraticSlackLevelSet φ r hm n), inter_subset_left, hn.ne', ?_⟩
  intro α hα u hu
  exact quadraticSlackLevelSet_lower (hc α hα.1) hα.2 hu

/-- Clip the coefficient to keep it finite even if the selected set has infinite mass. -/
theorem potentialUnitCostInput_of_mixture_quadratic_on_set {d : ℕ}
    (ν : Measure ℝ) (Λ : Set (Ambient d))
    (P : Ambient d → Ambient d → ℝ≥0∞) (V : ℝ → Ambient d → Ambient d → ℝ≥0∞)
    (A : Set ℝ) (hA : MeasurableSet A) (hmass : ν A ≠ 0) {k r : ℝ}
    (hk : 0 < k) (hr : 0 < r)
    (hquad : ∀ α ∈ A, ∀ x y, dist x y ≤ r →
      ENNReal.ofReal (k * (r - dist x y) ^ 2) ≤ V α x y)
    (hgap : ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 →
      latticePotentialEnergy Λ P + potentialEnergy (potentialMixture ν V) μ ≤ potentialEnergy P μ) :
    ∃ C : ℝ, 0 < C ∧ PotentialUnitCostInput Λ P r C (1 / 8) := by
  let c : ℝ≥0∞ := min 1 (ENNReal.ofReal k * ν A)
  have hc0 : c ≠ 0 := ne_of_gt (lt_min (by norm_num)
    (pos_iff_ne_zero.mpr (mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hk) hmass)))
  have hctop : c ≠ ∞ := ne_of_lt ((min_le_left _ _).trans_lt (by simp : (1 : ℝ≥0∞) < ∞))
  let K := c.toReal
  have hK : 0 < K := ENNReal.toReal_pos hc0 hctop
  have hkle : ENNReal.ofReal K ≤ ENNReal.ofReal k * ν A := by
    rw [show ENNReal.ofReal K = c from ENNReal.ofReal_toReal hctop]
    exact min_le_right _ _
  refine ⟨(K * r ^ 2)⁻¹, by positivity,
    potentialUnitCostInput_of_full_quadratic_slack Λ P (potentialMixture ν V) hK hr ?_ ?_⟩
  · intro μ hprob hμ hρ _
    exact hgap μ hprob hμ hρ
  · intro x y hxy
    have hl := potentialMixture_lower_on_parameter_set ν V hA
      (ENNReal.ofReal (k * (r - dist x y) ^ 2)) x y (fun α hα => hquad α hα x y hxy)
    rw [ENNReal.ofReal_mul hk.le] at hl
    rw [ENNReal.ofReal_mul hK.le]
    apply le_trans (mul_le_mul' hkle (le_refl _)) ?_
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hl

end E8Leech
