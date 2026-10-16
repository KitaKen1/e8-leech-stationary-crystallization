import E8Leech.GaussianMixtureCrystallization

/-!
# Retaining a common positive cost at an exceptional Gaussian parameter

Approach the exceptional parameter from above. Finite lattice sums converge,
the process Gaussian energy is antitone, and a common slack potential remains
in the inequality. No Schwartz witness at the limit parameter is required.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem potentialEnergy_mono {d : ℕ} {P V : Ambient d → Ambient d → ℝ≥0∞}
    (h : ∀ x y, V x y ≤ P x y) (μ : Measure (Configuration (Ambient d))) :
    potentialEnergy V μ ≤ potentialEnergy P μ :=
  lintegral_mono (fun c => orderedWindowEnergy_mono_potential h c (unitWindow d))

theorem gaussian_gap_of_right_parameter_interval {d : ℕ}
    (Λ : Set (Ambient d)) (μ : Measure (Configuration (Ambient d)))
    (V : Ambient d → Ambient d → ℝ≥0∞) {β b : ℝ} (hβb : β < b)
    (hgap : ∀ α ∈ Ioc β b, latticePotentialEnergy Λ (gaussianPotential α) +
      potentialEnergy V μ ≤ potentialEnergy (gaussianPotential α) μ) :
    latticePotentialEnergy Λ (gaussianPotential β) + potentialEnergy V μ ≤
      potentialEnergy (gaussianPotential β) μ := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hseq : Tendsto (fun n : ℕ => β + (b - β) * ((n : ℝ) + 1)⁻¹) atTop (𝓝 β) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnat))
  rw [latticePotentialEnergy, ENNReal.tsum_eq_iSup_sum, ENNReal.iSup_add]
  refine iSup_le fun s => ?_
  have hc : Continuous (fun α : ℝ => (∑ y ∈ s,
      if (y : Ambient d) = 0 then 0 else gaussianPotential α 0 (y : Ambient d)) +
        potentialEnergy V μ) := by
    apply Continuous.add ?_ continuous_const
    apply continuous_finsetSum
    intro y _
    split_ifs
    · exact continuous_const
    · unfold gaussianPotential gaussianKernel
      exact ENNReal.continuous_ofReal.comp (by fun_prop)
  apply le_of_tendsto (hc.tendsto β |>.comp hseq)
  apply Eventually.of_forall
  intro n
  have hinv : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
  have hα : β + (b - β) * ((n : ℝ) + 1)⁻¹ ∈ Ioc β b := by
    constructor
    · nlinarith only [mul_pos (sub_pos.mpr hβb) hinv]
    · have hi : ((n : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr
        (le_add_of_nonneg_left (Nat.cast_nonneg n))
      nlinarith only [mul_le_mul_of_nonneg_left hi (sub_pos.mpr hβb).le]
  calc
    _ ≤ latticePotentialEnergy Λ (gaussianPotential (β + (b - β) * ((n : ℝ) + 1)⁻¹)) +
        potentialEnergy V μ := add_le_add (ENNReal.sum_le_tsum _) le_rfl
    _ ≤ potentialEnergy (gaussianPotential (β + (b - β) * ((n : ℝ) + 1)⁻¹)) μ := hgap _ hα
    _ ≤ _ := gaussianPotentialEnergy_antitone μ hα.1.le

def quadraticClosePairPotential {d : ℕ} (k r : ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  ENNReal.ofReal (k * max 0 (r - dist x y) ^ 2)

theorem measurable_quadraticClosePairPotential {d : ℕ} (k r : ℝ) :
    Measurable (Function.uncurry (quadraticClosePairPotential (d := d) k r)) := by
  unfold Function.uncurry quadraticClosePairPotential
  fun_prop

theorem quadraticClosePairPotential_of_dist_le {d : ℕ} (k r : ℝ) {x y : Ambient d}
    (hxy : dist x y ≤ r) :
    quadraticClosePairPotential k r x y = ENNReal.ofReal (k * (r - dist x y) ^ 2) := by
  rw [quadraticClosePairPotential, max_eq_right (sub_nonneg.mpr hxy)]

end E8Leech
