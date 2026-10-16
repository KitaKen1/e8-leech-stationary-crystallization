import E8Leech.GaussianLatticeFiniteness
import E8Leech.OriginSlack

/-!
# A direct origin lower bound from the published weighted Gaussian lattice sum

The supplied v2 paper uses CKMRV (6.1) rather than a separate special-value
computation. The actual weighted lattice sum is finite and has a one-vector
lower bound. Identifying the constructed CKMRV function with that formula
remains an explicit proof obligation; no such function is postulated here.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

def weightedGaussianLatticeEnergy {d : ℕ} (Λ : Set (Ambient d)) (β : ℝ) : ℝ≥0∞ :=
  ∑' z : Λ, if (z : Ambient d) = 0 then 0 else
    ENNReal.ofReal (‖(z : Ambient d)‖ ^ 2 * gaussianKernel β (z : Ambient d))

theorem norm_sq_gaussian_half_scale_upper {d : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Ambient d) :
    ‖v‖ ^ 2 * gaussianKernel β v ≤ (2 / β) * gaussianKernel (β / 2) v := by
  have h := pow_mul_exp_neg_le_factorial_div (by positivity : 0 < β / 2)
    (sq_nonneg ‖v‖) 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h
  have hh := mul_le_mul_of_nonneg_right h (gaussianKernel_pos (β / 2) v).le
  have he : Real.exp (-(β / 2) * ‖v‖ ^ 2) * gaussianKernel (β / 2) v =
      gaussianKernel β v := by
    unfold gaussianKernel
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (‖v‖ ^ 2 * Real.exp (-(β / 2) * ‖v‖ ^ 2)) *
        gaussianKernel (β / 2) v := by rw [mul_assoc, he]
    _ ≤ (1 / (β / 2)) * gaussianKernel (β / 2) v := hh
    _ = _ := by congr 1; field_simp

theorem weighted_gaussian_lattice_energy_upper {d : ℕ} {β : ℝ} (hβ : 0 < β)
    (Λ : Set (Ambient d)) :
    weightedGaussianLatticeEnergy Λ β ≤ ENNReal.ofReal (2 / β) *
      latticePotentialEnergy Λ (gaussianPotential (β / 2)) := by
  unfold weightedGaussianLatticeEnergy latticePotentialEnergy
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : (z : Ambient d) = 0
  · simp [hz]
  · simp only [if_neg hz, gaussianPotential, gaussianKernel, zero_sub, norm_neg]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / β)]
    exact ENNReal.ofReal_le_ofReal (norm_sq_gaussian_half_scale_upper hβ (z : Ambient d))

theorem weighted_gaussian_lattice_energy_ne_top {d : ℕ} {β : ℝ} (hβ : 0 < β)
    (Λ : Set (Ambient d)) (n : ℕ) (hfinite : latticeRieszEnergy Λ (n : ℝ) ≠ ∞) :
    weightedGaussianLatticeEnergy Λ β ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (gaussian_lattice_energy_ne_top_of_riesz (by positivity) Λ n hfinite))
    (weighted_gaussian_lattice_energy_upper hβ Λ)

theorem weighted_gaussian_lattice_single_vector_lower {d : ℕ} {Λ : Set (Ambient d)}
    {β : ℝ} {z : Ambient d} (hz : z ∈ Λ) (hne : z ≠ 0)
    (hfinite : weightedGaussianLatticeEnergy Λ β ≠ ∞) :
    ‖z‖ ^ 2 * gaussianKernel β z ≤ (weightedGaussianLatticeEnergy Λ β).toReal := by
  have h := ENNReal.le_tsum (f := fun y : Λ => if (y : Ambient d) = 0 then 0 else
    ENNReal.ofReal (‖(y : Ambient d)‖ ^ 2 * gaussianKernel β (y : Ambient d))) ⟨z, hz⟩
  change (if z = 0 then 0 else ENNReal.ofReal (‖z‖ ^ 2 * gaussianKernel β z)) ≤
    weightedGaussianLatticeEnergy Λ β at h
  rw [if_neg hne] at h
  have ht := ENNReal.toReal_mono hfinite h
  rwa [ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _) (gaussianKernel_pos β z).le)] at ht

theorem origin_slack_lower_of_weighted_gaussian_formula {d : ℕ} {Λ : Set (Ambient d)}
    {α r slack : ℝ} (hd : 0 < (d : ℝ)) (m n : ℕ)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3))
    (hfinite : latticeRieszEnergy Λ (n : ℝ) ≠ ∞)
    {z : Ambient d} (hz : z ∈ Λ) (hne : z ≠ 0) (hnorm : ‖z‖ = r)
    (hformula : slack = (2 * Real.pi / d) * (Real.pi / α) ^ (m + 1) *
      (weightedGaussianLatticeEnergy Λ (Real.pi ^ 2 / α)).toReal) :
    (2 * Real.pi / d) * (3 : ℝ) ^ (m + 1) * r ^ 2 * Real.exp (-4 * Real.pi * r ^ 2) ≤
      slack := by
  have ha := gaussian_compact_interval_pos hα
  have hβ : 0 < Real.pi ^ 2 / α := by positivity
  have hw := weighted_gaussian_lattice_single_vector_lower hz hne
    (weighted_gaussian_lattice_energy_ne_top hβ Λ n hfinite)
  rw [hnorm] at hw
  have he : Real.exp (-4 * Real.pi * r ^ 2) ≤ gaussianKernel (Real.pi ^ 2 / α) z := by
    unfold gaussianKernel
    rw [hnorm]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right (gaussian_dual_parameter_block_upper hα)
      (sq_nonneg r)]
  have hl := (mul_le_mul_of_nonneg_left he (sq_nonneg r)).trans hw
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
    (gaussian_dual_compact_interval hα).1 (m + 1)
  rw [hformula]
  calc
    _ = (2 * Real.pi / d) * ((3 : ℝ) ^ (m + 1) *
        (r ^ 2 * Real.exp (-4 * Real.pi * r ^ 2))) := by ring
    _ ≤ (2 * Real.pi / d) * ((Real.pi / α) ^ (m + 1) *
        (weightedGaussianLatticeEnergy Λ (Real.pi ^ 2 / α)).toReal) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hp hl (by positivity) (by positivity))
        (div_pos (by positivity) hd).le
    _ = _ := by ring

theorem origin_slack_pos_of_weighted_gaussian_formula {d : ℕ} {Λ : Set (Ambient d)}
    {α r slack : ℝ} (hd : 0 < (d : ℝ)) (hr : 0 < r) (m n : ℕ)
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3))
    (hfinite : latticeRieszEnergy Λ (n : ℝ) ≠ ∞)
    {z : Ambient d} (hz : z ∈ Λ) (hne : z ≠ 0) (hnorm : ‖z‖ = r)
    (hformula : slack = (2 * Real.pi / d) * (Real.pi / α) ^ (m + 1) *
      (weightedGaussianLatticeEnergy Λ (Real.pi ^ 2 / α)).toReal) : 0 < slack :=
  (mul_pos (mul_pos (mul_pos (div_pos (by positivity) hd) (by positivity)) (pow_pos hr 2))
    (Real.exp_pos _)).trans_le
    (origin_slack_lower_of_weighted_gaussian_formula hd m n hα hfinite hz hne hnorm hformula)

theorem e8_origin_slack_pos_of_weighted_gaussian_formula {α slack : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3))
    (hformula : slack = (2 * Real.pi / 8) * (Real.pi / α) ^ 5 *
      (weightedGaussianLatticeEnergy e8Set (Real.pi ^ 2 / α)).toReal) : 0 < slack := by
  obtain ⟨z, hz, hne, hnorm⟩ := e8Set_minimum_attained
  exact origin_slack_pos_of_weighted_gaussian_formula (by norm_num : (0 : ℝ) < 8)
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)) 4 9 hα
    (e8_latticeRieszEnergy_ne_top (by norm_num)) hz hne hnorm hformula

theorem leech_origin_slack_pos_of_weighted_gaussian_formula {α slack : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 3))
    (hformula : slack = (2 * Real.pi / 24) * (Real.pi / α) ^ 13 *
      (weightedGaussianLatticeEnergy leechSet (Real.pi ^ 2 / α)).toReal) : 0 < slack := by
  obtain ⟨z, hz, hne, hnorm⟩ := leechSet_minimum_attained
  exact origin_slack_pos_of_weighted_gaussian_formula (by norm_num : (0 : ℝ) < 24)
    (by norm_num : (0 : ℝ) < 2) 12 25 hα
    (leech_latticeRieszEnergy_ne_top (by norm_num)) hz hne hnorm hformula

end E8Leech
