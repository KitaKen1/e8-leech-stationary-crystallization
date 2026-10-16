import E8Leech.E8KernelGrowthNearOne

/-!
# A common E8 quadratic cost on the right of π

Uniform cusp growth controls every small positive radius. Spatial continuity
fills the origin separately for each parameter. A separated positive block
controls the shortest-radius endpoint. No joint continuity of the improper
integral or certificate at π is assumed.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Filter
open scoped ENNReal Real Topology

theorem uniform_quadratic_slack_of_far_and_shifted_block
    (m : ℕ) (φ K : ℝ × ℝ → ℝ) {a b r A B V : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) (hroot : r ^ 2 = 2 ∨ r ^ 2 = 4)
    (hA : 0 < A) (hB : 0 < B) (hV : 0 < V) (S : Set ℝ) (hS : S ⊆ Icc a b)
    (hfar : ∀ α ∈ S, ∀ u ∈ Icc 0 (7 / 8 * r), A ≤ φ (α, u))
    (hnonneg : ∀ α ∈ S, ∀ t : ℝ, 0 < t → 0 ≤ K (π / α, t))
    (hblock : ∀ α ∈ S, ∀ t ∈ Icc V (V + 1), B ≤ K (π / α, t))
    (hint : ∀ α ∈ S, ∀ u ∈ Icc (7 / 8 * r) r,
      IntegrableOn (fun t => K (π / α, t) * Real.exp (-π * u ^ 2 * t)) (Ioi 0))
    (hfactor : ∀ α ∈ S, ∀ u ∈ Icc (7 / 8 * r) r,
      φ (α, u) = (π / α) ^ m * (4 * Real.sin (π * u ^ 2 / 2) ^ 2 *
        ∫ t in Ioi (0 : ℝ), K (π / α, t) * Real.exp (-π * u ^ 2 * t))) :
    ∃ k : ℝ, 0 < k ∧ ∀ α ∈ S, ∀ u ∈ Icc 0 r,
      k * (r - u) ^ 2 ≤ φ (α, u) := by
  let c := 4 * (π / b) ^ m * B * Real.exp (-4 * π * (V + 1)) * r ^ 2
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨min (A / r ^ 2) c, lt_min (div_pos hA (pow_pos hr 2)) hc, ?_⟩
  intro α hα u hu
  apply full_quadratic_slack_of_two_regions hA hr hu (hfar α hα)
  intro v hv
  have hv0 : 0 ≤ v := by linarith only [hv.1, hr]
  have hvsq := pow_le_pow_left₀ hv0 hv.2 2
  have hfour : v ^ 2 ≤ 4 := by rcases hroot with h | h <;> linarith only [hvsq, h]
  have hJ := gaussian_normalized_shifted_laplace_block_lower m K ha hB.le hV (hS hα) hfour
    (hnonneg α hα) (hblock α hα) (hint α hα v hv)
  have hsin := sine_squared_even_root_lower hr hroot hv.1 hv.2
  rw [hfactor α hα v hv]
  calc
    c * (r - v) ^ 2 = 4 * (r ^ 2 * (r - v) ^ 2) *
        ((π / b) ^ m * B * Real.exp (-4 * π * (V + 1))) := by dsimp [c]; ring
    _ ≤ 4 * Real.sin (π * v ^ 2 / 2) ^ 2 *
        ((π / b) ^ m * B * Real.exp (-4 * π * (V + 1))) := by gcongr
    _ ≤ 4 * Real.sin (π * v ^ 2 / 2) ^ 2 *
        ((π / α) ^ m * ∫ t in Ioi (0 : ℝ), K (π / α, t) * Real.exp (-π * v ^ 2 * t)) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = _ := by ring

theorem e8_uniform_quadratic_slack_right_pi :
    ∃ b k : ℝ, π < b ∧ 0 < k ∧ ∀ α ∈ Ioc π b,
      ∀ u ∈ Icc (0 : ℝ) (Real.sqrt 2),
        k * (Real.sqrt 2 - u) ^ 2 ≤ e8SlackProfile e8KernelNonneg (α, u) := by
  obtain ⟨a, c₁, T, ha, ha1, hc₁, hT, hlin⟩ := e8_kernel_linear_growth_left_of_one
  let b := π / a
  have hb : π < b := (lt_div_iff₀ ha).mpr (by nlinarith [Real.pi_pos])
  have hb0 : 0 < b := Real.pi_pos.trans hb
  have hπb : π / b = a := by dsimp [b]; field_simp
  have hq : ∀ α ∈ Ioc π b, π / α ∈ Icc a 1 := by
    intro α hα
    have h := gaussian_dual_interval Real.pi_pos ⟨hα.1.le, hα.2⟩
    simpa only [hπb, div_self Real.pi_ne_zero] using h
  have hgood : ∀ α ∈ Ioc π b, 0 < α ∧ α ≠ π := fun α hα =>
    ⟨Real.pi_pos.trans hα.1, hα.1.ne'⟩
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let L := min (4 * c₁ * Real.exp (-2) / π ^ 2)
    (4 * min (1 / (π * T)) (15 / 32) ^ 2 *
      (c₁ * T ^ 2 * Real.exp (-(49 * π / 16 * T))))
  have hm : 0 < min (1 / (π * T)) (15 / 32 : ℝ) :=
    lt_min (by positivity) (by norm_num)
  have hL : 0 < L := by dsimp [L]; positivity
  have hA : 0 < a ^ 4 * L := mul_pos (pow_pos ha 4) hL
  have hfarpos : ∀ α ∈ Ioc π b, ∀ u : ℝ, 0 < u → u ^ 2 ≤ 49 / 32 →
      a ^ 4 * L ≤ e8SlackProfile e8KernelNonneg (α, u) := by
    intro α hα u hu hu2
    obtain ⟨hα0, hαπ⟩ := hgood α hα
    have hqa := hq α hα
    have hq0 := ha.trans_le hqa.1
    have hq1 : π / α ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq hα0.ne').mp h).symm
    have hlower := sin_sq_laplace_lower hc₁ hT
      (fun t ht => e8KernelNonneg _ t hq0 ht) (hlin _ hqa) hu hu2
      (integrableOn_e8DualKernel hq0 hq1 hu.ne')
    change L ≤ _ at hlower
    rw [e8SlackProfile_eq e8KernelNonneg hα0 hαπ hu]
    exact mul_le_mul (pow_le_pow_left₀ ha.le hqa.1 4) hlower hL.le (pow_nonneg hq0.le 4)
  have hu2 : ∀ u ∈ Icc (0 : ℝ) (7 / 8 * Real.sqrt 2), u ^ 2 ≤ 49 / 32 := by
    intro u hu
    have hs := pow_le_pow_left₀ hu.1 hu.2 2
    nlinarith only [hs, hr2]
  have hfar : ∀ α ∈ Ioc π b, ∀ u ∈ Icc (0 : ℝ) (7 / 8 * Real.sqrt 2),
      a ^ 4 * L ≤ e8SlackProfile e8KernelNonneg (α, u) := by
    intro α hα u hu
    rcases eq_or_lt_of_le hu.1 with hzero | hpos
    · subst u
      refine ge_of_tendsto
        ((continuous_e8SlackProfile_radius e8KernelNonneg α).continuousAt.continuousWithinAt
          (s := Ioi 0)) ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 7 / 8 * Real.sqrt 2 by positivity)] with v hv
      exact hfarpos α hα v hv.1 (hu2 v ⟨hv.1.le, hv.2.le⟩)
    · exact hfarpos α hα u hpos (hu2 u hu)
  obtain ⟨B, hB, hblock⟩ := e8_gaussian_separated_block_lower Real.pi_pos hb.le
  obtain ⟨k, hk, hlower⟩ := uniform_quadratic_slack_of_far_and_shifted_block 4
    (e8SlackProfile e8KernelNonneg) e8DualKernel Real.pi_pos hb.le hr (Or.inl hr2) hA hB
    (gaussianSeparatedBlockStart_pos π b) (Ioc π b)
    (fun _ hα => ⟨hα.1.le, hα.2⟩) hfar
    (fun α hα t ht => e8KernelNonneg _ t (ha.trans_le (hq α hα).1) ht)
    (fun α hα => hblock _ (by
      simpa only [hπb, div_self Real.pi_ne_zero] using hq α hα))
    (fun α hα u hu => integrableOn_e8DualKernel (ha.trans_le (hq α hα).1)
      (fun h => (hgood α hα).2 ((div_eq_one_iff_eq (hgood α hα).1.ne').mp h).symm)
      (ne_of_gt (by linarith only [hu.1, hr])))
    (fun α hα u hu => e8SlackProfile_eq e8KernelNonneg (hgood α hα).1 (hgood α hα).2
      (by linarith only [hu.1, hr]))
  exact ⟨b, k, hb, hk, hlower⟩

end E8Leech
