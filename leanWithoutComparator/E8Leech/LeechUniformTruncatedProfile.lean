import E8Leech.LeechKernelGrowthNearOne

/-!
# Uniform lower bounds for the truncated Leech profile near q=1

A common linear tail controls small positive radii. A bounded cusp constant
and a positive leading coefficient control a whole neighborhood of the
Laplace boundary b=2π. Both removable kernel points are excluded in the tail
representative; this is necessary when q is below 1.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Filter Topology
open scoped ENNReal Real

/-- Both integrals in the cut-1 profile are nonnegative. -/
theorem leechHatProfile_integrals_nonneg {q b : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) :
    (0 ≤ ∫ t in Ioc (0 : ℝ) 1, leechDualKernel (q, t) * Real.exp (-b * t)) ∧
    0 ≤ ∫ t in Ioi (1 : ℝ), (leechDualKernel (q, t) -
      ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
        Real.exp (2 * π * t)) * Real.exp (-b * t) := by
  have hfin : volume ({q, q⁻¹} : Set ℝ) = 0 := (Set.toFinite {q, q⁻¹}).measure_zero _
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({q, q⁻¹} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hfin
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioc] with t ht ht01
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    exact mul_nonneg (leechKernelInequalities.hat_nonneg q t hq ht01.1 ht.1 ht.2)
      (Real.exp_pos _).le
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioi] with t ht ht1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    exact mul_nonneg (sub_nonneg.mpr
      (leechKernelInequalities.hat_trunc q t hq hq1 ht1.le ht.1 ht.2)) (Real.exp_pos _).le

/-- Discarding the two nonnegative integrals retains the explicit cusp term. -/
theorem leechHatProfile_re_ge_explicit {q b : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) (hb : 0 < b) :
    Real.sinc ((b - 2 * π) / 2) ^ 2 * Real.exp (-(b - 2 * π) * 1) *
      ((leechAxisCusp (-1) q 0).re +
        ((leechAxisCusp (-1) q 1).re + 1 * (leechAxisCusp (-1) q 0).re) * (b - 2 * π)) ≤
      (leechAxisRadialProfile (-1) q b).re := by
  obtain ⟨hI₁, hI₂⟩ := leechHatProfile_integrals_nonneg (b := b) hq hq1
  rw [leechHatProfile_re_eq hq hq1 hb]
  exact le_add_of_nonneg_left (mul_nonneg (by positivity) (add_nonneg hI₁ hI₂))

theorem leechHatProfile_re_lower_small_left_of_one :
    ∃ A : ℝ, 0 < A ∧ ∀ q ∈ Icc (1 / 2 : ℝ) 1, q ≠ 1 →
      ∀ b : ℝ, 0 < b → b < π → A ≤ (leechAxisRadialProfile (-1) q b).re := by
  obtain ⟨c₁, T, hc₁, hT, hlin⟩ := leech_trunc_linear_left_of_one
  let A := min (4 * c₁ * Real.exp (-2) / π ^ 2)
    (4 * min (1 / (π * T)) (15 / 32) ^ 2 * (c₁ * T ^ 2 * Real.exp (-(49 * π / 16 * T))))
  have hπ := Real.pi_pos
  have hmin : 0 < min (1 / (π * T)) (15 / 32 : ℝ) := lt_min (by positivity) (by norm_num)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A, hA, fun q hq hq1 b hb hsmall => ?_⟩
  have hq0 : 0 < q := by linarith only [hq.1]
  have ha1 := (leechAxisCusp_lead_pos_all hq0).le
  have hsum := (leechAxisCusp_sum_neg hq0).le
  have htr := leechKernelInequalities.hat_trunc q
  have hlinq := hlin q hq
  have hinttr := integrableOn_leechDualKernel_trunc hq0 hq1 hb
  have hI₁ := (leechHatProfile_integrals_nonneg (b := b) hq0 hq1).1
  have hfin : volume ({q, q⁻¹} : Set ℝ) = 0 := (Set.toFinite {q, q⁻¹}).measure_zero _
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({q, q⁻¹} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hfin
  rw [leechHatProfile_re_eq hq0 hq1 hb]
  generalize (leechAxisCusp (-1) q 0).re = a₁ at *
  generalize (leechAxisCusp (-1) q 1).re = a₀ at *
  have hsin : 0 ≤ 4 * Real.sin (b / 2) ^ 2 := by positivity
  have hexp0 : 0 ≤ Real.sinc ((b - 2 * π) / 2) ^ 2 * Real.exp (-(b - 2 * π) * 1) *
      (a₁ + (a₀ + 1 * a₁) * (b - 2 * π)) := by
    have h1 : 0 ≤ (a₀ + 1 * a₁) * (b - 2 * π) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (by linarith)
  -- the truncated kernel as a function on `(0, ∞)`
  set K : ℝ → ℝ := fun t => if 1 < t ∧ t ≠ q ∧ t ≠ q⁻¹ then
    leechDualKernel (q, t) - (a₁ * t + a₀) * Real.exp (2 * π * t) else 0 with hK
  have hK0 : ∀ t : ℝ, 0 < t → 0 ≤ K t := by
    intro t _
    simp only [hK]
    split_ifs with h
    · have h' := htr t hq0 hq1 h.1.le h.2.1 h.2.2
      simp only [leechDualKernel]
      linarith
    · exact le_rfl
  have hKT : ∀ t : ℝ, T ≤ t → c₁ * t ≤ K t := by
    intro t ht
    have hqi : q⁻¹ ≤ 2 := by
      simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hq.1
    have h1 : 1 < t ∧ t ≠ q ∧ t ≠ q⁻¹ :=
      ⟨by linarith, by linarith [hq.2], by linarith⟩
    simp only [hK, if_pos h1]
    exact hlinq t ht
  set ρ := Real.sqrt (b / π) with hρ
  have hρ2 : ρ ^ 2 = b / π := Real.sq_sqrt (by positivity)
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
  have hπρ : π * ρ ^ 2 = b := by rw [hρ2]; field_simp
  have hρmax : ρ ^ 2 ≤ 49 / 32 := by
    rw [hρ2, div_le_iff₀ hπ]
    linarith
  -- the integral of `K` is the second integral
  have hKeq : ∀ᵐ t ∂volume.restrict (Ioi (1 : ℝ)), K t * Real.exp (-π * ρ ^ 2 * t) =
      (leechDualKernel (q, t) - (a₁ * t + a₀) * Real.exp (2 * π * t)) * Real.exp (-b * t) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioi] with t ht ht1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    have h1 : 1 < t ∧ t ≠ q ∧ t ≠ q⁻¹ := ⟨ht1, ht.1, ht.2⟩
    simp only [hK, if_pos h1]
    rw [show -π * ρ ^ 2 * t = -b * t by rw [← hπρ]; ring]
  have hKzero : ∀ t ∈ Ioc (0 : ℝ) 1, K t * Real.exp (-π * ρ ^ 2 * t) = 0 := by
    intro t ht
    have h1 : ¬(1 < t ∧ t ≠ q ∧ t ≠ q⁻¹) := fun h => absurd h.1 (not_lt.mpr ht.2)
    simp only [hK, if_neg h1, zero_mul]
  have hint1 : IntegrableOn (fun t => K t * Real.exp (-π * ρ ^ 2 * t)) (Ioi 1) :=
    hinttr.congr_fun_ae (hKeq.mono fun t ht => ht.symm)
  have hint01 : IntegrableOn (fun t => K t * Real.exp (-π * ρ ^ 2 * t)) (Ioc 0 1) :=
    (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc (0 : ℝ) 1) volume).congr_fun
      (fun t ht => (hKzero t ht).symm) measurableSet_Ioc
  have hint0 : IntegrableOn (fun t => K t * Real.exp (-π * ρ ^ 2 * t)) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
    exact hint01.union hint1
  have hlow := sin_sq_laplace_lower hc₁ (by linarith : 1 ≤ T) hK0 hKT hρpos hρmax hint0
  have hsplit : ∫ t in Ioi (0 : ℝ), K t * Real.exp (-π * ρ ^ 2 * t) =
      ∫ t in Ioi (1 : ℝ), (leechDualKernel (q, t) -
        (a₁ * t + a₀) * Real.exp (2 * π * t)) * Real.exp (-b * t) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint01 hint1,
      setIntegral_congr_fun measurableSet_Ioc hKzero, integral_zero, zero_add]
    exact integral_congr_ae hKeq
  rw [hsplit, hπρ] at hlow
  have h1 := mul_nonneg hsin hI₁
  change A ≤ _
  have hdist : 4 * Real.sin (b / 2) ^ 2 *
      ((∫ t in Ioc (0 : ℝ) 1, leechDualKernel (q, t) * Real.exp (-b * t)) +
        ∫ t in Ioi (1 : ℝ), (leechDualKernel (q, t) -
          (a₁ * t + a₀) * Real.exp (2 * π * t)) * Real.exp (-b * t)) =
      4 * Real.sin (b / 2) ^ 2 *
        (∫ t in Ioc (0 : ℝ) 1, leechDualKernel (q, t) * Real.exp (-b * t)) +
      4 * Real.sin (b / 2) ^ 2 *
        ∫ t in Ioi (1 : ℝ), (leechDualKernel (q, t) -
          (a₁ * t + a₀) * Real.exp (2 * π * t)) * Real.exp (-b * t) := by ring
  rw [hdist]
  change A ≤ _ at hlow
  linarith only [hlow, h1, hexp0]

/-- A common positive lower bound through the boundary of ordinary Laplace convergence. -/
theorem leechHatProfile_re_lower_boundary_left_of_one :
    ∃ δ A : ℝ, 0 < δ ∧ δ ≤ π / 2 ∧ 0 < A ∧
      ∀ q ∈ Icc (1 / 2 : ℝ) 1, q ≠ 1 → ∀ b ∈ Icc π (2 * π + δ),
        A ≤ (leechAxisRadialProfile (-1) q b).re := by
  obtain ⟨m, hm, hlead⟩ := leech_lead_lower_on_compact
    (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)
  obtain ⟨M, hM⟩ := exists_leechAxisCusp_compact_bound (-1)
    (a := 1 / 2) (b := 1) (by norm_num)
  let N := |M| + 1
  have hN : 0 < N := by dsimp only [N]; positivity
  let δ := min (π / 2) (m / (2 * N))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδπ : δ ≤ π / 2 := min_le_left _ _
  have hδm : N * δ ≤ m / 2 := by
    have h := min_le_right (π / 2) (m / (2 * N))
    rw [le_div_iff₀ (by positivity : 0 < 2 * N)] at h
    dsimp only [δ]
    nlinarith only [h]
  obtain ⟨σ, hσ, hσlow⟩ := exists_sinc_lower (R := π / 2) (by positivity)
    (by linarith [Real.pi_pos])
  let A := σ ^ 2 * Real.exp (-δ) * (m / 2)
  refine ⟨δ, A, hδ, hδπ, by dsimp only [A]; positivity, ?_⟩
  intro q hq hq1 b hb
  have hq0 : 0 < q := by linarith only [hq.1]
  have hb0 : 0 < b := Real.pi_pos.trans_le hb.1
  have ha1 := hlead q hq
  have hsum := (leechAxisCusp_sum_neg hq0).le
  have hconst : -M ≤ (leechAxisCusp (-1) q 1).re :=
    le_trans (neg_le_neg (hM q hq 1)) (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  have hsumlow : -N ≤ (leechAxisCusp (-1) q 1).re + (leechAxisCusp (-1) q 0).re := by
    dsimp only [N]
    linarith only [hconst, ha1, hm, le_abs_self M]
  have hbr : m / 2 ≤ (leechAxisCusp (-1) q 0).re +
      ((leechAxisCusp (-1) q 1).re + 1 * (leechAxisCusp (-1) q 0).re) * (b - 2 * π) := by
    by_cases hble : b ≤ 2 * π
    · have hp := mul_nonneg_of_nonpos_of_nonpos hsum (sub_nonpos.mpr hble)
      nlinarith only [hp, ha1, hm]
    · have hp := mul_le_mul_of_nonneg_right hsumlow (by linarith : 0 ≤ b - 2 * π)
      have hbd := mul_le_mul_of_nonneg_left (show b - 2 * π ≤ δ by linarith only [hb.2]) hN.le
      nlinarith only [hp, hbd, hδm, ha1]
  have hs : σ ^ 2 ≤ Real.sinc ((b - 2 * π) / 2) ^ 2 :=
    pow_le_pow_left₀ hσ.le (hσlow _ ⟨by linarith only [hb.1], by linarith only [hb.2, hδπ, Real.pi_pos]⟩) 2
  have he : Real.exp (-δ) ≤ Real.exp (-(b - 2 * π) * 1) :=
    Real.exp_le_exp.mpr (by linarith only [hb.2])
  apply le_trans _ (leechHatProfile_re_ge_explicit hq0 hq1 hb0)
  exact mul_le_mul (mul_le_mul hs he (Real.exp_pos _).le (sq_nonneg _)) hbr
    (by positivity) (by positivity)

end E8Leech
