import E8Leech.LeechSlackProfile
import E8Leech.E8UnitCost
import E8Leech.LeechStabilityUnconditional

/-!
# The Leech analytic unit-cost input from the CKMRV data

Three inputs are hypotheses of this file and are *not* proved in it:

* `LeechKernelInequalities` (CKMRV (6.4) in dimension 24; proved in
  `LeechKernelInequalitiesProof`);
* `LeechFourierIdentities` (the identity (**) in dimension 24, for all radii; proved in
  `LeechFourierIdentityProof`);
* `LeechBlockBounds` (proved in `LeechBlockBoundsProof`): quantitative forms on the block
  `q ∈ [3, 4]`, where `q = π/α` for the
  Gaussian parameters `α ∈ [π/4, π/3]` used for the slack:
  a lower bound of `𝒦̂` on `[3,4] × [1,2]`, `a₁ ≥ m > 0`, `a₀ + (5/4) a₁ ≥ 0`, and linear growth
  `𝒦̂ − e^{2πt}(a₁ t + a₀) ≥ c₁ t` for `t ≥ T`.

From them: `AnalyticUnitCostInput leechSet s 2` for every `s > 0`
(`leech_analyticUnitCostInput_of_ckmrv`), hence the stationary crystallization target for the Leech
lattice (`leech_stationaryCrystallization_of_ckmrv`).

The slack `(π/α)¹² Re P_𝒦̂,π/α(πu²)` needs a positive lower bound for `u ∈ [0, 7/4]`, an interval
that contains the radius `√2` where the Laplace representation stops. With `b = πu²`:
for `π ≤ b ≤ 49π/16` the explicit term of the truncated form is bounded below (the two integrals
are nonnegative for every `b > 0`); for `0 < b ≤ π` the linear growth of the truncated kernel
gives the bound, as for `E8`; `u = 0` follows by continuity.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory Filter Topology
open UpperHalfPlane hiding I
open scoped ENNReal Real SchwartzMap FourierTransform

/-- **Quantitative bounds on the block `q ∈ [3, 4]`.** -/
structure LeechBlockBounds : Prop where
  block_lower : ∃ B : ℝ, 0 < B ∧ ∀ q ∈ Icc (3 : ℝ) 4, ∀ t ∈ Icc (1 : ℝ) 2,
    B ≤ leechDualKernel (q, t)
  lead_lower : ∃ m : ℝ, 0 < m ∧ ∀ q ∈ Icc (3 : ℝ) 4, m ≤ (leechAxisCusp (-1) q 0).re
  lead_ratio : ∀ q ∈ Icc (3 : ℝ) 4,
    0 ≤ (leechAxisCusp (-1) q 1).re + 5 / 4 * (leechAxisCusp (-1) q 0).re
  trunc_linear : ∃ c₁ T : ℝ, 0 < c₁ ∧ 4 < T ∧ ∀ q ∈ Icc (3 : ℝ) 4, ∀ t : ℝ, T ≤ t →
    c₁ * t ≤ leechDualKernel (q, t) -
      ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) * Real.exp (2 * π * t)

/-- `sinc` has a positive lower bound on `[−R, R]` for `R < π`. -/
theorem exists_sinc_lower {R : ℝ} (hR : 0 ≤ R) (hRπ : R < π) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ x ∈ Icc (-R) R, σ ≤ Real.sinc x := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by linarith))
    (contDiff_sinc.continuous.continuousOn (s := Icc (-R) R))
  refine ⟨Real.sinc x₀, ?_, fun x hx => hmin hx⟩
  rcases lt_trichotomy x₀ 0 with hneg | hzero | hpos
  · rw [Real.sinc_of_ne_zero hneg.ne]
    exact div_pos_of_neg_of_neg
      (Real.sin_neg_of_neg_of_neg_pi_lt hneg (by linarith [hx₀.1])) hneg
  · rw [hzero, Real.sinc_zero]
    exact one_pos
  · rw [Real.sinc_of_ne_zero hpos.ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [hx₀.2])) hpos

/-- **A positive lower bound of `F̃(iq, ·)` on the block, for `0 < b ≤ 49π/16`.** -/
theorem leechHatProfile_re_lower (H : LeechKernelInequalities) (U : LeechBlockBounds) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ q ∈ Icc (3 : ℝ) 4, ∀ b : ℝ, 0 < b → b ≤ 49 * π / 16 →
      A₀ ≤ (leechAxisRadialProfile (-1) q b).re := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hπ315 := Real.pi_lt_d2
  obtain ⟨m, hm, hmlow⟩ := U.lead_lower
  obtain ⟨c₁, T, hc₁, hT, hlin⟩ := U.trunc_linear
  obtain ⟨σ, hσ, hσlow⟩ := exists_sinc_lower (R := 17 * π / 32) (by positivity) (by linarith)
  have hfac : 0 < 1 - 17 * π / 64 := by linarith
  set A₁ : ℝ := σ ^ 2 * Real.exp (-(17 * π / 16)) * (m * (1 - 17 * π / 64)) with hA₁
  set A₂ : ℝ := min (4 * c₁ * Real.exp (-2) / π ^ 2)
    (4 * min (1 / (π * T)) (15 / 32) ^ 2 * (c₁ * T ^ 2 * Real.exp (-(49 * π / 16 * T)))) with hA₂
  have hA₁pos : 0 < A₁ := by positivity
  have hA₂pos : 0 < A₂ := by
    refine lt_min (by positivity) ?_
    have : 0 < min (1 / (π * T)) (15 / 32 : ℝ) := lt_min (by positivity) (by norm_num)
    positivity
  refine ⟨min A₁ A₂, lt_min hA₁pos hA₂pos, fun q hq b hb hbmax => ?_⟩
  have hq0 : 0 < q := by linarith [hq.1]
  have hq1 : q ≠ 1 := by linarith [hq.1]
  have ha1 := hmlow q hq
  have hsum := H.cusp_sum_nonpos q hq0 hq1
  have hratio := U.lead_ratio q hq
  have htr := H.hat_trunc q
  have hlinq := hlin q hq
  have hinttr := integrableOn_leechDualKernel_trunc hq0 hq1 hb
  rw [leechHatProfile_re_eq hq0 hq1 hb]
  generalize (leechAxisCusp (-1) q 0).re = a₁ at *
  generalize (leechAxisCusp (-1) q 1).re = a₀ at *
  -- the two integrals are nonnegative
  have hfin : volume ({q, q⁻¹} : Set ℝ) = 0 := (Set.toFinite {q, q⁻¹}).measure_zero _
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({q, q⁻¹} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hfin
  have hI₁ : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, leechDualKernel (q, t) * Real.exp (-b * t) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioc] with t ht ht01
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    exact mul_nonneg (H.hat_nonneg q t hq0 ht01.1 ht.1 ht.2) (Real.exp_pos _).le
  have hpt : ∀ᵐ t ∂volume.restrict (Ioi (1 : ℝ)),
      0 ≤ (leechDualKernel (q, t) - (a₁ * t + a₀) * Real.exp (2 * π * t)) *
        Real.exp (-b * t) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioi] with t ht ht1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
    refine mul_nonneg ?_ (Real.exp_pos _).le
    have h := htr t hq0 hq1 (le_of_lt ht1) ht.1 ht.2
    simp only [leechDualKernel]
    linarith
  have hI₂ : 0 ≤ ∫ t in Ioi (1 : ℝ), (leechDualKernel (q, t) -
      (a₁ * t + a₀) * Real.exp (2 * π * t)) * Real.exp (-b * t) := integral_nonneg_of_ae hpt
  have hsin : 0 ≤ 4 * Real.sin (b / 2) ^ 2 := by positivity
  rcases le_or_gt π b with hbig | hsmall
  · -- the explicit term
    have hx : (b - 2 * π) / 2 ∈ Icc (-(17 * π / 32)) (17 * π / 32) := by
      constructor <;> linarith
    have hs1 : σ ^ 2 ≤ Real.sinc ((b - 2 * π) / 2) ^ 2 :=
      pow_le_pow_left₀ hσ.le (hσlow _ hx) 2
    have he1 : Real.exp (-(17 * π / 16)) ≤ Real.exp (-(b - 2 * π) * 1) :=
      Real.exp_le_exp.mpr (by linarith)
    have hbr : m * (1 - 17 * π / 64) ≤ a₁ + (a₀ + 1 * a₁) * (b - 2 * π) := by
      rcases le_or_gt b (2 * π) with hle | hgt
      · have h1 : 0 ≤ (a₀ + 1 * a₁) * (b - 2 * π) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        nlinarith
      · have h1 : -(a₁ / 4) * (b - 2 * π) ≤ (a₀ + 1 * a₁) * (b - 2 * π) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have h2 : a₁ / 4 * (b - 2 * π) ≤ a₁ / 4 * (17 * π / 16) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have h3 : m * (1 - 17 * π / 64) ≤ a₁ * (1 - 17 * π / 64) :=
          mul_le_mul_of_nonneg_right ha1 hfac.le
        nlinarith
    have hexp : A₁ ≤ Real.sinc ((b - 2 * π) / 2) ^ 2 * Real.exp (-(b - 2 * π) * 1) *
        (a₁ + (a₀ + 1 * a₁) * (b - 2 * π)) := by
      rw [hA₁]
      exact mul_le_mul (mul_le_mul hs1 he1 (Real.exp_pos _).le (by positivity)) hbr
        (by positivity) (by positivity)
    have h0 : 0 ≤ 4 * Real.sin (b / 2) ^ 2 *
        ((∫ t in Ioc (0 : ℝ) 1, leechDualKernel (q, t) * Real.exp (-b * t)) +
          ∫ t in Ioi (1 : ℝ), (leechDualKernel (q, t) -
            (a₁ * t + a₀) * Real.exp (2 * π * t)) * Real.exp (-b * t)) :=
      mul_nonneg hsin (add_nonneg hI₁ hI₂)
    exact (min_le_left _ _).trans (by linarith)
  · -- the linear growth of the truncated kernel
    have hexp0 : 0 ≤ Real.sinc ((b - 2 * π) / 2) ^ 2 * Real.exp (-(b - 2 * π) * 1) *
        (a₁ + (a₀ + 1 * a₁) * (b - 2 * π)) := by
      have h1 : 0 ≤ (a₀ + 1 * a₁) * (b - 2 * π) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (by linarith)
    -- the truncated kernel as a function on `(0, ∞)`
    set K : ℝ → ℝ := fun t => if 1 < t ∧ t ≠ q then
      leechDualKernel (q, t) - (a₁ * t + a₀) * Real.exp (2 * π * t) else 0 with hK
    have hK0 : ∀ t : ℝ, 0 < t → 0 ≤ K t := by
      intro t _
      simp only [hK]
      split_ifs with h
      · have hne : t ≠ q⁻¹ := by
          have : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith [hq.1])
          linarith [h.1]
        have h' := htr t hq0 hq1 h.1.le h.2 hne
        simp only [leechDualKernel]
        linarith
      · exact le_rfl
    have hKT : ∀ t : ℝ, T ≤ t → c₁ * t ≤ K t := by
      intro t ht
      have h1 : 1 < t ∧ t ≠ q := ⟨by linarith, by linarith [hq.2]⟩
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
      have h1 : 1 < t ∧ t ≠ q := ⟨ht1, ht.1⟩
      simp only [hK, if_pos h1]
      rw [show -π * ρ ^ 2 * t = -b * t by rw [← hπρ]; ring]
    have hKzero : ∀ t ∈ Ioc (0 : ℝ) 1, K t * Real.exp (-π * ρ ^ 2 * t) = 0 := by
      intro t ht
      have h1 : ¬(1 < t ∧ t ≠ q) := fun h => absurd h.1 (not_lt.mpr ht.2)
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
    refine (min_le_right _ _).trans ?_
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
    linarith

/-! ## The unit-cost input -/

theorem integrableOn_leechDualKernel {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) {u : ℝ} (hu : 2 < u ^ 2) :
    IntegrableOn (fun v => leechDualKernel (q, v) * Real.exp (-Real.pi * u ^ 2 * v)) (Ioi 0) := by
  have hp := integrableOn_ckmrvLeechPlusKernel_laplace_imagAxis hq hq1 hu
  have hm := integrableOn_ckmrvLeechMinusKernel_laplace_imagAxis hq hq1 hu
  have hhat : IntegrableOn (fun t => ckmrvLeechHatKernel (imagPt q) (imagPt t) *
      (Real.exp (-(π * u ^ 2) * t) : ℂ)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.div_const (Integrable.sub hp hm) 2)
      (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, ckmrvLeechHatKernel]
    ring
  have h := Integrable.re hhat
  refine IntegrableOn.congr_fun h (fun v _ => ?_) measurableSet_Ioi
  simp only [leechDualKernel, RCLike.re_to_complex, Complex.re_mul_ofReal]
  congr 2
  ring

/-- **The slack as a dual Laplace transform**, in the range `u² > 2` of the representation. -/
theorem leechSlackProfile_eq_laplace {α u : ℝ} (hα : 0 < α) (hαπ : α ≠ π) (hu0 : 0 ≤ u)
    (hu : 2 < u ^ 2) :
    leechSlackProfile (α, u) = (π / α) ^ 12 * (4 * Real.sin (π * u ^ 2 / 2) ^ 2 *
      ∫ v in Ioi (0 : ℝ), leechDualKernel (π / α, v) * Real.exp (-π * u ^ 2 * v)) := by
  have hπ := Real.pi_pos
  have hq : 0 < π / α := div_pos hπ hα
  have hq1 : π / α ≠ 1 := fun h => hαπ ((div_eq_one_iff_eq hα.ne').mp h).symm
  rw [leechSlackProfile_eq hα hαπ hu0,
    leechAxisRadialProfile_eq_laplace (-1) hq hq1 (by nlinarith : 2 * π < π * u ^ 2),
    setIntegral_eq_ofReal_of_im_eq_zero measurableSet_Ioi fun t ht => by
      rw [Complex.im_mul_ofReal, leechAxisKernel_im im_neg_one hq ht, zero_mul],
    ← Complex.ofReal_mul, Complex.ofReal_re]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.re_mul_ofReal, leechAxisKernel_neg_one, leechDualKernel]
  congr 2
  ring

/-- The dual kernel with the value `0` at the singular points `t = q`, `t = q⁻¹`, where the Lean
kernel has a junk value. For a fixed `q` it agrees with `leechDualKernel` almost everywhere, and
it is nonnegative everywhere under `LeechKernelInequalities`. -/
def leechDualKernelReg (p : ℝ × ℝ) : ℝ :=
  if p.2 = p.1 ∨ p.2 = p.1⁻¹ then 0 else leechDualKernel p

theorem leechDualKernelReg_of_ne {q t : ℝ} (h1 : t ≠ q) (h2 : t ≠ q⁻¹) :
    leechDualKernelReg (q, t) = leechDualKernel (q, t) := by
  show (if t = q ∨ t = q⁻¹ then 0 else leechDualKernel (q, t)) = _
  rw [if_neg (not_or.mpr ⟨h1, h2⟩)]

theorem leechDualKernelReg_nonneg (H : LeechKernelInequalities) {q t : ℝ} (hq : 0 < q)
    (ht : 0 < t) : 0 ≤ leechDualKernelReg (q, t) := by
  by_cases h : t = q ∨ t = q⁻¹
  · show 0 ≤ (if t = q ∨ t = q⁻¹ then 0 else leechDualKernel (q, t))
    rw [if_pos h]
  · rw [not_or] at h
    rw [leechDualKernelReg_of_ne h.1 h.2]
    exact H.hat_nonneg q t hq ht h.1 h.2

theorem leechDualKernelReg_ae (q : ℝ) :
    (fun t => leechDualKernelReg (q, t)) =ᵐ[volume] fun t => leechDualKernel (q, t) := by
  have hfin : volume ({q, q⁻¹} : Set ℝ) = 0 := (Set.toFinite {q, q⁻¹}).measure_zero _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hfin] with t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
  exact leechDualKernelReg_of_ne ht.1 ht.2

/-- **The Leech analytic unit-cost input from the CKMRV data**: the kernel inequalities, the
Fourier identities and the bounds on the block (all three are hypotheses). -/
theorem leech_analyticUnitCostInput_of_ckmrv {s : ℝ} (hs : 0 < s) (H : LeechKernelInequalities)
    (hF : LeechFourierIdentities) (U : LeechBlockBounds) :
    ∃ C : ℝ, 0 < C ∧ AnalyticUnitCostInput leechSet s 2 C⁻¹ (1 / 8) := by
  obtain ⟨B, hB, hBlow⟩ := U.block_lower
  obtain ⟨A₀, hA₀, hA₀low⟩ := leechHatProfile_re_lower H U
  have hr : (0 : ℝ) < 2 := by norm_num
  have hr2 : (2 : ℝ) ^ 2 = 4 := by norm_num
  have hπ := Real.pi_pos
  have ha : 0 < π / 4 := by positivity
  have hab : π / 4 < π / 3 := by linarith
  have hgood : ∀ α ∈ Icc (π / 4) (π / 3), 0 < α ∧ α ≠ π := fun α hα =>
    ⟨gaussian_compact_interval_pos hα, by intro h; rw [h] at hα; linarith [hα.2]⟩
  have hq : ∀ α ∈ Icc (π / 4) (π / 3), π / α ∈ Icc (3 : ℝ) 4 := fun α hα =>
    gaussian_dual_compact_interval hα
  have hKnn : ∀ q ∈ Icc (3 : ℝ) 4, ∀ v : ℝ, 0 < v → 0 ≤ leechDualKernelReg (q, v) :=
    fun q hq v hv => leechDualKernelReg_nonneg H (by linarith [hq.1]) hv
  have hq1 : ∀ q ∈ Icc (3 : ℝ) 4, q ≠ 1 := fun q hq => by linarith [hq.1]
  -- the lower bound of the slack on `[π/4, π/3] × [0, 7/4]`
  have hApos : ∀ α ∈ Icc (π / 4) (π / 3), ∀ u : ℝ, 0 < u → u ≤ 7 / 8 * 2 →
      A₀ ≤ leechSlackProfile (α, u) := by
    intro α hα u hu humax
    obtain ⟨hα0, hαπ⟩ := hgood α hα
    have hqa := hq α hα
    rw [leechSlackProfile_eq hα0 hαπ hu.le]
    have hb0 : 0 < π * u ^ 2 := by positivity
    have hu2 : u ^ 2 ≤ 49 / 16 := by nlinarith
    have hbmax : π * u ^ 2 ≤ 49 * π / 16 := by nlinarith
    have hlow := hA₀low _ hqa _ hb0 hbmax
    have h1 : (1 : ℝ) ≤ (π / α) ^ 12 := one_le_pow₀ (by linarith [hqa.1])
    calc A₀ = 1 * A₀ := (one_mul _).symm
      _ ≤ (π / α) ^ 12 * (leechAxisRadialProfile (-1) (π / α) (π * u ^ 2)).re :=
        mul_le_mul h1 hlow hA₀.le (by positivity)
  have hAlower : ∀ α ∈ Icc (π / 4) (π / 3), ∀ u ∈ Icc 0 (7 / 8 * (2 : ℝ)),
      A₀ ≤ leechSlackProfile (α, u) := by
    intro α hα u hu
    rcases eq_or_lt_of_le hu.1 with h0 | hpos
    · subst h0
      have hf : Continuous fun u : ℝ => leechSlackProfile (α, u) := by
        simp only [leechSlackProfile]
        exact (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).sub
          (Complex.continuous_re.comp ((leechCertFamily α).continuous.comp
            (continuous_id.smul continuous_const)))
      refine ge_of_tendsto (hf.continuousAt.continuousWithinAt (s := Ioi 0)) ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 7 / 8 * 2 by norm_num)] with u' hu'
      exact hApos α hα u' hu'.1 hu'.2.le
    · exact hApos α hα u hpos hu.2
  -- the block lower bound and the factorization for the normalized kernel
  -- (the kernel is taken with the value `0` at the singular points: `leechDualKernelReg`)
  have hBlower : ∀ α ∈ Icc (π / 4) (π / 3), ∀ t ∈ Icc (1 : ℝ) 2,
      B ≤ gaussianDualLaplaceKernel 12 leechDualKernelReg (α, t) := by
    intro α hα t ht
    have hqa := hq α hα
    have hk := hBlow _ hqa t ht
    have h1 : (1 : ℝ) ≤ (π / α) ^ 12 := one_le_pow₀ (by linarith [hqa.1])
    have hne1 : t ≠ π / α := ne_of_lt (by linarith [hqa.1, ht.2])
    have hne2 : t ≠ (π / α)⁻¹ := by
      have hinv : (π / α)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith [hqa.1])
      exact ne_of_gt (by linarith [ht.1])
    simp only [gaussianDualLaplaceKernel]
    rw [leechDualKernelReg_of_ne hne1 hne2]
    exact hk.trans (le_mul_of_one_le_left (hB.le.trans hk) h1)
  have hKnonneg : ∀ α ∈ Icc (π / 4) (π / 3), ∀ t : ℝ, 0 < t →
      0 ≤ gaussianDualLaplaceKernel 12 leechDualKernelReg (α, t) := fun α hα t ht =>
    gaussianDualLaplaceKernel_nonneg 12 leechDualKernelReg hKnn hα ht
  have hu2 : ∀ u ∈ Icc (7 / 8 * (2 : ℝ)) 2, 2 < u ^ 2 := fun u hu => by nlinarith [hu.1]
  have hreg : ∀ (α u : ℝ), ∀ᵐ v ∂volume.restrict (Ioi (0 : ℝ)),
      leechDualKernelReg (π / α, v) * Real.exp (-π * u ^ 2 * v) =
        leechDualKernel (π / α, v) * Real.exp (-π * u ^ 2 * v) := by
    intro α u
    filter_upwards [ae_restrict_of_ae (leechDualKernelReg_ae (π / α))] with v hv
    have hv' : leechDualKernelReg (π / α, v) = leechDualKernel (π / α, v) := hv
    rw [hv']
  have hint : ∀ α ∈ Icc (π / 4) (π / 3), ∀ u ∈ Icc (7 / 8 * (2 : ℝ)) 2,
      IntegrableOn (fun t => gaussianDualLaplaceKernel 12 leechDualKernelReg (α, t) *
        Real.exp (-Real.pi * u ^ 2 * t)) (Ioi (0 : ℝ)) volume := by
    intro α hα u hu
    have hqa := hq α hα
    exact integrableOn_gaussianDualLaplaceKernel 12 leechDualKernelReg α u
      ((integrableOn_leechDualKernel (by linarith [hqa.1]) (hq1 _ hqa) (hu2 u hu)).congr_fun_ae
        ((hreg α u).mono fun v hv => hv.symm))
  have hfactor : ∀ α ∈ Icc (π / 4) (π / 3), ∀ u ∈ Icc (7 / 8 * (2 : ℝ)) 2,
      leechSlackProfile (α, u) = 4 * Real.sin (Real.pi * u ^ 2 / 2) ^ 2 *
        ∫ t in Ioi (0 : ℝ), gaussianDualLaplaceKernel 12 leechDualKernelReg (α, t) *
          Real.exp (-Real.pi * u ^ 2 * t) := by
    intro α hα u hu
    obtain ⟨hα0, hαπ⟩ := hgood α hα
    have hu0 : 0 ≤ u := by linarith [hu.1]
    rw [integral_gaussianDualLaplaceKernel, integral_congr_ae (hreg α u),
      leechSlackProfile_eq_laplace hα0 hαπ hu0 (hu2 u hu)]
    ring
  obtain ⟨k, hk, hlower⟩ := uniform_quadratic_slack_of_laplace_lower_bounds hr (Or.inr hr2)
    leechSlackProfile (gaussianDualLaplaceKernel 12 leechDualKernelReg) hA₀
    hAlower hB hBlower hKnonneg hint hfactor
  -- the gap for the true slack
  have hcertAE : ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
      GaussianSchwartzCertificate leechSet α (leechCertFamily α) :=
    ae_certificate_of_forall_ne π fun α hα hαπ => leechCertFamily_cert H hF hα hαπ
  have hgapT := gaussian_gap_ae_of_certificates hs.le 25
    (leech_latticeRieszEnergy_ne_top (by norm_num))
    leechCertFamily hcertAE leechSlackProfile (fun α v => leechSlackProfile_norm α v)
  -- the quadratic minorant is below the slack
  have hVle : ∀ α ∈ Icc (π / 4) (π / 3), ∀ ρ : ℝ, 0 ≤ ρ →
      ENNReal.ofReal (k * quadMinorant ((2 : ℝ)) ρ) ≤
        ENNReal.ofReal (leechSlackProfile (α, ρ)) := by
    intro α hα ρ hρ
    rcases le_or_gt ((2 : ℝ)) ρ with hfar | hnear
    · have h0 : quadMinorant ((2 : ℝ)) ρ = 0 := by
        simp only [quadMinorant, max_eq_left (by linarith : (2 : ℝ) - ρ ≤ 0)]
        norm_num
      rw [h0, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
    · apply ENNReal.ofReal_le_ofReal
      set sv := ((2 : ℝ) - ρ) / (2 : ℝ) with hsv
      have hsv0 : 0 < sv := div_pos (by linarith) hr
      have hq : quadMinorant ((2 : ℝ)) ρ = min (1 / 4) (sv ^ 2) := by
        simp only [quadMinorant, max_eq_right (by linarith : (0 : ℝ) ≤ (2 : ℝ) - ρ), hsv]
      rw [hq]
      rcases le_or_gt sv (1 / 2) with hsmall | hbig
      · have hlim : Tendsto (fun t : ℝ => k * t ^ 2) (𝓝[<] sv) (𝓝 (k * sv ^ 2)) :=
          ((continuous_const.mul (continuous_pow 2)).tendsto sv).mono_left nhdsWithin_le_nhds
        have hle : k * sv ^ 2 ≤ leechSlackProfile (α, ρ) := by
          refine le_of_tendsto hlim ?_
          filter_upwards [Ioo_mem_nhdsLT hsv0] with t ht
          refine hlower t ht.1 (by linarith [ht.2]) α hα ρ hρ ?_
          have : t < ((2 : ℝ) - ρ) / (2 : ℝ) := ht.2
          rw [lt_div_iff₀ hr] at this
          linarith
        exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hk.le).trans hle
      · have hle := hlower (1 / 2) (by norm_num) le_rfl α hα ρ hρ (by
          have : (1 / 2 : ℝ) < ((2 : ℝ) - ρ) / (2 : ℝ) := hbig
          rw [lt_div_iff₀ hr] at this
          linarith)
        have : k * min (1 / 4) (sv ^ 2) ≤ k * (1 / 2) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hk.le
          exact (min_le_left _ _).trans (by norm_num)
        exact this.trans hle
  -- the measurable minorant potential
  let V : ℝ → Ambient 24 → Ambient 24 → ℝ≥0∞ := fun α x y =>
    if α ∈ Icc (π / 4) (π / 3) then ENNReal.ofReal (k * quadMinorant ((2 : ℝ)) (dist x y))
    else 0
  have hV : Measurable (fun p : ℝ × (Ambient 24 × Ambient 24) => V p.1 p.2.1 p.2.2) := by
    refine Measurable.ite (measurableSet_Icc.preimage measurable_fst) ?_ measurable_const
    exact ENNReal.measurable_ofReal.comp (continuous_const.mul ((continuous_quadMinorant _).comp
      (continuous_dist.comp (continuous_snd.fst.prodMk continuous_snd.snd)))).measurable
  have hgapV : ∀ μ : Measure (Configuration (Ambient 24)), IsProbabilityMeasure μ →
      IsStationary μ → HasIntensity μ 1 → rieszEnergy s μ ≠ ∞ →
      ∀ᵐ α ∂volume.restrict (Ioi (0 : ℝ)),
        latticePotentialEnergy leechSet (gaussianPotential α) +
          (∫⁻ c, orderedWindowEnergy (V α) c (unitWindow 24) ∂μ) ≤
          ∫⁻ c, orderedWindowEnergy (gaussianPotential α) c (unitWindow 24) ∂μ := by
    intro μ hprob hμ hρ henergy
    filter_upwards [hgapT μ hprob hμ hρ henergy] with α hα
    refine le_trans (add_le_add le_rfl (lintegral_mono fun c =>
      orderedWindowEnergy_mono_potential (fun x y => ?_) c _)) hα
    by_cases hαI : α ∈ Icc (π / 4) (π / 3)
    · simp only [V, if_pos hαI]
      exact hVle α hαI _ dist_nonneg
    · simp only [V, if_neg hαI]
      exact zero_le
  have hlowerV : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ α ∈ Icc (π / 4) (π / 3),
      ∀ x y : Ambient 24, x ≠ y → dist x y < (2 : ℝ) * (1 - t) →
        ENNReal.ofReal (k * t ^ 2) ≤ V α x y := by
    intro t ht hhalf α hα x y _ hclose
    simp only [V, if_pos hα]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hk.le
    have hd : 0 ≤ dist x y := dist_nonneg
    have hpos : 0 < (2 : ℝ) - dist x y := by nlinarith
    simp only [quadMinorant, max_eq_right hpos.le]
    apply le_min (by nlinarith)
    have h1 : t ≤ ((2 : ℝ) - dist x y) / (2 : ℝ) := by
      rw [le_div_iff₀ hr]; nlinarith
    exact pow_le_pow_left₀ ht.le h1 2
  exact ⟨rieszIntervalGapCoefficient s (π / 4) (π / 3) k,
    rieszIntervalGapCoefficient_pos hs ha hab hk,
    analyticUnitCostInput_of_gaussian_gap_interval hs ha hab hk leechSet countable_leechSet
      ((2 : ℝ)) V hV hgapV hlowerV⟩


/-- **The stationary crystallization target for the Leech lattice from the CKMRV data.** The
kernel inequalities and the bounds on the block are proved later (`leechKernelInequalities`,
`leechBlockBounds`), and so are the Fourier identities (`leechFourierIdentities`); the Leech case
of the main theorem is `leechCrystallizationTarget_holds`. -/
theorem leech_stationaryCrystallization_of_ckmrv (H : LeechKernelInequalities)
    (hF : LeechFourierIdentities) (U : LeechBlockBounds) : leechCrystallizationTarget :=
  leech_stationaryCrystallization_of_analyticInput fun s hs => by
    have hs0 : 0 < s := lt_trans (by norm_num) hs
    obtain ⟨C, hC, h⟩ := leech_analyticUnitCostInput_of_ckmrv hs0 H hF U
    exact ⟨C⁻¹, 1 / 8, (inv_pos.mpr hC).le, by norm_num, h⟩

end E8Leech
