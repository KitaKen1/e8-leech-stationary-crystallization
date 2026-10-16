import E8Leech.E8KernelGrowthNearOne

/-!
# Uniform bounds for the Leech cusp coefficients near the self-dual parameter

The radial profile at zero is exactly the nongrowing cusp slope. Gaussian
duality bounds this coefficient below by the contribution of one shortest
Leech vector. Continuity extends the bound to the self-dual parameter q=1.
In particular the truncated kernel has a uniformly positive asymptotic slope
on every compact positive imaginary interval, including intervals through 1.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Set Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold

theorem continuous_leechMinusCusp (k : Fin 4) :
    Continuous (fun τ : ℍ => leechMinusCusp τ k) := by
  have h4 := ModularFormClass.continuous ModularForm.E₄
  have h6 := ModularFormClass.continuous ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hJ := continuous_kleinModularJ
  have hψ₁ := (mdifferentiable_ckmrvPsiBasis 1).continuous
  have hψ₂ := (mdifferentiable_ckmrvPsiBasis 2).continuous
  fin_cases k <;> dsimp [leechMinusCusp, leechMinusNZeroC, leechMinusGamma,
    leechMinusBeta, leechMinusAlpha] <;> fun_prop

theorem continuous_leechPlusCusp (k : Fin 4) :
    Continuous (fun τ : ℍ => leechPlusCusp τ k) := by
  have h4 := ModularFormClass.continuous ModularForm.E₄
  have h6 := ModularFormClass.continuous ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hJ := continuous_kleinModularJ
  have hτ : Continuous (fun τ : ℍ => (τ : ℂ)) := UpperHalfPlane.continuous_coe
  have hφ₁ := (mdifferentiable_ckmrvPhiBasis 1).continuous
  have hφ₂ := (mdifferentiable_ckmrvPhiBasis 2).continuous
  fin_cases k <;> dsimp [leechPlusCusp, leechPlusM1a, leechPlusM0a, leechPlusM1c,
    leechPlusM0c, leechPlusP2, leechPlusA0, leechPlusA1, leechPlusA2] <;> fun_prop

theorem continuousOn_leechAxisCusp (s : ℂ) (k : Fin 4) :
    ContinuousOn (fun q : ℝ => leechAxisCusp s q k) (Ioi 0) :=
  (((continuous_leechPlusCusp k).add
    (continuous_const.mul (continuous_leechMinusCusp k))).div_const 2).comp_continuousOn
      continuousOn_ofComplex_I_mul

theorem continuousOn_leechAxisCusp_re (s : ℂ) (k : Fin 4) :
    ContinuousOn (fun q : ℝ => (leechAxisCusp s q k).re) (Ioi 0) :=
  Complex.continuous_re.comp_continuousOn (continuousOn_leechAxisCusp s k)

/-- The value at the origin is the coefficient of the nongrowing linear term. -/
theorem leechAxisRadialProfile_zero (s : ℂ) (q : ℝ) :
    leechAxisRadialProfile s q 0 = leechAxisCusp s q 2 := by
  have hs : Real.sinc ((0 - 2 * π) / 2) = 0 := by
    rw [show (0 - 2 * π) / 2 = -π by ring, Real.sinc_neg,
      Real.sinc_of_ne_zero Real.pi_ne_zero, Real.sin_pi, zero_div]
  unfold leechAxisRadialProfile radialProfile cuspProfileSinc
  rw [hs]
  simp

theorem leechAxisCusp_two_lower_of_ne_one {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1) :
    Real.exp (-4 * π * q) ≤ (leechAxisCusp (-1) q 2).re := by
  have hα : 0 < π / q := div_pos Real.pi_pos hq
  have hαπ : π / q ≠ π := by
    intro h
    apply hq1
    have h' := (div_eq_iff hq.ne').mp h
    nlinarith [Real.pi_pos]
  have hqα : π / (π / q) = q := by field_simp
  have hdual : π ^ 2 / (π / q) = π * q := by field_simp
  have hs := leechSlackProfile_eq hα hαπ (le_refl (0 : ℝ))
  simp only [sq, mul_zero, leechAxisRadialProfile_zero, hqα] at hs
  have horigin := leech_gaussian_slack_origin_lower hα hαπ
  have hslack : leechSlackProfile (π / q, 0) =
      gaussianKernel (π / q) (0 : Ambient 24) - (leechCertFamily (π / q) 0).re := by
    simp [leechSlackProfile, gaussianKernel]
  rw [← hslack, hs, hqα, hdual] at horigin
  obtain ⟨z, hz, hne, hnorm⟩ := leechSet_minimum_attained
  have hL := gaussian_lattice_single_vector_lower hz hne
    (leech_gaussian_lattice_energy_ne_top (mul_pos Real.pi_pos hq))
  have hL' : Real.exp (-4 * π * q) ≤
      (latticePotentialEnergy leechSet (gaussianPotential (π * q))).toReal := by
    simpa only [gaussianKernel, hnorm, show -(π * q) * (2 : ℝ) ^ 2 = -4 * π * q by ring]
      using hL
  have hpow : 0 < q ^ 12 := pow_pos hq _
  exact hL'.trans (by nlinarith only [horigin, hpow])

/-- A quantitative lower bound, including the exceptional parameter q=1. -/
theorem leechAxisCusp_two_lower {q : ℝ} (hq : 0 < q) :
    Real.exp (-4 * π * q) ≤ (leechAxisCusp (-1) q 2).re := by
  by_cases hq1 : q = 1
  · subst q
    have hf : ContinuousAt (fun q : ℝ => Real.exp (-4 * π * q)) 1 := by fun_prop
    have hg : ContinuousAt (fun q : ℝ => (leechAxisCusp (-1) q 2).re) 1 :=
      (continuousOn_leechAxisCusp_re (-1) 2).continuousAt
        (isOpen_Ioi.mem_nhds (by norm_num))
    have hx : (1 : ℝ) ∈ closure (Ioi (1 : ℝ)) := by
      rw [closure_Ioi]
      exact (le_refl (1 : ℝ))
    apply ContinuousWithinAt.closure_le (f := fun q : ℝ => Real.exp (-4 * π * q))
      (g := fun q : ℝ => (leechAxisCusp (-1) q 2).re) hx
      hf.continuousWithinAt hg.continuousWithinAt
    intro q hq
    have hq' : 1 < q := hq
    exact leechAxisCusp_two_lower_of_ne_one (by linarith only [hq']) (ne_of_gt hq')
  · exact leechAxisCusp_two_lower_of_ne_one hq hq1

theorem leechAxisCusp_two_pos {q : ℝ} (hq : 0 < q) :
    0 < (leechAxisCusp (-1) q 2).re :=
  (Real.exp_pos _).trans_le (leechAxisCusp_two_lower hq)

theorem leechAxisCusp_two_compact_lower {a b q : ℝ} (ha : 0 < a) (hq : q ∈ Icc a b) :
    Real.exp (-4 * π * b) ≤ (leechAxisCusp (-1) q 2).re := by
  apply le_trans _ (leechAxisCusp_two_lower (ha.trans_le hq.1))
  exact Real.exp_le_exp.mpr (by nlinarith only [hq.2, Real.pi_pos])

/-- All four coefficients admit a common finite bound on any positive compact interval. -/
theorem exists_leechAxisCusp_compact_bound (s : ℂ) {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, ∀ q ∈ Icc a b, ∀ k : Fin 4, ‖leechAxisCusp s q k‖ ≤ M := by
  have hc : ContinuousOn (fun q : ℝ => leechAxisCusp s q) (Icc a b) :=
    continuousOn_pi.mpr fun k => (continuousOn_leechAxisCusp s k).mono
      (fun q hq => ha.trans_le hq.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨M, fun q hq k => (norm_le_pi_norm _ k).trans (hM q hq)⟩

end E8Leech
