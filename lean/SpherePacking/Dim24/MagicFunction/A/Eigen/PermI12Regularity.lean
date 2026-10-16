/-
Regularity lemmas needed for contour deformation.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12Prelude
public import SpherePacking.Basic.Domains.WedgeSet
import SpherePacking.ForMathlib.ScalarOneFormDiffContOnCl
import SpherePacking.ForMathlib.ScalarOneFormFDeriv


/-!
# Regularity for contour deformation on `wedgeSet`

This file establishes the regularity hypotheses needed for the contour deformation step in the
`I₁/I₂` permutation argument. Concretely, we show that the 1-form `scalarOneForm (Φ₃' r)` is
`DiffContOnCl` on the wedge domain `wedgeSet`, and that its within-derivative is symmetric.

## Main statements
* `diffContOnCl_ω_wedgeSet`
* `fderivWithin_ω_wedgeSet_symm`
-/

open Complex Real

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.AFourier
open MeasureTheory Set Complex Real Filter
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold

noncomputable section

open MagicFunction.Parametrisations
open MagicFunction


lemma tendsto_Φ₃'_one_within_closure_wedgeSet (r : ℝ) :
    Tendsto (Φ₃' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Bound the exponential factor near `1`.
  let expNorm : ℂ → ℝ := fun z ↦ ‖cexp ((π : ℂ) * Complex.I * (r : ℂ) * z)‖
  have hExp : ContinuousAt expNorm (1 : ℂ) := by
    dsimp [expNorm]
    fun_prop
  let M : ℝ := expNorm (1 : ℂ) + 1
  have hMpos : 0 < M := by
    have : 0 ≤ expNorm (1 : ℂ) := norm_nonneg _
    linarith
  obtain ⟨δexp, hδexp_pos, hδexp⟩ := (Metric.continuousAt_iff.1 hExp) 1 (by norm_num)
  have hExpBound : ∀ {z : ℂ}, dist z (1 : ℂ) < δexp → expNorm z ≤ M := by
    intro z hz
    have hdist : dist (expNorm z) (expNorm (1 : ℂ)) < 1 := hδexp hz
    have habs : |expNorm z - expNorm (1 : ℂ)| < 1 := by
      simpa [Real.dist_eq] using! hdist
    have hsub : expNorm z - expNorm (1 : ℂ) < 1 := lt_of_le_of_lt (le_abs_self _) habs
    have : expNorm z < expNorm (1 : ℂ) + 1 := by linarith
    exact le_of_lt (by simpa [M] using! this)
  -- From `varphi → 0` at `i∞`, get a uniform bound `‖varphi τ‖ ≤ 1` for large `im τ`.
  have htendNorm :
      Tendsto (fun τ : ℍ => ‖varphi τ‖) UpperHalfPlane.atImInfty (𝓝 (0 : ℝ)) :=
    (tendsto_zero_iff_norm_tendsto_zero).1 VarphiBounds.tendsto_varphi_atImInfty
  have hEv_lt : ∀ᶠ τ in UpperHalfPlane.atImInfty, ‖varphi τ‖ < (1 : ℝ) :=
    htendNorm.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rcases (Filter.eventually_atImInfty).1 hEv_lt with ⟨A0, hA0⟩
  let A : ℝ := max A0 1
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hvarphiBound : ∀ τ : ℍ, A ≤ τ.im → ‖varphi τ‖ ≤ (1 : ℝ) := by
    intro τ hτ
    have : ‖varphi τ‖ < (1 : ℝ) := hA0 τ (le_trans (le_max_left _ _) hτ)
    exact le_of_lt this
  -- Choose `δpow` so that `(dist z 1)^10 * M < ε`.
  have hdist0 : Tendsto (fun z : ℂ => dist z (1 : ℂ)) (𝓝 (1 : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa using!
      ((tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 (1 : ℂ)) (𝓝 (1 : ℂ))).dist
        (tendsto_const_nhds : Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝 (1 : ℂ)) (𝓝 (1 : ℂ))))
  have hpow0 : Tendsto (fun z : ℂ => (dist z (1 : ℂ)) ^ (10 : ℕ)) (𝓝 (1 : ℂ)) (𝓝 (0 : ℝ)) := by
    have hcont : ContinuousAt (fun t : ℝ => t ^ (10 : ℕ)) (0 : ℝ) := by
      fun_prop
    simpa using! (hcont.tendsto.comp hdist0)
  have hpowM :
      Tendsto (fun z : ℂ => (dist z (1 : ℂ)) ^ (10 : ℕ) * M) (𝓝 (1 : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa using! (hpow0.mul_const M)
  have hEv_pow :
      {z : ℂ | dist ((dist z (1 : ℂ)) ^ (10 : ℕ) * M) (0 : ℝ) < ε} ∈ 𝓝 (1 : ℂ) :=
    (Metric.tendsto_nhds.1 hpowM) ε hε
  rcases Metric.mem_nhds_iff.1 hEv_pow with ⟨δpow, hδpow_pos, hδpow⟩
  have hδpow' :
      ∀ {z : ℂ}, dist z (1 : ℂ) < δpow → dist ((dist z (1 : ℂ)) ^ (10 : ℕ) * M) (0 : ℝ) < ε := by
    assumption
  -- A radius making `im (mobiusInv (z-1))` large.
  let δA : ℝ := 1 / (2 * A)
  have hδA_pos : 0 < δA := by positivity
  -- Combine all constraints.
  let δ : ℝ := min δexp (min δpow δA)
  have hδpos : 0 < δ := lt_min hδexp_pos (lt_min hδpow_pos hδA_pos)
  refine ⟨δ, hδpos, ?_⟩
  intro z hzcl hdistz
  have hdist_exp : dist z (1 : ℂ) < δexp := lt_of_lt_of_le hdistz (min_le_left _ _)
  have hdist_pow : dist z (1 : ℂ) < δpow :=
    lt_of_lt_of_le hdistz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdist_A : dist z (1 : ℂ) < δA :=
    lt_of_lt_of_le hdistz (le_trans (min_le_right _ _) (min_le_right _ _))
  by_cases h1 : z = (1 : ℂ)
  · subst h1
    simpa [Φ₃'] using! hε
  have hzU : z ∈ UpperHalfPlane.upperHalfPlaneSet :=
    mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one (hz := hzcl) h1
  have hzIm : 0 < z.im := hzU
  -- Prepare the wedge bounds for `w = z - 1`.
  have habs_re : |z.re - 1| ≤ z.im := closure_wedgeSet_subset_abs_re_sub_one_le_im hzcl
  set w : ℂ := z - 1
  have hw_im : w.im = z.im := by simp [w]
  have hw_im_pos : 0 < w.im := by simpa [hw_im] using! hzIm
  have hw_im_nonneg : 0 ≤ w.im := le_of_lt hw_im_pos
  have hw_abs_re : |w.re| ≤ w.im := by
    simpa [w, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using! habs_re
  -- `‖varphi' (mobiusInv w)‖ ≤ 1` for `dist z 1 < 1/(2A)`.
  have hdist_pos : 0 < dist z (1 : ℂ) := dist_pos.2 h1
  have hA_lt : A < 1 / (2 * dist z (1 : ℂ)) := by
    -- invert `dist z 1 < 1/(2A)`.
    have hdist_lt : dist z (1 : ℂ) < 1 / (2 * A) := by simpa [δA] using! hdist_A
    have hpos : 0 < dist z (1 : ℂ) := hdist_pos
    have hpos' : 0 < (1 / (2 * A) : ℝ) := by
      have : 0 < (2 * A : ℝ) := by positivity
      simpa [one_div] using! inv_pos.2 this
    have hinv : (1 / (2 * A) : ℝ)⁻¹ < (dist z (1 : ℂ))⁻¹ :=
      (inv_lt_inv₀ hpos' hpos).2 hdist_lt
    have : (2 * A : ℝ) < 1 / dist z (1 : ℂ) := by simpa [one_div] using! hinv
    have h2A : A * (2 : ℝ) < 1 / dist z (1 : ℂ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using! this
    have hA' : A < (1 / dist z (1 : ℂ)) / 2 :=
      (lt_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).2 h2A
    have hdiv : (1 / dist z (1 : ℂ)) / 2 = 1 / (2 * dist z (1 : ℂ)) := by
      field_simp [ne_of_gt hpos]
    simpa [hdiv] using! hA'
  have hw_im_le_dist : w.im ≤ dist z (1 : ℂ) := by
    have habs : |w.im| ≤ ‖w‖ := by simpa using! Complex.abs_im_le_norm w
    have : w.im ≤ ‖w‖ := by
      simpa [abs_of_nonneg hw_im_nonneg] using! habs
    simpa [w, dist_eq_norm] using! this
  have hnormSq_le : Complex.normSq w ≤ 2 * (w.im ^ 2) := by
    have hre2 : w.re ^ 2 ≤ w.im ^ 2 := by
      have habs : |w.re| ≤ |w.im| := by simpa [abs_of_nonneg hw_im_nonneg] using! hw_abs_re
      exact (sq_le_sq.2 habs)
    have hsum : w.re ^ 2 + w.im ^ 2 ≤ w.im ^ 2 + w.im ^ 2 := by
      linarith [hre2]
    have hsum' : w.re ^ 2 + w.im ^ 2 ≤ 2 * (w.im ^ 2) := by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using! hsum
    simpa [Complex.normSq, pow_two, add_assoc, add_left_comm, add_comm] using! hsum'
  have him_mobius : (mobiusInv w).im = w.im / Complex.normSq w :=
    mobiusInv_im w
  have him_lower : A ≤ (mobiusInv w).im := by
    have hw0 : w ≠ 0 :=
      sub_ne_zero.mpr h1
    have hnormSq_pos : 0 < Complex.normSq w := by
      simpa [Complex.normSq_pos] using! (Complex.normSq_pos).2 hw0
    have h1' : (1 / (2 * dist z (1 : ℂ)) : ℝ) ≤ 1 / (2 * w.im) := by
      have hpos1 : 0 < 2 * w.im := by positivity
      have hpos2 : 0 < 2 * dist z (1 : ℂ) := by positivity
      have hle : 2 * w.im ≤ 2 * dist z (1 : ℂ) := by nlinarith [hw_im_le_dist]
      exact (one_div_le_one_div_of_le hpos1 hle)
    have h2' : (1 / (2 * w.im) : ℝ) ≤ w.im / Complex.normSq w := by
      have hw_im_ne : w.im ≠ 0 := ne_of_gt hw_im_pos
      have : w.im / (2 * (w.im ^ 2)) ≤ w.im / Complex.normSq w :=
        div_le_div_of_nonneg_left hw_im_nonneg hnormSq_pos hnormSq_le
      have hrew : w.im / (2 * (w.im ^ 2)) = 1 / (2 * w.im) := by
        field_simp [hw_im_ne]
      simpa [hrew] using! this
    have : (1 / (2 * dist z (1 : ℂ)) : ℝ) ≤ w.im / Complex.normSq w := le_trans h1' h2'
    have hA_le : A ≤ (1 / (2 * dist z (1 : ℂ)) : ℝ) := le_of_lt hA_lt
    have : A ≤ w.im / Complex.normSq w := le_trans hA_le this
    simpa [him_mobius] using! this
  have hτim : 0 < (mobiusInv w).im := mobiusInv_im_pos (z := w) hw_im_pos
  have hτbound :
      ‖varphi' (mobiusInv w)‖ ≤ (1 : ℝ) := by
    have : varphi' (mobiusInv w) = varphi ⟨mobiusInv w, hτim⟩ := by simp [varphi', hτim]
    have hnorm : ‖varphi ⟨mobiusInv w, hτim⟩‖ ≤ (1 : ℝ) :=
      hvarphiBound ⟨mobiusInv w, hτim⟩ (by simpa using! him_lower)
    simpa [this] using! hnorm
  -- Bound the whole expression.
  have hexpZ : expNorm z ≤ M := hExpBound hdist_exp
  have hpow : ‖(z - 1) ^ (10 : ℕ)‖ = (dist z (1 : ℂ)) ^ (10 : ℕ) := by
    simp [dist_eq_norm, norm_pow]
  have hmain :
      ‖Φ₃' r z‖ ≤ (dist z (1 : ℂ)) ^ (10 : ℕ) * M := by
    calc
      ‖Φ₃' r z‖ =
              ‖varphi' (-1 / (z - 1))‖ * ‖(z - 1) ^ (10 : ℕ)‖ *
                ‖cexp ((π : ℂ) * I * (r : ℂ) * z)‖ := by
              simp [Φ₃']
      _ ≤ (1 : ℝ) * ‖(z - 1) ^ (10 : ℕ)‖ * expNorm z := by
            -- `‖varphi'‖ ≤ 1` and `expNorm z = ‖cexp ...‖`.
            have : ‖varphi' (-1 / (z - 1))‖ ≤ (1 : ℝ) := by
              -- `-1/(z-1) = mobiusInv (z-1)`.
              simpa [w, mobiusInv, div_eq_mul_inv] using! hτbound
            gcongr
      _ ≤ (1 : ℝ) * ‖(z - 1) ^ (10 : ℕ)‖ * M := by
            gcongr
      _ = (dist z (1 : ℂ)) ^ (10 : ℕ) * M := by
            simp [hpow]
  have hsmall' : dist ((dist z (1 : ℂ)) ^ (10 : ℕ) * M) (0 : ℝ) < ε :=
    hδpow' (z := z) hdist_pow
  have hsmall : (dist z (1 : ℂ)) ^ (10 : ℕ) * M < ε := by
    have hnonneg : 0 ≤ (dist z (1 : ℂ)) ^ (10 : ℕ) * M := by
      positivity
    have hsmall'' := hsmall'
    rw [Real.dist_eq] at hsmall''
    rw [sub_zero] at hsmall''
    rw [abs_of_nonneg hnonneg] at hsmall''
    exact hsmall''
  have : ‖Φ₃' r z‖ < ε := lt_of_le_of_lt hmain hsmall
  simpa [dist_eq_norm] using! this

lemma differentiableOn_varphi'_upper :
    DifferentiableOn ℂ varphi' UpperHalfPlane.upperHalfPlaneSet := by
  -- `varphi'` agrees with `varphi ∘ ofComplex` on `{0 < im}`.
  have hvarphiOf :
      DifferentiableOn ℂ (fun z : ℂ => varphi (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff).1 (varphi_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) varphi)
  have hEq :
      Set.EqOn varphi' (fun z : ℂ => varphi (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hz' : 0 < z.im := hz
    simp [varphi', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  simpa [UpperHalfPlane.upperHalfPlaneSet] using! hvarphiOf.congr hEq

lemma differentiableOn_Φ₃'_upper (r : ℝ) :
    DifferentiableOn ℂ (Φ₃' r) UpperHalfPlane.upperHalfPlaneSet := by
  let s : Set ℂ := UpperHalfPlane.upperHalfPlaneSet
  have hne : ∀ z ∈ s, z - 1 ≠ 0 := by
    intro z hz
    have hz_im : 0 < z.im := hz
    intro h0
    have hz1 : z = (1 : ℂ) := sub_eq_zero.mp h0
    simp_all
  have hmob : DifferentiableOn ℂ (fun z : ℂ => (-1 : ℂ) / (z - 1)) s := by
    have hsub : DifferentiableOn ℂ (fun z : ℂ => z - (1 : ℂ)) s := by fun_prop
    have hinv : DifferentiableOn ℂ (fun z : ℂ => (z - (1 : ℂ))⁻¹) s :=
      hsub.inv (by
        intro z hz
        simpa using! (hne z hz))
    have hconst : DifferentiableOn ℂ (fun _ : ℂ => (-1 : ℂ)) s := by fun_prop
    exact DifferentiableOn.fun_div hconst hsub hne
  have hmap : MapsTo (fun z : ℂ => (-1 : ℂ) / (z - 1)) s s := by
    intro z hz
    have hz_im : 0 < z.im := hz
    have hz' : 0 < (z - 1).im := by simpa using! hz_im
    have him : 0 < ((-1 : ℂ) / (z - 1)).im := by
      simpa [mobiusInv, div_eq_mul_inv] using! (mobiusInv_im_pos (z := z - 1) hz')
    simpa [UpperHalfPlane.upperHalfPlaneSet] using! him
  have hvarphi : DifferentiableOn ℂ (fun z : ℂ => varphi' ((-1 : ℂ) / (z - 1))) s :=
    (differentiableOn_varphi'_upper.comp hmob hmap)
  have hpow : DifferentiableOn ℂ (fun z : ℂ => (z - 1) ^ (10 : ℕ)) s := by
    fun_prop
  have hexp : DifferentiableOn ℂ (fun z : ℂ => cexp ((π : ℂ) * I * (r : ℂ) * z)) s := by
    fun_prop
  -- Assemble.
  have hmul' :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          varphi' ((-1 : ℂ) / (z - 1)) *
            ((z - 1) ^ (10 : ℕ) * cexp ((π : ℂ) * I * (r : ℂ) * z))) s :=
    hvarphi.mul (hpow.mul hexp)
  have hEq :
      Set.EqOn (Φ₃' r)
        (fun z : ℂ =>
          varphi' ((-1 : ℂ) / (z - 1)) *
            ((z - 1) ^ (10 : ℕ) * cexp ((π : ℂ) * I * (r : ℂ) * z))) s := by
    intro z _
    simp [Φ₃', mul_assoc]
  simpa [s] using! (hmul'.congr hEq)

lemma diffContOnCl_Φ₃'_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (Φ₃' r) wedgeSet := by
  have hdiffC : DifferentiableOn ℂ (Φ₃' r) UpperHalfPlane.upperHalfPlaneSet :=
    differentiableOn_Φ₃'_upper (r := r)
  have hdiffR : DifferentiableOn ℝ (Φ₃' r) UpperHalfPlane.upperHalfPlaneSet :=
    hdiffC.restrictScalars ℝ
  have hcontU : ContinuousOn (Φ₃' r) UpperHalfPlane.upperHalfPlaneSet := hdiffC.continuousOn
  refine ⟨?_, ?_⟩
  · exact (hdiffR.mono wedgeSet_subset_upperHalfPlaneSet)
  · intro z hzcl
    by_cases h1 : z = (1 : ℂ)
    · subst h1
      have htend : Tendsto (Φ₃' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
        simpa using! (tendsto_Φ₃'_one_within_closure_wedgeSet (r := r))
      have hval : (Φ₃' r) (1 : ℂ) = 0 := by simp [Φ₃']
      simpa [ContinuousWithinAt, hval] using! htend
    · have hzU : z ∈ UpperHalfPlane.upperHalfPlaneSet :=
        mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one hzcl h1
      have hcontAt :
          ContinuousAt (Φ₃' r) z :=
        hcontU.continuousAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hzU)
      exact hcontAt.continuousWithinAt

/-- Regularity of the 1-form `scalarOneForm (Φ₃' r)` on the wedge domain `wedgeSet`. -/
public lemma diffContOnCl_ω_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (scalarOneForm (Φ₃' r)) wedgeSet :=
  ForMathlib.diffContOnCl_scalarOneForm (s := wedgeSet) (diffContOnCl_Φ₃'_wedgeSet r)

/-- Symmetry of the within-derivative of `scalarOneForm (Φ₃' r)` on `wedgeSet`. -/
public lemma fderivWithin_ω_wedgeSet_symm (r : ℝ) :
    ∀ x ∈ wedgeSet, ∀ u ∈ tangentConeAt ℝ wedgeSet x, ∀ v ∈ tangentConeAt ℝ wedgeSet x,
      fderivWithin ℝ (scalarOneForm (Φ₃' r)) wedgeSet x u v =
        fderivWithin ℝ (scalarOneForm (Φ₃' r)) wedgeSet x v u := by
  intro x hx u _ v _
  have hxU : x ∈ UpperHalfPlane.upperHalfPlaneSet := wedgeSet_subset_upperHalfPlaneSet hx
  have hfdiffAt : DifferentiableAt ℂ (Φ₃' r) x := by
    have hdiffC : DifferentiableOn ℂ (Φ₃' r) UpperHalfPlane.upperHalfPlaneSet :=
      differentiableOn_Φ₃'_upper (r := r)
    exact hdiffC.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hxU)
  simpa using!
    (SpherePacking.ForMathlib.fderivWithin_scalarOneForm_symm_of_isOpen
      (f := Φ₃' r) (s := wedgeSet) isOpen_wedgeSet hx (hfdiff := hfdiffAt))

end

end SpherePacking.Dim24.AFourier
