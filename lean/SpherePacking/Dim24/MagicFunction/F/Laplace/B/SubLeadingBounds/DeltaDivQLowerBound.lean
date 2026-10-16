-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.RemainderBound
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.TruncCoeffCertificate
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Aux03.Transforms
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Aux03.Integrability
public import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
public import SpherePacking.ModularForms.Delta.ImagAxis
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi1A
public import Mathlib.Analysis.Normed.Algebra.Exponential


/-!
# Lower bound for `‖Δ / q‖` on the imaginary axis

This file proves that `‖(Δ z) / q z‖` is bounded away from `0` along the imaginary axis for
`Im z ≥ 1` (equivalently, for `z = i t` with `t ≥ 1`). This lower bound is used to control
denominators in the subtract-leading Laplace continuation of the `BKernel` integral.

## Main definitions
* `q`

## Main statement
* `exists_lower_bound_norm_resToImagAxis_Ici_one`

-/

namespace SpherePacking.Dim24.LaplaceBSubLeadingBounds

noncomputable section

open scoped BigOperators Real Topology
open Complex Filter UpperHalfPlane

open AppendixA

/-- The nome `q(z) = exp(2π i z)` on `ℂ`, used in the product formula for `Δ`. -/
@[expose] public def q (z : ℂ) : ℂ := cexp (2 * π * Complex.I * z)

lemma Delta_div_q_eq_boundedfactor :
    (fun z : ℍ => (Δ z) / q (z : ℂ)) =
      fun z : ℍ => ∏' n : ℕ, (1 - cexp (2 * (π : ℂ) * Complex.I * (↑n + 1) * (z : ℂ))) ^ 24 := by
  funext z
  simp [Δ, q, div_eq_mul_inv, mul_left_comm, mul_comm]

lemma continuous_Delta_div_q : Continuous fun z : ℍ => (Δ z) / q (z : ℂ) := by
  have hΔ : Continuous (Δ : ℍ → ℂ) := SpecialValuesAux.continuous_Δ
  have hq : Continuous fun z : ℍ => q (z : ℂ) := by
    unfold q
    fun_prop
  have hq_ne : ∀ z : ℍ, q (z : ℂ) ≠ 0 := by
    intro z
    simp [q]
  simpa [div_eq_mul_inv] using! hΔ.mul (Continuous.inv₀ hq hq_ne)

/-- There is a uniform `c > 0` such that `c ≤ ‖(Δ/q)(i t)‖` for all `t ≥ 1`. -/
public lemma exists_lower_bound_norm_resToImagAxis_Ici_one :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t → c ≤ ‖(fun z : ℍ => (Δ z) / q (z : ℂ)).resToImagAxis t‖ := by
  let F : ℍ → ℂ := fun z : ℍ => (Δ z) / q (z : ℂ)
  have hF : Tendsto F atImInfty (𝓝 (1 : ℂ)) := by
    simpa [F, q, SpecialValuesVarphi₁Limits.q] using! SpecialValuesVarphi₁Limits.tendsto_Delta_div_q
  have hAxis : Tendsto F.resToImagAxis atTop (𝓝 (1 : ℂ)) :=
    Function.tendsto_resToImagAxis_atImInfty (F := F) (l := (1 : ℂ)) hF
  have hEv :
      ∀ᶠ t : ℝ in atTop, ‖F.resToImagAxis t - (1 : ℂ)‖ < (1 / 2 : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      hAxis.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)))
  rcases (eventually_atTop.1 hEv) with ⟨A0, hA0⟩
  let A : ℝ := max A0 1
  -- Lower bound on `[1,A]` via bounding the inverse norm on the compact interval.
  have hF0 : ∀ z : ℍ, F z ≠ 0 := by
    intro z
    exact div_ne_zero (Δ_ne_zero z) (by simp [q])
  have hcont_comp : Continuous fun x : Set.Icc (1 : ℝ) A => F.resToImagAxis (x : ℝ) := by
    have hcont_on : ContinuousOn F.resToImagAxis (Set.Icc (1 : ℝ) A) :=
      (Function.continuousOn_resToImagAxis_Ici_one_of (F := F) continuous_Delta_div_q).mono
        fun _ ht => ht.1
    simpa [continuousOn_iff_continuous_restrict] using! hcont_on
  have hnonzero : ∀ x : Set.Icc (1 : ℝ) A, F.resToImagAxis (x : ℝ) ≠ 0 := by
    intro x
    have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) x.property.1
    exact Function.resToImagAxis_ne_zero_of_pos (F := F) hF0 hx0
  let G : Set.Icc (1 : ℝ) A → ℂ := fun x => (F.resToImagAxis (x : ℝ))⁻¹
  have hcont_G : Continuous G := by
    simpa [G] using! (Continuous.inv₀ hcont_comp hnonzero)
  have hcomp : IsCompact (Set.range G) := isCompact_range hcont_G
  have hbound : Bornology.IsBounded (Set.range G) := hcomp.isBounded
  rcases hbound.subset_closedBall (c := (0 : ℂ)) with ⟨M, hM⟩
  let M' : ℝ := max M 1
  have hM'pos : 0 < M' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hG_le : ∀ x : Set.Icc (1 : ℝ) A, ‖G x‖ ≤ M' := by
    intro x
    have hx : G x ∈ Set.range G := ⟨x, rfl⟩
    have hx' : G x ∈ Metric.closedBall (0 : ℂ) M := hM hx
    have hnorm_le : ‖G x‖ ≤ M := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using! hx'
    exact le_trans hnorm_le (le_max_left _ _)
  have hSmall :
      ∀ t : ℝ, t ∈ Set.Icc (1 : ℝ) A → (1 / M') ≤ ‖F.resToImagAxis t‖ := by
    intro t htIcc
    let x : Set.Icc (1 : ℝ) A := ⟨t, htIcc⟩
    have hInv_le : ‖(F.resToImagAxis t)⁻¹‖ ≤ M' := by
      simpa [G] using! hG_le x
    have hInv_pos : 0 < ‖(F.resToImagAxis t)⁻¹‖ := by
      have : (F.resToImagAxis t)⁻¹ ≠ 0 := inv_ne_zero (by simpa using! hnonzero x)
      exact norm_pos_iff.2 this
    have hone :
        (1 / M') ≤ (1 / ‖(F.resToImagAxis t)⁻¹‖) := by
      have := one_div_le_one_div_of_le hInv_pos hInv_le
      simpa [one_div] using! this
    have honeEq : (1 / ‖(F.resToImagAxis t)⁻¹‖) = ‖F.resToImagAxis t‖ := by
      simp [norm_inv]
    exact le_of_le_of_eq hone honeEq
  have hLarge : ∀ t : ℝ, A ≤ t → (1 / 2 : ℝ) ≤ ‖F.resToImagAxis t‖ := by
    intro t htA
    have htA0 : A0 ≤ t := le_trans (le_max_left _ _) htA
    have hball : ‖F.resToImagAxis t - (1 : ℂ)‖ < (1 / 2 : ℝ) := hA0 t htA0
    have hsub : (1 : ℝ) - ‖F.resToImagAxis t‖ ≤ ‖(1 : ℂ) - F.resToImagAxis t‖ := by
      simpa using! (norm_sub_norm_le (1 : ℂ) (F.resToImagAxis t))
    have hsub' : (1 : ℝ) - ‖F.resToImagAxis t‖ ≤ ‖F.resToImagAxis t - (1 : ℂ)‖ := by
      simpa [norm_sub_rev] using! hsub
    linarith
  -- Global lower bound on `t ≥ 1`.
  refine ⟨min (1 / M') (1 / 2), by
    have hpos1 : 0 < (1 / M' : ℝ) := by positivity [hM'pos]
    have hpos2 : 0 < (1 / 2 : ℝ) := by norm_num
    exact lt_min hpos1 hpos2, ?_⟩
  intro t ht1
  rcases le_total t A with htA | hAt
  · have htIcc : t ∈ Set.Icc (1 : ℝ) A := ⟨ht1, htA⟩
    have hlow : (1 / M' : ℝ) ≤ ‖F.resToImagAxis t‖ := hSmall t htIcc
    exact le_trans (min_le_left _ _) hlow
  · have hlow : (1 / 2 : ℝ) ≤ ‖F.resToImagAxis t‖ := hLarge t hAt
    exact le_trans (min_le_right _ _) hlow

end

end SpherePacking.Dim24.LaplaceBSubLeadingBounds
