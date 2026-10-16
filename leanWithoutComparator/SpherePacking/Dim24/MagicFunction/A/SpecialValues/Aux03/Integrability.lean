-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Aux03.Transforms
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds


/-!
# Integrability bookkeeping on the strip `im = 1`

For the algebraic manipulations in the even-`u` special value argument, we use linearity of the
interval integral. This file provides the needed continuity and `IntervalIntegrable` facts.

## Main statements
* `SpecialValuesAux.continuous_Δ`
* `SpecialValuesAux.continuous_varphi₁`
* `SpecialValuesAux.aProfile_even_eq_periodIntegral_varphi₁`
-/


open scoped Real
open Complex Real

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

open MagicFunction.Parametrisations RealIntegrals intervalIntegral Complex MeasureTheory Set Filter
open UpperHalfPlane
open scoped Topology
open scoped UpperHalfPlane


lemma continuous_zI : Continuous zI := by
  -- `zI x = x + i`.
  simpa [zI] using! (Complex.continuous_ofReal.add continuous_const)

private lemma continuous_expU_comp (u : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    Continuous fun x : ℝ => expU u (g x) := by
  -- `expU u z = exp(π i u z)`.
  unfold expU
  fun_prop

lemma zI_ne_zero (x : ℝ) : zI x ≠ 0 := by
  intro hx
  have him : (zI x).im = 0 := by
    simpa using! (congrArg Complex.im hx)
  have : (1 : ℝ) = 0 := by
    convert (postTransparency := .instances) him using 1
    simp [zI]
  exact one_ne_zero this

lemma zI_sub_one_ne_zero (x : ℝ) : zI x - 1 ≠ 0 := by
  intro hx
  have him : (zI x - 1).im = 0 := by
    simpa using! (congrArg Complex.im hx)
  have : (1 : ℝ) = 0 := by
    -- `im (x+i-1) = 1`.
    convert (postTransparency := .instances) him using 1
    simp [zI, sub_eq_add_neg, add_im]
  exact one_ne_zero this

lemma continuous_expU_zI (u : ℝ) :
    Continuous (fun x : ℝ => expU u (zI x)) :=
  continuous_expU_comp (u := u) (g := fun x : ℝ => zI x) continuous_zI

lemma continuous_expU_zI_sub_one (u : ℝ) :
    Continuous (fun x : ℝ => expU u (zI x - 1)) := by
  have h : Continuous (fun x : ℝ => zI x - 1) := continuous_zI.sub continuous_const
  exact continuous_expU_comp (u := u) (g := fun x : ℝ => zI x - 1) h

def zH (x : ℝ) : UpperHalfPlane := ⟨zI x, zI_im_pos x⟩

def zHSubOne (x : ℝ) : UpperHalfPlane :=
  ⟨zI x - 1, by
    simp [zI, sub_eq_add_neg, add_im]⟩

lemma continuous_zH : Continuous zH := by
  -- `x ↦ ⟨zI x, _⟩` is continuous as a subtype map.
  simpa [zH] using! continuous_zI.upperHalfPlaneMk zI_im_pos

lemma continuous_zHSubOne : Continuous zHSubOne := by
  have hbase : Continuous fun x : ℝ => zI x - 1 := continuous_zI.sub continuous_const
  simpa [zHSubOne] using!
    hbase.upperHalfPlaneMk (fun x => by simp [zI, sub_eq_add_neg, add_im])

def zHS (x : ℝ) : UpperHalfPlane :=
  ⟨(-((zH x : UpperHalfPlane) : ℂ))⁻¹, (zH x).im_inv_neg_coe_pos⟩

def zHSSubOne (x : ℝ) : UpperHalfPlane :=
  ⟨(-((zHSubOne x : UpperHalfPlane) : ℂ))⁻¹, (zHSubOne x).im_inv_neg_coe_pos⟩

lemma continuous_zHS : Continuous zHS := by
  -- Continuity of `x ↦ (-(zI x))⁻¹` (no zeros along `im=1`).
  have hneg : Continuous fun x : ℝ => -((zI x : ℂ)) := continuous_zI.neg
  have hne : ∀ x : ℝ, -((zI x : ℂ)) ≠ 0 := by
    intro x
    simpa using! (neg_ne_zero.mpr (zI_ne_zero x))
  have hinv : Continuous fun x : ℝ => (-((zI x : ℂ)))⁻¹ := (Continuous.inv₀ hneg hne)
  -- Package into `ℍ`.
  exact hinv.upperHalfPlaneMk (fun x => (zH x).im_inv_neg_coe_pos)

lemma continuous_zHSSubOne : Continuous zHSSubOne := by
  have hbase : Continuous fun x : ℝ => zI x - 1 := continuous_zI.sub continuous_const
  have hneg : Continuous fun x : ℝ => -((zI x - 1 : ℂ)) := hbase.neg
  have hne : ∀ x : ℝ, -((zI x - 1 : ℂ)) ≠ 0 := by
    intro x
    simpa using! (neg_ne_zero.mpr (zI_sub_one_ne_zero x))
  have hinv : Continuous fun x : ℝ => (-((zI x - 1 : ℂ)))⁻¹ := (Continuous.inv₀ hneg hne)
  exact hinv.upperHalfPlaneMk (fun x => (zHSubOne x).im_inv_neg_coe_pos)

lemma continuous_F_zI (u : ℝ) : Continuous (fun x : ℝ => F u (zI x)) := by
  -- Rewrite `varphi'(-1/(zI x))` as `varphi (zHS x)` and use continuity.
  have hvarphi : Continuous fun x : ℝ => varphi (zHS x) :=
    (VarphiExpBounds.continuous_varphi.comp continuous_zHS)
  have hpow : Continuous fun x : ℝ => (zI x) ^ (10 : ℕ) := (continuous_zI.pow 10)
  have hexp : Continuous fun x : ℝ => expU u (zI x) := continuous_expU_zI (u := u)
  have hcont :
      Continuous (fun x : ℝ => (varphi (zHS x)) * (zI x) ^ (10 : ℕ) * expU u (zI x)) :=
    (hvarphi.mul hpow).mul hexp
  -- Identify this function with `F u (zI x)`.
  have hEq :
      (fun x : ℝ => F u (zI x)) =
        fun x : ℝ => (varphi (zHS x)) * (zI x) ^ (10 : ℕ) * expU u (zI x) := by
    funext x
    -- `(-1)/(zI x) = (zHS x : ℂ)` and `varphi'` agrees with `varphi` on `ℍ`.
    have hcoe : ((zHS x : UpperHalfPlane) : ℂ) = (-1 : ℂ) / (zI x) := by
      simp [zHS, zH, div_eq_mul_inv]
    have hvar :
        varphi' ((-1 : ℂ) / (zI x)) = varphi (zHS x) := by
      -- Rewrite `(-1)/z` to the coercion of `zHS x`.
      simpa [hcoe] using! (varphi'_coe_upperHalfPlane (z := (zHS x : UpperHalfPlane)))
    -- Unfold `F` and simplify.
    simp [F, hvar]
  simpa [hEq] using! hcont

lemma continuous_F_zI_sub_one (u : ℝ) :
    Continuous (fun x : ℝ => F u (zI x - 1)) := by
  have hvarphi : Continuous fun x : ℝ => varphi (zHSSubOne x) :=
    (VarphiExpBounds.continuous_varphi.comp continuous_zHSSubOne)
  have hpow : Continuous (fun x : ℝ => (zI x - 1) ^ (10 : ℕ)) := by
    have hbase : Continuous (fun x : ℝ => zI x - 1) := continuous_zI.sub continuous_const
    exact hbase.pow 10
  have hexp : Continuous (fun x : ℝ => expU u (zI x - 1)) :=
    continuous_expU_zI_sub_one (u := u)
  have hcont :
      Continuous (fun x : ℝ =>
        (varphi (zHSSubOne x)) * (zI x - 1) ^ (10 : ℕ) * expU u (zI x - 1)) :=
    (hvarphi.mul hpow).mul hexp
  have hEq :
      (fun x : ℝ => F u (zI x - 1)) =
        fun x : ℝ =>
          (varphi (zHSSubOne x)) * (zI x - 1) ^ (10 : ℕ) * expU u (zI x - 1) := by
    funext x
    have hcoe : ((zHSSubOne x : UpperHalfPlane) : ℂ) = (-1 : ℂ) / (zI x - 1) := by
      -- `zHSSubOne x` is `-(zI x - 1)` inverted; rewrite to `(-1)/(zI x - 1)`.
      have h1 : ((zHSSubOne x : UpperHalfPlane) : ℂ) = (-(zI x - 1 : ℂ))⁻¹ := by
        simp [zHSSubOne, zHSubOne]
      calc
        ((zHSSubOne x : UpperHalfPlane) : ℂ)
            = (-(zI x - 1 : ℂ))⁻¹ := h1
        _ = -((zI x - 1 : ℂ)⁻¹) := by
              -- Avoid rewriting `-(zI x - 1)` into `1 - zI x`.
              simpa using! (inv_neg (a := (zI x - 1 : ℂ)))
        _ = (-1 : ℂ) / (zI x - 1) := by simp [div_eq_mul_inv]
    have hvar :
        varphi' ((-1 : ℂ) / (zI x - 1)) = varphi (zHSSubOne x) := by
      simpa [hcoe] using! (varphi'_coe_upperHalfPlane (z := (zHSSubOne x : UpperHalfPlane)))
    -- Unfold `F` and simplify.
    simp [F, hvar]
  simpa [hEq] using! hcont
 
/-- Continuity of the discriminant modular form `Δ : ℍ → ℂ`. -/
public lemma continuous_Δ : Continuous (Δ : UpperHalfPlane → ℂ) := by
  -- `Δ` is the discriminant form; we use holomorphy of `Delta` and `Delta_apply`.
  have h : Continuous (fun z : UpperHalfPlane => (Delta z : ℂ)) :=
    (Delta.holo'.continuous)
  simpa [Delta_apply] using! h

/-- Continuity of `varphi₁ : ℍ → ℂ`. -/
public lemma continuous_varphi₁ : Continuous (varphi₁ : UpperHalfPlane → ℂ) := by
  -- Build continuity from the defining formula
  -- (a rational expression in holomorphic modular forms).
  have hE2 : Continuous (E₂ : UpperHalfPlane → ℂ) := E₂_holo'.continuous
  have hE4 : Continuous (E₄ : UpperHalfPlane → ℂ) := E₄.holo'.continuous
  have hE6 : Continuous (E₆ : UpperHalfPlane → ℂ) := E₆.holo'.continuous
  have hΔ : Continuous (Δ : UpperHalfPlane → ℂ) := continuous_Δ
  have hΔ2 : Continuous (fun z : UpperHalfPlane => (Δ z) ^ (2 : ℕ)) := hΔ.pow 2
  have hΔ2_ne : ∀ z : UpperHalfPlane, (Δ z) ^ (2 : ℕ) ≠ 0 := by
    intro z
    exact pow_ne_zero 2 (Δ_ne_zero z)
  have hΔ2inv : Continuous (fun z : UpperHalfPlane => ((Δ z) ^ (2 : ℕ))⁻¹) :=
    (Continuous.inv₀ hΔ2 hΔ2_ne)
  -- First quotient term.
  have hnum1 : Continuous (fun z : UpperHalfPlane => (E₆ z) * (E₄ z) ^ (2 : ℕ)) :=
    hE6.mul (hE4.pow 2)
  have hdiv1 :
      Continuous (fun z : UpperHalfPlane =>
        ((E₆ z) * (E₄ z) ^ (2 : ℕ)) / (Δ z) ^ (2 : ℕ)) := by
    refine (hnum1.mul hΔ2inv).congr (by intro z; simp [div_eq_mul_inv, mul_assoc])
  -- Second quotient term.
  have hpoly :
      Continuous (fun z : UpperHalfPlane =>
        ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ))) := by
    have h1 : Continuous (fun z : UpperHalfPlane => ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ))) :=
      continuous_const.mul (hE4.pow 3)
    have h2 : Continuous (fun z : UpperHalfPlane => ((25 : ℂ) * (E₆ z) ^ (2 : ℕ))) :=
      continuous_const.mul (hE6.pow 2)
    simpa [add_assoc] using! h1.add h2
  have hnum2 :
      Continuous (fun z : UpperHalfPlane =>
        (E₂ z) * (((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)))) :=
    hE2.mul hpoly
  have hdiv2 :
      Continuous (fun z : UpperHalfPlane =>
        (E₂ z * (((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)))) /
          (Δ z) ^ (2 : ℕ)) := by
    refine (hnum2.mul hΔ2inv).congr (by intro z; simp [div_eq_mul_inv, mul_assoc])
  -- Assemble the definition.
  have hterm1 :
      Continuous (fun z : UpperHalfPlane =>
        (- (6 * Complex.I) / π) * 48 *
          ((E₆ z) * (E₄ z) ^ (2 : ℕ)) / (Δ z) ^ (2 : ℕ)) := by
    have hconst :
        Continuous (fun _z : UpperHalfPlane => (- (6 * Complex.I) / π) * (48 : ℂ)) :=
      continuous_const
    refine (hconst.mul hdiv1).congr (by intro z; simp [mul_div_assoc, mul_assoc])
  have hterm2 :
      Continuous (fun z : UpperHalfPlane =>
        (12 * Complex.I) / π *
            (E₂ z * ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ))) /
          (Δ z) ^ (2 : ℕ)) := by
    have hconst : Continuous (fun _z : UpperHalfPlane => (12 * Complex.I) / π) := continuous_const
    refine (hconst.mul hdiv2).congr (by intro z; simp [mul_div_assoc, mul_assoc])
  -- Unfold `varphi₁` at the function level.
  change
      Continuous (fun z : UpperHalfPlane =>
        (- (6 * Complex.I) / π) * 48 * ((E₆ z) * (E₄ z) ^ (2 : ℕ)) / (Δ z) ^ (2 : ℕ) -
          (12 * Complex.I) / π *
              (E₂ z * ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ))) /
            (Δ z) ^ (2 : ℕ))
  exact hterm1.sub hterm2

lemma continuous_f0_zI (u : ℝ) : Continuous (fun x : ℝ => f0 u (zI x)) := by
  -- Along `im=1`, `varphi' (zI x) = varphi (zH x)`.
  have hvarphi : Continuous fun x : ℝ => varphi (zH x) :=
    (VarphiExpBounds.continuous_varphi.comp continuous_zH)
  have hpoly : Continuous fun x : ℝ => (((2 : ℂ) * (zI x)) - 1 : ℂ) :=
    (continuous_const.mul continuous_zI).sub continuous_const
  have hexp : Continuous fun x : ℝ => expU u (zI x) := continuous_expU_zI (u := u)
  have hcont :
      Continuous (fun x : ℝ =>
        (varphi (zH x)) * (((2 : ℂ) * (zI x)) - 1) * expU u (zI x)) :=
    (hvarphi.mul hpoly).mul hexp
  refine Continuous.congr hcont ?_
  intro x
  simp [f0, zH]

lemma continuous_varphi₁'_mul_expU_zI (u : ℝ) :
    Continuous (fun x : ℝ => varphi₁' (zI x) * expU u (zI x)) := by
  have hvarphi1 : Continuous fun x : ℝ => varphi₁ (zH x) :=
    (continuous_varphi₁.comp continuous_zH)
  have hexp : Continuous fun x : ℝ => expU u (zI x) := continuous_expU_zI (u := u)
  have hcont : Continuous fun x : ℝ => (varphi₁ (zH x)) * expU u (zI x) := hvarphi1.mul hexp
  simpa

/-- For even `u`, rewrite `aProfile u` as a single period integral of `varphi₁` on the line
`im = 1`. -/
public lemma aProfile_even_eq_periodIntegral_varphi₁ (u : ℝ) (hu : expU u 1 = 1) (hu0 : 0 ≤ u) :
    aProfile u =
      ∫ x : ℝ in (0 : ℝ)..1,
        (varphi₁ ⟨(x : ℂ) + Complex.I, by simp⟩) *
          Complex.exp (Real.pi * Complex.I * (u : ℂ) * ((x : ℂ) + Complex.I)) := by
  -- Reduce `aProfile` to `I₂'+I₄'+I₆'`.
  have ha : aProfile u = I₂' u + I₄' u + I₆' u := aProfile_even_reduction (u := u) hu
  -- Rewrite `I₂'` and `I₄'` as horizontal integrals of `F`.
  have hI2 : I₂' u = ∫ x : ℝ in (0 : ℝ)..1, F u (zI x) := by
    -- `I₂' u = (expU u 1)⁻¹ * ∫ F`, and `expU u 1 = 1`.
    simp [I₂'_as_F, hu]
  have hI4 : I₄' u = -∫ x : ℝ in (0 : ℝ)..1, F u (zI x - 1) := by
    -- `I₄' u = -(expU u 1) * ∫ F(z-1)`, and `expU u 1 = 1`.
    simp [I₄'_as_F, hu]
  -- Combine and use the strip cancellation for `f0`.
  have hsum :
      I₂' u + I₄' u + I₆' u =
        ∫ x : ℝ in (0 : ℝ)..1, (varphi₁' (zI x) * expU u (zI x)) := by
    -- Rewrite the sum using `hI2`, `hI4`.
    rw [hI2, hI4]
    -- Combine the two horizontal pieces into a single integral of the difference.
    have hI24 :
        (∫ x : ℝ in (0 : ℝ)..1, F u (zI x)) + (-∫ x : ℝ in (0 : ℝ)..1, F u (zI x - 1)) =
          ∫ x : ℝ in (0 : ℝ)..1, (F u (zI x) - F u (zI x - 1)) := by
      -- Use `integral_sub` (with `μ = volume`) and rewrite subtraction
      -- as addition with a negation.
      have hF : IntervalIntegrable (fun x : ℝ => F u (zI x)) volume (0 : ℝ) 1 :=
        (continuous_F_zI (u := u)).intervalIntegrable (μ := volume) 0 1
      have hG : IntervalIntegrable (fun x : ℝ => F u (zI x - 1)) volume (0 : ℝ) 1 :=
        (continuous_F_zI_sub_one (u := u)).intervalIntegrable (μ := volume) 0 1
      have hsub :=
        (intervalIntegral.integral_sub (μ := (volume : Measure ℝ))
          (f := fun x : ℝ => F u (zI x)) (g := fun x : ℝ => F u (zI x - 1)) hF hG
          (a := (0 : ℝ)) (b := (1 : ℝ)))
      -- `hsub` gives `∫ (f-g) = ∫ f - ∫ g`; rearrange.
      simpa [sub_eq_add_neg] using! hsub.symm
    -- Use the pointwise identity `F(z) - F(z-1) = f0(z) + varphi₁'(z)*expU(z)` at even `u`.
    have hdiff :
        ∀ x : ℝ, F u (zI x) - F u (zI x - 1) =
          f0 u (zI x) + varphi₁' (zI x) * expU u (zI x) := by
      intro x
      exact F_sub_F_sub_one (u := u) hu x
    -- Cancel `∫ f0 + I₆' = 0` using the strip lemma.
    have hcancel : (∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) + I₆' u = 0 :=
      f0_strip_cancel_I6 (u := u) hu hu0
    -- Rewrite the integral with `hdiff`, split the sum, and cancel.
    calc
      (∫ x : ℝ in (0 : ℝ)..1, F u (zI x)) +
          (-∫ x : ℝ in (0 : ℝ)..1, F u (zI x - 1)) + I₆' u =
        (∫ x : ℝ in (0 : ℝ)..1, (F u (zI x) - F u (zI x - 1))) + I₆' u := by
            simp [hI24]
      _ =
          (∫ x : ℝ in (0 : ℝ)..1,
              (f0 u (zI x) + varphi₁' (zI x) * expU u (zI x))) + I₆' u := by
            congr 1
            refine intervalIntegral.integral_congr ?_
            intro x hx
            simp [hdiff x]
      _ = ((∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) +
              (∫ x : ℝ in (0 : ℝ)..1, (varphi₁' (zI x) * expU u (zI x)))) + I₆' u := by
            -- Use `integral_add` with interval-integrability from continuity.
            have hf0 : IntervalIntegrable (fun x : ℝ => f0 u (zI x)) volume (0 : ℝ) 1 :=
              (continuous_f0_zI (u := u)).intervalIntegrable (μ := volume) 0 1
            have hg1 :
                IntervalIntegrable
                  (fun x : ℝ => varphi₁' (zI x) * expU u (zI x)) volume (0 : ℝ) 1 :=
              (continuous_varphi₁'_mul_expU_zI (u := u)).intervalIntegrable (μ := volume) 0 1
            have hadd :=
              (intervalIntegral.integral_add (μ := (volume : Measure ℝ))
                (f := fun x : ℝ => f0 u (zI x))
                (g := fun x : ℝ => varphi₁' (zI x) * expU u (zI x)) hf0 hg1
                (a := (0 : ℝ)) (b := (1 : ℝ)))
            -- Add the constant `I₆' u` to both sides.
            have hadd' := congrArg (fun t : ℂ => t + I₆' u) hadd
            exact hadd'
      _ = (∫ x : ℝ in (0 : ℝ)..1, (varphi₁' (zI x) * expU u (zI x))) := by
            -- Group as `(∫ f0 + I₆') + ∫ ...` and use `hcancel`.
            have hgroup :
                ((∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) +
                    (∫ x : ℝ in (0 : ℝ)..1, (varphi₁' (zI x) * expU u (zI x)))) + I₆' u =
                  ((∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) + I₆' u) +
                    (∫ x : ℝ in (0 : ℝ)..1, (varphi₁' (zI x) * expU u (zI x))) := by
              ac_rfl
            -- Apply the regrouping and cancel.
            calc
              ((∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) +
                    (∫ x : ℝ in (0 : ℝ)..1, (varphi₁' (zI x) * expU u (zI x)))) + I₆' u =
                  ((∫ x : ℝ in (0 : ℝ)..1, f0 u (zI x)) + I₆' u) +
                    (∫ x : ℝ in (0 : ℝ)..1, (varphi₁' (zI x) * expU u (zI x))) := hgroup
              _ = ∫ x : ℝ in (0 : ℝ)..1, (varphi₁' (zI x) * expU u (zI x)) := by
                  simp [hcancel]
  -- Combine with `ha` and unfold `varphi₁'`/`expU` on the line `im = 1`.
  rw [ha, hsum]
  -- On `zI x = x + i`, `varphi₁'` uses the positive-imaginary branch,
  -- and `expU` is the complex exponential.
  refine intervalIntegral.integral_congr ?_
  intro x hx
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! hx
  have hxIm : 0 < (zI x).im := zI_im_pos x
  simp [varphi₁', expU, zI]

end SpecialValuesAux

end

end SpherePacking.Dim24
