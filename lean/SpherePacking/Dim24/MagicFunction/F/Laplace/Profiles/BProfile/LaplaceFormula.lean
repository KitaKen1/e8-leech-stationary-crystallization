-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Profiles.BProfile.TailDifference
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims
import SpherePacking.Dim24.MagicFunction.F.Laplace.B.Basic
import SpherePacking.Dim24.MagicFunction.F.Laplace.Profiles.BProfile.IntegralLemmas


/-!
# Convergent Laplace formula for `bProfile` (`u > 4`)

This file proves the convergent Laplace representation of `bProfile` in the real range `u > 4`,
rewriting the contour integrals as a Laplace transform of `ψI'` on the positive imaginary axis.

## Main statement
* `bProfile_eq_laplace_psiI`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped UpperHalfPlane Interval Topology

open Complex Filter MeasureTheory Real SchwartzMap Set
open UpperHalfPlane
open MagicFunction.Parametrisations RealIntegrals SpecialValuesAux

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


/-- Convergent Laplace formula for `bProfile` in the real range `u > 4`. -/
public theorem bProfile_eq_laplace_psiI (u : ℝ) (hu : 4 < u) :
      bProfile u =
        (-4 * (Complex.I : ℂ)) * (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
          (∫ t in Set.Ioi (0 : ℝ), ψI' ((t : ℂ) * Complex.I) * Real.exp (-Real.pi * u * t)) := by
  have hu0 : 0 ≤ u := le_trans (by linarith) (le_of_lt hu)
  have hcontExpU : Continuous fun z : ℂ => expU u z := by
    simpa using! (continuous_expU (u := u))
  have hcontγ : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by
    simpa using! (continuous_ofReal.mul continuous_const)
  -- The `135` block gives the imaginary-axis segment (`0<t<1`) with the `exp(±πiu)` coefficient.
  have h135 := LaplaceB.J₁'_add_J₃'_add_J₅'_eq_imag_axis (u := u)
  -- Rewrite the `246` block using the `ψS` rectangle identity and the `ψT` rectangle identity.
  -- Start from the factorization in terms of `Bfun = HT + I•V`.
  let w : ℂ := expU u 1
  let HT : ℂ := ∫ x in (0 : ℝ)..1, ψT' ((x : ℂ) + Complex.I) * expU u ((x : ℂ) + Complex.I)
  let V : ℂ := ∫ t in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)
  let Itail : ℂ := ∫ t in Set.Ioi (1 : ℝ), ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)
  have hψS : (∫ x in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I) * expU u ((x : ℂ) + Complex.I)) =
      (1 + w) * (Complex.I : ℂ) • V := by
    simpa [w, V] using! (ψS_rect_integral_eq_one_add_expU_one_mul_vertical (u := u) hu0)
  have hψT :
      HT =
        (Complex.I : ℂ) •
            (∫ t in Set.Ioi (1 : ℝ),
              ψT' ((0 : ℂ) + (t : ℂ) * Complex.I) *
                expU u ((0 : ℂ) + (t : ℂ) * Complex.I)) -
          (Complex.I : ℂ) •
            (∫ t in Set.Ioi (1 : ℝ),
              ψT' ((1 : ℂ) + (t : ℂ) * Complex.I) *
                expU u ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa [HT, w] using! (ψT_rect_integral_eq_I_mul_tail_diff (u := u) hu)
  -- Convert the second vertical integral using `ψT'(z+1)=ψI'(z)` and `expU(z+1)=expU(z)*w`.
  have hshift :
      (∫ t in Set.Ioi (1 : ℝ), ψT' ((1 : ℂ) + (t : ℂ) * Complex.I) * expU u ((1 : ℂ) + (t : ℂ) *
      Complex.I)) =
        w * Itail := by
    have hcongr :
        (∫ t in Set.Ioi (1 : ℝ), ψT' ((1 : ℂ) + (t : ℂ) * Complex.I) * expU u ((1 : ℂ) + (t : ℂ) *
        Complex.I)) =
          ∫ t in Set.Ioi (1 : ℝ), (ψI' ((t : ℂ) * Complex.I)) * (expU u ((t : ℂ) * Complex.I) * w)
            := by
      refine MeasureTheory.integral_congr_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have hψ :
          ψT' ((Complex.I : ℂ) * (t : ℂ) + 1) = ψI' ((Complex.I : ℂ) * (t : ℂ)) :=
        LaplaceB.ψT'_add_one_eq_ψI' (z := (Complex.I : ℂ) * (t : ℂ))
      have hexp :
          expU u ((Complex.I : ℂ) * (t : ℂ) + 1) = expU u ((Complex.I : ℂ) * (t : ℂ)) * w := by
        simpa [w] using! (expU_add_one_mul (u := u) (z := (Complex.I : ℂ) * (t : ℂ)))
      -- Rewrite everything in terms of `z = I * t` and apply the `+1` shift lemmas.
      calc
        ψT' ((1 : ℂ) + (t : ℂ) * Complex.I) * expU u ((1 : ℂ) + (t : ℂ) * Complex.I)
            =
            ψT' ((Complex.I : ℂ) * (t : ℂ) + 1) * expU u ((Complex.I : ℂ) * (t : ℂ) + 1) := by
              simp [add_comm, mul_comm]
        _ = ψI' ((Complex.I : ℂ) * (t : ℂ)) * (expU u ((Complex.I : ℂ) * (t : ℂ)) * w) := by
              simp [hψ, hexp]
        _ = ψI' ((t : ℂ) * Complex.I) * (expU u ((t : ℂ) * Complex.I) * w) := by
              simp [mul_comm]
    have hpull :
        (∫ t in Set.Ioi (1 : ℝ), ψI' ((t : ℂ) * Complex.I) * (expU u ((t : ℂ) * Complex.I) * w)) =
          (∫ t in Set.Ioi (1 : ℝ), ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) * w
            := by
      simpa [mul_assoc] using!
        (MeasureTheory.integral_mul_const (μ := volume.restrict (Set.Ioi (1 : ℝ)))
          (f := fun t : ℝ => ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) w)
    calc
      (∫ t in Set.Ioi (1 : ℝ), ψT' ((1 : ℂ) + (t : ℂ) * Complex.I) * expU u ((1 : ℂ) + (t : ℂ) *
      Complex.I)) =
          (∫ t in Set.Ioi (1 : ℝ), ψI' ((t : ℂ) * Complex.I) * (expU u ((t : ℂ) * Complex.I) *
          w)) := hcongr
      _ = (∫ t in Set.Ioi (1 : ℝ), ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) *
      Complex.I)) * w := hpull
      _ = w * Itail := by simp [Itail, mul_comm]
  -- Express `HT + I•V = -I*(w-1)*Itail` by eliminating `ψS` using `ψI = ψS + ψT` on the tail.
  have htailI :
      Itail = (∫ t in Set.Ioi (1 : ℝ), ψS' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) +
              (∫ t in Set.Ioi (1 : ℝ), ψT' ((0 : ℂ) + (t : ℂ) * Complex.I) * expU u ((t : ℂ) *
              Complex.I))
                := by
    -- pointwise `ψI' = ψS' + ψT'` on the upper half-plane
    have hcongr :
        (∫ t in Set.Ioi (1 : ℝ), ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) =
          ∫ t in Set.Ioi (1 : ℝ),
            (ψS' ((t : ℂ) * Complex.I) + ψT' ((0 : ℂ) + (t : ℂ) * Complex.I)) * expU u ((t : ℂ) *
            Complex.I)
              := by
      refine MeasureTheory.integral_congr_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_trans (by norm_num) ht
      have hsum' :
          ψI' ((t : ℂ) * Complex.I) = ψS' ((t : ℂ) * Complex.I) + ψT' ((t : ℂ) * Complex.I) :=
        ψI'_eq_ψS'_add_ψT' (t := t) ht0
      simp [hsum', zero_add]
    -- Split the integral using linearity (needs integrability of each term).
    have hIntS :
        Integrable (fun t : ℝ => ψS' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I))
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
      have hf :
          Integrable (fun t : ℝ => ψS' (t * Complex.I)) (volume.restrict (Set.Ioi (1 : ℝ))) := by
        simpa [IntegrableOn] using! SpherePacking.Dim24.PsiSPrelims.integrableOn_ψS'_vertical_left
      have hg :
          AEStronglyMeasurable (fun t : ℝ => expU u (t * Complex.I)) (volume.restrict (Set.Ioi (1 :
          ℝ)))
            := by
        have : Continuous fun t : ℝ => expU u (t * Complex.I) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using! hcontExpU.comp hcontγ
        exact this.aestronglyMeasurable
      have hbound :
          ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi (1 : ℝ))), ‖expU u (t * Complex.I)‖ ≤ 1 := by
        refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        have ht0 : 0 ≤ (t * Complex.I).im := by
          have : 0 ≤ t := le_of_lt (lt_of_lt_of_le (by norm_num) (le_of_lt ht))
          simpa using! this
        exact norm_expU_le_one (u := u) hu0 (z := t * Complex.I) ht0
      simpa [mul_assoc] using! (hf.mul_bdd hg hbound)
    have hIntT :
        Integrable (fun t : ℝ => ψT' (t * Complex.I) * expU u (t * Complex.I))
          (volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [IntegrableOn] using! (integrableOn_ψT'_vertical_left_mul_expU (u := u) hu)
    -- distribute and split the integral
    calc
      Itail = ∫ t in Set.Ioi (1 : ℝ), (ψS' ((t : ℂ) * Complex.I) + ψT' ((0 : ℂ) + (t : ℂ) *
      Complex.I)) * expU u ((t : ℂ) * Complex.I)
        := by
        simpa [Itail] using! hcongr
      _ = (∫ t in Set.Ioi (1 : ℝ), ψS' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) +
            ∫ t in Set.Ioi (1 : ℝ), ψT' ((0 : ℂ) + (t : ℂ) * Complex.I) * expU u ((t : ℂ) *
            Complex.I)
              := by
          -- rewrite the integrand as a sum and apply `integral_add` on the restricted measure
          have hAdd :=
            (MeasureTheory.integral_add (μ := volume.restrict (Set.Ioi (1 : ℝ))) hIntS hIntT)
          simpa [add_mul, zero_add, add_assoc, add_left_comm, add_comm] using! hAdd
  -- Assemble `bProfile u = (J135) + (J246)` into `I*(w+w⁻¹-2)*∫ ψI(i t) e^{-π u t}`.
  -- For now, keep the coefficient in terms of `w` and convert (postTransparency := .instances) at the end using the trig lemma from
  -- `LaplaceA`.
  have hcoeff : (w + w⁻¹ - (2 : ℂ)) = (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
      Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) := by
    -- `w = expU u 1 = exp(π i u)` and `w⁻¹ = expU u (-1) = exp(-π i u)`.
    have hw : w = Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) := by
      simp [w, expU, mul_left_comm, mul_comm]
    have hwInv : w⁻¹ = Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) := by
      -- `exp(-z) = (exp z)⁻¹`.
      simpa [hw] using! (Complex.exp_neg (((Real.pi * u : ℝ) : ℂ) * Complex.I)).symm
    -- Rewrite `w⁻¹` first to avoid rewriting it into `(exp ...)⁻¹`.
    rw [hwInv, hw]
  have hw0 : w ≠ 0 := by simp [w, expU]
  -- Rewrite the segment identity in terms of `w` and the explicit imaginary-axis integrand.
  let V0 : ℂ :=
    ∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)
  have hV0 :
      (∫ t in (0 : ℝ)..1, ψI' (z₅' t) * expU u (z₅' t)) = V0 := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
    have hz5 : z₅' t = (t : ℂ) * Complex.I := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₅'_eq_of_mem (t := t) htIcc)
    simp [hz5, expU, mul_left_comm, mul_comm]
  have h135' : J₁' u + J₃' u + J₅' u = (Complex.I : ℂ) * ((w + w⁻¹ - (2 : ℂ)) * V0) := by
    -- Convert the coefficient to `w + w⁻¹ - 2` and rewrite the segment integral.
    -- Rewrite the segment integral to `V0`.
    calc
      J₁' u + J₃' u + J₅' u =
          (Complex.I : ℂ) *
            ((Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
                    Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
                (∫ t in (0 : ℝ)..1, ψI' (z₅' t) * expU u (z₅' t))) := by
          simpa using! h135
      _ = (Complex.I : ℂ) * ((w + w⁻¹ - (2 : ℂ)) * V0) := by
          simp [hcoeff, hV0, mul_assoc]
  -- Factor the `246` block (imported from `SpecialValuesAux`) and rewrite it as an imaginary-axis
  -- tail.
  have h246factor :
      J₂' u + J₄' u + J₆' u =
        (w⁻¹ - 1) * (HT + (Complex.I • V)) := by
    -- `SpecialValuesAux.J₂'_J₄'_J₆'_factor` uses its own `expU`; unfold both definitions.
    exact J₂'_J₄'_J₆'_factor u hu0
  -- Use `Itail = V + VT` (where `VT` is the `ψT` vertical piece) to eliminate `V` from `HT + I•V`.
  let VT : ℂ :=
    ∫ t in Set.Ioi (1 : ℝ), ψT' ((0 : ℂ) + (t : ℂ) * Complex.I) * expU u ((0 : ℂ) + (t : ℂ) *
    Complex.I)
  have hVT : VT = Itail - V := by
    have htailI' : Itail = V + VT := by
      simpa [V, VT, zero_add, add_assoc, mul_assoc, mul_left_comm, mul_comm] using! htailI
    exact Eq.symm (sub_eq_of_eq_add' htailI')
  have hHT : HT = (Complex.I : ℂ) • VT - (Complex.I : ℂ) • (w * Itail) := by
    calc
      HT =
          (Complex.I : ℂ) • VT -
            (Complex.I : ℂ) •
              (∫ t in Set.Ioi (1 : ℝ),
                  ψT' ((1 : ℂ) + (t : ℂ) * Complex.I) * expU u ((1 : ℂ) + (t : ℂ) * Complex.I))
                    := by
            simpa [VT] using! hψT
      _ = (Complex.I : ℂ) • VT - (Complex.I : ℂ) • (w * Itail) := by
            simp [hshift]
  have hBfun : HT + (Complex.I : ℂ) • V = (Complex.I : ℂ) • ((1 - w) * Itail) := by
      -- Substitute `HT = I•VT - I•(w*Itail)` and `VT = Itail - V`, then cancel the `I•V` terms.
      calc
        HT + (Complex.I : ℂ) • V
            = ((Complex.I : ℂ) • VT - (Complex.I : ℂ) • (w * Itail)) + (Complex.I : ℂ) • V := by
                simp [hHT]
        _ = ((Complex.I : ℂ) • (Itail - V) - (Complex.I : ℂ) • (w * Itail)) + (Complex.I : ℂ) • V
          := by
                simp [hVT]
        _ = (Complex.I : ℂ) • ((1 - w) * Itail) := by
                -- Switch to multiplication in `ℂ` and simplify.
                simp [smul_eq_mul, sub_eq_add_neg, mul_add, add_mul,
                  add_left_comm, add_comm]
  have h246' : J₂' u + J₄' u + J₆' u = (Complex.I : ℂ) * ((w + w⁻¹ - (2 : ℂ)) * Itail) := by
    have hww : (w⁻¹ - 1) * (1 - w) = (w + w⁻¹ - (2 : ℂ)) := by
      calc
        (w⁻¹ - 1) * (1 - w) = w⁻¹ * 1 - w⁻¹ * w - 1 * 1 + 1 * w := by ring
        _ = w⁻¹ - 1 - 1 + w := by simp [hw0, sub_eq_add_neg, add_left_comm, add_comm]
        _ = w + w⁻¹ - (2 : ℂ) := by ring
    have hwwTail : ((w⁻¹ - 1) * (1 - w)) * Itail = (w + w⁻¹ - (2 : ℂ)) * Itail := by
      simpa [mul_assoc] using! congrArg (fun z : ℂ => z * Itail) hww
    calc
      J₂' u + J₄' u + J₆' u = (w⁻¹ - 1) * (HT + (Complex.I • V)) := h246factor
      _ = (w⁻¹ - 1) * ((Complex.I : ℂ) • ((1 - w) * Itail)) := by
            simpa using! congrArg (fun x : ℂ => (w⁻¹ - 1) * x) hBfun
      _ = (Complex.I : ℂ) * (((w⁻¹ - 1) * (1 - w)) * Itail) := by
            simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = (Complex.I : ℂ) * ((w + w⁻¹ - (2 : ℂ)) * Itail) := by
            simp [hwwTail]
  -- Combine the two blocks into a single imaginary-axis integral.
  have hsum :
      bProfile u = (Complex.I : ℂ) * ((w + w⁻¹ - (2 : ℂ)) *
        (V0 + Itail)) := by
    dsimp [bProfile, RealIntegrals.b']
    have hgrp :
        J₁' u + J₂' u + J₃' u + J₄' u + J₅' u + J₆' u =
          (J₁' u + J₃' u + J₅' u) + (J₂' u + J₄' u + J₆' u) := by
      ac_rfl
    rw [hgrp, h135', h246']
    simp [mul_add]
  have hIall :
      (∫ t in Set.Ioi (0 : ℝ), ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) =
        V0 + Itail := by
    simpa [V0, Itail] using! (integral_Ioi_psiI'_expU_eq_interval_add_Ioi_one (u := u) hu0 hu)
  have hIallReal :
      (∫ t in Set.Ioi (0 : ℝ), ψI' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) =
        ∫ t in Set.Ioi (0 : ℝ), ψI' ((t : ℂ) * Complex.I) * Real.exp (-Real.pi * u * t) := by
    simpa using! (integral_Ioi_psiI'_expU_eq_real_exp (u := u))
  -- Put everything together: convert (postTransparency := .instances) the coefficient to `-4*sin^2` and use `hIall`/`hIallReal`.
  have hcoeffSin :
      (w + w⁻¹ - (2 : ℂ)) = -((4 * (Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    calc
      (w + w⁻¹ - (2 : ℂ)) =
          (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) := hcoeff
      _ = -((4 * (Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) :=
          LaplaceA.exp_pi_mul_I_add_exp_neg_pi_mul_I_sub_two (u := u)
  -- Final rewrite.
  rw [hsum]
  -- Replace `V0 + Itail` by the integral on `Ioi 0`, then convert (postTransparency := .instances) `expU` to `Real.exp`.
  rw [hIall.symm]
  rw [hIallReal]
  -- simplify the coefficient and scalars
  simp [hcoeffSin, mul_assoc]
  ring


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile
