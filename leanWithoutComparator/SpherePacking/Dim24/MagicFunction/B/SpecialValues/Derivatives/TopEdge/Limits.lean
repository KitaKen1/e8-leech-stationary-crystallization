-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.TopEdge.Base


/-!
# Limit of `TopEdge` as `T → ∞`

This file contains the final limit statement `TopEdge u T → Bfun u` as `T → ∞`, derived from the
rectangle identity and the vertical limit recorded in `TopEdge.Base`.

## Main statements
* `tendsto_TopEdge`
-/

open scoped Real
open scoped Topology
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter MeasureTheory intervalIntegral
open RealIntegrals
open scoped Interval

namespace Deriv

/-- As `T → ∞`, the top-edge integral `TopEdge u T` tends to `Bfun u`. -/
public lemma tendsto_TopEdge (u0 : ℝ) (hu : expU u0 1 = 1) (hu0 : 0 ≤ u0) :
    Tendsto (fun T : ℝ => TopEdge u0 T) atTop (𝓝 (Bfun u0)) := by
  let bottom : ℂ :=
    ∫ x in (0 : ℝ)..1, ψI' ((x : ℂ) + Complex.I) * expU u0 ((x : ℂ) + Complex.I)
  let V : ℂ :=
    ∫ (t : ℝ) in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u0 (t * Complex.I)
  have hdiff :
      Tendsto (fun T : ℝ => bottom - TopEdge u0 T) atTop (𝓝 ((Complex.I : ℂ) • V)) := by
    have hvert :
        Tendsto
          (fun T : ℝ =>
            (Complex.I : ℂ) • ∫ t in (1 : ℝ)..T, ψS' (t * Complex.I) * expU u0 (t * Complex.I))
          atTop (𝓝 ((Complex.I : ℂ) • V)) :=
      (tendsto_vertical_intervalIntegral (u := u0) hu0).const_smul (Complex.I : ℂ)
    refine Tendsto.congr' ?_ hvert
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hEq := TopEdge_sub_bottom_eq_vertical (u := u0) (T := T) hu hT
    simpa [bottom, V, sub_eq_add_neg, add_assoc] using! hEq.symm
  have hTop :
      Tendsto (fun T : ℝ => TopEdge u0 T) atTop (𝓝 (bottom - (Complex.I : ℂ) • V)) := by
    have hconst : Tendsto (fun _ : ℝ => bottom) atTop (𝓝 bottom) := tendsto_const_nhds
    have h := hconst.sub hdiff
    have hrew : (fun T : ℝ => bottom - (bottom - TopEdge u0 T)) = fun T : ℝ => TopEdge u0 T := by
      funext T; ring
    simpa [hrew] using! h
  have hbottom :
      bottom =
        (∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I)) +
          ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I) := by
    have hrel :
        ∀ t : ℝ,
          ψI' ((t : ℂ) + Complex.I) =
            ψS' ((t : ℂ) + Complex.I) + ψT' ((t : ℂ) + Complex.I) := by
      intro t
      have hz : 0 < (((t : ℂ) + Complex.I).im) := by simp
      have h :=
        congrArg
          (fun F : ℍ → ℂ => F (UpperHalfPlane.mk ((t : ℂ) + Complex.I) hz))
          ψS_add_ψT_eq_ψI
      simpa [ψI', ψS', ψT', hz, add_comm, add_left_comm, add_assoc] using! h.symm
    have hcongr :
        (∫ x in (0 : ℝ)..1, ψI' ((x : ℂ) + Complex.I) * expU u0 ((x : ℂ) + Complex.I)) =
          ∫ x in (0 : ℝ)..1,
            (ψS' ((x : ℂ) + Complex.I) + ψT' ((x : ℂ) + Complex.I)) *
              expU u0 ((x : ℂ) + Complex.I) := by
      refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
      intro t ht
      simp [hrel t]
    have hIntS :
        IntervalIntegrable (fun t : ℝ => ψS' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I))
          MeasureTheory.volume 0 1 := by
      have hcont :
          Continuous fun t : ℝ =>
            ψS' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I) := by
        have hS : Continuous fun t : ℝ => ψS' ((t : ℂ) + Complex.I) := by
          simpa using! SpherePacking.Dim24.PsiRewrites.continuous_ψS'_add_I
        have hE : Continuous fun t : ℝ => expU u0 ((t : ℂ) + Complex.I) := by
          have :
              Continuous fun t : ℝ => Real.pi * Complex.I * (u0 : ℂ) * ((t : ℂ) + Complex.I) := by
            fun_prop
          simpa [expU] using! this.cexp
        exact hS.mul hE
      exact (hcont.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)))
    have hIntT :
        IntervalIntegrable (fun t : ℝ => ψT' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I))
          MeasureTheory.volume 0 1 := by
      have hcont :
          Continuous fun t : ℝ =>
            ψT' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I) := by
        have hT : Continuous fun t : ℝ => ψT' ((t : ℂ) + Complex.I) := by
          simpa using! SpherePacking.Dim24.PsiRewrites.continuous_ψT'_add_I
        have hE : Continuous fun t : ℝ => expU u0 ((t : ℂ) + Complex.I) := by
          have :
              Continuous fun t : ℝ => Real.pi * Complex.I * (u0 : ℂ) * ((t : ℂ) + Complex.I) := by
            fun_prop
          simpa [expU] using! this.cexp
        exact hT.mul hE
      exact (hcont.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)))
    have hsplit :
        (∫ x in (0 : ℝ)..1,
            (ψS' ((x : ℂ) + Complex.I) + ψT' ((x : ℂ) + Complex.I)) *
              expU u0 ((x : ℂ) + Complex.I)) =
          (∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I)) +
            ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I) := by
      simpa [mul_add, add_mul] using!
        (intervalIntegral.integral_add (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun t : ℝ => ψS' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I))
          (g := fun t : ℝ => ψT' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I)) hIntS hIntT)
    simpa [bottom, hsplit] using! hcongr
  have hHS :
      (∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I)) =
        (2 : ℂ) * (Complex.I • V) := by
    simpa [V] using! HS_eq_twoI_V (u := u0) hu hu0
  have hB : bottom - (Complex.I : ℂ) • V = Bfun u0 := by
    dsimp [Bfun]
    rw [hbottom]
    simp [hHS, V, smul_eq_mul, add_assoc, sub_eq_add_neg, two_mul]
    ring
  have hTop' :
      Tendsto (fun T : ℝ => TopEdge u0 T) atTop (𝓝 (bottom - (Complex.I : ℂ) * V)) := by
    simpa [smul_eq_mul] using! hTop
  have hB' : bottom - (Complex.I : ℂ) * V = Bfun u0 := by
    simpa [smul_eq_mul] using! hB
  simpa [hB'] using! hTop'

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
