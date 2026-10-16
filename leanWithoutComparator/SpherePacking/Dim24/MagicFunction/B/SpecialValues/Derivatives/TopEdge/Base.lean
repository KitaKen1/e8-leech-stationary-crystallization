-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.EvenU.BProfileZeros
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.Rectangle
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.TopEdge.J6
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims


/-!
# Top-edge integrals for `Bfun` and `TopEdge`

This file defines the auxiliary quantities `Bfun u` and `TopEdge u T` used in the derivative
special-value computations for `bProfile`. It also proves the rectangle identity relating `TopEdge`
to a vertical integral of `ψS'` and records the limits needed to pass to `T → ∞`.

## Main definitions
* `Bfun`
* `TopEdge`

## Main statements
* `TopEdge_sub_bottom_eq_vertical`
* `tendsto_vertical_intervalIntegral`
* `HS_eq_twoI_V`
-/

open scoped Real
open scoped Topology
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter intervalIntegral
open RealIntegrals
open scoped Interval

namespace Deriv

/-- Evaluate `ψI'` on the upper half-plane by coercing to `ℍ`. -/
public lemma ψI'_eq_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    ψI' z = ψI (UpperHalfPlane.mk z hz) := by
  unfold ψI'
  simp [hz]

/-- The auxiliary function `Bfun u` appearing in the special-value computations for `bProfile`. -/
@[expose] public def Bfun (u : ℝ) : ℂ :=
  (∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) +
    (Complex.I •
      ∫ (t : ℝ) in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I))

/-- Integral of `ψI' z * expU u z` along the top edge of the rectangle of height `T`. -/
@[expose] public def TopEdge (u T : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    ψI' ((x : ℂ) + (T : ℂ) * Complex.I) * expU u ((x : ℂ) + (T : ℂ) * Complex.I)

/-- Rewrite `TopEdge u T` in terms of the bottom edge and a vertical integral of `ψS'`. -/
public lemma TopEdge_sub_bottom_eq_vertical (u T : ℝ) (hu : expU u 1 = 1) (hT : (1 : ℝ) ≤ T) :
    (∫ x in (0 : ℝ)..1, ψI' ((x : ℂ) + Complex.I) * expU u ((x : ℂ) + Complex.I)) - TopEdge u T =
      (Complex.I : ℂ) • ∫ t in (1 : ℝ)..T, ψS' (t * Complex.I) * expU u (t * Complex.I) := by
  simpa [TopEdge] using! (ψI_rect_integral_eq_top_sub_vertical (u := u) hu (T := T) hT)

lemma integrableOn_vertical_mul_expU (u : ℝ) (hu0 : 0 ≤ u) :
    MeasureTheory.IntegrableOn (fun t : ℝ => ψS' (t * Complex.I) * expU u (t * Complex.I))
      (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
  exact integrableOn_ψS'_mul_expU_vertical_left u hu0

/-- Limit of the vertical interval integral as `T → ∞`. -/
public lemma tendsto_vertical_intervalIntegral (u : ℝ) (hu0 : 0 ≤ u) :
    Tendsto (fun T : ℝ => ∫ t in (1 : ℝ)..T, ψS' (t * Complex.I) * expU u (t * Complex.I))
      atTop
        (𝓝
          (∫ (t : ℝ) in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I))) := by
  simpa using!
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := MeasureTheory.volume)
      (a := (1 : ℝ))
      (f := fun t : ℝ => ψS' (t * Complex.I) * expU u (t * Complex.I))
      (integrableOn_vertical_mul_expU (u := u) hu0)
      (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop))

/-- Relate the horizontal integral of `ψS'` on `Im z = 1` to the vertical integral on the
imaginary axis. -/
public lemma HS_eq_twoI_V (u : ℝ) (hu : expU u 1 = 1) (hu0 : 0 ≤ u) :
    (∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) =
      (2 : ℂ) *
        (Complex.I •
          ∫ (t : ℝ) in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)) := by
  have hsum : J₂' u + J₄' u + J₆' u = 0 := J₂'_J₄'_J₆'_zero_sum_of (u := u) hu hu0
  have hJ24 : J₂' u + J₄' u =
      ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) :=
    J₂'_J₄_as_ψS_horizontal_of (u := u) hu
  have hJ6 : J₆' u =
      (-2 : ℂ) *
        (Complex.I •
          ∫ (t : ℝ) in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)) :=
    J₆'_eq_vertical_Ioi (u := u)
  have hHSJ6 :
      (∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) +
          J₆' u =
        0 := by
    simpa [hJ24, add_assoc] using! hsum
  have hHS :
      (∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) = -J₆' u :=
    eq_neg_of_add_eq_zero_left hHSJ6
  calc
    (∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) = -J₆' u := hHS
    _ =
        -((-2 : ℂ) *
            (Complex.I •
              ∫ (t : ℝ) in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I))) := by
          simp [hJ6]
    _ =
        (2 : ℂ) *
          (Complex.I •
            ∫ (t : ℝ) in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)) := by
          ring

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
