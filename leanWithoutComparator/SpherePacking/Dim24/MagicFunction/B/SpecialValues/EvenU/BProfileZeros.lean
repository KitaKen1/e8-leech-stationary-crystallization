-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.EvenU.SumIdentities
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.TopEdge.J6
import SpherePacking.ForMathlib.IntervalIntegral


/-!
# Zeros of `bProfile` at even parameters

This file completes the `EvenU` special-value analysis for the dimension-24 magic function `b`.
We factor the block `J₂' u + J₄' u + J₆' u` to exhibit the linear factor `(expU u 1)⁻¹ - 1`, and
deduce vanishing results for the one-variable profile `bProfile`.

## Main statements
* `J₂'_J₄'_J₆'_factor`
* `bProfile_eq_zero_of`
* `bProfile_two`
* `bProfile_four`

-/

open scoped Real
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Set intervalIntegral
open MagicFunction.Parametrisations RealIntegrals
open scoped Interval

/-- Factorization of `J₂' u + J₄' u + J₆' u` exhibiting the linear factor `(expU u 1)⁻¹ - 1`. -/
public lemma J₂'_J₄'_J₆'_factor (u : ℝ) (hu0 : 0 ≤ u) :
    J₂' u + J₄' u + J₆' u =
      ((expU u 1)⁻¹ - 1) *
        ((∫ t in (0 : ℝ)..1,
              ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) +
          (Complex.I •
            ∫ (t : ℝ) in Ioi (1 : ℝ),
              ψS' (t * Complex.I) * expU u (t * Complex.I))) := by
  -- Set up the horizontal and vertical pieces.
  let w : ℂ := expU u 1
  let HS : ℂ := ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)
  let HT : ℂ := ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)
  let V : ℂ := ∫ (t : ℝ) in Ioi (1 : ℝ), (ψS' (t * Complex.I)) * expU u (t * Complex.I)
  -- First rewrite `J₂'+J₄'` into `HS` and `HT`.
  have hJ2 :
      J₂' u =
        (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) * w⁻¹ := by
    -- `z₂' t + 1 = t + I`, and `ψT'(z₂' t) = ψI'(t+I)`.
    dsimp [RealIntegrals.J₂', expU, w]
    have hcongr :
        (∫ t in (0 : ℝ)..1, ψT' (z₂' t) * expU u (z₂' t)) =
          ∫ t in (0 : ℝ)..1,
            ψI' ((t : ℂ) + Complex.I) * (expU u ((t : ℂ) + Complex.I) * (w)⁻¹) := by
      refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
      intro t ht
      have htIcc : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
      have hψ : ψT' (z₂' t) = ψI' ((t : ℂ) + Complex.I) := ψT'_z₂'_eq_ψI'_add_one (t := t) htIcc
      have hz : z₂' t + 1 = (t : ℂ) + Complex.I := by
        simp [MagicFunction.Parametrisations.z₂'_eq_of_mem (t := t) htIcc, add_left_comm, add_comm]
      have hw_ne : w ≠ 0 := by simp [w, expU]
      have hexp :
          expU u (z₂' t) = expU u ((t : ℂ) + Complex.I) * w⁻¹ := by
        have hmul := expU_add_one_mul (u := u) (z := z₂' t)
        have hstep : expU u ((t : ℂ) + Complex.I) = expU u (z₂' t) * w := by
          simpa [w, hz] using! hmul
        exact (eq_mul_inv_iff_mul_eq₀ hw_ne).mpr (id (Eq.symm hstep))
      simp [hψ, hexp]
    -- Pull out the constant `w⁻¹` on the right.
    have hpull :
        (∫ t in (0 : ℝ)..1,
            ψI' ((t : ℂ) + Complex.I) * (expU u ((t : ℂ) + Complex.I) * w⁻¹)) =
          (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) * w⁻¹ := by
      simpa [mul_assoc] using!
        (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume)
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun t : ℝ => ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))
          (w⁻¹))
    have hcongr' :
        (∫ t in (0 : ℝ)..1,
              ψT' (z₂' t) * Complex.exp (↑π * Complex.I * ↑u * z₂' t)) =
          ∫ t in (0 : ℝ)..1,
            ψI' ((t : ℂ) + Complex.I) *
              (Complex.exp (↑π * Complex.I * ↑u * ((t : ℂ) + Complex.I)) *
                (Complex.exp (↑π * Complex.I * ↑u))⁻¹) := by
      simpa [expU, w, mul_assoc, mul_left_comm, mul_comm] using!
        hcongr
    have hpull' :
        (∫ t in (0 : ℝ)..1,
              ψI' ((t : ℂ) + Complex.I) *
                (Complex.exp (↑π * Complex.I * ↑u * ((t : ℂ) + Complex.I)) *
                  (Complex.exp (↑π * Complex.I * ↑u))⁻¹)) =
            (∫ t in (0 : ℝ)..1,
                  ψI' ((t : ℂ) + Complex.I) *
                    Complex.exp (↑π * Complex.I * ↑u * ((t : ℂ) + Complex.I))) *
              (Complex.exp (↑π * Complex.I * ↑u))⁻¹ := by
      simpa [expU, w, mul_assoc, mul_left_comm, mul_comm] using!
        hpull
    have htrans := hcongr'.trans hpull'
    simpa [mul_one, mul_assoc] using! htrans
  have hJ4 : J₄' u = -HT := by
    -- Same reparametrization as in the `u=0` case, but with the exponential factor included.
    have hEq :
        (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t) * expU u (z₄' t)) =
          ∫ t in (0 : ℝ)..1,
            (-1 : ℂ) *
              (ψT' ((1 - t : ℂ) + Complex.I) * expU u ((1 - t : ℂ) + Complex.I)) := by
      refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
      intro t ht
      have htIcc : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
      have hz4 : z₄' t = (1 - t : ℂ) + Complex.I := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
          (MagicFunction.Parametrisations.z₄'_eq_of_mem (t := t) htIcc)
      simp [hz4]
    -- Use the involution `t ↦ 1 - t` on `[0,1]`.
    let f : ℝ → ℂ := fun t : ℝ => ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)
    have hneg :
        (∫ t in (0 : ℝ)..1, (-1 : ℂ) * f (1 - t)) = -∫ t in (0 : ℝ)..1, f t :=
      SpherePacking.ForMathlib.intervalIntegral_neg_one_mul_comp_one_sub_eq_neg (f := f)
    dsimp [RealIntegrals.J₄'] at *
    -- `J₄' u` has an extra `(-1)` already; isolate `HT`.
    have : J₄' u = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * (ψT' (z₄' t) * expU u (z₄' t)) := by
      simp [RealIntegrals.J₄', expU, mul_assoc, mul_left_comm, mul_comm]
    -- Combine and finish.
    -- Note: `HT` is exactly `∫ f t`.
    have hHT : HT = ∫ t in (0 : ℝ)..1, f t := rfl
    -- Now rewrite.
    have : J₄' u = -HT := by
      -- Move to the `z₄'`-parametrized integral.
      -- The `hEq` lemma changes `z₄' t` to `(1-t)+I` pointwise.
      calc
        J₄' u = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * (ψT' (z₄' t) * expU u (z₄' t)) := this
        _ =
            ∫ t in (0 : ℝ)..1,
              (-1 : ℂ) *
                (ψT' ((1 - t : ℂ) + Complex.I) * expU u ((1 - t : ℂ) + Complex.I)) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using! hEq
        _ = -∫ t in (0 : ℝ)..1, f t := by
              simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using! hneg
        _ = -HT := by simp [hHT]
    exact this
  have hrel :
      ∀ t : ℝ,
        ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I) = ψS' ((t : ℂ) + Complex.I) := by
    intro t
    have hz : 0 < (((t : ℂ) + Complex.I).im) := by simp
    have h := congrArg (fun F : ℍ → ℂ => F (UpperHalfPlane.mk ((t : ℂ) + Complex.I) hz))
      ψS_add_ψT_eq_ψI
    have h' :
        ψI' ((t : ℂ) + Complex.I) =
          ψS' ((t : ℂ) + Complex.I) + ψT' ((t : ℂ) + Complex.I) := by
      simpa [ψI', ψS', ψT', hz] using! h.symm
    exact Eq.symm (eq_sub_of_add_eq (id (Eq.symm h')))
  -- Convert `J₂'+J₄'` into `HS` and `HT`.
  have hJ24 :
      J₂' u + J₄' u =
        HS * w⁻¹ + (w⁻¹ - 1) * HT := by
    -- `HS` comes from `ψI' - ψT' = ψS'` on the segment.
    have hI :
        ∫ t in (0 : ℝ)..1,
            ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) =
          HS + HT := by
      -- pointwise: `ψI' = ψS' + ψT'`, multiply by `expU` and integrate.
      have hcongr :
          (∫ t in (0 : ℝ)..1,
                ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) =
            ∫ t in (0 : ℝ)..1,
              (ψS' ((t : ℂ) + Complex.I) + ψT' ((t : ℂ) + Complex.I)) *
                expU u ((t : ℂ) + Complex.I) := by
        refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) (fun t ht => ?_)
        have hz :
            ψI' ((t : ℂ) + Complex.I) =
              ψS' ((t : ℂ) + Complex.I) + ψT' ((t : ℂ) + Complex.I) :=
          (sub_eq_iff_eq_add).1 (hrel t)
        simp [hz]
      -- Split integral of sum.
      have hsplit :
          (∫ t in (0 : ℝ)..1,
              (ψS' ((t : ℂ) + Complex.I) + ψT' ((t : ℂ) + Complex.I)) *
                expU u ((t : ℂ) + Complex.I)) =
            HS + HT := by
        -- use linearity
        have hScont : Continuous fun t : ℝ =>
            ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
          have : Continuous fun t : ℝ => ψS' ((t : ℂ) + Complex.I) := by
            simpa using! SpherePacking.Dim24.PsiRewrites.continuous_ψS'_add_I
          have hE : Continuous fun t : ℝ => expU u ((t : ℂ) + Complex.I) := by
            have : Continuous fun t : ℝ =>
                Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) + Complex.I) := by
              fun_prop
            simpa [expU] using! this.cexp
          exact this.mul hE
        have hTcont : Continuous fun t : ℝ =>
            ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
          -- analogous to `hScont`
          have : Continuous fun t : ℝ => ψT' ((t : ℂ) + Complex.I) := by
            simpa using! SpherePacking.Dim24.PsiRewrites.continuous_ψT'_add_I
          have hE : Continuous fun t : ℝ => expU u ((t : ℂ) + Complex.I) := by
            have : Continuous fun t : ℝ =>
                Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) + Complex.I) := by
              fun_prop
            simpa [expU] using! this.cexp
          exact this.mul hE
        have hIntS :
            IntervalIntegrable
              (fun t : ℝ => ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))
              MeasureTheory.volume (0 : ℝ) 1 :=
          hScont.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        have hIntT :
            IntervalIntegrable
              (fun t : ℝ => ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))
              MeasureTheory.volume (0 : ℝ) 1 :=
          hTcont.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        -- `HS` and `HT` are exactly these integrals.
        have :
            (∫ t in (0 : ℝ)..1,
                (ψS' ((t : ℂ) + Complex.I) + ψT' ((t : ℂ) + Complex.I)) *
                  expU u ((t : ℂ) + Complex.I)) =
              HS + HT := by
          -- Expand and use `integral_add`.
          have hcore :
              (∫ t in (0 : ℝ)..1,
                  (ψS' ((t : ℂ) + Complex.I) + ψT' ((t : ℂ) + Complex.I)) *
                    expU u ((t : ℂ) + Complex.I)) =
                (∫ t in (0 : ℝ)..1,
                      ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) +
                  ∫ t in (0 : ℝ)..1,
                    ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
            -- rewrite as `sub`? but directly:
            simpa [mul_add, add_mul, add_assoc, add_left_comm, add_comm] using!
              (intervalIntegral.integral_add
                (μ := MeasureTheory.volume)
                (a := (0 : ℝ))
                (b := (1 : ℝ))
                (f := fun t : ℝ => ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))
                (g := fun t : ℝ => ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))
                hIntS
                hIntT)
          simpa [HS, HT] using! hcore
        exact this
      simp [hcongr, hsplit]
    -- Now substitute into `J₂'+J₄'`.
    grind only
  -- Now relate `HS` and `V` by the open rectangle deformation, but keep track of `w`.
  let fU : ℂ → ℂ := fun z : ℂ => ψS' z * expU u z
  have hrect :
      (∫ (x : ℝ) in (0 : ℝ)..1,
            fU (x + (1 : ℝ) * Complex.I)) +
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ),
              fU ((1 : ℂ) + t * Complex.I)) -
            (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ),
              fU ((0 : ℂ) + t * Complex.I)) =
        0 := by
    simpa [fU] using! integral_boundary_open_rect_ψS'_mul_expU_eq_zero (u := u) hu0
  have hright :
      (∫ (t : ℝ) in Ioi (1 : ℝ), fU ((1 : ℂ) + t * Complex.I)) =
        -(w * ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) := by
    have hEq :
        (fun t : ℝ => fU ((1 : ℂ) + t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Ioi (1 : ℝ))]
          fun t : ℝ => -(w * fU (t * Complex.I)) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
      have hI : (Complex.I : ℂ) * (t : ℂ) = (t : ℂ) * Complex.I := by
        simp [mul_comm]
      have hψ : ψS' ((1 : ℂ) + t * Complex.I) = -ψS' (t * Complex.I) :=
        SpherePacking.Dim24.PsiSPrelims.ψS'_add_one (t := t) ht0
      have hexp : expU u ((1 : ℂ) + t * Complex.I) = expU u (t * Complex.I) * w := by
        simpa [w, add_assoc, add_left_comm, add_comm] using!
          (expU_add_one_mul (u := u) (z := (t : ℂ) * Complex.I))
      grind only
    have hEqInt :
        (∫ (t : ℝ) in Ioi (1 : ℝ), fU ((1 : ℂ) + t * Complex.I)) =
          ∫ (t : ℝ) in Ioi (1 : ℝ), -(w * fU (t * Complex.I)) := by
      simpa using! (MeasureTheory.integral_congr_ae hEq)
    -- Pull out constants and simplify.
    have hwconst :
        (∫ (t : ℝ) in Ioi (1 : ℝ), -(w * fU (t * Complex.I))) =
          -(w * ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) := by
      simp [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
    simpa [hwconst] using! hEqInt
  have hHS :
      HS = (1 + w) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) := by
    -- Rewrite `hrect` using `hright` and solve for the horizontal integral.
    have h' :
        (∫ (x : ℝ) in (0 : ℝ)..1, fU (x + (1 : ℝ) * Complex.I)) +
            (Complex.I • (-(w * ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)))) -
              (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU ((0 : ℂ) + t * Complex.I)) = 0 := by
      simpa [hright] using! hrect
    -- `fU (x + 1*I) = fU ((x:ℂ) + I)` and `fU ((0:ℂ)+t*I) = fU (t*I)`.
    have h'' :
        (∫ (x : ℝ) in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) =
          (1 + w) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) := by
      -- rearrange `h'`
      -- First, simplify the `0 + t*I` term.
      have h0 : (fun t : ℝ => fU ((0 : ℂ) + t * Complex.I)) = fun t : ℝ => fU (t * Complex.I) := by
        funext t; simp
      -- Now solve.
      -- Move the vertical terms to the RHS.
      -- We'll solve by commutative-ring normalization after rewriting.
      -- Start from `h'` and isolate the first term.
      -- `simp` then `ring_nf` should handle.
      -- (We avoid fragile `linarith` over `ℂ`.)
      -- Use `simp` to rewrite the second and third terms and then `ring`.
      -- Convert everything to `HS`/`V`.
      -- Expand and simplify `h'`.
      have hsol :
          (∫ (x : ℝ) in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) =
            (1 + w) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) := by
        -- From `h'`:
        -- horizontal + I•(-w*V) - I•V = 0
        -- so horizontal = (1+w) * I•V.
        have : (∫ (x : ℝ) in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) +
              (Complex.I • (-(w * ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)))) -
              (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) = 0 := by
          simpa [h0] using! h'
        -- Rewrite the `•` as multiplication.
        -- Then solve by `ring`.
        -- Convert to an equation without subtraction.
        have : (∫ (x : ℝ) in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) =
              (1 + w) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) := by
          -- `simp` turns it into a ring identity.
          -- Use `linear_combination` style over commutative ring `ℂ`.
          -- We'll just `ring_nf` after rewriting.
          -- Convert: `a + I•(-(w*V)) - I•V = 0` -> `a = (1+w) * I•V`.
          -- `simp` knows `smul_eq_mul`.
          -- Finish by normalization in the commutative ring `ℂ`.
          -- Let's do it explicitly.
          -- Move terms:
          -- a = (I•V) + (I•(w*V)).
          -- then factor `(1+w)`.
          have htmp :
              (∫ (x : ℝ) in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) +
                  ((Complex.I • (-(w * ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)))) -
                    (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I))) =
                0 := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! this
          have hEq :
              (∫ (x : ℝ) in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) =
                -(((Complex.I • (-(w * ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)))) -
                    (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)))) :=
            eq_neg_of_add_eq_zero_left htmp
          -- Simplify the RHS and factor `(1+w)` in the commutative ring `ℂ`.
          have hEq0 :
              (∫ (x : ℝ) in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) =
                (Complex.I : ℂ) * (∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) +
                  (Complex.I : ℂ) * (w * (∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I))) := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_eq_mul, mul_assoc] using!
              hEq
          have hEq1 :
              (∫ (x : ℝ) in (0 : ℝ)..1, fU ((x : ℂ) + Complex.I)) =
                (1 + w) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) := by
            -- Normalize the algebra and convert (postTransparency := .instances) `•` to multiplication.
            have :
                (Complex.I : ℂ) *
                    (∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) +
                  (Complex.I : ℂ) *
                    (w * (∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I))) =
                  (1 + w) *
                    ((Complex.I : ℂ) * (∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I))) := by
              ring_nf
            -- Put everything together.
            calc
              (∫ (x : ℝ) in (0 : ℝ)..1,
                    fU ((x : ℂ) + Complex.I)) =
                  (Complex.I : ℂ) * (∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) +
                    (Complex.I : ℂ) *
                      (w * (∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I))) := by
                    simpa using! hEq0
              _ =
                  (1 + w) * ((Complex.I : ℂ) * (∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I))) :=
                    this
              _ = (1 + w) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), fU (t * Complex.I)) := by
                    simp [smul_eq_mul]
          exact hEq1
        exact this
      exact hsol
    -- Identify the LHS with `HS` and replace the RHS integral by `V`.
    assumption
  -- Rewrite `J₆'` in terms of `V`.
  have hJ6 :
      J₆' u = (-2 : ℂ) * (Complex.I • V) := by
    simpa [V] using! (Deriv.J₆'_eq_vertical_Ioi (u := u))
  -- Assemble the factorization.
  -- Use `HS = (1+w) * I•V` and `J₆' = (-2) * I•V` to factor out `(w⁻¹ - 1)`.
  have hHS' : HS = (1 + w) * (Complex.I • V) := by
    -- Replace `fU` by `ψS' * expU` and `V` by its definition.
    -- `HS` already matches the horizontal integral of `fU`.
    simpa [HS, fU, V, mul_assoc, mul_left_comm, mul_comm] using!
      hHS
  calc
    J₂' u + J₄' u + J₆' u =
        (HS * w⁻¹ + (w⁻¹ - 1) * HT) + J₆' u := by
      simp [hJ24, add_assoc]
    _ = (w⁻¹ * HS + (w⁻¹ - 1) * HT) + J₆' u := by ring_nf
    _ = (w⁻¹ - 1) * ((HT) + (Complex.I • V)) := by
      -- Expand `HS` and `J₆'` in terms of `V`, then factor.
      have hw : w ≠ 0 := by simp [w, expU]
      simp [hHS', hJ6, smul_eq_mul, two_mul, sub_eq_add_neg]
      field_simp [hw]
      ring_nf
    _ = ((expU u 1)⁻¹ - 1) *
          ((∫ t in (0 : ℝ)..1,
                ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) +
            (Complex.I •
              ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I))) := by
          simp [w, HT, V]

/-- If `expU u 1 = 1` and `0 ≤ u`, then the profile `bProfile u` vanishes. -/
public lemma bProfile_eq_zero_of (u : ℝ) (hu : expU u 1 = 1) (hu0 : 0 ≤ u) :
    bProfile u = 0 := by
  have h135 : J₁' u + J₃' u + J₅' u = 0 := J₁'_J₃'_J₅'_zero_sum_of (u := u) hu
  have h246 : J₂' u + J₄' u + J₆' u = 0 := J₂'_J₄'_J₆'_zero_sum_of (u := u) hu hu0
  dsimp [bProfile, RealIntegrals.b']
  calc
    J₁' u + J₂' u + J₃' u + J₄' u + J₅' u + J₆' u =
        (J₁' u + J₃' u + J₅' u) + (J₂' u + J₄' u + J₆' u) := by ac_rfl
    _ = 0 := by simp [h135, h246]

/-- The profile `bProfile` vanishes at `u = 2`. -/
public lemma bProfile_two : bProfile (2 : ℝ) = 0 := by
  have hu : expU (2 : ℝ) 1 = 1 := by
    -- `exp(π i * 2) = exp(2π i) = 1`.
    simpa [expU, mul_assoc, mul_left_comm, mul_comm] using! (Complex.exp_two_pi_mul_I)
  simpa using! bProfile_eq_zero_of (u := (2 : ℝ)) hu (by norm_num)

/-- The profile `bProfile` vanishes at `u = 4`. -/
public lemma bProfile_four : bProfile (4 : ℝ) = 0 := by
  have hu : expU (4 : ℝ) 1 = 1 := by
    -- `exp(π i * 4) = exp(4π i) = 1`.
    have h2 : ((2 : ℤ) : ℂ) = (2 : ℂ) := by norm_num
    have h4 : (2 : ℂ) * (2 : ℂ) = (4 : ℂ) := by norm_num
    simpa [expU, mul_assoc, mul_left_comm, mul_comm, h2, h4] using!
      (Complex.exp_int_mul_two_pi_mul_I (n := (2 : ℤ)))
  simpa using! bProfile_eq_zero_of (u := (4 : ℝ)) hu (by norm_num)

end SpecialValuesAux.EvenU
end

end SpherePacking.Dim24
