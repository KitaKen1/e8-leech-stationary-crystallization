-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.Rectangle
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Basic
import SpherePacking.ForMathlib.IntervalIntegral

/-!
# The integral `J₆'` as a vertical integral

This file records a measure-theoretic reparametrization rewriting `J₆'` as a vertical integral on
`Ioi (1 : ℝ)`. It is used in the `EvenU` special-values development.

## Main statements
* `Deriv.J₆'_eq_vertical_Ioi`
-/

open scoped Real
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open intervalIntegral
open MagicFunction.Parametrisations RealIntegrals
open scoped Interval

namespace Deriv

/-- Rewrite `J₆'` as a vertical integral on `Ioi (1 : ℝ)`. -/
public lemma J₆'_eq_vertical_Ioi (u : ℝ) :
    J₆' u =
      (-2 : ℂ) *
        (Complex.I •
          ∫ (t : ℝ) in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)) := by
  let fU : ℂ → ℂ := fun z : ℂ => ψS' z * expU u z
  have hJ6_unfold :
      J₆' u =
        (-2 : ℂ) *
          ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) * expU u (z₆' t) := by
    simp [RealIntegrals.J₆', expU]
  have hIci :
      (∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) * expU u (z₆' t)) =
        ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) * expU u (z₆' t) := by
    exact MeasureTheory.integral_Ici_eq_integral_Ioi
  have hparam :
      (∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) * expU u (z₆' t)) =
        ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * ψS' (t * Complex.I) * expU u (t * Complex.I) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht' : t ∈ Set.Ici (1 : ℝ) := le_of_lt (by simpa [Set.mem_Ioi] using! ht)
    simp [MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t) ht', mul_comm]
  have hpull :
      (∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * (ψS' (t * Complex.I) * expU u (t * Complex.I))) =
        (Complex.I : ℂ) * ∫ t in Set.Ioi (1 : ℝ), fU (t * Complex.I) := by
    simp [fU, MeasureTheory.integral_const_mul]
  calc
    J₆' u =
        (-2 : ℂ) *
          ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) * expU u (z₆' t) := hJ6_unfold
    _ =
        (-2 : ℂ) *
          ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) * expU u (z₆' t) := by
          simpa [mul_assoc] using! congrArg (fun x : ℂ => (-2 : ℂ) * x) hIci
    _ =
        (-2 : ℂ) *
          ∫ t in Set.Ioi (1 : ℝ),
            (Complex.I : ℂ) * ψS' (t * Complex.I) * expU u (t * Complex.I) := by
          simpa [mul_assoc] using! congrArg (fun x : ℂ => (-2 : ℂ) * x) hparam
    _ = (-2 : ℂ) * (Complex.I • ∫ t in Set.Ioi (1 : ℝ), fU (t * Complex.I)) := by
          have hpull' :
              (∫ t in Set.Ioi (1 : ℝ),
                    (Complex.I : ℂ) * ψS' (t * Complex.I) * expU u (t * Complex.I)) =
                (Complex.I : ℂ) * ∫ t in Set.Ioi (1 : ℝ), fU (t * Complex.I) := by
            simpa [mul_assoc] using! hpull
          calc
            (-2 : ℂ) *
                ∫ t in Set.Ioi (1 : ℝ),
                  (Complex.I : ℂ) * ψS' (t * Complex.I) * expU u (t * Complex.I) =
                (-2 : ℂ) * ((Complex.I : ℂ) * ∫ t in Set.Ioi (1 : ℝ), fU (t * Complex.I)) := by
                  simp [hpull']
            _ = (-2 : ℂ) * (Complex.I • ∫ t in Set.Ioi (1 : ℝ), fU (t * Complex.I)) := by
                  simp [smul_eq_mul]
    _ = (-2 : ℂ) *
          (Complex.I •
            ∫ (t : ℝ) in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)) := by
          simp [fU]

/-- Rewrite the sum `J₂' u + J₄' u` as a horizontal integral of `ψS'` along `t + I`. -/
public lemma J₂'_J₄_as_ψS_horizontal_of (u : ℝ) (hu : expU u 1 = 1) :
    J₂' u + J₄' u =
      ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
  have hJ2 :
      J₂' u =
        ∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
    rw [RealIntegrals.J₂']
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
    have hψ : ψT' (z₂' t) = ψI' ((t : ℂ) + Complex.I) := ψT'_z₂'_eq_ψI'_add_one (t := t) htIcc
    have hz : z₂' t + 1 = (t : ℂ) + Complex.I := by
      simp [MagicFunction.Parametrisations.z₂'_eq_of_mem (t := t) htIcc, add_left_comm, add_comm]
    have hexp : expU u (z₂' t) = expU u ((t : ℂ) + Complex.I) := by
      simpa [hz] using! (expU_add_one (u := u) hu (z := z₂' t)).symm
    calc
      ψT' (z₂' t) * Complex.exp (Real.pi * Complex.I * (u : ℂ) * z₂' t) =
          ψT' (z₂' t) * expU u (z₂' t) := by simp [expU]
      _ = ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by simp [hψ, hexp]
  have hJ4 :
      J₄' u =
        -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
    -- This is the `u`-version of the reparametrization used in `Part3b`.
    have hEq :
        (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t) * expU u (z₄' t)) =
          ∫ t in (0 : ℝ)..1,
            (-1 : ℂ) *
              (ψT' ((1 - t : ℂ) + Complex.I) * expU u ((1 - t : ℂ) + Complex.I)) := by
      refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
      have hz4 : z₄' t = (1 - t : ℂ) + Complex.I := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
          (MagicFunction.Parametrisations.z₄'_eq_of_mem (t := t) htIcc)
      simp [hz4]
    let f : ℝ → ℂ := fun t : ℝ => ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)
    have hneg :
        (∫ t in (0 : ℝ)..1, (-1 : ℂ) * f (1 - t)) = -∫ t in (0 : ℝ)..1, f t := by
      exact SpherePacking.ForMathlib.intervalIntegral_neg_one_mul_comp_one_sub_eq_neg (f := f)
    have hJ4' :
        J₄' u = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * (ψT' (z₄' t) * expU u (z₄' t)) := by
      simp [RealIntegrals.J₄', expU, mul_assoc, mul_left_comm, mul_comm]
    calc
      J₄' u
          = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * (ψT' (z₄' t) * expU u (z₄' t)) := hJ4'
      _ =
          ∫ t in (0 : ℝ)..1,
            (-1 : ℂ) * (ψT' ((1 - t : ℂ) + Complex.I) * expU u ((1 - t : ℂ) + Complex.I)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using! hEq
      _ = -∫ t in (0 : ℝ)..1, f t := by
            simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using! hneg
      _ = -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := rfl
  have hrel :
      ∀ t : ℝ,
        ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I) = ψS' ((t : ℂ) + Complex.I) := by
    intro t
    have hz : 0 < (((t : ℂ) + Complex.I).im) := by simp
    have h :=
      congrArg
        (fun F : ℍ → ℂ => F (UpperHalfPlane.mk ((t : ℂ) + Complex.I) hz))
        ψS_add_ψT_eq_ψI
    have h' :
        ψI' ((t : ℂ) + Complex.I) =
          ψS' ((t : ℂ) + Complex.I) + ψT' ((t : ℂ) + Complex.I) := by
      simpa [ψI', ψS', ψT', hz] using! h.symm
    exact Eq.symm (eq_sub_of_add_eq (id (Eq.symm h')))
  have hSub :
      ∫ t in (0 : ℝ)..1,
          (ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) -
            ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) =
        (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) -
          ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
    have hcontI :
        Continuous fun t : ℝ =>
          ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
      have : Continuous fun t : ℝ => ψI' ((t : ℂ) + Complex.I) := by
        simpa using! SpherePacking.Dim24.PsiRewrites.continuous_ψI'_add_I
      have hcontE : Continuous fun t : ℝ => expU u ((t : ℂ) + Complex.I) := by
        have :
            Continuous fun t : ℝ =>
              (Real.pi : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) + Complex.I) := by
          fun_prop
        simpa [expU] using! this.cexp
      exact this.mul hcontE
    have hcontT :
        Continuous fun t : ℝ =>
          ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
      have : Continuous fun t : ℝ => ψT' ((t : ℂ) + Complex.I) := by
        simpa using! SpherePacking.Dim24.PsiRewrites.continuous_ψT'_add_I
      have hcontE : Continuous fun t : ℝ => expU u ((t : ℂ) + Complex.I) := by
        have :
            Continuous fun t : ℝ =>
              (Real.pi : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) + Complex.I) := by
          fun_prop
        simpa [expU] using! this.cexp
      exact this.mul hcontE
    have hIntI :
        IntervalIntegrable (fun t : ℝ => ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))
          MeasureTheory.volume 0 1 :=
      (hcontI.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)))
    have hIntT :
        IntervalIntegrable (fun t : ℝ => ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))
          MeasureTheory.volume 0 1 :=
      (hcontT.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)))
    exact integral_sub hIntI hIntT
  have hCongr :
      ∫ t in (0 : ℝ)..1,
          (ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) -
            ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) =
        ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
    refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
    intro t ht
    have hfac :
        ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) -
            ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) =
          (ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I)) *
            expU u ((t : ℂ) + Complex.I) := by
      ring
    simp [hfac, hrel t]
  grind only

end Deriv

end EvenU

end SpecialValuesAux

end

end SpherePacking.Dim24
