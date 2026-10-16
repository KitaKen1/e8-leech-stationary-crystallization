-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.TopEdge.Base
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.TopEdge.Limits
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.CuspAtInfinity
import SpherePacking.Dim24.MagicFunction.SpecialValuesExpU


/-!
# Special value `Bfun 4 = 2`

This file proves the special value used in the derivative computation of `bProfile` at `u = 4`.
The proof compares the top-edge limit defining `Bfun 4` with the cusp asymptotic of `ψI`.

## Main statements
* `Bfun_four`
-/

open scoped Real
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter intervalIntegral UpperHalfPlane
open RealIntegrals
open scoped Topology Interval

namespace Deriv

/-- Special value: `Bfun 4 = 2`. -/
public lemma Bfun_four : Bfun (4 : ℝ) = (2 : ℂ) := by
  -- Compare the two limits of `TopEdge(4,T)`: it tends to `Bfun 4` by the rectangle argument,
  -- and to `2` by the cusp expansion.
  have hu : expU (4 : ℝ) 1 = 1 := by
    have h2 : ((2 : ℤ) : ℂ) = (2 : ℂ) := by norm_num
    have h4 : (2 : ℂ) * (2 : ℂ) = (4 : ℂ) := by norm_num
    simpa [expU, mul_assoc, mul_left_comm, mul_comm, h2, h4] using!
      (Complex.exp_int_mul_two_pi_mul_I (n := (2 : ℤ)))
  have hTopB : Tendsto (fun T : ℝ => TopEdge (4 : ℝ) T) atTop (𝓝 (Bfun (4 : ℝ))) :=
    tendsto_TopEdge (u0 := (4 : ℝ)) hu (by norm_num)
  have hF :
      Tendsto
        (fun z : ℍ => ψI z * Complex.exp (4 * Real.pi * Complex.I * (z : ℂ)))
        atImInfty (𝓝 (2 : ℂ)) :=
    tendsto_ψI_mul_cexp_four_pi_mul_I
  have hTop2 : Tendsto (fun T : ℝ => TopEdge (4 : ℝ) T) atTop (𝓝 (2 : ℂ)) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    have hEv :
        ∀ᶠ z in atImInfty,
          ‖ψI z * Complex.exp (4 * Real.pi * Complex.I * (z : ℂ)) - (2 : ℂ)‖ < ε / 2 := by
      simpa [dist_eq_norm] using! (Metric.tendsto_nhds.1 hF) (ε / 2) (by nlinarith)
    rcases (Filter.eventually_atImInfty).1 hEv with ⟨A, hA⟩
    refine (eventually_atTop.2 ⟨max A 1, ?_⟩)
    intro T hT
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hT)
    have hAT : A ≤ T := le_trans (le_max_left _ _) hT
    let fT : ℝ → ℂ :=
      fun x : ℝ =>
        ψI' ((x : ℂ) + (T : ℂ) * Complex.I) * expU (4 : ℝ) ((x : ℂ) + (T : ℂ) * Complex.I)
    have hbound : ∀ x ∈ Ι (0 : ℝ) 1, ‖fT x - (2 : ℂ)‖ ≤ ε / 2 := by
      intro x hx
      have hz0 : 0 < ((x : ℂ) + (T : ℂ) * Complex.I).im := by
        simpa [Complex.add_im, Complex.mul_im] using! hTpos
      let zH : ℍ := UpperHalfPlane.mk ((x : ℂ) + (T : ℂ) * Complex.I) hz0
      have hzIm : A ≤ zH.im := by
        simpa [zH, UpperHalfPlane.im, Complex.add_im, Complex.mul_im] using! hAT
      have hA' := hA zH hzIm
      have hf :
          fT x = ψI zH * Complex.exp (4 * Real.pi * Complex.I * (zH : ℂ)) := by
        have hψI' : ψI' ((x : ℂ) + (T : ℂ) * Complex.I) = ψI zH := by
          simpa [zH] using! (ψI'_eq_of_im_pos (z := (x : ℂ) + (T : ℂ) * Complex.I) hz0)
        have hexp : expU (4 : ℝ) ((x : ℂ) + (T : ℂ) * Complex.I) =
            Complex.exp (4 * Real.pi * Complex.I * (zH : ℂ)) := by
          simp [expU, zH, mul_assoc, mul_left_comm, mul_comm]
        simp [fT, hψI', hexp]
      exact le_of_lt (by simpa [hf] using! hA')
    have hdiff :
        TopEdge (4 : ℝ) T - (2 : ℂ) = ∫ x in (0 : ℝ)..1, (fT x - (2 : ℂ)) := by
      have hIntF : IntervalIntegrable fT MeasureTheory.volume (0 : ℝ) 1 := by
        have hcont : Continuous fT := by
          have hψ : Continuous fun x : ℝ => ψI' ((x : ℂ) + (T : ℂ) * Complex.I) := by
            let φ : ℝ → ℍ := fun x =>
              UpperHalfPlane.mk ((x : ℂ) + (T : ℂ) * Complex.I) (by
                simpa [Complex.add_im, Complex.mul_im] using! hTpos)
            have hφ : Continuous φ := by
              fun_prop
            have hEq :
                (fun x : ℝ => ψI' ((x : ℂ) + (T : ℂ) * Complex.I)) = fun x : ℝ => ψI (φ x) := by
              funext x
              have hxIm : 0 < ((x : ℂ) + (T : ℂ) * Complex.I).im := by
                simpa [Complex.add_im, Complex.mul_im] using! hTpos
              have hxmk :
                  (UpperHalfPlane.mk ((x : ℂ) + (T : ℂ) * Complex.I) hxIm : ℍ) = φ x := by
                ext
                rfl
              simpa [hxmk] using! (ψI'_eq_of_im_pos (z := (x : ℂ) + (T : ℂ) * Complex.I) hxIm)
            simpa [hEq] using! (continuous_ψI.comp hφ)
          have hE : Continuous fun x : ℝ => expU (4 : ℝ) ((x : ℂ) + (T : ℂ) * Complex.I) := by
            have :
                Continuous fun x : ℝ =>
                  Real.pi * Complex.I * ((4 : ℝ) : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I) := by
              fun_prop
            simpa [expU, mul_assoc, mul_left_comm, mul_comm] using! this.cexp
          simpa [fT] using! hψ.mul hE
        exact (hcont.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)))
      have hIntC : IntervalIntegrable (fun _ : ℝ => (2 : ℂ)) MeasureTheory.volume (0 : ℝ) 1 := by
        simp
      have hsub :=
        (intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fT) (g := fun _ : ℝ => (2 : ℂ)) hIntF hIntC)
      have hconst : (∫ x in (0 : ℝ)..1, (2 : ℂ)) = (2 : ℂ) := by
        simp [intervalIntegral.integral_const]
      simpa [TopEdge, fT, hconst, sub_eq_add_neg, add_assoc] using! hsub.symm
    have hnorm :
        ‖∫ x in (0 : ℝ)..1, (fT x - (2 : ℂ))‖ ≤ (ε / 2) * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have hle : ‖TopEdge (4 : ℝ) T - (2 : ℂ)‖ ≤ ε / 2 := by
      simpa [hdiff] using! (hnorm.trans_eq (by simp))
    have hlt : ‖TopEdge (4 : ℝ) T - (2 : ℂ)‖ < ε := by
      have : (ε / 2 : ℝ) < ε := by nlinarith
      exact lt_of_le_of_lt hle this
    simpa [dist_eq_norm] using! hlt
  exact tendsto_nhds_unique hTopB hTop2

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
