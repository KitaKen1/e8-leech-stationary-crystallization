-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.TopEdge.Base
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.TopEdge.Limits
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.CuspCoefficient.PsiI


/-!
# Special value `Bfun 2 = -464`

This file proves the special value used in the derivative computation of `bProfile` at `u = 2`.
The proof compares the top-edge limit defining `Bfun 2` with a cusp-coefficient computation for
`ψI`.

## Main statements
* `Bfun_two`
-/

open scoped Real
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Complex Filter intervalIntegral UpperHalfPlane
open scoped Topology Interval

namespace Deriv

/-- Special value: `Bfun 2 = -464`. -/
public lemma Bfun_two : Bfun (2 : ℝ) = (-464 : ℂ) := by
  -- Compare the two limits of `TopEdge(2,T)`: it tends to `Bfun 2` by the rectangle argument,
  -- and to `-464` from the `qHalf^2` coefficient at the cusp
  -- (the `exp(-2π i x)` term averages to `0`).
  have hu : expU (2 : ℝ) 1 = 1 := by
    -- `exp(π i * 2) = exp(2π i) = 1`.
    simpa [expU, mul_assoc, mul_left_comm, mul_comm] using! (Complex.exp_two_pi_mul_I)
  have hTopB : Tendsto (fun T : ℝ => TopEdge (2 : ℝ) T) atTop (𝓝 (Bfun (2 : ℝ))) :=
    tendsto_TopEdge (u0 := (2 : ℝ)) hu (by norm_num)
  have hF :
      Tendsto
          (fun z : ℍ =>
            (ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ)) - (2 : ℂ)) / (qHalf z) ^ (2 : ℕ))
          atImInfty (𝓝 (-464 : ℂ)) :=
    tendsto_ψI_mul_cexp_four_pi_mul_I_sub_two_div_qHalf_sq
  have hTop464 : Tendsto (fun T : ℝ => TopEdge (2 : ℝ) T) atTop (𝓝 (-464 : ℂ)) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    have hEv :
        ∀ᶠ z in atImInfty,
          ‖(ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ)) - (2 : ℂ)) / (qHalf z) ^ (2 : ℕ) -
              (-464 : ℂ)‖ <
            ε / 2 := by
      simpa [dist_eq_norm] using!
        (Metric.tendsto_nhds.1 hF) (ε / 2) (by nlinarith)
    rcases (Filter.eventually_atImInfty).1 hEv with ⟨A, hA⟩
    refine (eventually_atTop.2 ⟨max A 1, ?_⟩)
    intro T hT
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hT)
    have hAT : A ≤ T := le_trans (le_max_left _ _) hT
    -- Package points on the top edge as `ℍ`.
    let zH : ℝ → ℍ :=
      fun x : ℝ =>
        UpperHalfPlane.mk ((x : ℂ) + (T : ℂ) * Complex.I)
          (by simpa [Complex.add_im, Complex.mul_im] using! hTpos)
    let fT : ℝ → ℂ :=
      fun x : ℝ =>
        ψI' ((x : ℂ) + (T : ℂ) * Complex.I) *
          expU (2 : ℝ) ((x : ℂ) + (T : ℂ) * Complex.I)
    let hTfun : ℝ → ℂ :=
      fun x : ℝ =>
        (ψI (zH x) * cexp (4 * Real.pi * Complex.I * (zH x : ℂ)) - (2 : ℂ)) /
          (qHalf (zH x)) ^ (2 : ℕ)
    -- Use the `atImInfty` bound uniformly for `x ∈ [0,1]`.
    have hbound : ∀ x ∈ Ι (0 : ℝ) 1, ‖hTfun x - (-464 : ℂ)‖ ≤ ε / 2 := by
      intro x hx
      have hzIm : A ≤ (zH x).im := by
        simpa [zH, UpperHalfPlane.im, Complex.add_im, Complex.mul_im] using! hAT
      exact le_of_lt (by simpa [hTfun] using! (hA (zH x) hzIm))
    -- The extra term `2 / (qHalf(z)^2)` integrates to `0` on `[0,1]`.
    have hExtra : (∫ x in (0 : ℝ)..1, (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ)) = 0 := by
      -- `qHalf(zH x)^2 = exp(2π i (x+Ti))`, so the integrand is a constant multiple of
      -- `exp(-2π i x)`.
      have hq :
          ∀ x : ℝ,
            (qHalf (zH x)) ^ (2 : ℕ) =
              cexp (2 * Real.pi * Complex.I * ((x : ℂ) + (T : ℂ) * Complex.I)) := by
        intro x
        have h := (Complex.exp_nat_mul (((Real.pi : ℂ) * ((zH x : ℂ))) * Complex.I) 2).symm
        have hmul :
            (2 : ℂ) * (((Real.pi : ℂ) * ((zH x : ℂ))) * Complex.I) =
              2 * Real.pi * Complex.I * ((x : ℂ) + (T : ℂ) * Complex.I) := by
          simp [zH]
          ring_nf
        simpa [qHalf, zH, hmul, mul_assoc, mul_left_comm, mul_comm] using! h
      have hsplit :
          (fun x : ℝ => (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ)) =
            fun x : ℝ =>
              (2 : ℂ) * cexp (2 * Real.pi * (T : ℂ)) *
                cexp (-2 * Real.pi * Complex.I * (x : ℂ)) := by
        funext x
        have hinv :
            (cexp (2 * Real.pi * Complex.I * ((x : ℂ) + (T : ℂ) * Complex.I)))⁻¹ =
              cexp (2 * Real.pi * (T : ℂ)) * cexp (-2 * Real.pi * Complex.I * (x : ℂ)) := by
          have harg :
              -(2 * Real.pi * Complex.I * ((x : ℂ) + (T : ℂ) * Complex.I)) =
                (2 * Real.pi * (T : ℂ)) + (-2 * Real.pi * Complex.I * (x : ℂ)) := by
            ring_nf
            simp [mul_assoc, mul_left_comm, mul_comm, add_comm]
          calc
            (cexp (2 * Real.pi * Complex.I * ((x : ℂ) + (T : ℂ) * Complex.I)))⁻¹ =
                cexp (-(2 * Real.pi * Complex.I * ((x : ℂ) + (T : ℂ) * Complex.I))) := by
                  simpa using!
                    (Complex.exp_neg
                        (2 * Real.pi * Complex.I * ((x : ℂ) + (T : ℂ) * Complex.I))).symm
            _ = cexp ((2 * Real.pi * (T : ℂ)) + (-2 * Real.pi * Complex.I * (x : ℂ))) := by
                  simp [harg]
            _ = cexp (2 * Real.pi * (T : ℂ)) * cexp (-2 * Real.pi * Complex.I * (x : ℂ)) := by
                  simpa using!
                    (Complex.exp_add (2 * Real.pi * (T : ℂ))
                      (-2 * Real.pi * Complex.I * (x : ℂ)))
        have hq0 : (qHalf (zH x)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero (zH x))
        calc
          (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ) =
              (2 : ℂ) * ((qHalf (zH x)) ^ (2 : ℕ))⁻¹ := by
            simp [div_eq_mul_inv]
          _ =
              (2 : ℂ) * (cexp (2 * Real.pi * Complex.I * ((x : ℂ) + (T : ℂ) * Complex.I)))⁻¹ := by
            simp [hq x]
          _ =
              (2 : ℂ) *
                (cexp (2 * Real.pi * (T : ℂ)) * cexp (-2 * Real.pi * Complex.I * (x : ℂ))) := by
            simp [hinv]
          _ =
              (2 : ℂ) * cexp (2 * Real.pi * (T : ℂ)) *
                cexp (-2 * Real.pi * Complex.I * (x : ℂ)) := by
            ring
      have hint : (∫ x in (0 : ℝ)..1, cexp (-2 * Real.pi * Complex.I * (x : ℂ))) = 0 := by
        set c : ℂ := -2 * Real.pi * Complex.I
        have hc : c ≠ 0 := by
          have hpi : (Real.pi : ℂ) ≠ 0 := by
            exact_mod_cast (ne_of_gt Real.pi_pos)
          have h2 : (-2 : ℂ) ≠ 0 := by norm_num
          have hI : (Complex.I : ℂ) ≠ 0 := by simp
          dsimp [c]
          exact mul_ne_zero (mul_ne_zero h2 hpi) hI
        have hc1 : Complex.exp c = (1 : ℂ) := by
          calc
            Complex.exp c = Complex.exp (-(2 * Real.pi * Complex.I)) := by simp [c, mul_assoc]
            _ = (Complex.exp (2 * Real.pi * Complex.I))⁻¹ := by
                  simpa using! (Complex.exp_neg (2 * Real.pi * Complex.I))
            _ = 1 := by simp [Complex.exp_two_pi_mul_I]
        have hInt :
            (∫ x in (0 : ℝ)..1, Complex.exp (c * x)) =
              (Complex.exp (c * (1 : ℝ)) - Complex.exp (c * (0 : ℝ))) / c := by
          simpa [c] using!
            (integral_exp_mul_complex (a := (0 : ℝ)) (b := (1 : ℝ)) (c := c) hc)
        have hInt0 : (∫ x in (0 : ℝ)..1, Complex.exp (c * x)) = 0 := by
          have : (Complex.exp (c * (1 : ℝ)) - Complex.exp (c * (0 : ℝ))) / c = 0 := by
            simp [hc1]
          exact hInt.trans this
        assumption
      -- Put together (factor out the constants).
      simp_all
    -- Rewrite `TopEdge(2,T)` as `∫ hTfun`.
    have hInt : TopEdge (2 : ℝ) T = ∫ x in (0 : ℝ)..1, hTfun x := by
      -- Pointwise: `ψI * expU 2 = hTfun + 2/qHalf^2`.
      have hfT : ∀ x, fT x = hTfun x + (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ) := by
        intro x
        have hz0 : 0 < ((x : ℂ) + (T : ℂ) * Complex.I).im := by
          simpa [Complex.add_im, Complex.mul_im] using! hTpos
        have hψI' : ψI' ((x : ℂ) + (T : ℂ) * Complex.I) = ψI (zH x) := by
          simpa [zH] using! (ψI'_eq_of_im_pos (z := (x : ℂ) + (T : ℂ) * Complex.I) hz0)
        have hexpU : expU (2 : ℝ) ((x : ℂ) + (T : ℂ) * Complex.I) = (qHalf (zH x)) ^ (2 : ℕ) := by
          -- `expU 2 z = exp(2π i z) = qFull(z) = qHalf(z)^2`.
          have : expU (2 : ℝ) ((x : ℂ) + (T : ℂ) * Complex.I) = qFull (zH x) := by
            simp [expU, qFull, zH, mul_assoc, mul_left_comm, mul_comm]
          calc
            expU (2 : ℝ) ((x : ℂ) + (T : ℂ) * Complex.I) = qFull (zH x) := this
            _ = (qHalf (zH x)) ^ (2 : ℕ) := by
                  simpa using! (qFull_eq_qHalf_sq (z := zH x))
        have hq0 : (qHalf (zH x)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero (zH x))
        have hq4 :
            (qHalf (zH x)) ^ (4 : ℕ) = cexp (4 * Real.pi * Complex.I * (zH x : ℂ)) := by
          have h := (Complex.exp_nat_mul (((Real.pi : ℂ) * ((zH x : ℂ))) * Complex.I) 4).symm
          have hmul :
              (4 : ℂ) * (((Real.pi : ℂ) * ((zH x : ℂ))) * Complex.I) =
                4 * Real.pi * Complex.I * (zH x : ℂ) := by
            ring
          simpa [qHalf, hmul, mul_assoc, mul_left_comm, mul_comm] using! h
        have hrel :
            ψI (zH x) * (qHalf (zH x)) ^ (2 : ℕ) =
              (ψI (zH x) * cexp (4 * Real.pi * Complex.I * (zH x : ℂ))) /
                (qHalf (zH x)) ^ (2 : ℕ) := by
          have hq4' : cexp (4 * Real.pi * Complex.I * (zH x : ℂ)) = (qHalf (zH x)) ^ (4 : ℕ) := by
            simpa using! hq4.symm
          -- Rewrite the numerator, then cancel `q^2`.
          rw [hq4']
          field_simp [hq0]
        -- Now expand `(a-2)/q + 2/q = a/q`.
        have hsplit' :
            (ψI (zH x) * cexp (4 * Real.pi * Complex.I * (zH x : ℂ))) / (qHalf (zH x)) ^ (2 : ℕ) =
              (ψI (zH x) * cexp (4 * Real.pi * Complex.I * (zH x : ℂ)) - (2 : ℂ)) /
                  (qHalf (zH x)) ^ (2 : ℕ) +
                (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ) := by
          field_simp [hq0]
          ring_nf
        -- Put together.
        calc
          fT x = ψI (zH x) * (qHalf (zH x)) ^ (2 : ℕ) := by
            simp [fT, hψI', hexpU]
          _ =
              (ψI (zH x) * cexp (4 * Real.pi * Complex.I * (zH x : ℂ))) /
                (qHalf (zH x)) ^ (2 : ℕ) := hrel
          _ = hTfun x + (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ) := by
            simp [hTfun, hsplit']
      -- Establish interval-integrability from continuity.
      have hzHcont : Continuous zH := by
        fun_prop
      have hqHalfCont : Continuous qHalf := by
        have hcoe : Continuous fun z : ℍ => (z : ℂ) := UpperHalfPlane.continuous_coe
        have hlin : Continuous fun z : ℍ => ((Real.pi : ℂ) * (z : ℂ)) := continuous_const.mul hcoe
        have hlin' : Continuous fun z : ℍ => ((Real.pi : ℂ) * (z : ℂ)) * Complex.I :=
          hlin.mul continuous_const
        simpa [qHalf] using! hlin'.cexp
      have hqCont : Continuous fun x : ℝ => qHalf (zH x) := hqHalfCont.comp hzHcont
      have hq2Cont : Continuous fun x : ℝ => (qHalf (zH x)) ^ (2 : ℕ) := hqCont.pow 2
      have hq2Inv : Continuous fun x : ℝ => ((qHalf (zH x)) ^ (2 : ℕ))⁻¹ := by
        refine hq2Cont.inv₀ ?_
        intro x
        exact pow_ne_zero 2 (qHalf_ne_zero (zH x))
      have hψCont : Continuous fun x : ℝ => ψI (zH x) := continuous_ψI.comp hzHcont
      have hExpCont : Continuous fun x : ℝ => cexp (4 * Real.pi * Complex.I * (zH x : ℂ)) := by
        fun_prop
      have hTfunCont : Continuous hTfun := by
        have hEq : hTfun = fun x : ℝ =>
            (ψI (zH x) * cexp (4 * Real.pi * Complex.I * (zH x : ℂ)) - (2 : ℂ)) *
              ((qHalf (zH x)) ^ (2 : ℕ))⁻¹ := by
          funext x
          simp [hTfun, div_eq_mul_inv]
        have hnum :
            Continuous fun x : ℝ =>
              ψI (zH x) * cexp (4 * Real.pi * Complex.I * (zH x : ℂ)) - (2 : ℂ) :=
          (hψCont.mul hExpCont).sub continuous_const
        simpa [hEq] using! hnum.mul hq2Inv
      have hExtraCont : Continuous fun x : ℝ => (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ) := by
        have hEq :
            (fun x : ℝ => (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ)) =
              fun x : ℝ => (2 : ℂ) * ((qHalf (zH x)) ^ (2 : ℕ))⁻¹ := by
          funext x
          simp [div_eq_mul_inv]
        simpa [hEq] using! (continuous_const.mul hq2Inv)
      have hIntH : IntervalIntegrable hTfun MeasureTheory.volume (0 : ℝ) 1 :=
        (hTfunCont.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)))
      have hIntExtra :
          IntervalIntegrable
              (fun x : ℝ => (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ))
              MeasureTheory.volume (0 : ℝ) 1 :=
        (hExtraCont.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)))
      have hsum :=
        (intervalIntegral.integral_add (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := hTfun) (g := fun x : ℝ => (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ)) hIntH hIntExtra)
      have : ∫ x in (0 : ℝ)..1, fT x = ∫ x in (0 : ℝ)..1, hTfun x := by
        calc
          ∫ x in (0 : ℝ)..1, fT x =
              ∫ x in (0 : ℝ)..1, (hTfun x + (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ)) := by
            refine intervalIntegral.integral_congr ?_
            intro x hx
            simp [hfT x]
          _ =
              (∫ x in (0 : ℝ)..1, hTfun x) +
                ∫ x in (0 : ℝ)..1, (2 : ℂ) / (qHalf (zH x)) ^ (2 : ℕ) := by
            exact hsum
          _ = ∫ x in (0 : ℝ)..1, hTfun x := by simp [hExtra]
      simpa [TopEdge, fT, zH] using! this
    -- Bound `‖TopEdge - (-464)‖` by integrating the pointwise bound.
    have hdiff :
        TopEdge (2 : ℝ) T - (-464 : ℂ) = ∫ x in (0 : ℝ)..1, (hTfun x - (-464 : ℂ)) := by
      have hIntC : IntervalIntegrable (fun _ : ℝ => (-464 : ℂ)) MeasureTheory.volume (0 : ℝ) 1 := by
        exact
          (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ))
            (b := (1 : ℝ)))
      have hIntH : IntervalIntegrable hTfun MeasureTheory.volume (0 : ℝ) 1 := by
        have hzHcont : Continuous zH := by
          fun_prop
        have hqHalfCont : Continuous qHalf := by
          have hcoe : Continuous fun z : ℍ => (z : ℂ) := UpperHalfPlane.continuous_coe
          have hlin : Continuous fun z : ℍ => ((Real.pi : ℂ) * (z : ℂ)) := continuous_const.mul hcoe
          have hlin' : Continuous fun z : ℍ => ((Real.pi : ℂ) * (z : ℂ)) * Complex.I :=
            hlin.mul continuous_const
          simpa [qHalf] using! hlin'.cexp
        have hqCont : Continuous fun x : ℝ => qHalf (zH x) := hqHalfCont.comp hzHcont
        have hq2Cont : Continuous fun x : ℝ => (qHalf (zH x)) ^ (2 : ℕ) := hqCont.pow 2
        have hq2Inv : Continuous fun x : ℝ => ((qHalf (zH x)) ^ (2 : ℕ))⁻¹ := by
          refine hq2Cont.inv₀ ?_
          intro x
          exact pow_ne_zero 2 (qHalf_ne_zero (zH x))
        have hψCont : Continuous fun x : ℝ => ψI (zH x) := continuous_ψI.comp hzHcont
        have hExpCont : Continuous fun x : ℝ => cexp (4 * Real.pi * Complex.I * (zH x : ℂ)) := by
          fun_prop
        have hTfunCont : Continuous hTfun := by
          have hEq : hTfun = fun x : ℝ =>
              (ψI (zH x) * cexp (4 * Real.pi * Complex.I * (zH x : ℂ)) - (2 : ℂ)) *
                ((qHalf (zH x)) ^ (2 : ℕ))⁻¹ := by
            funext x
            simp [hTfun, div_eq_mul_inv]
          have hnum :
              Continuous fun x : ℝ =>
                ψI (zH x) * cexp (4 * Real.pi * Complex.I * (zH x : ℂ)) - (2 : ℂ) :=
            (hψCont.mul hExpCont).sub continuous_const
          simpa [hEq] using! hnum.mul hq2Inv
        exact
          hTfunCont.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
      have hsub :=
        intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := hTfun) (g := fun _ : ℝ => (-464 : ℂ)) hIntH hIntC
      have hconst : (∫ x in (0 : ℝ)..1, (-464 : ℂ)) = (-464 : ℂ) := by
        simp [intervalIntegral.integral_const]
      simpa [hInt, hconst, sub_eq_add_neg, add_assoc] using! hsub.symm
    have hnorm :
        ‖∫ x in (0 : ℝ)..1, (hTfun x - (-464 : ℂ))‖ ≤ (ε / 2) * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
        have := hbound x hx
        simpa [sub_eq_add_neg, add_assoc] using! this)
    have hle : ‖TopEdge (2 : ℝ) T - (-464 : ℂ)‖ ≤ ε / 2 := by
      simpa [hdiff] using! (hnorm.trans_eq (by simp))
    have hlt : ‖TopEdge (2 : ℝ) T - (-464 : ℂ)‖ < ε := by
      have : (ε / 2 : ℝ) < ε := by nlinarith
      exact lt_of_le_of_lt hle this
    simpa [dist_eq_norm] using! hlt
  exact tendsto_nhds_unique hTopB hTop464

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
