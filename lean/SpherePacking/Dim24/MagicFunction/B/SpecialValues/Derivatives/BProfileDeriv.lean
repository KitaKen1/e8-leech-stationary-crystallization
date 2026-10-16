-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.BfunTwo
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.BfunFour
import SpherePacking.Dim24.MagicFunction.B.Defs.J4Smooth
import SpherePacking.ForMathlib.IntervalIntegral


/-!
# Derivatives of `bProfile` at `u = 2` and `u = 4`

These are obtained from the factorization of the `246` block together with the special values
`Bfun 2 = -464` and `Bfun 4 = 2`.

## Main statements
* `bProfile_hasDerivAt_two`
* `bProfile_hasDerivAt_four`
-/

open scoped Real

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open intervalIntegral
open RealIntegrals
open scoped Topology Interval

namespace Deriv

/-- Reparametrize `J₄' u` as minus the integral over the top edge `x ↦ x + i`. -/
public lemma J₄'_eq_neg_topEdge (u : ℝ) :
    J₄' u =
      -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
  -- Same reparametrization as in `J₂'_J₄'_J₆'_factor`, isolated as a reusable lemma.
  have hEq :
      (∫ t in (0 : ℝ)..1,
            (-1 : ℂ) * ψT' (MagicFunction.Parametrisations.z₄' t) *
              expU u (MagicFunction.Parametrisations.z₄' t)) =
        ∫ t in (0 : ℝ)..1,
          (-1 : ℂ) *
            (ψT' ((1 - t : ℂ) + Complex.I) * expU u ((1 - t : ℂ) + Complex.I)) := by
    refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
    have hz4 : MagicFunction.Parametrisations.z₄' t = (1 - t : ℂ) + Complex.I := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
        (MagicFunction.Parametrisations.z₄'_eq_of_mem (t := t) htIcc)
    simp [hz4]
  let f : ℝ → ℂ := fun t : ℝ => ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)
  have hneg :
      (∫ t in (0 : ℝ)..1, (-1 : ℂ) * f (1 - t)) = -∫ t in (0 : ℝ)..1, f t := by
    exact SpherePacking.ForMathlib.intervalIntegral_neg_one_mul_comp_one_sub_eq_neg (f := f)
  have hJ4 :
      J₄' u =
          ∫ t in (0 : ℝ)..1,
            (-1 : ℂ) *
              (ψT' (MagicFunction.Parametrisations.z₄' t) *
                expU u (MagicFunction.Parametrisations.z₄' t)) := by
    simp [RealIntegrals.J₄', expU, mul_assoc, mul_left_comm, mul_comm]
  -- Assemble: rewrite `z₄' t`, then integrate with the substitution `t ↦ 1 - t`.
  calc
    J₄' u =
          ∫ t in (0 : ℝ)..1,
            (-1 : ℂ) *
              (ψT' (MagicFunction.Parametrisations.z₄' t) *
                expU u (MagicFunction.Parametrisations.z₄' t)) := hJ4
    _ =
        ∫ t in (0 : ℝ)..1,
          (-1 : ℂ) *
            (ψT' ((1 - t : ℂ) + Complex.I) * expU u ((1 - t : ℂ) + Complex.I)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using! hEq
    _ = -∫ t in (0 : ℝ)..1, f t := by
          simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using! hneg
    _ = -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := rfl

lemma Bfun_eq_neg_J₄'_add_neg_half_J₆' (u : ℝ) :
    Bfun u = (-J₄' u) + (-1 / 2 : ℂ) * J₆' u := by
  have hTop :
      (∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) = -J₄' u := by
    have h := J₄'_eq_neg_topEdge (u := u)
    have h' := congrArg Neg.neg h
    simpa using! h'.symm
  have hJ6 := J₆'_eq_vertical_Ioi (u := u)
  have hVert :
      (Complex.I •
          ∫ (t : ℝ) in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)) =
        (-1 / 2 : ℂ) * J₆' u := by
    -- Package the vertical term as `X` to avoid rewriting issues.
    grind only
  -- Use the two identifications.
  dsimp [Bfun]
  simpa [hTop, hVert, add_assoc]

end Deriv

lemma hasDerivAt_expU_one_inv_sub_one (u0 : ℝ) :
    HasDerivAt (fun u : ℝ => (expU u 1)⁻¹ - 1)
      (-(expU u0 1)⁻¹ * ((Real.pi : ℂ) * Complex.I)) u0 := by
  -- Write `(expU u 1)⁻¹` as `cexp (c * u)` with `c = -π i`.
  let c : ℂ := -((Real.pi : ℂ) * Complex.I)
  have hlinC : HasDerivAt (fun z : ℂ => c * z) c (u0 : ℂ) := by
    simpa using! (hasDerivAt_const_mul c (x := (u0 : ℂ)))
  have hlinR : HasDerivAt (fun u : ℝ => c * (u : ℂ)) c u0 :=
    HasDerivAt.comp_ofReal (z := u0) hlinC
  have hexp :
      HasDerivAt (fun u : ℝ => Complex.exp (c * (u : ℂ)))
        (Complex.exp (c * (u0 : ℂ)) * c) u0 := by
    simpa using! hlinR.cexp
  have hinv :
      (fun u : ℝ => (expU u 1)⁻¹) = fun u : ℝ => Complex.exp (c * (u : ℂ)) := by
    funext u
    have : expU u 1 = Complex.exp ((Real.pi : ℂ) * Complex.I * (u : ℂ)) := by
      simp [expU, mul_left_comm, mul_comm]
    have : (expU u 1)⁻¹ = Complex.exp (-((Real.pi : ℂ) * Complex.I * (u : ℂ))) := by
      simpa [this] using! (Complex.exp_neg ((Real.pi : ℂ) * Complex.I * (u : ℂ))).symm
    simpa [c, mul_assoc, mul_left_comm, mul_comm] using! this
  have hexp' :
      HasDerivAt (fun u : ℝ => (expU u 1)⁻¹) (Complex.exp (c * (u0 : ℂ)) * c) u0 := by
    simpa [hinv] using! hexp
  have hsub :
      HasDerivAt (fun u : ℝ => (expU u 1)⁻¹ - 1) (Complex.exp (c * (u0 : ℂ)) * c) u0 :=
    hexp'.sub_const (1 : ℂ)
  have hexp0 : Complex.exp (c * (u0 : ℂ)) = (expU u0 1)⁻¹ :=
    (congrArg (fun f : ℝ → ℂ => f u0) hinv).symm
  grind only

/-- Derivative of `bProfile` at `u = 4`. -/
public lemma bProfile_hasDerivAt_four :
    HasDerivAt bProfile ((-2 : ℝ) * (π : ℝ) * Complex.I) (4 : ℝ) := by
  -- Split `bProfile` into the `135` and `246` blocks.
  let f135 : ℝ → ℂ := fun u : ℝ => J₁' u + J₃' u + J₅' u
  let f246 : ℝ → ℂ := fun u : ℝ => J₂' u + J₄' u + J₆' u
  have hb : bProfile = fun u : ℝ => f135 u + f246 u := by
    funext u
    simp [bProfile, RealIntegrals.b', f135, f246, add_assoc, add_left_comm]
  have hu : expU (4 : ℝ) 1 = 1 := by
    have h2 : ((2 : ℤ) : ℂ) = (2 : ℂ) := by norm_num
    have h4 : (2 : ℂ) * (2 : ℂ) = (4 : ℂ) := by norm_num
    simpa [expU, mul_assoc, mul_left_comm, mul_comm, h2, h4] using!
      (Complex.exp_int_mul_two_pi_mul_I (n := (2 : ℤ)))
  have h135 : HasDerivAt f135 0 (4 : ℝ) := J₁'_J₃'_J₅'_hasDerivAt_zero_of (u0 := (4 : ℝ)) hu
  -- Factor the `246` block as `a * Bfun` in a neighborhood of `4`.
  let a : ℝ → ℂ := fun u : ℝ => (expU u 1)⁻¹ - 1
  let b : ℝ → ℂ := fun u : ℝ => Deriv.Bfun u
  have hEq : f246 =ᶠ[𝓝 (4 : ℝ)] fun u : ℝ => a u * b u := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 4)] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    simpa [f246, a, b, Deriv.Bfun] using! (J₂'_J₄'_J₆'_factor (u := u) hu0)
  have ha : HasDerivAt a (-(expU (4 : ℝ) 1)⁻¹ * ((Real.pi : ℂ) * Complex.I)) (4 : ℝ) :=
    hasDerivAt_expU_one_inv_sub_one (u0 := (4 : ℝ))
  have hb_diff : DifferentiableAt ℝ b (4 : ℝ) := by
    have hbfun : b = fun u : ℝ => (-J₄' u) + (-1 / 2 : ℂ) * J₆' u := by
      funext u
      simpa [b] using! (Deriv.Bfun_eq_neg_J₄'_add_neg_half_J₆' (u := u))
    have hJ4 : DifferentiableAt ℝ RealIntegrals.J₄' (4 : ℝ) :=
      (Schwartz.J4Smooth.contDiff_J₄'.contDiffAt (x := (4 : ℝ))).differentiableAt (by simp)
    have hIoi : Set.Ioi (-1 : ℝ) ∈ nhds (4 : ℝ) :=
      isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 4)
    have hJ6 : DifferentiableAt ℝ RealIntegrals.J₆' (4 : ℝ) := by
      have hcont := Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1
      exact (hcont.contDiffAt (x := (4 : ℝ)) hIoi).differentiableAt (by simp)
    simp_all
  have hb' : HasDerivAt b (deriv b (4 : ℝ)) (4 : ℝ) := hb_diff.hasDerivAt
  have hab :
      HasDerivAt (fun u : ℝ => a u * b u)
        ((-(expU (4 : ℝ) 1)⁻¹ * ((Real.pi : ℂ) * Complex.I)) * b (4 : ℝ) +
          a (4 : ℝ) * deriv b (4 : ℝ))
        (4 : ℝ) :=
    ha.mul hb'
  have ha0 : a (4 : ℝ) = 0 := by simp [a, hu]
  have hb4 : b (4 : ℝ) = (2 : ℂ) := by
    simpa [b] using! Deriv.Bfun_four
  have hab'' : HasDerivAt (fun u : ℝ => a u * b u) (-(2 * (Real.pi : ℂ) * Complex.I)) (4 : ℝ) := by
    simpa [ha0, hb4, hu, a, mul_assoc, mul_left_comm, mul_comm] using! hab
  have h246 : HasDerivAt f246 (-(2 * (Real.pi : ℂ) * Complex.I)) (4 : ℝ) :=
    hab''.congr_of_eventuallyEq hEq
  have hbprof :
      HasDerivAt (fun u : ℝ => f135 u + f246 u) (-(2 * (Real.pi : ℂ) * Complex.I)) (4 : ℝ) :=
    by simpa using! h135.add h246
  have hbprof' : HasDerivAt bProfile (-(2 * (Real.pi : ℂ) * Complex.I)) (4 : ℝ) := by
    simpa [hb] using! hbprof
  simpa [mul_assoc] using! hbprof'

/-- Derivative of `bProfile` at `u = 2`. -/
public lemma bProfile_hasDerivAt_two :
    HasDerivAt bProfile ((464 : ℝ) * (π : ℝ) * Complex.I) (2 : ℝ) := by
  -- Split `bProfile` into the `135` and `246` blocks.
  let f135 : ℝ → ℂ := fun u : ℝ => J₁' u + J₃' u + J₅' u
  let f246 : ℝ → ℂ := fun u : ℝ => J₂' u + J₄' u + J₆' u
  have hb : bProfile = fun u : ℝ => f135 u + f246 u := by
    funext u
    simp [bProfile, RealIntegrals.b', f135, f246, add_assoc, add_left_comm]
  have hu : expU (2 : ℝ) 1 = 1 := by
    simpa [expU, mul_assoc, mul_left_comm, mul_comm] using! (Complex.exp_two_pi_mul_I)
  have h135 : HasDerivAt f135 0 (2 : ℝ) := J₁'_J₃'_J₅'_hasDerivAt_zero_of (u0 := (2 : ℝ)) hu
  let a : ℝ → ℂ := fun u : ℝ => (expU u 1)⁻¹ - 1
  let b : ℝ → ℂ := fun u : ℝ => Deriv.Bfun u
  have hEq : f246 =ᶠ[𝓝 (2 : ℝ)] fun u : ℝ => a u * b u := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 2)] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    simpa [f246, a, b, Deriv.Bfun] using! (J₂'_J₄'_J₆'_factor (u := u) hu0)
  have ha : HasDerivAt a (-(expU (2 : ℝ) 1)⁻¹ * ((Real.pi : ℂ) * Complex.I)) (2 : ℝ) :=
    hasDerivAt_expU_one_inv_sub_one (u0 := (2 : ℝ))
  have hb_diff : DifferentiableAt ℝ b (2 : ℝ) := by
    have hbfun : b = fun u : ℝ => (-J₄' u) + (-1 / 2 : ℂ) * J₆' u := by
      funext u
      simpa [b] using! (Deriv.Bfun_eq_neg_J₄'_add_neg_half_J₆' (u := u))
    have hJ4 : DifferentiableAt ℝ RealIntegrals.J₄' (2 : ℝ) :=
      (Schwartz.J4Smooth.contDiff_J₄'.contDiffAt (x := (2 : ℝ))).differentiableAt (by simp)
    have hIoi : Set.Ioi (-1 : ℝ) ∈ nhds (2 : ℝ) :=
      isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 2)
    have hJ6 : DifferentiableAt ℝ RealIntegrals.J₆' (2 : ℝ) := by
      have hcont := Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1
      exact (hcont.contDiffAt (x := (2 : ℝ)) hIoi).differentiableAt (by simp)
    simp_all
  have hb' : HasDerivAt b (deriv b (2 : ℝ)) (2 : ℝ) := hb_diff.hasDerivAt
  have hab :
      HasDerivAt (fun u : ℝ => a u * b u)
        ((-(expU (2 : ℝ) 1)⁻¹ * ((Real.pi : ℂ) * Complex.I)) * b (2 : ℝ) +
          a (2 : ℝ) * deriv b (2 : ℝ))
        (2 : ℝ) :=
    ha.mul hb'
  have ha0 : a (2 : ℝ) = 0 := by simp [a, hu]
  have hb2 : b (2 : ℝ) = (-464 : ℂ) := by
    simpa [b] using! Deriv.Bfun_two
  have hab'' :
      HasDerivAt (fun u : ℝ => a u * b u) (((464 : ℂ) * (Real.pi : ℂ) * Complex.I)) (2 : ℝ) := by
    -- Simplify the product rule constant using `a 2 = 0`, `b 2 = -464`, and `expU 2 1 = 1`.
    simpa [ha0, hb2, hu, a, mul_assoc, mul_left_comm, mul_comm] using! hab
  have h246 : HasDerivAt f246 ((464 : ℂ) * (Real.pi : ℂ) * Complex.I) (2 : ℝ) :=
    hab''.congr_of_eventuallyEq hEq
  have hbprof :
      HasDerivAt (fun u : ℝ => f135 u + f246 u) ((464 : ℂ) * (Real.pi : ℂ) * Complex.I) (2 : ℝ) :=
    by simpa using! h135.add h246
  have hbprof' : HasDerivAt bProfile ((464 : ℂ) * (Real.pi : ℂ) * Complex.I) (2 : ℝ) := by
    simpa [hb] using! hbprof
  -- Match the file's normalization.
  simpa [mul_assoc] using! hbprof'

end SpecialValuesAux.EvenU
end

end SpherePacking.Dim24
