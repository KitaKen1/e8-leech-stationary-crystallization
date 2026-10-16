-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.ModularForms.Psi.Defs
public import SpherePacking.Dim24.MagicFunction.Radial
public import SpherePacking.ForMathlib.RadialSchwartz.OneSided
public import SpherePacking.MagicFunction.IntegralParametrisations
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import SpherePacking.Dim24.ModularForms.Psi.Relations


/-!
# Total extensions and contour-integral decomposition for `bProfile`

We define total extensions `ψ*' : ℂ → ℂ` of the modular forms `ψ* : ℍ → ℂ`, equal to `0` outside
the upper half-plane, and use them to express the one-variable profile `bProfile` as a sum of six
contour integrals `J₁', ..., J₆'` (as in `dim_24.tex`).

The file also records exponential bounds on the imaginary axis in `PsiExpBounds`, used to control
the tail integral `J₆'`.

## Main definitions
* `ψI'`, `ψS'`, `ψT'`
* `RealIntegrals.J₁'`, ..., `RealIntegrals.J₆'`, `RealIntegrals.b'`, `bProfile`

## Main statements
* `differentiableOn_ψT'_upper`, `ψT'_eq_ψI'_add_one`
* `PsiExpBounds.exists_bound_norm_H₂_resToImagAxis_exp_Ici_one`
* `PsiRewrites.ψS_apply_eq_factor`
-/

namespace SpherePacking.Dim24

noncomputable section

open scoped UpperHalfPlane Manifold
open scoped Complex

open Complex

open intervalIntegral
open MagicFunction.Parametrisations


/--
Total extension of `ψI : ℍ → ℂ` to a function on `ℂ`, defined as `0` off the upper half-plane.
-/
@[expose] public def ψI' (z : ℂ) : ℂ := if hz : 0 < z.im then ψI ⟨z, hz⟩ else 0

/--
Total extension of `ψS : ℍ → ℂ` to a function on `ℂ`, defined as `0` off the upper half-plane.
-/
@[expose] public def ψS' (z : ℂ) : ℂ := if hz : 0 < z.im then ψS ⟨z, hz⟩ else 0

/--
Total extension of `ψT : ℍ → ℂ` to a function on `ℂ`, defined as `0` off the upper half-plane.
-/
@[expose] public def ψT' (z : ℂ) : ℂ := if hz : 0 < z.im then ψT ⟨z, hz⟩ else 0

lemma differentiableOn_ψT_ofComplex :
    DifferentiableOn ℂ
      (fun z : ℂ => ψT (UpperHalfPlane.ofComplex z))
      UpperHalfPlane.upperHalfPlaneSet := by
  have hψI :
      DifferentiableOn ℂ
        (fun z : ℂ => ψI (UpperHalfPlane.ofComplex z))
        UpperHalfPlane.upperHalfPlaneSet :=
    differentiableOn_ψI_ofComplex
  have hadd : DifferentiableOn ℂ (fun z : ℂ => z + 1) UpperHalfPlane.upperHalfPlaneSet := by
    fun_prop
  have hmaps :
      Set.MapsTo (fun z : ℂ => z + 1)
        UpperHalfPlane.upperHalfPlaneSet
        UpperHalfPlane.upperHalfPlaneSet := by
    intro z hz
    simpa [UpperHalfPlane.upperHalfPlaneSet, Complex.add_im] using! hz
  have hcomp :
      DifferentiableOn ℂ
        (fun z : ℂ => ψI (UpperHalfPlane.ofComplex (z + 1)))
        UpperHalfPlane.upperHalfPlaneSet := by
    simpa [Function.comp] using! (hψI.comp hadd hmaps)
  refine hcomp.congr ?_
  intro z hz
  have hz' : 0 < z.im := by simpa [UpperHalfPlane.upperHalfPlaneSet] using! hz
  have hz1 : 0 < (z + 1).im := by simpa [Complex.add_im] using! hz'
  have hvadd :
      ((1 : ℝ) +ᵥ (UpperHalfPlane.ofComplex z) : ℍ) = UpperHalfPlane.ofComplex (z + 1) := by
    ext1
    simp
      [ UpperHalfPlane.ofComplex_apply_of_im_pos hz'
      , UpperHalfPlane.ofComplex_apply_of_im_pos hz1
      , UpperHalfPlane.coe_vadd
      , add_comm
      ]
  have hψ : ψT (UpperHalfPlane.ofComplex z) = ψI (UpperHalfPlane.ofComplex (z + 1)) := by
    simp [ψT, modular_slash_T_apply, hvadd]
  exact hψ

/-- The total extension `ψT'` is complex-differentiable on the upper half-plane. -/
public lemma differentiableOn_ψT'_upper :
    DifferentiableOn ℂ ψT' UpperHalfPlane.upperHalfPlaneSet := by
  refine (differentiableOn_ψT_ofComplex).congr ?_
  intro z hz
  have hz' : 0 < z.im := by simpa [UpperHalfPlane.upperHalfPlaneSet] using! hz
  simp [ψT', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']

/-- Translation identity for the total extensions: `ψT' z = ψI' (z + 1)`. -/
public lemma ψT'_eq_ψI'_add_one (z : ℂ) : ψT' z = ψI' (z + 1) := by
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa [Complex.add_im] using! hz
    have htrans :
        ((1 : ℝ) +ᵥ (UpperHalfPlane.mk z hz : ℍ)) = (UpperHalfPlane.mk (z + 1) hz' : ℍ) := by
      ext
      simp [UpperHalfPlane.coe_vadd, add_comm]
    have hψ : ψT (UpperHalfPlane.mk z hz : ℍ) = ψI (UpperHalfPlane.mk (z + 1) hz' : ℍ) := by
      simp [ψT, modular_slash_T_apply, htrans]
    simp [ψT', ψI', hz]
    simpa [UpperHalfPlane.mk] using! hψ
  · have hz' : ¬ 0 < (z + 1).im := by simpa [Complex.add_im] using! hz
    simp [ψT', ψI', hz]

lemma ψI'_periodic_two (z : ℂ) : ψI' (z + 2) = ψI' z := by
  by_cases hz : 0 < z.im
  · have hz2 : 0 < (z + 2).im := by simpa [Complex.add_im] using! hz
    have hper : ψI (UpperHalfPlane.mk (z + 2) hz2) = ψI (UpperHalfPlane.mk z hz) := by
      have h' := SpherePacking.Dim24.ψI_periodic_two (z := (UpperHalfPlane.mk z hz : ℍ))
      have hcoe :
          (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ (UpperHalfPlane.mk z hz : ℍ))) : ℍ) =
            (UpperHalfPlane.mk (z + 2) hz2 : ℍ) := by
        ext
        simp [UpperHalfPlane.coe_vadd, add_comm, add_left_comm]
        norm_num
      simpa [hcoe] using! h'
    simpa [ψI', hz, hz2] using! hper
  · have hz2 : ¬ 0 < (z + 2).im := by simpa [Complex.add_im] using! hz
    simp [ψI', hz]

/-!
## Real-integral decomposition of the one-variable profile

Following `dim_24.tex`, Lemma 3.1 (`lemma:minusone`), after the contour shifts one obtains a sum
of integrals over the standard parametrizations `z₁', z₂', ..., z₆'`.

Here `u` corresponds to the paper's `r^2` in the exponential `exp(π i r^2 z)`.
-/

namespace RealIntegrals

/--
First contour-integral term in the decomposition of `bProfile`,
along the parametrization `z₁'`.
-/
@[expose] public def J₁' (u : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (Complex.I : ℂ) * ψT' (z₁' t) * cexp (Real.pi * Complex.I * (u : ℂ) * (z₁' t))

/--
Second contour-integral term in the decomposition of `bProfile`,
along the parametrization `z₂'`.
-/
@[expose] public def J₂' (u : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    ψT' (z₂' t) * cexp (Real.pi * Complex.I * (u : ℂ) * (z₂' t))

/--
Third contour-integral term in the decomposition of `bProfile`,
along the parametrization `z₃'`.
-/
@[expose] public def J₃' (u : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (Complex.I : ℂ) * ψT' (z₃' t) * cexp (Real.pi * Complex.I * (u : ℂ) * (z₃' t))

/--
Fourth contour-integral term in the decomposition of `bProfile`,
along the parametrization `z₄'`.
-/
@[expose] public def J₄' (u : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (-1 : ℂ) * ψT' (z₄' t) * cexp (Real.pi * Complex.I * (u : ℂ) * (z₄' t))

/--
Fifth contour-integral term in the decomposition of `bProfile`,
along the parametrization `z₅'`.
-/
@[expose] public def J₅' (u : ℝ) : ℂ :=
  (-2 : ℂ) * ∫ t in (0 : ℝ)..1,
    (Complex.I : ℂ) * ψI' (z₅' t) * cexp (Real.pi * Complex.I * (u : ℂ) * (z₅' t))

/--
Tail contour-integral term in the decomposition of `bProfile`,
over `t ∈ [1,∞)` along `z₆'`.
-/
@[expose] public def J₆' (u : ℝ) : ℂ :=
  (-2 : ℂ) * ∫ t in Set.Ici (1 : ℝ),
    (Complex.I : ℂ) * ψS' (z₆' t) * cexp (Real.pi * Complex.I * (u : ℂ) * (z₆' t))

/-- Sum of the six contour-integral pieces defining `bProfile`. -/
@[expose] public def b' (u : ℝ) : ℂ := J₁' u + J₂' u + J₃' u + J₄' u + J₅' u + J₆' u

end RealIntegrals

/-- One-variable profile used for the radial Schwartz function: `u ↦ b'(u)`. -/
@[expose] public def bProfile (u : ℝ) : ℂ := RealIntegrals.b' u

/-!
## Exponential bounds for `H₂` on the imaginary axis

This reproduces (in the dim-24 namespace) the key estimate from the dimension-8 development:
`‖H₂(it)‖ ≤ C * exp(-π t)` for `t ≥ 1`.

This estimate, together with algebraic rewrites of `ψS`, dominates the tail integral `J₆'`.
-/

namespace PsiExpBounds

open scoped UpperHalfPlane
open UpperHalfPlane Filter Topology
open HurwitzKernelBounds

lemma norm_Θ₂_term_resToImagAxis (n : ℤ) (t : ℝ) (ht : 0 < t) :
    ‖Θ₂_term n ⟨Complex.I * t, by simp [ht]⟩‖ =
      Real.exp (-Real.pi * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
  set τ : ℍ := ⟨(Complex.I : ℂ) * t, by simp [ht]⟩
  have hτ : (τ : ℂ) = (Complex.I : ℂ) * t := rfl
  have hterm :
      Θ₂_term n τ =
        cexp (Real.pi * (Complex.I : ℂ) * (τ : ℂ) / 4) *
          jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ) := by
    simp [Θ₂_term_as_jacobiTheta₂_term, hτ, mul_assoc]
  have hnorm_pref :
      ‖cexp (Real.pi * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ = Real.exp (-Real.pi * (t / 4)) := by
    have harg :
        (Real.pi * (Complex.I : ℂ) * (τ : ℂ) / 4 : ℂ) = (-(Real.pi * (t / 4)) : ℂ) := by
      have hI : ∀ x : ℂ, (Complex.I : ℂ) * ((Complex.I : ℂ) * x) = -x :=
        fun x => I_mul_I_mul x
      calc
        (Real.pi * (Complex.I : ℂ) * (τ : ℂ) / 4 : ℂ)
            = (Real.pi : ℂ) * ((Complex.I : ℂ) * ((Complex.I : ℂ) * ((t / 4 : ℝ) : ℂ))) := by
                simp [hτ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ = (Real.pi : ℂ) * (-( ((t / 4 : ℝ) : ℂ))) := by simp [hI]
        _ = (-(Real.pi * (t / 4)) : ℂ) := by simp
    have : ‖cexp (-(Real.pi * (t / 4)) : ℂ)‖ = Real.exp (-(Real.pi * (t / 4))) := by
      simp [Complex.norm_exp]
    simpa [harg] using! this
  have hnorm_core :
      ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ =
        Real.exp (-Real.pi * (n : ℝ) ^ 2 * t - 2 * Real.pi * (n : ℝ) * (t / 2)) := by
    have h := norm_jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)
    simpa [hτ] using! h
  have hcalc :
      Real.exp (-Real.pi * (t / 4)) *
          Real.exp (-Real.pi * (n : ℝ) ^ 2 * t - 2 * Real.pi * (n : ℝ) * (t / 2)) =
        Real.exp (-Real.pi * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
    calc
      Real.exp (-Real.pi * (t / 4)) *
          Real.exp (-Real.pi * (n : ℝ) ^ 2 * t - 2 * Real.pi * (n : ℝ) * (t / 2))
          =
          Real.exp
            ((-Real.pi * (t / 4)) +
              (-Real.pi * (n : ℝ) ^ 2 * t - 2 * Real.pi * (n : ℝ) * (t / 2))) := by
            simp [Real.exp_add]
      _ = Real.exp (-Real.pi * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
            congr 1
            ring
  have :
      ‖Θ₂_term n τ‖ = Real.exp (-Real.pi * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
    calc
      ‖Θ₂_term n τ‖ =
          ‖cexp (Real.pi * (Complex.I : ℂ) * (τ : ℂ) / 4)‖ *
            ‖jacobiTheta₂_term n ((τ : ℂ) / 2) (τ : ℂ)‖ := by
              simp [hterm]
      _ = Real.exp (-Real.pi * (t / 4)) *
          Real.exp (-Real.pi * (n : ℝ) ^ 2 * t - 2 * Real.pi * (n : ℝ) * (t / 2)) := by
            simp [hnorm_pref, hnorm_core]
      _ = Real.exp (-Real.pi * (((n : ℝ) + (1 / 2)) ^ 2) * t) := hcalc
  simpa [τ] using! this

lemma norm_Θ₂_resToImagAxis_le (t : ℝ) (ht : 0 < t) :
    ‖Θ₂.resToImagAxis t‖ ≤
      (2 * Real.exp (-Real.pi * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - Real.exp (-Real.pi * t)) := by
  set τ : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hsumm :
      Summable (fun n : ℤ => ‖Θ₂_term n τ‖) := by
    have hfi : Summable (f_int 0 (1 / 2 : ℝ) t) := summable_f_int 0 (1 / 2 : ℝ) ht
    refine hfi.congr ?_
    intro n
    have hn : ‖Θ₂_term n τ‖ = Real.exp (-Real.pi * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
      simpa [τ] using! norm_Θ₂_term_resToImagAxis n t ht
    simp [HurwitzKernelBounds.f_int, hn, pow_zero, one_mul]
  have htri :
      ‖Θ₂.resToImagAxis t‖ ≤ ∑' n : ℤ, ‖Θ₂_term n τ‖ := by
    change ‖ResToImagAxis Θ₂ t‖ ≤ ∑' n : ℤ, ‖Θ₂_term n τ‖
    have hrepr : (∑' n : ℤ, Θ₂_term n τ) = ResToImagAxis Θ₂ t := by
      simp [ResToImagAxis, Θ₂, τ, ht]
    simpa [hrepr] using! (norm_tsum_le_tsum_norm hsumm)
  have ha : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hsum :
      (∑' n : ℤ, ‖Θ₂_term n τ‖) = F_int 0 ((1 / 2 : ℝ) : UnitAddCircle) t := by
    have hterm : (fun n : ℤ => ‖Θ₂_term n τ‖) = fun n : ℤ => f_int 0 (1 / 2 : ℝ) t n := by
      funext n
      have hn : ‖Θ₂_term n τ‖ = Real.exp (-Real.pi * (((n : ℝ) + (1 / 2)) ^ 2) * t) := by
        simpa [τ] using! norm_Θ₂_term_resToImagAxis n t ht
      simp [HurwitzKernelBounds.f_int, hn, pow_zero, one_mul]
    tauto
  have hFint :
      F_int 0 ((1 / 2 : ℝ) : UnitAddCircle) t =
        F_nat 0 (1 / 2 : ℝ) t + F_nat 0 (1 / 2 : ℝ) t := by
    have h := F_int_eq_of_mem_Icc 0 (a := (1 / 2 : ℝ)) ha ht
    have hsub : (1 : ℝ) - (2⁻¹ : ℝ) = (2⁻¹ : ℝ) := by norm_num
    simpa [hsub] using! h
  have hbd_nat :
      ‖F_nat 0 (1 / 2 : ℝ) t‖ ≤
          Real.exp (-Real.pi * ((1 / 2 : ℝ) ^ 2) * t) / (1 - Real.exp (-Real.pi * t)) :=
    F_nat_zero_le (a := (1 / 2 : ℝ)) (ha := (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))) ht
  have hF_nat_nonneg : 0 ≤ F_nat 0 (1 / 2 : ℝ) t := by
    have _hs : Summable (f_nat 0 (1 / 2 : ℝ) t) := summable_f_nat 0 (1 / 2 : ℝ) ht
    have : 0 ≤ (∑' n : ℕ, f_nat 0 (1 / 2 : ℝ) t n) :=
      tsum_nonneg (fun n => by
        simp only [HurwitzKernelBounds.f_nat, pow_zero, one_div]
        positivity)
    simpa [F_nat] using! this
  have hbd_nat' :
      F_nat 0 (1 / 2 : ℝ) t ≤
          Real.exp (-Real.pi * ((1 / 2 : ℝ) ^ 2) * t) / (1 - Real.exp (-Real.pi * t)) := by
    have hF_nat_nonneg' : 0 ≤ F_nat 0 (2⁻¹ : ℝ) t := by simpa using! hF_nat_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hF_nat_nonneg'] using! hbd_nat
  grind only

/--
Exponential bound for `H₂` on the imaginary axis: there is `C` with
`‖H₂.resToImagAxis t‖ ≤ C * exp(-π t)` for `t ≥ 1`.
-/
public theorem exists_bound_norm_H₂_resToImagAxis_exp_Ici_one :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ‖H₂.resToImagAxis t‖ ≤ C * Real.exp (-Real.pi * t) := by
  let Cθ : ℝ := (2 : ℝ) / (1 - Real.exp (-Real.pi))
  refine ⟨Cθ ^ 4, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hΘ2 : ‖Θ₂.resToImagAxis t‖ ≤ Cθ * Real.exp (-Real.pi * (t / 4)) := by
    have hmain := norm_Θ₂_resToImagAxis_le t ht0
    have hden :
        (1 - Real.exp (-Real.pi * t)) ≥ (1 - Real.exp (-Real.pi)) := by
      have hmono : Real.exp (-Real.pi * t) ≤ Real.exp (-Real.pi : ℝ) := by
        have : (-Real.pi * t) ≤ (-Real.pi : ℝ) := by nlinarith [Real.pi_pos, ht]
        exact Real.exp_le_exp.2 this
      linarith
    have hquarter :
        Real.exp (-Real.pi * ((1 / 2 : ℝ) ^ 2) * t) = Real.exp (-Real.pi * (t / 4)) := by
      congr 1
      ring
    have hquarter' :
        (2 * Real.exp (-Real.pi * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - Real.exp (-Real.pi * t)) =
          (2 * Real.exp (-Real.pi * (t / 4))) / (1 - Real.exp (-Real.pi * t)) := by
      simpa using! congrArg (fun u => (2 * u) / (1 - Real.exp (-Real.pi * t))) hquarter
    have hden_pos : 0 < (1 - Real.exp (-Real.pi : ℝ)) := by
      have : Real.exp (-Real.pi : ℝ) < 1 := by
        simpa [Real.exp_lt_one_iff] using! (show (-Real.pi : ℝ) < 0 by nlinarith [Real.pi_pos])
      exact sub_pos.2 this
    have hden' : (1 - Real.exp (-Real.pi : ℝ)) ≤ (1 - Real.exp (-Real.pi * t)) := by
      linarith [hden]
    have hnum_nonneg : 0 ≤ (2 * Real.exp (-Real.pi * (t / 4))) := by positivity
    calc
      ‖Θ₂.resToImagAxis t‖ ≤
          (2 * Real.exp (-Real.pi * ((1 / 2 : ℝ) ^ 2) * t)) / (1 - Real.exp (-Real.pi * t)) := hmain
      _ = (2 * Real.exp (-Real.pi * (t / 4))) / (1 - Real.exp (-Real.pi * t)) := hquarter'
      _ ≤ (2 * Real.exp (-Real.pi * (t / 4))) / (1 - Real.exp (-Real.pi : ℝ)) := by
            exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden'
      _ = Cθ * Real.exp (-Real.pi * (t / 4)) := by
            simp [Cθ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hH2 : ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ 4 := by
    simp [H₂, Function.resToImagAxis, ResToImagAxis, ht0, norm_pow]
  have hpow : ‖Θ₂.resToImagAxis t‖ ^ 4 ≤ (Cθ * Real.exp (-Real.pi * (t / 4))) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) hΘ2 4
  calc
    ‖H₂.resToImagAxis t‖ = ‖Θ₂.resToImagAxis t‖ ^ 4 := hH2
    _ ≤ (Cθ * Real.exp (-Real.pi * (t / 4))) ^ 4 := hpow
    _ = (Cθ ^ 4) * Real.exp (-Real.pi * t) := by
          have hexp : Real.exp (-Real.pi * (t / 4)) ^ 4 = Real.exp (-Real.pi * t) := by
            calc
              Real.exp (-Real.pi * (t / 4)) ^ 4 = Real.exp (4 * (-Real.pi * (t / 4))) := by
                    simpa using! (Real.exp_nat_mul (-Real.pi * (t / 4)) 4).symm
              _ = Real.exp (-Real.pi * t) := by
                    congr 1
                    ring
          calc
            (Cθ * Real.exp (-Real.pi * (t / 4))) ^ 4 =
                (Cθ ^ 4) * (Real.exp (-Real.pi * (t / 4)) ^ 4) := by
                  simp [mul_pow]
            _ = (Cθ ^ 4) * Real.exp (-Real.pi * t) := by
                  rw [hexp]


end PsiExpBounds

/-!
## Algebraic rewrites for `ψS`

For analytic estimates on the imaginary axis, it is convenient to rewrite `ψS` in terms of the
theta modular forms `H₂,H₃,H₄` and the discriminant `Δ`.
-/

namespace PsiRewrites

open scoped Manifold

/-- Express `Δ` via the theta modular forms (Jacobi's product identity). -/
public lemma Delta_eq_H₂_H₃_H₄_apply (z : ℍ) :
    (Δ z : ℂ) = ((H₂ z) * (H₃ z) * (H₄ z)) ^ 2 / (256 : ℂ) := by
  simpa [Delta_apply] using! (Delta_eq_H₂_H₃_H₄ z)

/-- Rewrite `ψS` with denominator `H₃^4 H₄^4` (eliminating `Δ`). -/
public theorem ψS_apply_eq_factor (z : ℍ) :
    ψS z =
      -((256 : ℂ) ^ (2 : ℕ)) *
        (7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3) /
          ((H₃ z) ^ 4 * (H₄ z) ^ 4) := by
  have hΔ := Delta_eq_H₂_H₃_H₄_apply z
  have hH2 : H₂ z ≠ 0 := H₂_ne_zero z
  have hH3 : H₃ z ≠ 0 := H₃_ne_zero z
  have hH4 : H₄ z ≠ 0 := H₄_ne_zero z
  rw [ψS_apply z, hΔ]
  field_simp [hH2, hH3, hH4]

/-- Continuity of the modular form `ψS` as a function on `ℍ`. -/
public lemma continuous_ψS : Continuous ψS := by
  have hH2 : Continuous H₂ := by
    simpa [H₂_SIF] using! (H₂_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ⇑H₂_SIF).continuous
  have hH3 : Continuous H₃ := by
    simpa [H₃_SIF] using! (H₃_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ⇑H₃_SIF).continuous
  have hH4 : Continuous H₄ := by
    simpa [H₄_SIF] using! (H₄_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ⇑H₄_SIF).continuous
  have hψ :
      ψS =
        fun z : ℍ =>
          -((256 : ℂ) ^ (2 : ℕ)) *
              (7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3) /
                ((H₃ z) ^ 4 * (H₄ z) ^ 4) := by
    funext z
    simpa using! (ψS_apply_eq_factor z)
  rw [hψ]
  have hden0 : ∀ z : ℍ, (H₃ z) ^ 4 * (H₄ z) ^ 4 ≠ 0 := by
    intro z
    exact mul_ne_zero (pow_ne_zero 4 (H₃_ne_zero z)) (pow_ne_zero 4 (H₄_ne_zero z))
  have hnum :
      Continuous fun z : ℍ =>
        -((256 : ℂ) ^ (2 : ℕ)) *
          (7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3) := by
    fun_prop
  have hden : Continuous fun z : ℍ => (H₃ z) ^ (4 : ℕ) * (H₄ z) ^ (4 : ℕ) := by
    fun_prop
  exact hnum.div hden hden0

private def φAddI : ℝ → ℍ :=
  fun t => UpperHalfPlane.mk ((t : ℂ) + Complex.I) (by simp)

private lemma continuous_φAddI : Continuous φAddI := by
  simpa [φAddI] using!
    (Continuous.upperHalfPlaneMk (f := fun t : ℝ => (t : ℂ) + Complex.I) (by fun_prop)
      (by intro _; simp))

/-- Continuity of the shifted total extension `t ↦ ψS' (t + i)` on `ℝ`. -/
public lemma continuous_ψS'_add_I : Continuous (fun t : ℝ => ψS' ((t : ℂ) + Complex.I)) := by
  have hEq : (fun t : ℝ => ψS' ((t : ℂ) + Complex.I)) = fun t : ℝ => ψS (φAddI t) := by
    funext t
    simp [ψS', φAddI]
  simpa [hEq] using! (continuous_ψS.comp continuous_φAddI)

/-- Continuity of the shifted total extension `t ↦ ψI' (t + i)` on `ℝ`. -/
public lemma continuous_ψI'_add_I : Continuous (fun t : ℝ => ψI' ((t : ℂ) + Complex.I)) := by
  have hEq : (fun t : ℝ => ψI' ((t : ℂ) + Complex.I)) = fun t : ℝ => ψI (φAddI t) := by
    funext t
    simp [ψI', φAddI]
  simpa [hEq] using! ((SpherePacking.Dim24.continuous_ψI).comp continuous_φAddI)

/-- Continuity of the shifted total extension `t ↦ ψT' (t + i)` on `ℝ`. -/
public lemma continuous_ψT'_add_I : Continuous (fun t : ℝ => ψT' ((t : ℂ) + Complex.I)) := by
  have hEq : (fun t : ℝ => ψT' ((t : ℂ) + Complex.I)) = fun t : ℝ => ψT (φAddI t) := by
    funext t
    simp [ψT', φAddI]
  simpa [hEq] using! ((SpherePacking.Dim24.continuous_ψT).comp continuous_φAddI)

end PsiRewrites

end

end SpherePacking.Dim24
