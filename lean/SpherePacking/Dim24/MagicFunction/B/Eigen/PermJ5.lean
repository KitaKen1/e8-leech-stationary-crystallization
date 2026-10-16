-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.Dim24.MagicFunction.A.Eigen.GaussianFourier
import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ12ContourIdentity
import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ5Integrability


/-!
# The `J₅` permutation and the `-1` eigenvalue of `b`

This file completes the Fourier permutation argument for the dim-24 magic function `b`. The main
step is the `J₅/J₆` identity, proved via the `t ↦ 1/t` change of variables and an integrability
argument for Fubini. We then assemble this with the `J₁`--`J₄` contour deformation identities to
obtain the `-1` eigenvalue.

## Main statements
* `eig_b`
-/

open scoped FourierTransform Real
open Complex

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

namespace SpherePacking.Dim24.BFourier
open MeasureTheory Set Filter
open scoped RealInnerProductSpace

noncomputable section

lemma J₆'_eq (r : ℝ) :
    RealIntegrals.J₆' r =
      (-2 : ℂ) *
        ∫ s in Ici (1 : ℝ),
          (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * r * s) := by
  simp only [RealIntegrals.J₆', mul_assoc]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
  intro s hs
  have hz : MagicFunction.Parametrisations.z₆' s = (Complex.I : ℂ) * (s : ℂ) := by
    -- `z₆'` is `I*s` on `Ici 1`.
    simpa using! (MagicFunction.Parametrisations.z₆'_eq_of_mem (t := s) hs)
  -- Reduce the lambda-application form and rewrite `z₆' s`.
  simp only [neg_mul, mul_eq_mul_left_iff, I_ne_zero, or_false]
  rw [hz]
  -- Simplify the exponential using `I * I = -1`.
  have hexp :
      cexp (↑π * ((Complex.I : ℂ) * ((r : ℂ) * ((Complex.I : ℂ) * (s : ℂ))))) =
        cexp (-(↑π * (r : ℂ) * (s : ℂ))) := by
    have harg :
        (↑π : ℂ) * ((Complex.I : ℂ) * ((r : ℂ) * ((Complex.I : ℂ) * (s : ℂ)))) =
          (-(↑π * (r : ℂ) * (s : ℂ))) := by
      ring_nf
      simp
    simp [harg]
  rw [hexp]
  simp [mul_assoc]

theorem perm_J₅ : FT J₅ = -J₆ := by
  ext w
  -- Reduce to the underlying function equality `𝓕 J₅ = -J₆`.
  simp only [FourierTransform.fourierCLE_apply, SchwartzMap.neg_apply]
  -- Rewrite the RHS via the explicit radial profile (avoid unfolding the Schwartz construction).
  rw [J₆_apply]
  change 𝓕 (J₅ : ℝ²⁴ → ℂ) w = -RealIntegrals.J₆' (‖w‖ ^ 2)
  rw [Real.fourier_eq' (J₅ : ℝ²⁴ → ℂ) w]
  simp only [smul_eq_mul, J₅_apply]
  -- Rewrite `J₅'` using the `t ↦ 1/t` substitution.
  have hJ5' (x : ℝ²⁴) :
      RealIntegrals.J₅' (‖x‖ ^ 2) =
        (-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s := by
    simpa using! (J5Change.Complete_Change_of_Variables (r := (‖x‖ ^ 2)))
  simp only [hJ5', mul_assoc]
  -- Move the phase factor inside the `s`-integral so we can use Fubini.
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  have hmul :
      (fun x : ℝ²⁴ ↦
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) =
        fun x : ℝ²⁴ ↦
          ∫ s in Ici (1 : ℝ),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * J5Change.g (‖x‖ ^ 2) s := by
    ext x
    exact Eq.symm (integral_const_mul (cexp (↑(-2 * (π * ⟪x, w⟫)) * I)) (J5Change.g (‖x‖ ^ 2)))
  -- Apply Fubini to swap the order of integration.
  let f : ℝ²⁴ → ℝ → ℂ := fun x s ↦ PermJ5.kernel w (x, s)
  have hint : Integrable (Function.uncurry f)
      ((volume : Measure ℝ²⁴).prod μs) := by
    have hint' :
        Integrable (PermJ5.kernel w) ((volume : Measure ℝ²⁴).prod μs) := by
      simpa [μs, SpherePacking.Integration.μIciOne] using! (PermJ5.integrable_kernel (w := w))
    simpa [f, Function.uncurry] using! hint'
  have hswap :=
    MeasureTheory.integral_integral_swap (μ := (volume : Measure ℝ²⁴)) (ν := μs) (f := f) hint
  -- Compute the inner integral using the Gaussian Fourier transform.
  have hinner (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
      (∫ x : ℝ²⁴, f x s) =
        (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hs_ne0 : s ≠ 0 := ne_of_gt hs0
    have hcancel : ((s ^ (-12 : ℤ)) : ℂ) * (s ^ 12 : ℂ) = 1 :=
      AFourier.zpow_neg_twelve_mul_pow_twelve (s := s) hs_ne0
    have hfactor :
        (fun x : ℝ²⁴ ↦ f x s) =
          fun x : ℝ²⁴ ↦
            ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) := by
      funext x
      dsimp [f, PermJ5.kernel, J5Change.g]
      simp
      ac_rfl
    calc
      (∫ x : ℝ²⁴, f x s) =
          ∫ x : ℝ²⁴,
            ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) :=
            congrArg (fun F : ℝ²⁴ → ℂ => ∫ x, F x) hfactor
      _ =
          ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
            ∫ x : ℝ²⁴,
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s) := by
            exact integral_const_mul (-I * ψS' (I * ↑s) * ↑s ^ (-12)) fun a =>
              cexp (↑(-2 * (π * ⟪a, w⟫)) * I) * cexp (-↑π * ↑‖a‖ ^ 2 / ↑s)
      _ =
          ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
            ((s ^ 12 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s)) := by
            rw [SpherePacking.ForMathlib.integral_phase_gaussian_even
              (k := 12) (w := w) (s := s) hs0]
      _ = (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
            calc
              ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
                    ((s ^ 12 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s))
                  =
                  (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) *
                    ((((s ^ (-12 : ℤ)) : ℂ) * (s ^ 12 : ℂ))) *
                      cexp (-π * (‖w‖ ^ 2) * s) := by
                        ac_rfl
              _ = (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
                    rw [hcancel]
                    simp [mul_assoc]
  have htoIter :
      (∫ x : ℝ²⁴,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) =
        ∫ x : ℝ²⁴, ∫ s in Ici (1 : ℝ), f x s := by
    simpa [f, PermJ5.kernel] using!
      congrArg (fun F : ℝ²⁴ → ℂ => ∫ x, F x) hmul
  have hswap' :
      (∫ x : ℝ²⁴, ∫ s in Ici (1 : ℝ), f x s) =
        ∫ s in Ici (1 : ℝ), ∫ x : ℝ²⁴, f x s := by
    simpa [μs] using! hswap
  have hAE :
      (fun s : ℝ ↦ ∫ x : ℝ²⁴, f x s) =ᵐ[μs]
        fun s : ℝ ↦ (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs
    simpa [f] using! hinner s hs
  have hintEq :
      (∫ s in Ici (1 : ℝ), ∫ x : ℝ²⁴, f x s) =
        ∫ s in Ici (1 : ℝ), (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    simpa [μs] using! (MeasureTheory.integral_congr_ae hAE)
  -- Finish: match `-J₆`.
  have hmain :
      (∫ x : ℝ²⁴,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
        (-2 : ℂ) *
          ∫ s in Ici (1 : ℝ),
            (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hpull :
        (∫ x : ℝ²⁴,
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
          (-2 : ℂ) *
            (∫ x : ℝ²⁴,
                cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                  ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) := by
      have hfun :
          (fun x : ℝ²⁴ ↦
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
            fun x : ℝ²⁴ ↦
              (-2 : ℂ) *
                (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                  ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) := by
        funext x
        ac_rfl
      calc
        (∫ x : ℝ²⁴,
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
            ∫ x : ℝ²⁴,
              (-2 : ℂ) *
                (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                  ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) :=
              congrArg (fun F : ℝ²⁴ → ℂ => ∫ x, F x) hfun
        _ = (-2 : ℂ) *
              ∫ x : ℝ²⁴,
                cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                  ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s :=
              integral_const_mul (-2) fun a =>
                cexp (↑(-2 * (π * ⟪a, w⟫)) * I) * ∫ (s : ℝ) in Ici 1, J5Change.g (‖a‖ ^ 2) s
    rw [hpull, htoIter, hswap', hintEq]
  -- Compare the computed `s`-integral with the explicit representation of `J₆'`.
  rw [hmain]
  rw [J₆'_eq (r := ‖w‖ ^ 2)]
  have hneg :
      (fun s : ℝ ↦
          (-I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) =
        fun s : ℝ ↦
          -((Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) := by
    funext s
    ring
  have hInt :
      (∫ s in Ici (1 : ℝ),
            (-I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) =
        ∫ s in Ici (1 : ℝ),
          -((Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) := by
    exact congrArg (fun F : ℝ → ℂ => ∫ s in Ici (1 : ℝ), F s) hneg
  rw [hInt]
  have hnegint :
      (∫ s in Ici (1 : ℝ),
            -((Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s))) =
        -(∫ s in Ici (1 : ℝ),
              (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) := by
    exact
      (MeasureTheory.integral_neg
        (μ := (volume : Measure ℝ).restrict (Ici (1 : ℝ)))
        (f := fun s : ℝ ↦
          (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)))
  rw [hnegint]
  simp [mul_assoc]

theorem perm_J₆ : FT J₆ = -J₅ := by
  have heven : (fun x : ℝ²⁴ ↦ J₆ (-x)) = fun x ↦ J₆ x := by
    funext x
    simp [J₆, mkRadial]
  have hsymm : (FT).symm J₆ = FT J₆ :=
    AFourier.fourierTransformCLE_symm_eq_of_even (f := J₆) heven
  have h := (congrArg (FT).symm perm_J₅).symm
  simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply, ← hsymm] at h ⊢
  rw [← h, neg_neg]

end
end BFourier

/-- The Fourier transform of the dim-24 magic function `b` is `-b`. -/
public theorem eig_b : FT b = -b := by
  /- Proof sketch (paper Lemma 3.1):
  Apply the radial Fourier transform to the defining contour expression for `b`.
  Use the transformation laws of `ψI,ψS,ψT` under `S` together with the relation
  `ψT | S = -ψT` to obtain the eigenvalue `-1`. -/
  rw [BFourier.b_eq_sum_integrals]
  have hrw :
      BFourier.J₁ + BFourier.J₂ + BFourier.J₃ + BFourier.J₄ + BFourier.J₅ + BFourier.J₆ =
        (BFourier.J₁ + BFourier.J₂) + (BFourier.J₃ + BFourier.J₄) + BFourier.J₅ + BFourier.J₆ := by
    ac_rfl
  rw [hrw, map_add, map_add, map_add, BFourier.perm_J₁_J₂, BFourier.perm_J₃_J₄, BFourier.perm_J₅,
    BFourier.perm_J₆]
  abel

end SpherePacking.Dim24
