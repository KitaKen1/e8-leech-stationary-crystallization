-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
import SpherePacking.Dim24.MagicFunction.B.Defs.J5SmoothIntegrals
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSlash
import SpherePacking.ForMathlib.IteratedDeriv


/-!
# Smoothness and one-sided Schwartz decay for `RealIntegrals.J₃'`

This is the easy term: it is obtained from `J₅'` by translating the contour by `1` and using the
modular relation `ψT ∣[-10] T = ψI`, i.e. `ψT(z+1) = ψI(z)`.

## Main statements
* `Schwartz.J3Smooth.ψT'_z₃'_eq_ψI'_z₅'`
* `Schwartz.J3Smooth.contDiff_J₃'`
* `Schwartz.J3Smooth.decay_J₃'`
-/

noncomputable section

namespace SpherePacking.Dim24.Schwartz.J3Smooth

open scoped Interval UpperHalfPlane

open Complex Real Set MeasureTheory
open UpperHalfPlane
open MagicFunction.Parametrisations
open RealIntegrals


section Modular

open ModularGroup Matrix ModularForm
open scoped MatrixGroups ModularForm

/-- Translation identity on the contour: `ψT' (z₃' t) = ψI' (z₅' t)`. -/
public lemma ψT'_z₃'_eq_ψI'_z₅' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₃' t) = ψI' (z₅' t) := by
  by_cases ht0 : 0 < t
  · have hz3 : 0 < (z₃' t).im := im_z₃'_pos (t := t) ( ⟨ht0, ht.2⟩)
    have hz5 : 0 < (z₅' t).im := im_z₅'_pos (t := t) ( ⟨ht0, ht.2⟩)
    -- Use `ψT ∣[-10] T = ψI`, i.e. `ψT(z+1) = ψI(z)`.
    have hrel :=
      congrArg (fun F : UpperHalfPlane → ℂ => F ⟨z₅' t, hz5⟩) PsiSlash.ψT_slash_T
    have hT : ψT (((1 : ℝ) +ᵥ ⟨z₅' t, hz5⟩ : UpperHalfPlane)) = ψI ⟨z₅' t, hz5⟩ := by
      simpa [modular_slash_T_apply] using! hrel
    have htrans :
        ((1 : ℝ) +ᵥ ⟨z₅' t, hz5⟩ : UpperHalfPlane) = ⟨z₃' t, hz3⟩ := by
      ext1
      simp [z₃'_eq_of_mem (t := t) ht, z₅'_eq_of_mem (t := t) ht, add_comm]
    simp [ψT', ψI', hz3, hz5, htrans] at hT ⊢
    simpa using! hT
  · have h0 : t = 0 := by
      have ht0' : 0 ≤ t := ht.1
      exact le_antisymm (le_of_not_gt ht0) ht0'
    simp [ψT', ψI', h0, z₃'_eq_of_mem (t := 0) (by simp),
      z₅'_eq_of_mem (t := 0) (by simp)]

end Modular

lemma cexp_mul_z₃'_eq (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₃' t)) =
      cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₅' t)) *
        cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ)) := by
  have hz : z₃' t = z₅' t + 1 := z₃'_eq_z₅'_add_one (t := t) ht
  calc
    cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₃' t)) =
        cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₅' t + 1)) := by simp [hz]
    _ = cexp
          ((Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₅' t)) +
            (Real.pi * (Complex.I : ℂ) * (x : ℂ))) := by
          simp [mul_add, mul_assoc, mul_left_comm, mul_comm]
    _ =
        cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₅' t)) *
          cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ)) := by
          simp [Complex.exp_add]

lemma J₃'_eq (x : ℝ) :
    J₃' x = (-1 / 2 : ℂ) * cexp ((Real.pi : ℂ) * Complex.I * (x : ℂ)) * J₅' x := by
  have hJ3 :
      J₃' x =
        (∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) *
              cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₅' t))) *
          cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ)) := by
    calc
      J₃' x =
          ∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψT' (z₃' t) *
              cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₃' t)) := by
            simp [RealIntegrals.J₃']
      _ =
          ∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) *
              cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₅' t)) *
                cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ)) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            have htIcc : t ∈ Icc (0 : ℝ) 1 := by
              simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
            have hψ : ψT' (z₃' t) = ψI' (z₅' t) := ψT'_z₃'_eq_ψI'_z₅' (t := t) htIcc
            have hcexp :
                cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₃' t)) =
                  cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₅' t)) *
                    cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ)) :=
              cexp_mul_z₃'_eq (x := x) (t := t) htIcc
            grind only
      _ =
        (∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) *
              cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₅' t))) *
          cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ)) := by
          simp [intervalIntegral.integral_mul_const]
  have hK :
      (∫ t in (0 : ℝ)..1,
          (Complex.I : ℂ) * ψI' (z₅' t) *
            cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₅' t))) =
        (-1 / 2 : ℂ) * J₅' x := by
    set K : ℂ :=
      ∫ t in (0 : ℝ)..1,
        (Complex.I : ℂ) * ψI' (z₅' t) *
          cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₅' t))
    have hJ5 : J₅' x = (-2 : ℂ) * K := by
      simp [RealIntegrals.J₅', K, mul_assoc, mul_left_comm, mul_comm]
    grind only
  calc
    J₃' x = ((-1 / 2 : ℂ) * J₅' x) * cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ)) := by
      simpa [hK] using! hJ3
    _ = (-1 / 2 : ℂ) * cexp ((Real.pi : ℂ) * Complex.I * (x : ℂ)) * J₅' x := by
      ring_nf

/-- The contour-integral term `J₃'` is smooth on `ℝ`. -/
public theorem contDiff_J₃' : ContDiff ℝ (⊤ : ℕ∞) J₃' := by
  have hExpLin : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ (Real.pi : ℂ) * Complex.I * (x : ℂ)) :=
    (contDiff_const.mul contDiff_const).mul ofRealCLM.contDiff
  have hExp : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ cexp ((Real.pi : ℂ) * Complex.I * (x : ℂ))) :=
    hExpLin.cexp
  have hJ5 : ContDiff ℝ (⊤ : ℕ∞) J₅' := J5Smooth.contDiff_J₅'
  have hmul :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ ↦ (-1 / 2 : ℂ) * cexp ((Real.pi : ℂ) * Complex.I * (x : ℂ)) * J₅' x) := by
    exact (contDiff_const.mul hExp).mul hJ5
  have hEq :
      (fun x : ℝ ↦ (-1 / 2 : ℂ) * cexp ((Real.pi : ℂ) * Complex.I * (x : ℂ)) * J₅' x) = J₃' := by
    funext x
    simpa [mul_assoc, mul_left_comm, mul_comm] using! (J₃'_eq (x := x)).symm
  simpa [hEq] using! hmul

/-- One-sided Schwartz decay for `J₃'` on `x ≥ 0`. -/
public theorem decay_J₃' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₃' x‖ ≤ C := by
  intro k n
  -- Split off the bounded oscillatory factor `(-1/2) * exp(iπx)`.
  let c : ℂ := (Real.pi : ℂ) * Complex.I
  let e : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * c)
  let f : ℝ → ℂ := fun x ↦ (-1 / 2 : ℂ) • e x
  have he_cont : ContDiff ℝ (⊤ : ℕ∞) e := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ (x : ℂ) * c) :=
      (ofRealCLM.contDiff.mul contDiff_const)
    simpa [e] using! hlin.cexp
  have hf_cont : ContDiff ℝ (⊤ : ℕ∞) f := by
    simpa [f] using! (he_cont.const_smul (-1 / 2 : ℂ))
  have hJ5_cont : ContDiff ℝ (⊤ : ℕ∞) J₅' := J5Smooth.contDiff_J₅'
  have hbound_f :
      ∀ m : ℕ, ∀ x : ℝ, ‖iteratedFDeriv ℝ m f x‖ ≤ (1 / 2 : ℝ) * Real.pi ^ m :=
    fun m x => ForMathlib.norm_iteratedFDeriv_smul_cexp_mul_pi_I_le m x
  have hdec5 :
      ∀ m : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ m J₅' x‖ ≤ C := by
    intro m
    simpa using! (J5Smooth.decay_J₅' (k := k) (n := m))
  rcases
      (SpherePacking.ForMathlib.decay_iteratedFDeriv_mul_of_bound_left (f := f) (g := J₅')
        (k := k) (n := n) (B := fun m ↦ (1 / 2 : ℝ) * Real.pi ^ m)
        hf_cont hJ5_cont (hbound_f := hbound_f) (hdec_g := hdec5)) with
    ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x hx
  have hJ3fun : J₃' = fun y : ℝ ↦ f y * J₅' y := by
    funext y
    simp [f, e, c, mul_assoc, mul_left_comm, mul_comm, J₃'_eq (x := y)]
  simpa [hJ3fun] using! hC x hx

end SpherePacking.Dim24.Schwartz.J3Smooth

end
