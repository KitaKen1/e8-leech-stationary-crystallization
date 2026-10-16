-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.Prelude


/-!
# Gaussian Fourier lemmas

This file contains small Fourier-transform identities for Gaussians in dimension `24`
used in the permutation arguments.

## Main statements
* `fourierTransformCLE_symm_eq_of_even`
* `zpow_neg_twelve_mul_pow_twelve`
-/

open scoped SchwartzMap

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.AFourier

noncomputable section


/-- For an even Schwartz function, the inverse Fourier transform equals the Fourier transform. -/
public lemma fourierTransformCLE_symm_eq_of_even (f : 𝓢(ℝ²⁴, ℂ))
    (heven : (fun x : ℝ²⁴ ↦ f (-x)) = fun x ↦ f x) :
    (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)).symm f =
      FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ) f := by
  ext x
  simp [FourierTransform.fourierCLE_symm_apply, FourierTransform.fourierCLE_apply,
    SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg, heven]

/-- A zpow/pow cancellation used when simplifying Gaussian prefactors. -/
public lemma zpow_neg_twelve_mul_pow_twelve (s : ℝ) (hs : s ≠ 0) :
    ((s ^ (-12 : ℤ)) : ℂ) * (s ^ 12 : ℂ) = 1 := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  simpa using! (zpow_add₀ hsC (-12 : ℤ) (12 : ℤ)).symm

end

end SpherePacking.Dim24.AFourier
