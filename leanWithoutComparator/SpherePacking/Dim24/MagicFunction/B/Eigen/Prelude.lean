/-
Fourier eigenfunction property of `b` (dimension 24): `𝓕 b = -b`.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
public import SpherePacking.Dim24.MagicFunction.B.Defs.J2Smooth
public import SpherePacking.Dim24.MagicFunction.B.Defs.J4Smooth
public import SpherePacking.Dim24.MagicFunction.MkRadial
public import SpherePacking.Contour.MobiusInv.Basic
public import SpherePacking.ForMathlib.ScalarOneForm
public import SpherePacking.Dim24.ModularForms.Psi.Relations
public import SpherePacking.ModularForms.SlashActionAuxil
import SpherePacking.Tactic.NormNumI
import SpherePacking.Contour.MobiusInv.PermJ12PsiFourier
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.MeasureTheory.Integral.ExpDecay


/-!
# Fourier eigenfunction setup for `b` in dimension `24`

This file is the dim-24 analogue of `SpherePacking/MagicFunction/b/Eigenfunction.lean`.

We work with the six one-variable pieces `J₁', ..., J₆'`, lift them to radial Schwartz maps on
`ℝ²⁴`, and package the Fourier permutation argument into the auxiliary definitions and lemmas used
by `eig_b`.

The analytic permutation lemmas follow the dim-8 contour/Fubini/Gaussian argument, with the
appropriate changes of exponents and weights (`4 ↦ 12`, `-2 ↦ -10`).

## Main definitions
* `J₁`, `J₂`, `J₃`, `J₄`, `J₅`, `J₆`
* `Ψ₁'`, `Ψ₁_fourier`

## Main statements
* `b_eq_sum_integrals`
* `ψT'_mobiusInv_eq_div`
* `Ψ₁_fourier_eq_neg_deriv_mul`
-/


open scoped FourierTransform Real SchwartzMap UpperHalfPlane
open Complex

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.BFourier

noncomputable section


/-- The radial Schwartz map on `ℝ²⁴` associated to the profile `RealIntegrals.J₁'`. -/
@[expose] public def J₁ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.J₁'
    (by simpa using! RadialSchwartz.cutoffC_contDiff.mul Schwartz.J1Smooth.contDiff_J₁')
    Schwartz.J1Smooth.decay_J₁'

/-- The radial Schwartz map on `ℝ²⁴` associated to the profile `RealIntegrals.J₂'`. -/
@[expose] public def J₂ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.J₂'
    (by simpa using! RadialSchwartz.cutoffC_contDiff.mul Schwartz.J2Smooth.contDiff_J₂')
    Schwartz.J2Smooth.decay_J₂'

/-- The radial Schwartz map on `ℝ²⁴` associated to the profile `RealIntegrals.J₃'`. -/
@[expose] public def J₃ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.J₃'
    (by simpa using! RadialSchwartz.cutoffC_contDiff.mul Schwartz.J3Smooth.contDiff_J₃')
    Schwartz.J3Smooth.decay_J₃'

/-- The radial Schwartz map on `ℝ²⁴` associated to the profile `RealIntegrals.J₄'`. -/
@[expose] public def J₄ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.J₄'
    (by simpa using! RadialSchwartz.cutoffC_contDiff.mul Schwartz.J4Smooth.contDiff_J₄')
    Schwartz.J4Smooth.decay_J₄'

/-- The radial Schwartz map on `ℝ²⁴` associated to the profile `RealIntegrals.J₅'`. -/
@[expose] public def J₅ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.J₅'
    (by simpa using! RadialSchwartz.cutoffC_contDiff.mul Schwartz.J5Smooth.contDiff_J₅')
    Schwartz.J5Smooth.decay_J₅'

/-- The radial Schwartz map on `ℝ²⁴` associated to the profile `RealIntegrals.J₆'`. -/
@[expose] public def J₆ : 𝓢(ℝ²⁴, ℂ) :=
  mkRadial RealIntegrals.J₆'
    (by
      simpa using!
        (RadialSchwartz.contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1
          (f := RealIntegrals.J₆') Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1))
    Schwartz.J6Smooth.decay_J₆'

/-- Evaluation of `J₁` in terms of its one-variable radial profile `J₁'`. -/
public lemma J₁_apply (x : ℝ²⁴) : (J₁ x) = RealIntegrals.J₁' (‖x‖ ^ 2) := by
  simp [J₁, SpherePacking.Dim24.mkRadial]

/-- Evaluation of `J₂` in terms of its one-variable radial profile `J₂'`. -/
public lemma J₂_apply (x : ℝ²⁴) : (J₂ x) = RealIntegrals.J₂' (‖x‖ ^ 2) := by
  simp [J₂, SpherePacking.Dim24.mkRadial]

/-- Evaluation of `J₃` in terms of its one-variable radial profile `J₃'`. -/
public lemma J₃_apply (x : ℝ²⁴) : (J₃ x) = RealIntegrals.J₃' (‖x‖ ^ 2) := by
  simp [J₃, SpherePacking.Dim24.mkRadial]

/-- Evaluation of `J₄` in terms of its one-variable radial profile `J₄'`. -/
public lemma J₄_apply (x : ℝ²⁴) : (J₄ x) = RealIntegrals.J₄' (‖x‖ ^ 2) := by
  simp [J₄, SpherePacking.Dim24.mkRadial]

/-- Evaluation of `J₅` in terms of its one-variable radial profile `J₅'`. -/
public lemma J₅_apply (x : ℝ²⁴) : (J₅ x) = RealIntegrals.J₅' (‖x‖ ^ 2) := by
  simp [J₅, SpherePacking.Dim24.mkRadial]

/-- Evaluation of `J₆` in terms of its one-variable radial profile `J₆'`. -/
public lemma J₆_apply (x : ℝ²⁴) : (J₆ x) = RealIntegrals.J₆' (‖x‖ ^ 2) := by
  simp [J₆, SpherePacking.Dim24.mkRadial]

/-- Decompose `b` as the sum of the six contour pieces `J₁, ..., J₆`. -/
public lemma b_eq_sum_integrals : b = J₁ + J₂ + J₃ + J₄ + J₅ + J₆ := by
  ext x
  simp [b, bProfile, RealIntegrals.b', J₁_apply, J₂_apply, J₃_apply, J₄_apply, J₅_apply, J₆_apply,
    add_assoc, add_left_comm, add_comm]

/-! ### Shared Gaussian/Fourier lemmas

Use the canonical dimension-24 Gaussian Fourier transform and evenness lemmas in
`SpherePacking.Dim24.AFourier` (via `SpherePacking.Dim24.MagicFunction.A.Eigen.GaussianFourier`).
-/

section PermJ12

/-!
### Permutation for `J₁+J₂`

We follow the dim-8 proof in `SpherePacking/MagicFunction/b/Eigenfunction.lean`, adapting:
- dimension `8 ↦ 24` (Fourier Gaussian factor `((I/z)^(4)) ↦ ((I/z)^(12))`),
- weight `-2 ↦ -10` (so the `S`-action gives a `(z : ℂ)^(10)` factor).
-/

/-- The contour integrand for the `J₁/J₂` pieces: `ψT' z * exp(π i r z)`. -/
@[expose] public def Ψ₁' (r : ℝ) (z : ℂ) : ℂ :=
  ψT' z * cexp ((π : ℂ) * Complex.I * (r : ℂ) * z)

/-- The Fourier-side integrand for the `J₁/J₂` pieces, using the dim-24 Gaussian factor. -/
@[expose] public def Ψ₁_fourier (r : ℝ) (z : ℂ) : ℂ :=
  ψT' z * (((I : ℂ) / z) ^ (12 : ℕ)) * cexp ((π : ℂ) * Complex.I * (r : ℂ) * (-1 / z))

/-- Transformation rule for `ψT'` under Möbius inversion `z ↦ -1/z` (weight `-10`). -/
public lemma ψT'_mobiusInv_eq_div (z : ℂ) (hz : 0 < z.im) :
    ψT' (mobiusInv z) = -(ψT' z) / z ^ (10 : ℕ) := by
  let zH : UpperHalfPlane := ⟨z, hz⟩
  have hz0 : (zH : ℂ) ≠ 0 := by
    intro hz0
    have : z.im = 0 := by simpa [zH] using! congrArg Complex.im hz0
    exact (lt_irrefl (0 : ℝ)) (this ▸ hz)
  have hz10 : ((zH : ℂ) ^ (10 : ℕ) : ℂ) ≠ 0 := pow_ne_zero 10 hz0
  -- Evaluate `ψT ∣[-10] S = -ψT` at `zH`.
  have h := congrArg (fun F : UpperHalfPlane → ℂ => F zH) (SpherePacking.Dim24.ψT_S_action)
  have hS :
      (SlashAction.map (-10) ModularGroup.S ψT) zH =
        ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) * (zH : ℂ) ^ (10 : ℕ) := by
    simpa using! (modular_slash_S_apply (f := ψT) (k := (-10 : ℤ)) (z := zH))
  have hS' :
      ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) * (zH : ℂ) ^ (10 : ℕ) =
        -ψT zH := by
    simpa [hS] using! h
  have hdiv :
      ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) =
        (-ψT zH) / (zH : ℂ) ^ (10 : ℕ) :=
    (eq_div_iff hz10).2 hS'
  -- Identify the Möbius image point: `(-zH)⁻¹ = mobiusInv z`.
  have hz' : 0 < (mobiusInv z).im := mobiusInv_im_pos z hz
  have hmk :
      (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos : UpperHalfPlane) =
        ⟨mobiusInv z, hz'⟩ := by
    ext1
    simp [zH, mobiusInv, inv_neg]
  -- Convert to `ψT'` on `ℂ`.
  have hTz : ψT' z = ψT zH := by simp [ψT', hz, zH]
  have hTw : ψT' (mobiusInv z) = ψT ⟨mobiusInv z, hz'⟩ := by
    have hpos : 0 < (mobiusInv z).im := hz'
    simp [ψT', hpos]
  have hmkψ :
      ψT ⟨mobiusInv z, hz'⟩ =
        ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) := by
    simpa using! congrArg ψT hmk.symm
  calc
    ψT' (mobiusInv z) = ψT ⟨mobiusInv z, hz'⟩ := hTw
    _ = ψT (UpperHalfPlane.mk (-zH)⁻¹ zH.im_inv_neg_coe_pos) := hmkψ
    _ = (-ψT zH) / (zH : ℂ) ^ (10 : ℕ) := hdiv
    _ = -(ψT' z) / z ^ (10 : ℕ) := by
      simp [hTz, zH, div_eq_mul_inv]

/-- Relate `Ψ₁_fourier` to `Ψ₁'` composed with Möbius inversion via `deriv mobiusInv`. -/
public lemma Ψ₁_fourier_eq_neg_deriv_mul (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Ψ₁_fourier r z = -(deriv mobiusInv z) * Ψ₁' r (mobiusInv z) := by
  have hψ : ψT' (mobiusInv z) = -(ψT' z) / z ^ (10 : ℕ) :=
    ψT'_mobiusInv_eq_div (z := z) hz
  have hI : (Complex.I : ℂ) ^ (10 + 2) = (1 : ℂ) := by
    norm_num1
  simpa [Ψ₁', Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm] using!
    (SpherePacking.Contour.permJ12_Ψ₁_fourier_eq_neg_deriv_mul
      (ψ := ψT') (A := (π : ℂ) * Complex.I) (q := 10) (r := r) (z := z) hz
      (hψ := hψ) (hI := hI))


end PermJ12


end
end SpherePacking.Dim24.BFourier
