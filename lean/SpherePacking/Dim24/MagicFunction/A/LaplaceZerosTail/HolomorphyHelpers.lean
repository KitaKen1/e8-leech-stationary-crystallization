/-
Tail deformation and Laplace identities for the Leech-radius zeros of the +1 eigenfunction `a`.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Defs
public import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
public import Mathlib.MeasureTheory.Integral.ExpDecay
import SpherePacking.ForMathlib.UpperHalfPlane
import SpherePacking.Dim24.ModularForms.Psi.Defs
import SpherePacking.ModularForms.Lv1Lv2Identities


/-!
# Holomorphy helpers for the Laplace-zero tail deformation

This file collects complex-differentiability and shift identities for the integrands `Φ₂'`,
`Φ₄'`, `Φ₅'`, and `Φ₆'` on the upper half-plane. These lemmas are used in the tail deformation
arguments leading to Laplace identities and zeros at the Leech radii.

## Main statements
* `differentiableAt_Φ₂'`, `differentiableAt_Φ₄'`
* `I₂'_eq_intervalIntegral_bottom`, `I₄'_eq_intervalIntegral_bottom`
* `Φ₂'_sub_two_mul_Φ₅'_add_Φ₄'_eq_two_mul_Φ₆'`
-/


open Complex Real MeasureTheory Filter intervalIntegral
open scoped UpperHalfPlane Interval

namespace SpherePacking.Dim24

noncomputable section

open UpperHalfPlane MatrixGroups
open MagicFunction.Parametrisations
open RealIntegrals RealIntegrals.ComplexIntegrands

namespace LaplaceZerosTail


def upperHalfPlaneSet : Set ℂ := {z : ℂ | 0 < z.im}

lemma differentiableAt_varphi' {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    DifferentiableAt ℂ varphi' z := by
  -- Use `varphi_holo' : MDifferentiable ... varphi` and the bridge lemma
  -- `UpperHalfPlane.mdifferentiableAt_iff`.
  have hdiffOn :
      DifferentiableOn ℂ (varphi ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet := by
    -- `UpperHalfPlane.mdifferentiable_iff` identifies `MDifferentiable` on `ℍ` with
    -- `DifferentiableOn` on the open subset `{z | 0 < z.im}`.
    simpa [upperHalfPlaneSet] using! (UpperHalfPlane.mdifferentiable_iff).1 (varphi_holo' : _)
  have hdiffAt : DifferentiableAt ℂ (varphi ∘ UpperHalfPlane.ofComplex) z :=
    (hdiffOn z hz).differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  -- On a neighborhood inside `{Im z > 0}`, `varphi'` agrees with `varphi ∘ ofComplex`.
  have hEq :
      (fun w : ℂ => varphi' w) =ᶠ[nhds z] fun w : ℂ => varphi (UpperHalfPlane.ofComplex w) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    simp [varphi', hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  exact hdiffAt.congr_of_eventuallyEq hEq

lemma differentiableAt_neg_one_div_add_real (a : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    DifferentiableAt ℂ (fun w : ℂ => (-1 : ℂ) / (w + a)) z := by
  -- A rational function with nonvanishing denominator on `{Im z > 0}`.
  have hz0 : (0 : ℝ) < z.im := by simpa [upperHalfPlaneSet] using! hz
  have hz' : z + a ≠ 0 := by
    intro h
    have : (z + a).im = 0 := by simp [h]
    have : z.im = 0 := by simpa using! this
    exact (lt_irrefl (0 : ℝ)) (this ▸ hz0)
  simp_all

lemma differentiableAt_neg_one_div_add_one {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    DifferentiableAt ℂ (fun w : ℂ => (-1 : ℂ) / (w + 1)) z := by
  simpa using! (differentiableAt_neg_one_div_add_real (a := 1) (z := z) hz)

lemma differentiableAt_neg_one_div_sub_one {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    DifferentiableAt ℂ (fun w : ℂ => (-1 : ℂ) / (w - 1)) z := by
  simpa [sub_eq_add_neg] using!
    (differentiableAt_neg_one_div_add_real (a := -1) (z := z) hz)

lemma im_neg_one_div_add_real_pos (a : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    0 < ((-1 : ℂ) / (z + a)).im := by
  -- Package as an `ℍ` point and use `im_inv_neg_coe_pos`.
  set zH : ℍ := ⟨z, hz⟩
  set w : ℍ := a +ᵥ zH
  have hw : 0 < ((-w : ℂ)⁻¹).im := UpperHalfPlane.im_inv_neg_coe_pos w
  have hw' : ((-w : ℂ)⁻¹) = (-1 : ℂ) / (z + a) := by
    have hwcoe : (w : ℂ) = z + a := by simp [w, zH, add_comm]
    calc
      ((-w : ℂ)⁻¹) = -((w : ℂ)⁻¹) := by simp
      _ = -((z + a)⁻¹) := by simp [hwcoe]
      _ = (-1 : ℂ) / (z + a) := by simp [div_eq_mul_inv]
  simpa [hw'] using! hw

lemma im_neg_one_div_add_one_pos {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    0 < ((-1 : ℂ) / (z + 1)).im := by
  simpa using! (im_neg_one_div_add_real_pos (a := 1) (z := z) hz)

lemma im_neg_one_div_sub_one_pos {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    0 < ((-1 : ℂ) / (z - 1)).im := by
  simpa [sub_eq_add_neg] using! (im_neg_one_div_add_real_pos (a := -1) (z := z) hz)

/-- Complex differentiability of `Φ₂' u` at points of the upper half-plane. -/
public lemma differentiableAt_Φ₂' (u : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    DifferentiableAt ℂ (Φ₂' u) z := by
  -- `Φ₂' = Φ₁'` in this development.
  dsimp [Φ₂', Φ₁']
  have h1 : DifferentiableAt ℂ (fun w : ℂ => varphi' ((-1 : ℂ) / (w + 1))) z := by
    have hg : DifferentiableAt ℂ (fun w : ℂ => (-1 : ℂ) / (w + 1)) z :=
      differentiableAt_neg_one_div_add_real (a := 1) (z := z) hz
    have him : ((-1 : ℂ) / (z + 1)) ∈ upperHalfPlaneSet :=
      im_neg_one_div_add_real_pos (a := 1) (z := z) hz
    have hφ : DifferentiableAt ℂ varphi' ((-1 : ℂ) / (z + 1)) :=
      differentiableAt_varphi' (z := (-1 : ℂ) / (z + 1)) him
    exact hφ.comp z hg
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (w + 1) ^ (10 : ℕ)) z := by fun_prop
  have h3 :
      DifferentiableAt ℂ (fun w : ℂ => cexp (Real.pi * Complex.I * (u : ℂ) * w)) z := by
    fun_prop
  -- `mul` is left-associative, matching the definition of `Φ₁'`.
  exact (h1.mul h2).mul h3

/-- Complex differentiability of `Φ₄' u` at points of the upper half-plane. -/
public lemma differentiableAt_Φ₄' (u : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    DifferentiableAt ℂ (Φ₄' u) z := by
  dsimp [Φ₄', Φ₃']
  have h1 : DifferentiableAt ℂ (fun w : ℂ => varphi' ((-1 : ℂ) / (w - 1))) z := by
    have hg : DifferentiableAt ℂ (fun w : ℂ => (-1 : ℂ) / (w - 1)) z :=
      by
        simpa [sub_eq_add_neg] using!
          (differentiableAt_neg_one_div_add_real (a := -1) (z := z) hz)
    have him : ((-1 : ℂ) / (z - 1)) ∈ upperHalfPlaneSet :=
      by
        simpa [sub_eq_add_neg] using! (im_neg_one_div_add_real_pos (a := -1) (z := z) hz)
    have hφ : DifferentiableAt ℂ varphi' ((-1 : ℂ) / (z - 1)) :=
      differentiableAt_varphi' (z := (-1 : ℂ) / (z - 1)) him
    exact hφ.comp z hg
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (w - 1) ^ (10 : ℕ)) z := by fun_prop
  have h3 :
      DifferentiableAt ℂ (fun w : ℂ => cexp (Real.pi * Complex.I * (u : ℂ) * w)) z := by
    fun_prop
  exact (h1.mul h2).mul h3

/-!
### Helper: finite-rectangle deformation

We deform within a bounded strip, assuming directly that the top-edge interval integral tends to
`0` as the height tends to `∞`.
-/

/-!
### Bottom-edge rewrites for `I₂'` and `I₄'`
-/

/-- Rewrite `I₂' u` as an interval integral along the bottom edge `x ↦ x + i`, `x ∈ [-1, 0]`. -/
public lemma I₂'_eq_intervalIntegral_bottom (u : ℝ) :
    RealIntegrals.I₂' u =
      ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + Complex.I) := by
  dsimp [RealIntegrals.I₂']
  simp only [RealIntegrands.Φ₂]
  let g : ℝ → ℂ := fun x : ℝ => Φ₂' u ((x : ℂ) + Complex.I)
  have hcongr :
      (∫ t in (0 : ℝ)..1, Φ₂' u (z₂' t)) =
        ∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ)) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using! ht
    have hz : z₂' t = (-1 : ℂ) + (t : ℂ) + (Complex.I : ℂ) := by
      simpa using! (z₂'_eq_of_mem (t := t) ht')
    dsimp [g]
    simp [hz, add_comm]
  have hshift :
      (∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ))) = ∫ x in (-1 : ℝ)..0, g x := by
    norm_num
  calc
    (∫ t in (0 : ℝ)..1, Φ₂' u (z₂' t)) =
        ∫ t in (0 : ℝ)..1, g (t + (-1 : ℝ)) := hcongr
    _ = ∫ x in (-1 : ℝ)..0, g x := hshift
    _ = ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + Complex.I) := by
        simp [g]

/-- Rewrite `I₄' u` as an interval integral along the bottom edge `x ↦ x + i`, `x ∈ [1, 0]`. -/
public lemma I₄'_eq_intervalIntegral_bottom (u : ℝ) :
    RealIntegrals.I₄' u =
      ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + Complex.I) := by
  dsimp [RealIntegrals.I₄']
  simp only [RealIntegrands.Φ₄]
  let g : ℝ → ℂ := fun x : ℝ => Φ₄' u ((x : ℂ) + Complex.I)
  have hrew :
      (∫ t in (0 : ℝ)..1, (-1 : ℂ) * Φ₄' u (z₄' t)) =
        ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using! ht
    have hz : z₄' t = (1 : ℂ) - (t : ℂ) + (Complex.I : ℂ) := by
      simpa using! (z₄'_eq_of_mem (t := t) ht')
    have hcast : ((1 - t : ℝ) : ℂ) = (1 : ℂ) - (t : ℂ) := by
      norm_cast
    dsimp [g]
    simp [hz, sub_eq_add_neg]
  rw [hrew]
  have hcomp : (∫ t in (0 : ℝ)..1, g (1 - t)) = ∫ t in (0 : ℝ)..1, g t := by
    norm_num
  calc
    ∫ t in (0 : ℝ)..1, (-1 : ℂ) * g (1 - t)
        = (-1 : ℂ) * ∫ t in (0 : ℝ)..1, g (1 - t) := by simp
    _ = (-1 : ℂ) * ∫ t in (0 : ℝ)..1, g t := by rw [hcomp]
    _ = -∫ t in (0 : ℝ)..1, g t := by simp
    _ = ∫ t in (1 : ℝ)..0, g t := by
          simpa using! (intervalIntegral.integral_symm (a := (0 : ℝ)) (b := (1 : ℝ)) (f := g)).symm

/-- Rearrange `A + B - C = 0` as `A = C - B`. -/
public lemma eq_sub_of_add_sub_eq_zero {A B C : ℂ} (h : A + B - C = 0) : A = C - B := by
  grind only

/-
From here on we develop the tail deformation (vertical rays and finite-difference identity)
needed for the Laplace-factorization of `aProfile` at the Leech radii.
-/

/-!
### Shift identities on the vertical rays
-/

/-- Shift identity for `Φ₂'` along the vertical ray `z = -1 + i t`. -/
public lemma Φ₂'_shift_left (u t : ℝ) :
    Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * Φ₅' u ((t : ℂ) * Complex.I) := by
  -- On `z = -1 + i t`, we have `z+1 = i t` so the algebraic part of `Φ₂'` matches `Φ₅'`,
  -- and the exponential weight picks up the factor `exp(-π i u)`.
  simp [Φ₂', Φ₁', Φ₅', mul_add, mul_assoc, mul_left_comm, mul_comm,
    div_eq_mul_inv, Complex.exp_add]

/-- Shift identity for `Φ₄'` along the vertical ray `z = 1 + i t`. -/
public lemma Φ₄'_shift_right (u t : ℝ) :
    Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * Φ₅' u ((t : ℂ) * Complex.I) := by
  -- On `z = 1 + i t`, we have `z-1 = i t` so the algebraic part of `Φ₄'` matches `Φ₅'`,
  -- and the exponential weight picks up the factor `exp(π i u)`.
  simp [Φ₄', Φ₃', Φ₅', mul_add, mul_assoc, mul_left_comm, mul_comm,
    div_eq_mul_inv, Complex.exp_add]

/-!
### Finite-difference identity on the imaginary axis

This packages the modular-form "second difference" identity into a pointwise identity for the
`Φⱼ'` integrands (needed to cancel the vertical-ray pieces in `I₂' + I₄' + I₆'`).
-/

/--
A modular-form identity for `varphi` under the `S`-action, with the appropriate powers of `z`.
-/
public lemma varphi_S_mul_pow (z : ℍ) :
    (z : ℂ) ^ (10 : ℕ) * varphi (ModularGroup.S • z) =
      (z : ℂ) ^ (2 : ℕ) * varphi z + (z : ℂ) * varphi₁ z + varphi₂ z := by
  have hz : (z : ℂ) ≠ 0 := by
    simpa using! (UpperHalfPlane.ne_zero z)
  have h := varphi_S_transform (z := z)
  -- Multiply the `z^8`-identity by `z^2`.
  grind only

lemma varphi_periodic_neg_one (z : ℍ) : varphi ((-1 : ℝ) +ᵥ z) = varphi z := by
  have hv : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ z) = z :=
    vadd_neg_vadd 1 z
  have h := varphi_periodic (z := (-1 : ℝ) +ᵥ z)
  have : varphi z = varphi ((-1 : ℝ) +ᵥ z) := by simpa [hv] using! h
  exact this.symm

lemma varphi₁_periodic_neg_one (z : ℍ) : varphi₁ ((-1 : ℝ) +ᵥ z) = varphi₁ z := by
  have hv : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ z) = z :=
    vadd_neg_vadd 1 z
  have h := varphi₁_periodic (z := (-1 : ℝ) +ᵥ z)
  have : varphi₁ z = varphi₁ ((-1 : ℝ) +ᵥ z) := by simpa [hv] using! h
  exact this.symm

lemma varphi₂_periodic_neg_one (z : ℍ) : varphi₂ ((-1 : ℝ) +ᵥ z) = varphi₂ z := by
  have hv : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ z) = z :=
    vadd_neg_vadd 1 z
  have h := varphi₂_periodic (z := (-1 : ℝ) +ᵥ z)
  have : varphi₂ z = varphi₂ ((-1 : ℝ) +ᵥ z) := by simpa [hv] using! h
  exact this.symm

lemma varphi_secondDifference (z : ℍ) :
    ((↑((1 : ℝ) +ᵥ z) : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • ((1 : ℝ) +ᵥ z))
      - 2 * (((z : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • z))
      + ((↑((-1 : ℝ) +ᵥ z) : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • ((-1 : ℝ) +ᵥ z)) =
        2 * varphi z := by
  have h1 := varphi_S_mul_pow (z := (1 : ℝ) +ᵥ z)
  have h0 := varphi_S_mul_pow (z := z)
  have hm1 := varphi_S_mul_pow (z := (-1 : ℝ) +ᵥ z)
  have hperφ : varphi ((1 : ℝ) +ᵥ z) = varphi z := varphi_periodic (z := z)
  have hperφ₁ : varphi₁ ((1 : ℝ) +ᵥ z) = varphi₁ z := varphi₁_periodic (z := z)
  have hperφ₂ : varphi₂ ((1 : ℝ) +ᵥ z) = varphi₂ z := varphi₂_periodic (z := z)
  have hperφm : varphi ((-1 : ℝ) +ᵥ z) = varphi z := varphi_periodic_neg_one (z := z)
  have hperφ₁m : varphi₁ ((-1 : ℝ) +ᵥ z) = varphi₁ z := varphi₁_periodic_neg_one (z := z)
  have hperφ₂m : varphi₂ ((-1 : ℝ) +ᵥ z) = varphi₂ z := varphi₂_periodic_neg_one (z := z)
  rw [h1, h0, hm1]
  simp [UpperHalfPlane.coe_vadd, hperφ, hperφ₁, hperφ₂, hperφm, hperφ₁m, hperφ₂m, pow_two]
  ring

lemma coe_vadd_one (z : ℍ) : ((1 : ℝ) +ᵥ z : ℂ) = (z : ℂ) + (1 : ℂ) := by
  have h : ((1 : ℝ) +ᵥ z : ℂ) = (1 : ℂ) + (z : ℂ) := by
    simp
  exact h.trans (add_comm (1 : ℂ) (z : ℂ))

lemma coe_vadd_neg_one (z : ℍ) : ((-1 : ℝ) +ᵥ z : ℂ) = (z : ℂ) - (1 : ℂ) := by
  have h : ((-1 : ℝ) +ᵥ z : ℂ) = (-1 : ℂ) + (z : ℂ) := by
    simp
  have h' : ((-1 : ℝ) +ᵥ z : ℂ) = (z : ℂ) + (-1 : ℂ) := h.trans (add_comm (-1 : ℂ) (z : ℂ))
  simpa [sub_eq_add_neg] using! h'

lemma varphi_S_eq (w : ℍ) : varphi (ModularGroup.S • w) = varphi' ((-1 : ℂ) / (w : ℂ)) := by
  have hcoe : varphi (ModularGroup.S • w) = varphi' ((ModularGroup.S • w : ℍ) : ℂ) :=
    (varphi'_coe_upperHalfPlane (z := ModularGroup.S • w)).symm
  have harg : ((ModularGroup.S • w : ℍ) : ℂ) = (-1 : ℂ) / (w : ℂ) := by
    simpa using! (ModularGroup.coe_S_smul (z := w))
  grind only

lemma varphi_S_eq_toGL (w : ℍ) :
    varphi
        (Matrix.SpecialLinearGroup.toGL
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S) • w) =
      varphi' ((-1 : ℂ) / (w : ℂ)) := by
  simpa using! (varphi_S_eq (w := w))

/-- The `(+1)`-translated `S`-term appearing in the finite-difference identity equals `Φ₂'`. -/
public lemma Φ₂'_term_eq (u : ℝ) (z : ℍ) :
    ((↑((1 : ℝ) +ᵥ z) : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • ((1 : ℝ) +ᵥ z)) *
        cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ)) =
      Φ₂' u (z : ℂ) := by
  have hz1 : (↑((1 : ℝ) +ᵥ z) : ℂ) = (z : ℂ) + (1 : ℂ) := coe_vadd_one (z := z)
  have hvar0 := varphi_S_eq_toGL (w := (1 : ℝ) +ᵥ z)
  have hvar :
      varphi
          (Matrix.SpecialLinearGroup.toGL
                ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S) •
              ((1 : ℝ) +ᵥ z)) =
        varphi' ((-1 : ℂ) / ((z : ℂ) + (1 : ℂ))) := by
    simpa [hz1] using! hvar0
  dsimp [ComplexIntegrands.Φ₂', ComplexIntegrands.Φ₁', Φ₂', Φ₁']
  rw [hvar]
  ring

/-- The `S`-term appearing in the finite-difference identity equals `Φ₅'`. -/
public lemma Φ₅'_term_eq (u : ℝ) (z : ℍ) :
    (((z : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • z)) *
        cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ)) =
      Φ₅' u (z : ℂ) := by
  have hvar : varphi
        (Matrix.SpecialLinearGroup.toGL
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S) • z) =
      varphi' ((-1 : ℂ) / (z : ℂ)) :=
    varphi_S_eq_toGL (w := z)
  dsimp [ComplexIntegrands.Φ₅', Φ₅']
  rw [hvar]
  ring

/-- The `(-1)`-translated `S`-term appearing in the finite-difference identity equals `Φ₄'`. -/
public lemma Φ₄'_term_eq (u : ℝ) (z : ℍ) :
    ((↑((-1 : ℝ) +ᵥ z) : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • ((-1 : ℝ) +ᵥ z)) *
        cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ)) =
      Φ₄' u (z : ℂ) := by
  have hzm1 : (↑((-1 : ℝ) +ᵥ z) : ℂ) = (z : ℂ) - (1 : ℂ) := coe_vadd_neg_one (z := z)
  have hvar0 := varphi_S_eq_toGL (w := (-1 : ℝ) +ᵥ z)
  have hvar :
      varphi
          (Matrix.SpecialLinearGroup.toGL
                ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S) •
              ((-1 : ℝ) +ᵥ z)) =
        varphi' ((-1 : ℂ) / ((z : ℂ) - (1 : ℂ))) := by
    simpa [hzm1] using! hvar0
  dsimp [ComplexIntegrands.Φ₄', ComplexIntegrands.Φ₃', Φ₄', Φ₃']
  rw [hvar]
  rw [(UpperHalfPlane.coe_vadd (x := (-1 : ℝ)) (z := z)).symm]
  rw [hzm1]
  ring

/-- The "middle" term in the finite-difference identity equals `Φ₆'`. -/
public lemma Φ₆'_term_eq (u : ℝ) (z : ℍ) :
    varphi z * cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ)) = Φ₆' u (z : ℂ) := by
  have hvar : varphi z = varphi' (z : ℂ) := by
    simp [varphi'_coe_upperHalfPlane]
  dsimp [ComplexIntegrands.Φ₆', Φ₆']
  rw [hvar]

/-- The finite-difference identity for the `Φⱼ'` integrands, on the upper half-plane. -/
public lemma Φ₂'_sub_two_mul_Φ₅'_add_Φ₄'_eq_two_mul_Φ₆'_uhp (u : ℝ) (z : ℍ) :
    Φ₂' u (z : ℂ) - 2 * Φ₅' u (z : ℂ) + Φ₄' u (z : ℂ) = 2 * Φ₆' u (z : ℂ) := by
  let E : ℂ := cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))
  let A : ℂ := ((↑((1 : ℝ) +ᵥ z) : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • ((1 : ℝ) +ᵥ z))
  let B : ℂ := ((z : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • z)
  let C : ℂ := ((↑((-1 : ℝ) +ᵥ z) : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • ((-1 : ℝ) +ᵥ z))
  let D : ℂ := varphi z
  have hSD0 : A - 2 * B + C = 2 * D := by
    dsimp [A, B, C, D]
    simpa using! (varphi_secondDifference (z := z))
  have hmul : (A - 2 * B + C) * E = (2 * D) * E := congrArg (fun w : ℂ => w * E) hSD0
  have hdist : A * E - 2 * (B * E) + C * E = 2 * D * E := by
    simpa [sub_eq_add_neg, add_assoc, add_mul, sub_mul, mul_add, mul_assoc, two_mul] using! hmul
  have hA : A * E = Φ₂' u (z : ℂ) := by
    dsimp [A, E]
    simpa [mul_assoc] using! (Φ₂'_term_eq (u := u) (z := z))
  have hB : B * E = Φ₅' u (z : ℂ) := by
    dsimp [B, E]
    simpa [mul_assoc] using! (Φ₅'_term_eq (u := u) (z := z))
  have hC : C * E = Φ₄' u (z : ℂ) := by
    dsimp [C, E]
    simpa [mul_assoc] using! (Φ₄'_term_eq (u := u) (z := z))
  have hD : D * E = Φ₆' u (z : ℂ) := by
    dsimp [D, E]
    simpa using! (Φ₆'_term_eq (u := u) (z := z))
  simpa [hA, hB, hC, hD, sub_eq_add_neg, add_assoc, mul_assoc] using! hdist

/-- The finite-difference identity specialized to the imaginary axis `z = i t`, `t > 0`. -/
public lemma Φ₂'_sub_two_mul_Φ₅'_add_Φ₄'_eq_two_mul_Φ₆' (u t : ℝ) (ht : 0 < t) :
    Φ₂' u ((t : ℂ) * Complex.I) - 2 * Φ₅' u ((t : ℂ) * Complex.I) + Φ₄' u ((t : ℂ) * Complex.I) =
      2 * Φ₆' u ((t : ℂ) * Complex.I) := by
  let z : ℍ := it t ht
  have h := Φ₂'_sub_two_mul_Φ₅'_add_Φ₄'_eq_two_mul_Φ₆'_uhp (u := u) (z := z)
  have hz0 : (z : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by rfl
  have hz : (z : ℂ) = (t : ℂ) * Complex.I := hz0.trans (mul_comm (Complex.I : ℂ) (t : ℂ))
  rw [hz] at h
  exact h


end LaplaceZerosTail

end

end SpherePacking.Dim24
