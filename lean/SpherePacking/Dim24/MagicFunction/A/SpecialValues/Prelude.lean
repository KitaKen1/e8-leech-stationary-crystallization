/-
Special values and derivatives of the +1 eigenfunction `a` (dimension 24).

Paper reference: `dim_24.tex`, the value list following equation (2.16).
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Defs
public import SpherePacking.Dim24.MagicFunction.Radial
public import SpherePacking.Dim24.MagicFunction.SpecialValuesExpU
import Mathlib.Tactic.FieldSimp


/-!
# Prelude for special values of `a`

This file introduces the radial restriction `aRadial` and records periodicity and `S`-transform
identities for `varphi`, `varphi₁`, and `varphi₂` used to simplify contour integrals at the even
profile values `u = 0, 2, 4`.

## Main definitions
* `aRadial`
* `SpecialValuesAux.varphi₁'`, `SpecialValuesAux.varphi₂'`

## Main statements
* `aRadial_eq_aProfile`
* `SpecialValuesAux.I₁'_I₃'_I₅'_sum_of_even`
* `SpecialValuesAux.varphi_S_transform_mul_pow10`
-/


local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

/-
Noncomputable because `axisVec` is noncomputable (it uses `EuclideanSpace.single` on `ℝ`).
-/
noncomputable section

/-- One-variable restriction of `a`, matching the paper's notation `a(r)` (with `r ≥ 0`). -/
@[expose] public def aRadial (r : ℝ) : ℂ := a (axisVec r)

/-- Relation between the radial restriction `aRadial` and the profile function `aProfile`. -/
public lemma aRadial_eq_aProfile (r : ℝ) : aRadial r = aProfile (r ^ (2 : ℕ)) := by
  -- Reduce to the defining formula `a x = aProfile (‖x‖^2)`.
  simp [aRadial, Dim24.a, Dim24.aAux, norm_axisVec_sq]


namespace SpecialValuesAux

open MagicFunction.Parametrisations
open RealIntegrals
open intervalIntegral Complex MeasureTheory Set
open scoped Topology

-- `expU` and its basic periodicity lemmas live in `Dim24.MagicFunction.SpecialValuesExpU`.

/--
At even profile values (encoded by `expU u 1 = 1`), the sum of the vertical-segment integrals
`I₁' + I₃' + I₅'` cancels.
-/
public lemma I₁'_I₃'_I₅'_sum_of_even (u : ℝ) (hu : expU u 1 = 1) :
    (I₁' u + I₃' u + I₅' u : ℂ) = 0 := by
  -- At even `u` the exponential is `1`-periodic, so the three vertical-segment pieces match
  -- pointwise and cancel with coefficients `1 + 1 - 2 = 0`.
  have hI1 :
      I₁' u =
        ∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) *
            (varphi' (-1 / (z₅' t)) * (z₅' t) ^ (10 : ℕ) *
              Complex.exp (Real.pi * Complex.I * (u : ℂ) * z₅' t)) := by
    -- `z₁' t + 1 = z₅' t` and `expU` is periodic at even `u`.
    rw [I₁']
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
    -- Rewrite `z₁' t` and `z₁' t + 1`.
    have hz : z₁' t + 1 = z₅' t := by
      simp [z₁'_eq_of_mem (t := t) htIcc, z₅'_eq_of_mem (t := t) htIcc, add_assoc]
    have hexp : expU u (z₁' t) = expU u (z₅' t) := expU_z₁'_eq_z₅' (u := u) hu t htIcc
    have hcexp :
        Complex.exp (Real.pi * Complex.I * (u : ℂ) * z₁' t) =
          Complex.exp (Real.pi * Complex.I * (u : ℂ) * z₅' t) := by
      simpa [expU] using! hexp
    -- Unfold and rewrite; finish by commutativity/associativity.
    unfold RealIntegrands.Φ₁
    unfold ComplexIntegrands.Φ₁'
    -- Rewrite `z₁' t + 1` and the exponential factor.
    rw [hz, hcexp]
  have hI3 :
      I₃' u =
        ∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) *
            (varphi' (-1 / (z₅' t)) * (z₅' t) ^ (10 : ℕ) *
              Complex.exp (Real.pi * Complex.I * (u : ℂ) * z₅' t)) := by
    -- `z₃' t - 1 = z₅' t` and `expU` is periodic at even `u`.
    rw [I₃']
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
    have hz : z₃' t - 1 = z₅' t := by
      simp [z₃'_eq_of_mem (t := t) htIcc, z₅'_eq_of_mem (t := t) htIcc, sub_eq_add_neg,
        add_assoc, add_comm]
    have hexp : expU u (z₃' t) = expU u (z₅' t) := expU_z₃'_eq_z₅' (u := u) hu t htIcc
    have hcexp :
        Complex.exp (Real.pi * Complex.I * (u : ℂ) * z₃' t) =
          Complex.exp (Real.pi * Complex.I * (u : ℂ) * z₅' t) := by
      simpa [expU] using! hexp
    unfold RealIntegrands.Φ₃
    unfold ComplexIntegrands.Φ₃'
    rw [hz, hcexp]
  have hI5 :
      I₅' u =
        (-2 : ℂ) * ∫ t in (0 : ℝ)..1,
          (Complex.I : ℂ) *
            (varphi' (-1 / (z₅' t)) * (z₅' t) ^ (10 : ℕ) *
              Complex.exp (Real.pi * Complex.I * (u : ℂ) * z₅' t)) := by
    simp [RealIntegrals.I₅', I₅', RealIntegrands.Φ₅, ComplexIntegrands.Φ₅', mul_assoc,
      mul_left_comm, mul_comm]
  -- Assemble.
  simp [hI1, hI3, hI5]
  ring

/-!
### Total extensions and periodicity for `varphi₁` and `varphi₂`

We will use them when rewriting contour integrands via the S-transformation law for `varphi`.
-/

/-- Total extension of `varphi₁` to a function on `ℂ`, equal to `varphi₁` on `im z > 0`. -/
@[expose] public def varphi₁' (z : ℂ) : ℂ := if hz : 0 < z.im then varphi₁ ⟨z, hz⟩ else 0

/-- Total extension of `varphi₂` to a function on `ℂ`, equal to `varphi₂` on `im z > 0`. -/
@[expose] public def varphi₂' (z : ℂ) : ℂ := if hz : 0 < z.im then varphi₂ ⟨z, hz⟩ else 0

/-- Simplify `varphi₁'` at points with positive imaginary part. -/
@[simp] public lemma varphi₁'_def {z : ℂ} (hz : 0 < z.im) : varphi₁' z = varphi₁ ⟨z, hz⟩ := by
  simp [varphi₁', hz]

/-- Simplify `varphi₂'` at points with positive imaginary part. -/
@[simp] public lemma varphi₂'_def {z : ℂ} (hz : 0 < z.im) : varphi₂' z = varphi₂ ⟨z, hz⟩ := by
  simp [varphi₂', hz]

/-- On `ℍ`, `varphi₁'` agrees with `varphi₁`. -/
@[simp] public lemma varphi₁'_coe_upperHalfPlane (z : UpperHalfPlane) :
    varphi₁' (z : ℂ) = varphi₁ z := by
  simpa [varphi₁'] using! (varphi₁'_def (z := (z : ℂ)) (UpperHalfPlane.im_pos z))

/-- On `ℍ`, `varphi₂'` agrees with `varphi₂`. -/
@[simp] public lemma varphi₂'_coe_upperHalfPlane (z : UpperHalfPlane) :
    varphi₂' (z : ℂ) = varphi₂ z := by
  simpa [varphi₂'] using! (varphi₂'_def (z := (z : ℂ)) (UpperHalfPlane.im_pos z))

/-- Periodicity of `varphi` under translation by `1` on `ℍ`. -/
public lemma varphi_periodic (z : UpperHalfPlane) :
    varphi (((1 : ℝ) +ᵥ z) : UpperHalfPlane) = varphi z := by
  simpa using! (_root_.SpherePacking.Dim24.varphi_periodic (z := z))

/-- Periodicity of `varphi₁` under translation by `1` on `ℍ`. -/
public lemma varphi₁_periodic (z : UpperHalfPlane) :
    varphi₁ (((1 : ℝ) +ᵥ z) : UpperHalfPlane) = varphi₁ z := by
  simpa using! (_root_.SpherePacking.Dim24.varphi₁_periodic (z := z))

/-- Periodicity of `varphi₂` under translation by `1` on `ℍ`. -/
public lemma varphi₂_periodic (z : UpperHalfPlane) :
    varphi₂ (((1 : ℝ) +ᵥ z) : UpperHalfPlane) = varphi₂ z := by
  simpa using! (_root_.SpherePacking.Dim24.varphi₂_periodic (z := z))

/-- `S`-transform identity for `varphi`, rewritten after multiplying by `z^10`. -/
public lemma varphi_S_transform_mul_pow10 (z : UpperHalfPlane) :
    ((z : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • z) =
      ((z : ℂ) ^ (2 : ℕ)) * varphi z + (z : ℂ) * varphi₁ z + varphi₂ z := by
  have hz : (z : ℂ) ≠ 0 := by
    simpa using! (UpperHalfPlane.ne_zero z)
  have h := varphi_S_transform (z := z)
  -- Multiply the `z^8`-identity by `z^2`.
  grind only

end SpecialValuesAux

/-!
## Strip-contour reduction for the even special values

For `u = 0,2,4` we have `exp(π i u) = 1`, so the vertical-segment pieces cancel and the remaining
horizontal pieces can be rewritten using the `S`-transformation law for `varphi`. The `varphi` part
then cancels against the tail integral `I₆'` by Cauchy-Goursat on an infinite vertical strip,
leaving only a period integral of `varphi₁`.

This section sets up that reduction; the `varphi₁` period integrals are evaluated in the
final special-value development.
-/


end

end SpherePacking.Dim24
