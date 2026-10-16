-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Mobius inversion

Basic API for the Mobius inversion map `z ↦ -z⁻¹` used throughout the project.

This module defines `SpherePacking.mobiusInv` and records elementary algebraic and derivative
facts, so downstream contour developments do not duplicate wrapper lemmas.
-/

namespace SpherePacking

noncomputable section

/-- The Mobius inversion map `z ↦ -z⁻¹`. -/
@[expose] public def mobiusInv (z : ℂ) : ℂ := -z⁻¹

/-- Algebraic simplification of `mobiusInv z - 1`. -/
public lemma mobiusInv_sub_one (z : ℂ) (hz0 : z ≠ 0) :
    mobiusInv z - 1 = -(z + 1) / z := by
  simp [mobiusInv, sub_eq_add_neg, div_eq_mul_inv, hz0, add_mul]

/-- Imaginary part of `mobiusInv z` in terms of `z.im` and `‖z‖^2`. -/
public lemma mobiusInv_im (z : ℂ) : (mobiusInv z).im = z.im / Complex.normSq z := by
  simp [mobiusInv, Complex.inv_im, div_eq_mul_inv]

/-- If `z` is in the upper half-plane, then so is `mobiusInv z`. -/
public lemma mobiusInv_im_pos (z : ℂ) (hz : 0 < z.im) : 0 < (mobiusInv z).im := by
  simpa [mobiusInv_im] using div_pos hz (Complex.normSq_pos.2 (fun hz0 => hz.ne' (by simp [hz0])))

/-- Complex derivative of `mobiusInv`. -/
public lemma deriv_mobiusInv (z : ℂ) :
    deriv mobiusInv z = (1 : ℂ) / z ^ (2 : ℕ) := by
  simp [show mobiusInv = (fun z : ℂ => -z⁻¹) from rfl, deriv_inv, div_eq_mul_inv]

/-- Real Fréchet derivative of `mobiusInv` at a nonzero point. -/
public lemma hasFDerivAt_mobiusInv_real (z : ℂ) (hz : z ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) mobiusInv (ContinuousLinearMap.mulLeftRight ℝ ℂ z⁻¹ z⁻¹) z := by
  have h := (hasFDerivAt_inv' (𝕜 := ℝ) (R := ℂ) hz).neg
  rw [neg_neg] at h
  exact h

/-- Derivative of `mobiusInv` composed with a line segment `AffineMap.lineMap a b`. -/
public lemma hasDerivAt_mobiusInv_comp_lineMap (a b : ℂ) (t : ℝ)
    (h0 : AffineMap.lineMap a b t ≠ 0) :
    HasDerivAt (fun s : ℝ => mobiusInv (AffineMap.lineMap a b s))
      ((b - a) / (AffineMap.lineMap a b t) ^ (2 : ℕ)) t := by
  simpa [mobiusInv, div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm, Function.comp_def, Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.neg_def, Pi.smul_def, Pi.div_def] using ((hasFDerivAt_mobiusInv_real (z := AffineMap.lineMap a b t) h0).comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := a) (b := b) (x := t)))

end

end SpherePacking
