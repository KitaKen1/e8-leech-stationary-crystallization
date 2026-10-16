-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.DeltaQHalf.Base
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.DeltaQHalf.InvSq


/-!
# `qHalf`-expansion consequences for `H₂` at the cusp `i∞`

This file proves limit statements for `H₂` normalized by powers of `qHalf`, used in the
cusp-coefficient computation for `ψI`.

## Main statements
* `tendsto_H₂_div_qHalf`
* `tendsto_H₂_sub_sixteen_mul_qHalf_div_qHalf_sq`
* `tendsto_H₂_sq_div_qHalf_sq`
-/

open scoped Real
open scoped Topology
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter UpperHalfPlane

namespace Deriv

/-- Leading term of `H₂` at the cusp: `H₂(z) / qHalf(z) → 16`. -/
public lemma tendsto_H₂_div_qHalf :
    Tendsto (fun z : ℍ => H₂ z / qHalf z) atImInfty (𝓝 (16 : ℂ)) := by
  have h := tendsto_H₂_div_qHalf_sub_const_div_qHalf_sq
  have hq2 :
      Tendsto (fun z : ℍ => (qHalf z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) :=
    tendsto_qHalf_sq_atImInfty
  have hmul :
      Tendsto
          (fun z : ℍ =>
            (qHalf z) ^ (2 : ℕ) * ((H₂ z / qHalf z - (16 : ℂ)) / (qHalf z) ^ (2 : ℕ)))
          atImInfty (𝓝 (0 : ℂ)) := by
    simpa [mul_zero] using! (hq2.mul h)
  have hEq :
      (fun z : ℍ => H₂ z / qHalf z) =
        fun z : ℍ =>
          (16 : ℂ) + (qHalf z) ^ (2 : ℕ) * ((H₂ z / qHalf z - (16 : ℂ)) / (qHalf z) ^ (2 : ℕ)) := by
    funext z
    have hq0 : qHalf z ≠ 0 := qHalf_ne_zero z
    have hq2z : (qHalf z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hq0
    field_simp [hq0, hq2z]
    ring
  have :
      Tendsto
          (fun z : ℍ =>
            (16 : ℂ) + (qHalf z) ^ (2 : ℕ) * ((H₂ z / qHalf z - (16 : ℂ)) / (qHalf z) ^ (2 : ℕ)))
          atImInfty (𝓝 (16 : ℂ)) := by
    simpa [add_zero] using! (tendsto_const_nhds.add hmul)
  simpa [hEq] using! this

/-- After subtracting `16 * qHalf`, the remainder of `H₂` is `o(qHalf^2)` at the cusp. -/
public lemma tendsto_H₂_sub_sixteen_mul_qHalf_div_qHalf_sq :
    Tendsto
        (fun z : ℍ => (H₂ z - (16 : ℂ) * qHalf z) / (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (0 : ℂ)) := by
  have hH2 := tendsto_H₂_div_qHalf_sub_const_div_qHalf_sq
  have hEq :
      (fun z : ℍ => (H₂ z - (16 : ℂ) * qHalf z) / (qHalf z) ^ (2 : ℕ)) =
        fun z : ℍ => qHalf z * ((H₂ z / qHalf z - (16 : ℂ)) / (qHalf z) ^ (2 : ℕ)) := by
    funext z
    have hq0 : qHalf z ≠ 0 := qHalf_ne_zero z
    have hq2z : (qHalf z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hq0
    field_simp [hq0, hq2z]
  have :
      Tendsto (fun z : ℍ => qHalf z * ((H₂ z / qHalf z - (16 : ℂ)) / (qHalf z) ^ (2 : ℕ))) atImInfty
        (𝓝 (0 * (64 : ℂ))) := tendsto_qHalf_atImInfty.mul hH2
  simpa [hEq, mul_zero] using! this

/-- Quadratic normalization of `H₂`: `(H₂ z)^2 / qHalf(z)^2 → 16^2` at the cusp. -/
public lemma tendsto_H₂_sq_div_qHalf_sq :
    Tendsto
        (fun z : ℍ => (H₂ z) ^ (2 : ℕ) / (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 ((16 : ℂ) ^ (2 : ℕ))) := by
  have hH2 := tendsto_H₂_div_qHalf
  have hEq :
      (fun z : ℍ => (H₂ z) ^ (2 : ℕ) / (qHalf z) ^ (2 : ℕ)) =
        fun z : ℍ => (H₂ z / qHalf z) ^ (2 : ℕ) := by
    funext z
    have hq0 : qHalf z ≠ 0 := qHalf_ne_zero z
    field_simp [hq0]
  simpa [hEq] using! (hH2.pow 2)

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
