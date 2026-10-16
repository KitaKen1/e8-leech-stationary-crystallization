-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.DeltaQHalf.Base


/-!
# Cusp expansion of `(Δ / qHalf^2)⁻²` to order `qHalf^2`

This file deduces the corresponding expansion for the inverse square of the normalized discriminant
`Δ / qHalf^2`:
`((Δ / qHalf^2)⁻² - 1) / qHalf^2 → 48`.

## Main statements
* `tendsto_Delta_div_qHalf_sq_inv_sq_sub_one_div_qHalf_sq`
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

/-- As `Im z → ∞`, the normalized error `((Δ z / qHalf(z)^2)⁻² - 1) / qHalf(z)^2` tends to `48`. -/
public lemma tendsto_Delta_div_qHalf_sq_inv_sq_sub_one_div_qHalf_sq :
    Tendsto
        (fun z : ℍ =>
          (((Δ z) / (qHalf z) ^ (2 : ℕ) : ℂ)⁻¹ ^ (2 : ℕ) - (1 : ℂ)) / (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (48 : ℂ)) := by
  -- If `D = Δ/q^2 = 1 - 24 q^2 + o(q^2)`, then `D⁻² = 1 + 48 q^2 + o(q^2)`.
  let q2 : ℍ → ℂ := fun z : ℍ => (qHalf z) ^ (2 : ℕ)
  let D : ℍ → ℂ := fun z : ℍ => (Δ z) / q2 z
  have hDsub :
      Tendsto (fun z : ℍ => (D z - (1 : ℂ)) / q2 z) atImInfty (𝓝 (-24 : ℂ)) := by
    simpa [D, q2] using! tendsto_Delta_div_qHalf_sq_sub_one_div_qHalf_sq
  have hD : Tendsto D atImInfty (𝓝 (1 : ℂ)) := by
    have hq : Tendsto q2 atImInfty (𝓝 (0 : ℂ)) := by
      simpa [q2] using! (tendsto_qHalf_atImInfty.pow 2)
    have hEq : D = fun z : ℍ => (1 : ℂ) + q2 z * ((D z - (1 : ℂ)) / q2 z) := by
      funext z
      have hq2z : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
      field_simp [D, q2, hq2z]
      ring_nf
    have hmul : Tendsto (fun z : ℍ => q2 z * ((D z - (1 : ℂ)) / q2 z)) atImInfty (𝓝 (0 : ℂ)) := by
      simpa [zero_mul] using! (hq.mul hDsub)
    have hform :
        Tendsto (fun z : ℍ => (1 : ℂ) + q2 z * ((D z - (1 : ℂ)) / q2 z)) atImInfty (𝓝 (1 : ℂ)) := by
      simpa [add_zero] using! (tendsto_const_nhds.add hmul)
    exact (tendsto_congr (congrFun (id (Eq.symm hEq)))).mp hform
  have hD2 : Tendsto (fun z : ℍ => (D z) ^ (2 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using! (hD.pow 2)
  have hD2inv : Tendsto (fun z : ℍ => ((D z) ^ (2 : ℕ))⁻¹) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using! (hD2.inv₀ (by simp))
  have hDplus : Tendsto (fun z : ℍ => D z + (1 : ℂ)) atImInfty (𝓝 (2 : ℂ)) := by
    have h1 : Tendsto (fun _ : ℍ => (1 : ℂ)) atImInfty (𝓝 (1 : ℂ)) := tendsto_const_nhds
    have hconst : (1 : ℂ) + (1 : ℂ) = (2 : ℂ) := by norm_num
    simpa [hconst] using! (hD.add h1)
  have hD2sub :
      Tendsto (fun z : ℍ => ((D z) ^ (2 : ℕ) - (1 : ℂ)) / q2 z) atImInfty (𝓝 (-48 : ℂ)) := by
    have hEq :
        (fun z : ℍ => ((D z) ^ (2 : ℕ) - (1 : ℂ)) / q2 z) =
          fun z : ℍ => ((D z - (1 : ℂ)) / q2 z) * (D z + (1 : ℂ)) := by
      funext z
      ring
    have :
        Tendsto (fun z : ℍ => ((D z - (1 : ℂ)) / q2 z) * (D z + (1 : ℂ))) atImInfty
          (𝓝 ((-24 : ℂ) * (2 : ℂ))) :=
      hDsub.mul hDplus
    have hconst : ((-24 : ℂ) * (2 : ℂ)) = (-48 : ℂ) := by norm_num
    simpa [hEq, hconst] using! this
  have hEq :
      (fun z : ℍ => (((D z) ^ (2 : ℕ))⁻¹ - (1 : ℂ)) / q2 z) =
        fun z : ℍ => -(((D z) ^ (2 : ℕ) - (1 : ℂ)) / q2 z) * ((D z) ^ (2 : ℕ))⁻¹ := by
    funext z
    have hq2z : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
    have hD0 : D z ≠ 0 := by
      have hΔ0 : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
      exact div_ne_zero hΔ0 hq2z
    have hD2 : (D z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hD0
    field_simp [q2, hq2z, hD2]
    ring_nf
  have hmain :
      Tendsto
          (fun z : ℍ =>
            -(((D z) ^ (2 : ℕ) - (1 : ℂ)) / q2 z) * ((D z) ^ (2 : ℕ))⁻¹)
          atImInfty (𝓝 (-((-48 : ℂ) * (1 : ℂ)))) := by
    simpa [mul_assoc] using! (hD2sub.mul hD2inv).neg
  have hconst : -((-48 : ℂ) * (1 : ℂ)) = (48 : ℂ) := by norm_num
  have hres :
      Tendsto (fun z : ℍ => (((D z) ^ (2 : ℕ))⁻¹ - (1 : ℂ)) / q2 z) atImInfty (𝓝 (48 : ℂ)) := by
    simp_all
  -- Rewrite `(Δ/q2)⁻²` as `((D^2)⁻¹)`.
  simpa [D, q2, pow_two] using! hres

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
