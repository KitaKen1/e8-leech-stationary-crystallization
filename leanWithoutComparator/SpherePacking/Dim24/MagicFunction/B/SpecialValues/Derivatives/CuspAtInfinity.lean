-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.ModularForms.Psi.Relations
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.TopEdge.Base
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.TopEdge.Limits


/-!
# Asymptotic of `ψI` at the cusp `i∞`

We prove `ψI(z) * exp(4π i z) → 2` as `Im z → ∞`. This is the key analytic input for the special
value `Bfun 4 = 2`.

## Main statements
* `tendsto_ψI_mul_cexp_four_pi_mul_I`
-/

open scoped Real
open scoped Topology
open scoped UpperHalfPlane
open scoped Complex

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter UpperHalfPlane

namespace Deriv

/-- As `Im z → ∞`, the normalized expression `ψI z * exp(4π i z)` tends to `2`. -/
public lemma tendsto_ψI_mul_cexp_four_pi_mul_I :
    Tendsto
      (fun z : ℍ => ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ)))
      atImInfty (𝓝 (2 : ℂ)) := by
  have hψ : ψI =
        fun z : ℍ =>
          (7 * (H₄ z) ^ 5 * (H₂ z) ^ 2 + 7 * (H₄ z) ^ 6 * (H₂ z) + 2 * (H₄ z) ^ 7) /
            (Δ z) ^ 2 := by
    funext z
    simpa using! (SpherePacking.Dim24.ψI_eq_H z)
  let P : ℍ → ℂ :=
    fun z : ℍ => ∏' (n : ℕ), (1 - cexp (2 * π * Complex.I * (↑n + 1) * (z : ℂ))) ^ 24
  have hΔ : ∀ z : ℍ, (Δ z) ^ (2 : ℕ) = cexp (4 * π * Complex.I * (z : ℂ)) * (P z) ^ (2 : ℕ) := by
    intro z
    have hExp :
        (cexp (2 * π * Complex.I * (z : ℂ))) ^ (2 : ℕ) = cexp (4 * π * Complex.I * (z : ℂ)) := by
      have h := (Complex.exp_nat_mul (2 * π * Complex.I * (z : ℂ)) 2).symm
      have hmul : (2 : ℂ) * (2 * π * Complex.I * (z : ℂ)) = 4 * π * Complex.I * (z : ℂ) := by
        ring
      simpa [hmul] using! h
    calc
      (Δ z) ^ (2 : ℕ) = (cexp (2 * π * Complex.I * (z : ℂ)) * P z) ^ (2 : ℕ) := by
        simp [Δ, P]
      _ = (cexp (2 * π * Complex.I * (z : ℂ))) ^ (2 : ℕ) * (P z) ^ (2 : ℕ) := by
        simp [mul_pow]
      _ = cexp (4 * π * Complex.I * (z : ℂ)) * (P z) ^ (2 : ℕ) := by
        simp [hExp]
  have hP : Tendsto P atImInfty (𝓝 (1 : ℂ)) := by
    exact Delta_boundedfactor
  have hnum :
      Tendsto (fun z : ℍ =>
        (7 * (H₄ z) ^ 5 * (H₂ z) ^ 2 + 7 * (H₄ z) ^ 6 * (H₂ z) + 2 * (H₄ z) ^ 7))
        atImInfty (𝓝 (2 : ℂ)) := by
    have hH2 : Tendsto H₂ atImInfty (𝓝 (0 : ℂ)) := H₂_tendsto_atImInfty
    have hH4 : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
    have hterm1 :
        Tendsto (fun z : ℍ => 7 * (H₄ z) ^ 5 * (H₂ z) ^ 2) atImInfty (𝓝 (0 : ℂ)) := by
      have hcore :
          Tendsto (fun z : ℍ => (H₄ z) ^ 5 * (H₂ z) ^ 2) atImInfty
            (𝓝 ((1 : ℂ) ^ 5 * (0 : ℂ) ^ 2)) :=
        (hH4.pow 5).mul (hH2.pow 2)
      have h7 : Tendsto (fun _ : ℍ => (7 : ℂ)) atImInfty (𝓝 (7 : ℂ)) := tendsto_const_nhds
      have :
          Tendsto (fun z : ℍ => (7 : ℂ) * ((H₄ z) ^ 5 * (H₂ z) ^ 2))
            atImInfty (𝓝 ((7 : ℂ) * ((1 : ℂ) ^ 5 * (0 : ℂ) ^ 2))) := h7.mul hcore
      simpa [mul_assoc] using! this
    have hterm2 :
        Tendsto (fun z : ℍ => 7 * (H₄ z) ^ 6 * (H₂ z)) atImInfty (𝓝 (0 : ℂ)) := by
      have hcore :
          Tendsto (fun z : ℍ => (H₄ z) ^ 6 * (H₂ z)) atImInfty (𝓝 ((1 : ℂ) ^ 6 * (0 : ℂ))) :=
        (hH4.pow 6).mul hH2
      have h7 : Tendsto (fun _ : ℍ => (7 : ℂ)) atImInfty (𝓝 (7 : ℂ)) := tendsto_const_nhds
      have :
          Tendsto (fun z : ℍ => (7 : ℂ) * ((H₄ z) ^ 6 * (H₂ z)))
            atImInfty (𝓝 ((7 : ℂ) * ((1 : ℂ) ^ 6 * (0 : ℂ)))) := h7.mul hcore
      simpa [mul_assoc] using! this
    have hterm3 :
        Tendsto (fun z : ℍ => 2 * (H₄ z) ^ 7) atImInfty (𝓝 (2 : ℂ)) := by
      simpa using! (tendsto_const_nhds.mul (hH4.pow 7))
    have :
        Tendsto (fun z : ℍ => (7 * (H₄ z) ^ 5 * (H₂ z) ^ 2 + 7 * (H₄ z) ^ 6 * (H₂ z)))
          atImInfty (𝓝 (0 : ℂ)) := by
      simpa using! hterm1.add hterm2
    have :
        Tendsto (fun z : ℍ =>
            (7 * (H₄ z) ^ 5 * (H₂ z) ^ 2 + 7 * (H₄ z) ^ 6 * (H₂ z)) + (2 * (H₄ z) ^ 7))
          atImInfty (𝓝 (0 + (2 : ℂ))) := this.add hterm3
    simpa [add_assoc] using! this
  have hrew :
      (fun z : ℍ => ψI z * cexp (4 * Real.pi * Complex.I * (z : ℂ))) =
        fun z : ℍ =>
          (7 * (H₄ z) ^ 5 * (H₂ z) ^ 2 + 7 * (H₄ z) ^ 6 * (H₂ z) + 2 * (H₄ z) ^ 7) / (P z) ^ 2 := by
    funext z
    rw [hψ]
    have hΔ' := hΔ z
    have hfac :
        cexp (4 * π * Complex.I * (z : ℂ)) * ((Δ z) ^ (2 : ℕ))⁻¹ = ((P z) ^ (2 : ℕ))⁻¹ := by
      have hΔinv :
          ((Δ z) ^ (2 : ℕ))⁻¹ = (cexp (4 * π * Complex.I * (z : ℂ)) * (P z) ^ (2 : ℕ))⁻¹ := by
        simpa using! congrArg Inv.inv hΔ'
      -- Cancel the exponential factor using `hΔinv`.
      -- `a * (a*b)⁻¹ = b⁻¹` in a commutative group (`ℂ`).
      calc
        cexp (4 * π * Complex.I * (z : ℂ)) * ((Δ z) ^ (2 : ℕ))⁻¹
            =
              cexp (4 * π * Complex.I * (z : ℂ)) *
                (cexp (4 * π * Complex.I * (z : ℂ)) * (P z) ^ (2 : ℕ))⁻¹ := by
                simp [hΔinv]
        _ = ((P z) ^ (2 : ℕ))⁻¹ := by
              simp [mul_comm]
    -- Replace `1/(Δ^2) * exp(4πiz)` by `1/(P^2)`.
    grind only
  have hden : Tendsto (fun z : ℍ => (P z) ^ (2 : ℕ)) atImInfty (𝓝 ((1 : ℂ) ^ (2 : ℕ))) :=
    hP.pow 2
  have hden' : Tendsto (fun z : ℍ => ((P z) ^ (2 : ℕ))⁻¹) atImInfty (𝓝 ((1 : ℂ) ^ (2 : ℕ))⁻¹) :=
    (hden.inv₀ (by simp))
  have :
      Tendsto
        (fun z : ℍ =>
          (7 * (H₄ z) ^ 5 * (H₂ z) ^ 2 + 7 * (H₄ z) ^ 6 * (H₂ z) + 2 * (H₄ z) ^ 7) *
            ((P z) ^ (2 : ℕ))⁻¹)
        atImInfty (𝓝 ((2 : ℂ) * ((1 : ℂ) ^ (2 : ℕ))⁻¹)) :=
    hnum.mul hden'
  have hone : ((1 : ℂ) ^ (2 : ℕ))⁻¹ = (1 : ℂ) := by simp
  simpa [hrew, div_eq_mul_inv, hone] using! this

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
