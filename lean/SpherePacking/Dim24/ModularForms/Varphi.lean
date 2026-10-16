/-
The quasimodular form `varphi` used in the `+1` eigenfunction construction in `ℝ²⁴`.

Paper reference: `dim_24.tex`, Section 2 (`sec:a`).
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.ModularForms.Eisenstein
public import SpherePacking.ModularForms.E2.Transform
public import SpherePacking.ModularForms.Delta.ImagAxis


/-!
# The quasimodular form `varphi`

This file defines the weakly holomorphic quasimodular form `varphi` of weight `-8` and depth `2`
used in the `+1` eigenfunction construction in `ℝ²⁴`.

It also defines the auxiliary forms `varphi₁` and `varphi₂` appearing in the `S`-transformation
law for `varphi`.

## Main definitions
* `varphi`
* `varphi₁`
* `varphi₂`

## Main statements
* `varphi_periodic`
* `varphi₁_periodic`
* `varphi₂_periodic`
* `varphi_S_transform`

## Implementation notes
We also record holomorphy facts used for Cauchy-Goursat arguments on rectangles in the upper
half-plane.
-/

namespace SpherePacking.Dim24

noncomputable section

open scoped Real BigOperators Manifold
open UpperHalfPlane MatrixGroups Complex
open ModularForm hiding E E₄ E₆

/-- The weakly holomorphic quasimodular form `varphi` of weight `-8` and depth `2`. -/
@[expose]
public def varphi (z : ℍ) : ℂ :=
  ((25 * (E₄ z) ^ 4 - 49 * (E₆ z) ^ 2 * (E₄ z))
      + 48 * (E₆ z) * (E₄ z) ^ 2 * (E₂ z)
      + ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2) * (E₂ z) ^ 2) / (Δ z) ^ 2

/-- The auxiliary form `varphi₁` appearing in the S-transformation law for `varphi`. -/
@[expose]
public def varphi₁ (z : ℍ) : ℂ :=
  (- (6 * Complex.I) / π) * 48 * ((E₆ z) * (E₄ z) ^ 2) / (Δ z) ^ 2
    - (12 * Complex.I) / π * (E₂ z * ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2)) / (Δ z) ^ 2

/-- The auxiliary form `varphi₂` appearing in the S-transformation law for `varphi`. -/
@[expose]
public def varphi₂ (z : ℍ) : ℂ :=
  (-36) * ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2) / (π ^ 2 * (Δ z) ^ 2)

/-!
### Periodicity

The basic modular forms `E₂,E₄,E₆,Δ` are periodic with period `1`, hence so are `varphi`, `varphi₁`,
and `varphi₂`. These lemmas are used throughout the `+1` eigenfunction construction.
-/

/-- Periodicity of `varphi` under translation by `1`. -/
public lemma varphi_periodic (z : ℍ) : varphi ((1 : ℝ) +ᵥ z) = varphi z := by
  simp [varphi, E₂_periodic, E₄_periodic, E₆_periodic, Δ_periodic, -E4_apply, -E6_apply]

/-- Periodicity of `varphi₁` under translation by `1`. -/
public lemma varphi₁_periodic (z : ℍ) : varphi₁ ((1 : ℝ) +ᵥ z) = varphi₁ z := by
  simp [varphi₁, E₂_periodic, E₄_periodic, E₆_periodic, Δ_periodic, -E4_apply, -E6_apply]

/-- Periodicity of `varphi₂` under translation by `1`. -/
public lemma varphi₂_periodic (z : ℍ) : varphi₂ ((1 : ℝ) +ᵥ z) = varphi₂ z := by
  simp [varphi₂, E₄_periodic, E₆_periodic, Δ_periodic, -E4_apply, -E6_apply]

/-- Quasimodularity relation for `varphi` under `S : z ↦ -1/z`. -/
public theorem varphi_S_transform (z : ℍ) :
    (z : ℂ) ^ (8 : ℕ) * varphi (ModularGroup.S • z) =
      varphi z + varphi₁ z / z + varphi₂ z / (z ^ 2) := by
  /- Proof sketch:
  Expand `varphi` in terms of `E₂,E₄,E₆,Δ`, use the known transformation laws
  `E₂_S_transform`, `E₄_S_transform`, `E₆_S_transform`, `Δ_S_transform`,
  and then collect terms in powers of `1/z` coming from the quasimodular correction in `E₂`.
  -/
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  -- Abbreviate the pieces of the numerator that are independent of `E₂`.
  set A : ℂ :=
    (25 * (E₄ z) ^ 4 - 49 * (E₆ z) ^ 2 * (E₄ z)) / (Δ z) ^ 2 with hA
  set B : ℂ := 48 * (E₆ z) * (E₄ z) ^ 2 / (Δ z) ^ 2 with hB
  set C : ℂ := ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2) / (Δ z) ^ 2 with hC
  have hD2 : (Δ z : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (Δ_ne_zero z)
  have hvarphi : varphi z = A + B * (E₂ z) + C * (E₂ z) ^ 2 := by
    -- Expand `varphi` and clear the common denominator `(Δ z)^2`.
    simp [varphi, hA, hB, hC]
    field_simp [hD2]
  have hvarphi₁ :
      varphi₁ z = (- (6 * Complex.I) / π) * B - (12 * Complex.I) / π * (E₂ z * C) := by
    simp [varphi₁, hB, hC, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
    field_simp [hπ, hD2]
  have hvarphi₂ : varphi₂ z = (-36) / (π ^ 2) * C := by
    simp [varphi₂, hC, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- Apply the S-transformation laws and factor out the weight contribution.
  have hE2S :
      E₂ (↑ModularGroup.S • z) = z ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) := by
    simpa using! (E₂_S_transform z)
  have hE4S : E₄ (↑ModularGroup.S • z) = z ^ (4 : ℕ) * E₄ z := by
    simpa using! (E₄_S_transform z)
  have hE6S : E₆ (↑ModularGroup.S • z) = z ^ (6 : ℕ) * E₆ z := by
    simpa using! (E₆_S_transform z)
  have hΔS : Δ (↑ModularGroup.S • z) = z ^ (12 : ℕ) * Δ z := by
    simpa using! (Δ_S_transform z)
  unfold varphi
  rw [hE2S, hE4S, hE6S, hΔS]
  -- After rewriting, everything is a rational expression in `z`
  -- and the values of `E₂,E₄,E₆,Δ` at `z`.
  -- We simplify the `z`-powers first.
  have hzpow :
      (z : ℂ) ^ (8 : ℕ) *
          (((25 * (z ^ (4 : ℕ) * E₄ z) ^ 4
                    - 49 * (z ^ (6 : ℕ) * E₆ z) ^ 2 * (z ^ (4 : ℕ) * E₄ z)
                    + 48 * (z ^ (6 : ℕ) * E₆ z) * (z ^ (4 : ℕ) * E₄ z) ^ 2 *
                        (z ^ 2 * (E₂ z + 6 / (π * Complex.I * z)))
                    + ((-49) * (z ^ (4 : ℕ) * E₄ z) ^ 3 + 25 * (z ^ (6 : ℕ) * E₆ z) ^ 2) *
                        (z ^ 2 * (E₂ z + 6 / (π * Complex.I * z))) ^ 2) /
                (z ^ (12 : ℕ) * Δ z) ^ 2)) =
        ((25 * (E₄ z) ^ 4 - 49 * (E₆ z) ^ 2 * (E₄ z) +
              48 * (E₆ z) * (E₄ z) ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) +
              ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2) *
                (E₂ z + 6 / (π * Complex.I * z)) ^ 2) /
            (Δ z) ^ 2) := by
    -- All terms in the big numerator carry the same `z^16` factor, while the denominator is `z^24`.
    -- Multiplying by `z^8` cancels the remaining `z`-powers.
    have hz0 : (z : ℂ) ^ (12 : ℕ) ≠ 0 := pow_ne_zero _ hz
    field_simp [hz0, hz]
  -- Use `hzpow` to reduce to expanding the quasimodular correction `(E₂ z + 6/(πIz))`.
  rw [hzpow]
  -- Replace the RHS `varphi z + varphi₁/z + varphi₂/z^2` by the `A,B,C`-expansion.
  -- Let `c = 6/(πIz)`. Then:
  -- `A + B*(E₂+c) + C*(E₂+c)^2 = (A + B*E₂ + C*E₂^2) + c*(B + 2C*E₂) + c^2*C`.
  set c : ℂ := 6 / (π * Complex.I * z) with hc
  have hc1 : c = (- (6 * Complex.I) / π) / z := by
    have hπI : (π : ℂ) * Complex.I ≠ 0 := mul_ne_zero hπ hI
    calc
      c = (6 : ℂ) / ((π : ℂ) * Complex.I * z) := by simp [hc, mul_assoc]
      _ = ((6 : ℂ) / ((π : ℂ) * Complex.I)) / z := by
            field_simp [hz, hπI]
      _ = (- (6 * Complex.I) / (π : ℂ)) / z := by
            field_simp [hπ, hI, Complex.inv_I]
            simp [Complex.I_sq]
  have hc2 : c ^ 2 = (-36) / (π ^ 2) / (z ^ 2) := by
    rw [hc1]
    field_simp [hz, hπ]
    simp [Complex.I_sq]
    ring_nf
  -- Now finish by expanding and matching coefficients.
  -- First rewrite the goal in terms of `A,B,C`.
  grind only


/-- Holomorphy of `varphi` on the upper half-plane. -/
public theorem varphi_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) varphi := by
  -- Reduce to differentiability of `varphi ∘ ofComplex` on the open set `{z : ℂ | 0 < z.im}`.
  refine (UpperHalfPlane.mdifferentiable_iff).2 ?_
  let s : Set ℂ := {z : ℂ | 0 < z.im}
  -- Build differentiability facts for the building blocks.
  have hE2 : DifferentiableOn ℂ (E₂ ∘ UpperHalfPlane.ofComplex) s :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₂_holo')
  have hE4 : DifferentiableOn ℂ ((E₄ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) s :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₄.holo')
  have hE6 : DifferentiableOn ℂ ((E₆ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) s :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₆.holo')
  have hΔ : DifferentiableOn ℂ (Δ ∘ UpperHalfPlane.ofComplex) s := by
    -- `Δ` is the `Delta` cusp form on `Γ(1)`.
    -- We use the holomorphy of `Delta` and the definitional equality `Delta_apply`.
    simpa [Delta_apply] using!
      (UpperHalfPlane.mdifferentiable_iff.mp
        (Delta.holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => Delta z)))
  -- Powers of holomorphic functions.
  have hE4_2 :
      DifferentiableOn ℂ (fun z : ℂ => (E₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ)) s :=
    hE4.pow 2
  have hE4_3 :
      DifferentiableOn ℂ (fun z : ℂ => (E₄ (UpperHalfPlane.ofComplex z)) ^ (3 : ℕ)) s :=
    hE4.pow 3
  have hE4_4 :
      DifferentiableOn ℂ (fun z : ℂ => (E₄ (UpperHalfPlane.ofComplex z)) ^ (4 : ℕ)) s :=
    hE4.pow 4
  have hE6_2 :
      DifferentiableOn ℂ (fun z : ℂ => (E₆ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ)) s :=
    hE6.pow 2
  have hE2_2 :
      DifferentiableOn ℂ (fun z : ℂ => (E₂ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ)) s :=
    hE2.pow 2
  have hΔ_2 :
      DifferentiableOn ℂ (fun z : ℂ => (Δ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ)) s :=
    hΔ.pow 2
  have hΔ2_ne :
      ∀ z : ℂ, z ∈ s → (Δ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ) ≠ 0 := by
    intro z hz
    have hz' : 0 < z.im := hz
    -- On `{0 < z.im}`, `ofComplex z` is definitionally `⟨z, hz'⟩`.
    have hof : UpperHalfPlane.ofComplex z = ⟨z, hz'⟩ :=
      UpperHalfPlane.ofComplex_apply_of_im_pos hz'
    -- Use nonvanishing of `Δ` on `ℍ`.
    have hΔ0 : Δ (⟨z, hz'⟩ : ℍ) ≠ 0 := Δ_ne_zero (⟨z, hz'⟩ : ℍ)
    simpa [hof] using! (pow_ne_zero 2 hΔ0)
  -- Assemble the numerator as a polynomial expression.
  have hnum :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          ((25 : ℂ) * (E₄ (UpperHalfPlane.ofComplex z)) ^ 4 -
              (49 : ℂ) * (E₆ (UpperHalfPlane.ofComplex z)) ^ 2 *
                  (E₄ (UpperHalfPlane.ofComplex z)) +
              (48 : ℂ) * (E₆ (UpperHalfPlane.ofComplex z)) *
                  (E₄ (UpperHalfPlane.ofComplex z)) ^ 2 * (E₂ (UpperHalfPlane.ofComplex z)) +
              ((-49 : ℂ) * (E₄ (UpperHalfPlane.ofComplex z)) ^ 3 +
                    (25 : ℂ) * (E₆ (UpperHalfPlane.ofComplex z)) ^ 2) *
                (E₂ (UpperHalfPlane.ofComplex z)) ^ 2))
        s := by
    have hE4_1 : DifferentiableOn ℂ (fun z : ℂ => E₄ (UpperHalfPlane.ofComplex z)) s := hE4
    have hE6_1 : DifferentiableOn ℂ (fun z : ℂ => E₆ (UpperHalfPlane.ofComplex z)) s := hE6
    have hE2_1 : DifferentiableOn ℂ (fun z : ℂ => E₂ (UpperHalfPlane.ofComplex z)) s := hE2
    let term1 : ℂ → ℂ := fun z : ℂ => (25 : ℂ) * (E₄ (UpperHalfPlane.ofComplex z)) ^ 4
    let term2 : ℂ → ℂ := fun z : ℂ =>
      (49 : ℂ) * (E₆ (UpperHalfPlane.ofComplex z)) ^ 2 * (E₄ (UpperHalfPlane.ofComplex z))
    let term3 : ℂ → ℂ := fun z : ℂ =>
      (48 : ℂ) *
        (E₆ (UpperHalfPlane.ofComplex z)) *
        (E₄ (UpperHalfPlane.ofComplex z)) ^ 2 *
        (E₂ (UpperHalfPlane.ofComplex z))
    let term4 : ℂ → ℂ := fun z : ℂ =>
      ((-49 : ℂ) * (E₄ (UpperHalfPlane.ofComplex z)) ^ 3 +
            (25 : ℂ) * (E₆ (UpperHalfPlane.ofComplex z)) ^ 2) *
          (E₂ (UpperHalfPlane.ofComplex z)) ^ 2
    have hterm1 : DifferentiableOn ℂ term1 s := by
      simpa [term1] using! (hE4_4.const_mul (25 : ℂ))
    have hterm2 : DifferentiableOn ℂ term2 s := by
      have h49E6 :
          DifferentiableOn ℂ
            (fun z : ℂ => (49 : ℂ) * (E₆ (UpperHalfPlane.ofComplex z)) ^ 2) s :=
        hE6_2.const_mul (49 : ℂ)
      simpa [term2] using! h49E6.mul hE4_1
    have hterm3 : DifferentiableOn ℂ term3 s := by
      have h48E6 :
          DifferentiableOn ℂ (fun z : ℂ => (48 : ℂ) * E₆ (UpperHalfPlane.ofComplex z)) s :=
        hE6_1.const_mul (48 : ℂ)
      simpa [term3] using! ((h48E6.mul hE4_2).mul hE2_1)
    have hterm4 : DifferentiableOn ℂ term4 s := by
      have hpoly :
          DifferentiableOn ℂ
            (fun z : ℂ =>
              (-49 : ℂ) * (E₄ (UpperHalfPlane.ofComplex z)) ^ 3 +
                (25 : ℂ) * (E₆ (UpperHalfPlane.ofComplex z)) ^ 2) s := by
        simpa [mul_assoc] using!
          (hE4_3.const_mul (-49 : ℂ)).add (hE6_2.const_mul (25 : ℂ))
      simpa [term4] using! hpoly.mul hE2_2
    have h12 : DifferentiableOn ℂ (fun z : ℂ => term1 z - term2 z) s := hterm1.sub hterm2
    have h123 : DifferentiableOn ℂ (fun z : ℂ => (term1 z - term2 z) + term3 z) s :=
      h12.add hterm3
    exact DifferentiableOn.fun_add h123 hterm4
  -- Finish by dividing by `Δ^2`.
  have hdiv :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (((25 : ℂ) * (E₄ (UpperHalfPlane.ofComplex z)) ^ 4 -
              (49 : ℂ) * (E₆ (UpperHalfPlane.ofComplex z)) ^ 2 *
                  (E₄ (UpperHalfPlane.ofComplex z)) +
              (48 : ℂ) * (E₆ (UpperHalfPlane.ofComplex z)) *
                  (E₄ (UpperHalfPlane.ofComplex z)) ^ 2 * (E₂ (UpperHalfPlane.ofComplex z)) +
              ((-49 : ℂ) * (E₄ (UpperHalfPlane.ofComplex z)) ^ 3 +
                    (25 : ℂ) * (E₆ (UpperHalfPlane.ofComplex z)) ^ 2) *
                (E₂ (UpperHalfPlane.ofComplex z)) ^ 2) /
            (Δ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ)))
        s :=
    hnum.div hΔ_2 hΔ2_ne
  -- `varphi ∘ ofComplex` is definitionally this quotient.
  simpa [s, varphi, Function.comp_def] using! hdiv

end

end SpherePacking.Dim24
