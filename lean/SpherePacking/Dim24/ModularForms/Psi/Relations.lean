-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.ModularForms.Psi.Defs


/-!
# Relations among `ψI`, `ψS`, `ψT`

This file proves the relations `ψS + ψT = ψI` and derives formulas for the induced `S`-action
on `ψT`.

## References
* `dim_24.tex`, Section 3 (`sec:b`).
-/

namespace SpherePacking.Dim24

open scoped UpperHalfPlane Real ModularForm Manifold
open UpperHalfPlane Complex ModularGroup MatrixGroups ModularForm SlashAction

noncomputable section

/-- The modular discriminant `Δ` is holomorphic on the upper half-plane. -/
public lemma mdifferentiable_Δ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Δ := by
  simpa [Delta_apply] using! (Delta.holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => Delta z))

/-- Rewrite `ψI` in terms of the auxiliary functions `H₂` and `H₄`. -/
public lemma ψI_eq_H (z : ℍ) :
    ψI z =
      (7 * (H₄ z) ^ 5 * (H₂ z) ^ 2
            + 7 * (H₄ z) ^ 6 * (H₂ z)
            + 2 * (H₄ z) ^ 7) / (Δ z) ^ 2 := by
  have h8 : Θ₂ z ^ 8 = (Θ₂ z ^ 4) ^ 2 := by
    simpa [show (4 * 2 : ℕ) = 8 by decide] using! (pow_mul (Θ₂ z) 4 2)
  have h20 : Θ₄ z ^ 20 = (Θ₄ z ^ 4) ^ 5 := by
    simpa [show (4 * 5 : ℕ) = 20 by decide] using! (pow_mul (Θ₄ z) 4 5)
  have h24 : Θ₄ z ^ 24 = (Θ₄ z ^ 4) ^ 6 := by
    simpa [show (4 * 6 : ℕ) = 24 by decide] using! (pow_mul (Θ₄ z) 4 6)
  have h28 : Θ₄ z ^ 28 = (Θ₄ z ^ 4) ^ 7 := by
    simpa [show (4 * 7 : ℕ) = 28 by decide] using! (pow_mul (Θ₄ z) 4 7)
  simp [ψI, H₂, H₄, h8, h20, h24, h28]

/-- Complex differentiability of `z ↦ ψI (ofComplex z)` on the upper half-plane subset of `ℂ`. -/
public lemma differentiableOn_ψI_ofComplex :
    DifferentiableOn ℂ
      (fun z : ℂ => ψI (UpperHalfPlane.ofComplex z))
      UpperHalfPlane.upperHalfPlaneSet := by
  have hH2 :
      DifferentiableOn ℂ
        (fun z : ℂ => H₂ (UpperHalfPlane.ofComplex z))
        UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff (f := H₂)).1 (by
      simpa [H₂_SIF] using!
        (H₂_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⇑H₂_SIF))
  have hH4 :
      DifferentiableOn ℂ
        (fun z : ℂ => H₄ (UpperHalfPlane.ofComplex z))
        UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff (f := H₄)).1 (by
      simpa [H₄_SIF] using!
        (H₄_SIF_MDifferentiable : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⇑H₄_SIF))
  have hΔ :
      DifferentiableOn ℂ
        (fun z : ℂ => Δ (UpperHalfPlane.ofComplex z))
        UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff (f := Δ)).1 (by
      simpa [Delta_apply] using!
        (Delta.holo' : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⇑Delta.toSlashInvariantForm))
  have hnum :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          7 * (H₄ (UpperHalfPlane.ofComplex z)) ^ 5 * (H₂ (UpperHalfPlane.ofComplex z)) ^ 2 +
            7 * (H₄ (UpperHalfPlane.ofComplex z)) ^ 6 * (H₂ (UpperHalfPlane.ofComplex z)) +
              2 * (H₄ (UpperHalfPlane.ofComplex z)) ^ 7)
        UpperHalfPlane.upperHalfPlaneSet := by
    fun_prop
  have hden_ne :
      ∀ z : ℂ, z ∈ UpperHalfPlane.upperHalfPlaneSet →
        (Δ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ) ≠ 0 := by
    intro z hz
    exact pow_ne_zero 2 (Δ_ne_zero (UpperHalfPlane.ofComplex z))
  have hdiv :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (7 * (H₄ (UpperHalfPlane.ofComplex z)) ^ 5 * (H₂ (UpperHalfPlane.ofComplex z)) ^ 2 +
                7 * (H₄ (UpperHalfPlane.ofComplex z)) ^ 6 * (H₂ (UpperHalfPlane.ofComplex z)) +
                  2 * (H₄ (UpperHalfPlane.ofComplex z)) ^ 7) /
            (Δ (UpperHalfPlane.ofComplex z)) ^ 2)
        UpperHalfPlane.upperHalfPlaneSet :=
    hnum.div (hΔ.pow 2) hden_ne
  refine hdiv.congr ?_
  intro z hz
  simpa [mul_assoc, add_assoc, add_left_comm, add_comm] using! (ψI_eq_H (UpperHalfPlane.ofComplex z))

/-- Explicit formula for `ψS` obtained from the `S`-slash action on `ψI`. -/
public lemma ψS_apply (z : ℍ) :
    ψS z =
      -((7 * (H₂ z) ^ 5 * (H₄ z) ^ 2
              + 7 * (H₂ z) ^ 6 * (H₄ z)
              + 2 * (H₂ z) ^ 7) / (Δ z) ^ 2) := by
  have hzSpos : 0 < (-(z : ℂ)⁻¹).im := by
    simpa [inv_neg] using! z.im_inv_neg_coe_pos
  set zS : ℍ := UpperHalfPlane.mk (-(z : ℂ)⁻¹) hzSpos
  have hzS : ModularGroup.S • z = zS := by
    ext
    simpa [zS, div_eq_mul_inv] using! (ModularGroup.coe_S_smul (z := z))
  have hz0 : (z : ℂ) ≠ 0 := ne_zero z
  have hH2 : H₂ zS = -(H₄ z) * (z : ℂ) ^ (2 : ℕ) := by
    have h := congrFun H₂_S_action z
    have hz2 : (z : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hz0
    have h' : H₂ zS * ((z : ℂ) ^ (2 : ℕ))⁻¹ = -(H₄ z) := by
      simpa [hzS, zS, modular_slash_S_apply, zpow_neg, zpow_ofNat] using! h
    exact (mul_inv_eq_iff_eq_mul₀ hz2).mp h'
  have hH4 : H₄ zS = -(H₂ z) * (z : ℂ) ^ (2 : ℕ) := by
    have h := congrFun H₄_S_action z
    have hz2 : (z : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hz0
    have h' : H₄ zS * ((z : ℂ) ^ (2 : ℕ))⁻¹ = -(H₂ z) := by
      simpa [hzS, zS, modular_slash_S_apply, zpow_neg, zpow_ofNat] using! h
    exact (mul_inv_eq_iff_eq_mul₀ hz2).mp h'
  have hΔ : Δ zS = (z : ℂ) ^ (12 : ℕ) * Δ z := by
    simpa [hzS] using! (Δ_S_transform z)
  simp [ψS, modular_slash_S_apply, zS, ψI_eq_H, hΔ, hH2, hH4]
  have hΔ0 : Δ z ≠ 0 := Δ_ne_zero z
  field_simp [hz0, hΔ0]
  ring

lemma ψT_apply (z : ℍ) :
    ψT z =
      (7 * (H₃ z) ^ 5 * (H₂ z) ^ 2
            - 7 * (H₃ z) ^ 6 * (H₂ z)
            + 2 * (H₃ z) ^ 7) / (Δ z) ^ 2 := by
  have hH2 : H₂ ((1 : ℝ) +ᵥ z) = -H₂ z := by
    have := congrFun H₂_T_action z
    simpa [modular_slash_T_apply] using! this
  have hH4 : H₄ ((1 : ℝ) +ᵥ z) = H₃ z := by
    have := congrFun H₄_T_action z
    simpa [modular_slash_T_apply] using! this
  have hΔ : Δ ((1 : ℝ) +ᵥ z) = Δ z := by
    simpa using! (Δ_periodic z)
  simp [ψT, modular_slash_T_apply, ψI_eq_H, hH2, hH4, hΔ, sub_eq_add_neg]

/-- Continuity of `ψI` on the upper half-plane. -/
public lemma continuous_ψI : Continuous ψI := by
  have hH2 : Continuous H₂ := mdifferentiable_H₂.continuous
  have hH4 : Continuous H₄ := mdifferentiable_H₄.continuous
  have hΔ : Continuous Δ := mdifferentiable_Δ.continuous
  have hψ :
      ψI =
        fun z : ℍ =>
          (7 * (H₄ z) ^ 5 * (H₂ z) ^ 2 + 7 * (H₄ z) ^ 6 * (H₂ z) + 2 * (H₄ z) ^ 7) /
            (Δ z) ^ 2 := by
    funext z
    simpa using! (ψI_eq_H z)
  rw [hψ]
  have hnum :
      Continuous fun z : ℍ =>
        (7 * (H₄ z) ^ 5 * (H₂ z) ^ 2 + 7 * (H₄ z) ^ 6 * (H₂ z) + 2 * (H₄ z) ^ 7) := by
    fun_prop
  have hden : Continuous fun z : ℍ => (Δ z) ^ (2 : ℕ) := by fun_prop
  exact hnum.div hden (fun z => pow_ne_zero 2 (Δ_ne_zero z))

/-- Continuity of `ψT` on the upper half-plane. -/
public lemma continuous_ψT : Continuous ψT := by
  have hEq : ψT = fun z : ℍ => ψI ((1 : ℝ) +ᵥ z) := by
    funext z
    simp [ψT, modular_slash_T_apply]
  have htrans : Continuous fun z : ℍ => ((1 : ℝ) +ᵥ z : ℍ) := by
    let g : ℍ → ℍ :=
      fun z => ⟨(1 : ℂ) + (z : ℂ), by simpa [Complex.add_im] using! z.2⟩
    have hg : Continuous g := by
      fun_prop
    assumption
  simpa [hEq] using! continuous_ψI.comp htrans

/-- The function `ψI` is periodic with period `2` in the `T`-direction. -/
public lemma ψI_periodic_two (z : ℍ) :
    ψI (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z)) : ℍ) = ψI z := by
  -- Use `ψI_eq_H` and the `T`-action on `H₂,H₃,H₄` (hence `T^2`-periodicity).
  have hH2_T : H₂ ((1 : ℝ) +ᵥ z) = -H₂ z := by
    have h := congrFun (H₂_T_action : (H₂ ∣[(2 : ℤ)] T) = -H₂) z
    simpa [modular_slash_T_apply] using! h
  have hH2_T2 : H₂ (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z)) : ℍ) = H₂ z := by
    have h := congrFun (H₂_T_action : (H₂ ∣[(2 : ℤ)] T) = -H₂) ((1 : ℝ) +ᵥ z)
    -- `H₂(z+2) = -H₂(z+1) = -(-H₂ z) = H₂ z`.
    simpa [modular_slash_T_apply, hH2_T, neg_neg] using! h
  have hH4_T : H₄ ((1 : ℝ) +ᵥ z) = H₃ z := by
    have h := congrFun (H₄_T_action : (H₄ ∣[(2 : ℤ)] T) = H₃) z
    simpa [modular_slash_T_apply] using! h
  have hH3_T : H₃ ((1 : ℝ) +ᵥ z) = H₄ z := by
    have h := congrFun (H₃_T_action : (H₃ ∣[(2 : ℤ)] T) = H₄) z
    simpa [modular_slash_T_apply] using! h
  have hH4_T2 : H₄ (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z)) : ℍ) = H₄ z := by
    have h1 : H₄ (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z)) : ℍ) = H₃ ((1 : ℝ) +ᵥ z) := by
      have h := congrFun (H₄_T_action : (H₄ ∣[(2 : ℤ)] T) = H₃) ((1 : ℝ) +ᵥ z)
      simpa [modular_slash_T_apply] using! h
    -- `H₃(z+1) = H₄(z)`.
    exact h1.trans (by simpa using! hH3_T)
  have hΔ_T : Δ ((1 : ℝ) +ᵥ z) = Δ z := Δ_periodic z
  have hΔ_T2 : Δ (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z)) : ℍ) = Δ z := by
    -- `Δ(z+2) = Δ(z+1) = Δ(z)`.
    simpa [hΔ_T] using! (Δ_periodic ((1 : ℝ) +ᵥ z))
  -- Now finish by rewriting both sides with `ψI_eq_H`.
  rw [ψI_eq_H (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z)) : ℍ), ψI_eq_H z]
  simp [hH2_T2, hH4_T2, hΔ_T2]

/-- Main relation: `ψS + ψT = ψI`. -/
public theorem ψS_add_ψT_eq_ψI : (fun z : ℍ => ψS z + ψT z) = ψI := by
  /- Proof sketch:
  Unfold `ψI` and the slash actions defining `ψS,ψT`.
  Use:
  - the theta transformation laws under `S,T` (available in `JacobiTheta`),
  - Jacobi's identity, to obtain the explicit expressions for `ψS,ψT`,
  then check their sum equals `ψI`. -/
  ext z
  simp [ψS_apply z, ψT_apply z, ψI_eq_H z, sub_eq_add_neg]
  have hΔz : (Δ z) ^ 2 ≠ 0 := pow_ne_zero 2 (Δ_ne_zero z)
  field_simp [hΔz]
  have hJac : H₃ z = H₂ z + H₄ z := by
    simpa [Pi.add_apply] using! (congrFun jacobi_identity z).symm
  simp [hJac]
  ring

/-- Shift relation for `ψS`: translating by `1` negates `ψS`. -/
public lemma ψS_add_one (z : ℍ) : ψS (((1 : ℝ) +ᵥ z) : ℍ) = -ψS z := by
  -- Combine `ψS + ψT = ψI` with `ψT(z) = ψI(z+1)` and `ψI(z+2) = ψI(z)`.
  have hsum0 : ψS z + ψT z = ψI z := congrFun ψS_add_ψT_eq_ψI z
  have hS0 : ψS z = ψI z - ψT z := eq_sub_of_add_eq hsum0
  have hT0 : ψT z = ψI (((1 : ℝ) +ᵥ z) : ℍ) := by
    simp [ψT, modular_slash_T_apply]
  have hS0' : ψS z = ψI z - ψI (((1 : ℝ) +ᵥ z) : ℍ) := by simpa [hT0] using! hS0
  have hsum1 :
      ψS (((1 : ℝ) +ᵥ z) : ℍ) + ψT (((1 : ℝ) +ᵥ z) : ℍ) = ψI (((1 : ℝ) +ᵥ z) : ℍ) :=
    congrFun ψS_add_ψT_eq_ψI (((1 : ℝ) +ᵥ z) : ℍ)
  have hS1 :
      ψS (((1 : ℝ) +ᵥ z) : ℍ) = ψI (((1 : ℝ) +ᵥ z) : ℍ) - ψT (((1 : ℝ) +ᵥ z) : ℍ) :=
    eq_sub_of_add_eq hsum1
  have hT1 :
      ψT (((1 : ℝ) +ᵥ z) : ℍ) = ψI (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z)) : ℍ) := by
    simp [ψT, modular_slash_T_apply]
  have hper : ψI (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z)) : ℍ) = ψI z := ψI_periodic_two (z := z)
  simp_all

/-- The `S`-slash action sends `ψT` to `-ψT`. -/
public theorem ψT_S_action : (ψT ∣[-10] S) = -ψT := by
  /- Proof sketch:
  Starting from `ψS_add_ψT_eq_ψI`, apply `|_{-10} S` to both sides and use:
  - `ψI | S = ψS` by definition,
  - `ψS | S = ψI` (since `S^2 = -I` and weight is even),
  to isolate `ψT | S` and conclude it equals `-ψT`. -/
  have hrel : ψS + ψT = ψI := by
    simpa [Pi.add_apply] using! ψS_add_ψT_eq_ψI
  have hsl : (ψS + ψT) ∣[-10] S = ψI ∣[-10] S :=
    congrArg (fun f : ℍ → ℂ => f ∣[-10] S) hrel
  have hSS : (ψS ∣[-10] S) = ψI := by
    have hEven : Even (-10 : ℤ) := by decide
    calc
      (ψS ∣[-10] S) = ψI ∣[-10] (S * S) := by
        simpa [ψS] using! (SlashAction.slash_mul (-10 : ℤ) S S ψI).symm
      _ = ψI ∣[-10] (-1 : SL(2, ℤ)) := by simp [ModularGroup.modular_S_sq]
      _ = ψI ∣[-10] (1 : SL(2, ℤ)) := by
        simpa using! (ModularForm.slash_neg_one' (k := (-10 : ℤ)) ψI hEven)
      _ = ψI := by simp
  have hsl' : (ψS ∣[-10] S) + (ψT ∣[-10] S) = ψS := by
    simpa [add_slash, ψS] using! hsl
  have h1 : ψI + (ψT ∣[-10] S) = ψS := by simpa [hSS] using! hsl'
  have hψS : ψS = ψI - ψT :=
    eq_sub_of_add_eq hrel
  calc
    (ψT ∣[-10] S) = ψS - ψI :=
      Eq.symm (sub_eq_of_eq_add' (id (Eq.symm h1)))
    _ = -ψT := by
      simp [hψS, sub_eq_add_neg, add_left_comm, add_comm]

end

open Filter
open scoped Topology

/-- `ψS` tends to `0` at imaginary infinity. -/
public lemma tendsto_ψS_atImInfty : Tendsto ψS UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
  -- Use the factorization of `ψS` in terms of `H₂,H₃,H₄`.
  have hEq : ψS = fun z : ℍ =>
      -((256 : ℂ) ^ (2 : ℕ)) *
        ((7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3) /
          ((H₃ z) ^ 4 * (H₄ z) ^ 4)) := by
    funext z
    have hΔ : (Δ z : ℂ) = ((H₂ z) * (H₃ z) * (H₄ z)) ^ 2 / (256 : ℂ) := by
      simpa [Delta_apply] using! (Delta_eq_H₂_H₃_H₄ z)
    have hΔ0 : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    have hH2 : H₂ z ≠ 0 := by
      exact H₂_ne_zero z
    have hH3 : H₃ z ≠ 0 := by
      exact H₃_ne_zero z
    have hH4 : H₄ z ≠ 0 := by
      exact H₄_ne_zero z
    -- Turn the `Δ` denominator into `H₃^4 H₄^4` using Jacobi's identity.
    rw [ψS_apply z, hΔ]
    field_simp [hH2, hH3, hH4]
  -- Limits of theta modular forms at `i∞`.
  have hH2 : Tendsto H₂ UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := H₂_tendsto_atImInfty
  have hH3 : Tendsto H₃ UpperHalfPlane.atImInfty (𝓝 (1 : ℂ)) := H₃_tendsto_atImInfty
  have hH4 : Tendsto H₄ UpperHalfPlane.atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
  have hnum :
      Tendsto
        (fun z : ℍ =>
          7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3)
        UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
    have hH4sq :
        Tendsto (fun z : ℍ => (H₄ z) ^ (2 : ℕ)) UpperHalfPlane.atImInfty (𝓝 (1 : ℂ)) := by
      simpa using! (hH4.pow 2)
    have hH2sq :
        Tendsto (fun z : ℍ => (H₂ z) ^ (2 : ℕ)) UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
      simpa using! (hH2.pow 2)
    have hH2cu :
        Tendsto (fun z : ℍ => (H₂ z) ^ (3 : ℕ)) UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
      simpa using! (hH2.pow 3)
    have hterm1 :
        Tendsto (fun z : ℍ => (7 : ℂ) * (H₂ z) * (H₄ z) ^ (2 : ℕ))
          UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
      simpa [mul_assoc] using! (tendsto_const_nhds.mul (hH2.mul hH4sq))
    have hterm2 :
        Tendsto (fun z : ℍ => (7 : ℂ) * (H₂ z) ^ (2 : ℕ) * (H₄ z))
          UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
      simpa [mul_assoc] using! (tendsto_const_nhds.mul (hH2sq.mul hH4))
    have hterm3 :
        Tendsto (fun z : ℍ => (2 : ℂ) * (H₂ z) ^ (3 : ℕ))
          UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
      simpa [mul_assoc] using! (tendsto_const_nhds.mul hH2cu)
    simpa [mul_assoc, add_assoc, add_left_comm, add_comm] using! (hterm1.add (hterm2.add hterm3))
  have hden :
      Tendsto (fun z : ℍ => (H₃ z) ^ (4 : ℕ) * (H₄ z) ^ (4 : ℕ))
        UpperHalfPlane.atImInfty (𝓝 (1 : ℂ)) := by
    simpa [mul_assoc] using! (hH3.pow 4).mul (hH4.pow 4)
  have hquo :
      Tendsto
        (fun z : ℍ =>
          (7 * (H₂ z) * (H₄ z) ^ 2 + 7 * (H₂ z) ^ 2 * (H₄ z) + 2 * (H₂ z) ^ 3) /
            ((H₃ z) ^ 4 * (H₄ z) ^ 4))
        UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
    simpa using! (hnum.div hden (by norm_num))
  have hconst :
      Tendsto (fun _ : ℍ => (-((256 : ℂ) ^ (2 : ℕ)) : ℂ))
        UpperHalfPlane.atImInfty (𝓝 (-((256 : ℂ) ^ (2 : ℕ)) : ℂ)) :=
    tendsto_const_nhds
  simpa [hEq, mul_assoc] using! (hconst.mul hquo)

end SpherePacking.Dim24
