-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Aux03.Transforms
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Aux03.Integrability


/-!
# Period integrals of `varphi₁` on horizontal lines

For the even special values `u = 0,2,4`, `expU u` is `1`-periodic, so we can move the
period integral of `varphi₁` from height `1` to an arbitrarily large height `m` using
Cauchy-Goursat on a rectangle. Combined with the `atImInfty` limit of
`varphi₁(z) * exp(2π i z)`, this evaluates the integrals for `u = 2,4`.
-/

open scoped Manifold
open Complex Real

namespace SpherePacking.Dim24

noncomputable section


namespace SpecialValuesAux

open scoped Interval Real Topology
open Filter Complex MeasureTheory Set intervalIntegral UpperHalfPlane

lemma varphi₁'_add_one (z : ℂ) (hz : 0 < z.im) : varphi₁' (z + 1) = varphi₁' z := by
  let zH : ℍ := ⟨z, hz⟩
  have hz1 : 0 < (z + 1).im := by simpa using! hz
  let z1H : ℍ := ⟨z + 1, hz1⟩
  have hvadd : ((1 : ℝ) +ᵥ zH : ℍ) = z1H := by
    ext1
    simp [zH, z1H, add_comm]
  calc
    varphi₁' (z + 1) = varphi₁ z1H := by
      -- Use the `im>0` branch of the total extension.
      simpa [z1H] using! (varphi₁'_def (z := z + 1) hz1)
    _ = varphi₁ ((1 : ℝ) +ᵥ zH) := by simp [hvadd]
    _ = varphi₁ zH := varphi₁_periodic zH
    _ = varphi₁' z := by simp [varphi₁', hz, zH]

lemma continuousOn_varphi₁' : ContinuousOn varphi₁' {z : ℂ | 0 < z.im} := by
  -- Continuity of `varphi₁` on `ℍ` and of the subtype embedding `z ↦ ⟨z,hz⟩`.
  rw [continuousOn_iff_continuous_restrict]
  let h : {z : ℂ | 0 < z.im} → ℍ := fun z => ⟨z, z.property⟩
  have hcont_h : Continuous h := by
    -- `Subtype.val` is continuous and the proof component is bundled.
    simpa [h] using! Continuous.upperHalfPlaneMk continuous_subtype_val (fun z => z.property)
  have hcont : Continuous fun z : {z : ℂ | 0 < z.im} => varphi₁ (h z) :=
    (continuous_varphi₁.comp hcont_h)
  -- Identify the restricted function with `varphi₁'`.
  refine hcont.congr ?_
  intro z
  have hz : 0 < (z : ℂ).im := z.property
  simp [varphi₁', hz, h]

public lemma differentiableOn_varphi₁OfComplex :
    DifferentiableOn ℂ (fun z : ℂ => varphi₁ (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} := by
  -- This follows the pattern used earlier for `varphi`: build differentiability for each block.
  let s : Set ℂ := {z : ℂ | 0 < z.im}
  have hE2 : DifferentiableOn ℂ (E₂ ∘ UpperHalfPlane.ofComplex) s :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₂_holo')
  have hE4 : DifferentiableOn ℂ ((E₄ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) s :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₄.holo')
  have hE6 : DifferentiableOn ℂ ((E₆ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) s :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₆.holo')
  have hΔ : DifferentiableOn ℂ (Δ ∘ UpperHalfPlane.ofComplex) s := by
    simpa [Delta_apply] using!
      (UpperHalfPlane.mdifferentiable_iff.mp
        (Delta.holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => Delta z)))
  -- Abbreviations.
  let E2c : ℂ → ℂ := fun z => E₂ (UpperHalfPlane.ofComplex z)
  let E4c : ℂ → ℂ := fun z => E₄ (UpperHalfPlane.ofComplex z)
  let E6c : ℂ → ℂ := fun z => E₆ (UpperHalfPlane.ofComplex z)
  let Δc : ℂ → ℂ := fun z => Δ (UpperHalfPlane.ofComplex z)
  have hE2c : DifferentiableOn ℂ E2c s := by simpa [E2c, Function.comp_def] using! hE2
  have hE4c : DifferentiableOn ℂ E4c s := by simpa [E4c, Function.comp_def] using! hE4
  have hE6c : DifferentiableOn ℂ E6c s := by simpa [E6c, Function.comp_def] using! hE6
  have hΔc : DifferentiableOn ℂ Δc s := by simpa [Δc, Function.comp_def] using! hΔ
  have hΔ2 : DifferentiableOn ℂ (fun z : ℂ => (Δc z) ^ (2 : ℕ)) s := hΔc.pow 2
  have hΔ2_ne : ∀ z : ℂ, z ∈ s → (Δc z) ^ (2 : ℕ) ≠ 0 := by
    intro z hz
    have hz' : 0 < z.im := hz
    have hof : UpperHalfPlane.ofComplex z = ⟨z, hz'⟩ :=
      UpperHalfPlane.ofComplex_apply_of_im_pos hz'
    have hΔ0 : Δ (⟨z, hz'⟩ : ℍ) ≠ 0 := Δ_ne_zero (⟨z, hz'⟩ : ℍ)
    simpa [Δc, hof] using! (pow_ne_zero 2 hΔ0)
  -- Build the numerator of `varphi₁ ∘ ofComplex`.
  have hE4_2 : DifferentiableOn ℂ (fun z : ℂ => (E4c z) ^ (2 : ℕ)) s := hE4c.pow 2
  have hE4_3 : DifferentiableOn ℂ (fun z : ℂ => (E4c z) ^ (3 : ℕ)) s := hE4c.pow 3
  have hE6_2 : DifferentiableOn ℂ (fun z : ℂ => (E6c z) ^ (2 : ℕ)) s := hE6c.pow 2
  have hnum1 : DifferentiableOn ℂ (fun z : ℂ => (E6c z) * (E4c z) ^ (2 : ℕ)) s :=
    hE6c.mul hE4_2
  have hnum2 :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          E2c z * ((-49 : ℂ) * (E4c z) ^ (3 : ℕ) + (25 : ℂ) * (E6c z) ^ (2 : ℕ))) s := by
    have hpoly :
        DifferentiableOn ℂ
          (fun z : ℂ => (-49 : ℂ) * (E4c z) ^ (3 : ℕ) + (25 : ℂ) * (E6c z) ^ (2 : ℕ)) s :=
      (hE4_3.const_mul (-49 : ℂ)).add (hE6_2.const_mul (25 : ℂ))
    exact hE2c.mul hpoly
  have hdiv1 :
      DifferentiableOn ℂ
        (fun z : ℂ => ((E6c z) * (E4c z) ^ (2 : ℕ)) / (Δc z) ^ (2 : ℕ)) s := by
    simpa [div_eq_mul_inv] using! (hnum1.mul (hΔ2.inv hΔ2_ne))
  have hdiv2 :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (E2c z * ((-49 : ℂ) * (E4c z) ^ (3 : ℕ) + (25 : ℂ) * (E6c z) ^ (2 : ℕ))) /
            (Δc z) ^ (2 : ℕ)) s := by
    simpa [div_eq_mul_inv] using! (hnum2.mul (hΔ2.inv hΔ2_ne))
  have hterm1 :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          ((- (6 * Complex.I) / π) * (48 : ℂ)) *
            (((E6c z) * (E4c z) ^ (2 : ℕ)) / (Δc z) ^ (2 : ℕ))) s := by
    -- Scalar multiplication preserves differentiability.
    simpa [mul_assoc, mul_left_comm, mul_comm] using!
      (hdiv1.const_mul ((- (6 * Complex.I) / π) * (48 : ℂ)))
  have hterm2 :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          ((12 * Complex.I) / π) *
              ((E2c z * ((-49 : ℂ) * (E4c z) ^ (3 : ℕ) + (25 : ℂ) * (E6c z) ^ (2 : ℕ))) /
                (Δc z) ^ (2 : ℕ))) s := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using!
      (hdiv2.const_mul ((12 * Complex.I) / π))
  -- Assemble `varphi₁` (in a factorized form matching `hterm1/hterm2`).
  have hcomb :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          ((- (6 * Complex.I) / π) * (48 : ℂ)) *
              (((E6c z) * (E4c z) ^ (2 : ℕ)) / (Δc z) ^ (2 : ℕ)) -
            ((12 * Complex.I) / π) *
              ((E2c z * ((-49 : ℂ) * (E4c z) ^ (3 : ℕ) + (25 : ℂ) * (E6c z) ^ (2 : ℕ))) /
                (Δc z) ^ (2 : ℕ))) s :=
    hterm1.sub hterm2
  -- `hcomb` is definitionally `varphi₁ ∘ ofComplex`.
  simpa
      [Dim24.varphi₁, E2c, E4c, E6c, Δc, Function.comp_def, mul_assoc, mul_left_comm, mul_comm,
        mul_div_assoc] using! hcomb

lemma differentiableOn_varphi₁' :
    DifferentiableOn ℂ varphi₁' {z : ℂ | 0 < z.im} := by
  -- On `{Im>0}`, `varphi₁'` agrees locally with `varphi₁ ∘ ofComplex`.
  intro z hz
  have hAt :
      DifferentiableAt ℂ (fun w : ℂ => varphi₁ (UpperHalfPlane.ofComplex w)) z :=
    (differentiableOn_varphi₁OfComplex z hz).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds hz)
  have hEq :
      (fun w : ℂ => varphi₁' w) =ᶠ[𝓝 z]
        fun w : ℂ => varphi₁ (UpperHalfPlane.ofComplex w) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    simp [varphi₁', hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  exact (hAt.congr_of_eventuallyEq hEq).differentiableWithinAt

/-- Rectangle identity: for even `u`, the period integral of `varphi₁' * expU u` at height `1`
agrees with the corresponding integral at height `m ≥ 1`. -/
public lemma strip_identity_varphi₁_mul_expU (u : ℝ) (hu : expU u 1 = 1) (m : ℝ) (hm : 1 ≤ m) :
    (∫ x : ℝ in (0 : ℝ)..1,
        varphi₁' (x + (1 : ℝ) * Complex.I) * expU u (x + (1 : ℝ) * Complex.I)) =
      ∫ x : ℝ in (0 : ℝ)..1,
        varphi₁' (x + m * Complex.I) * expU u (x + m * Complex.I) := by
  -- Apply Cauchy-Goursat on the rectangle and cancel vertical sides by periodicity.
  let g : ℂ → ℂ := fun z => varphi₁' z * expU u z
  have hC : ContinuousOn g (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (1 : ℝ) m) := by
    have hvar : ContinuousOn varphi₁' {z : ℂ | 0 < z.im} := continuousOn_varphi₁'
    have hexp : Continuous fun z : ℂ => expU u z := by
      simpa using! (continuous_expU (u := u))
    have hexpOn :
        ContinuousOn (fun z : ℂ => expU u z) (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (1 : ℝ) m) :=
      hexp.continuousOn
    have hvarOn : ContinuousOn varphi₁' (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (1 : ℝ) m) := by
      refine hvar.mono ?_
      intro z hz
      have hzIm : z.im ∈ Set.uIcc (1 : ℝ) m := (mem_reProdIm.1 hz).2
      have hzIm1 : (1 : ℝ) ≤ z.im := by
        have : z.im ∈ Set.Icc (1 : ℝ) m := by simpa [Set.uIcc_of_le hm] using! hzIm
        exact this.1
      exact lt_of_lt_of_le (by norm_num) hzIm1
    simpa [g] using! hvarOn.mul hexpOn
  have hD : DifferentiableOn ℂ g (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (1 : ℝ) m) := by
    have hvar : DifferentiableOn ℂ varphi₁' {z : ℂ | 0 < z.im} := differentiableOn_varphi₁'
    have hexp : Differentiable ℂ (fun z : ℂ => expU u z) := by
      intro z
      simpa using! (differentiableAt_expU (u := u) (z := z))
    have hexpOn :
        DifferentiableOn ℂ (fun z : ℂ => expU u z)
          (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (1 : ℝ) m) :=
      hexp.differentiableOn
    have hvarOn :
        DifferentiableOn ℂ varphi₁' (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (1 : ℝ) m) := by
      refine hvar.mono ?_
      intro z hz
      have hzIm : z.im ∈ Set.Ioo (1 : ℝ) m := (mem_reProdIm.1 hz).2
      exact lt_trans (by norm_num) hzIm.1
    simpa [g] using! hvarOn.mul hexpOn
  have hrect :
      (∫ x : ℝ in (0 : ℝ)..1, g (x + (1 : ℝ) * Complex.I)) -
          (∫ x : ℝ in (0 : ℝ)..1, g (x + m * Complex.I)) +
          Complex.I • (∫ y : ℝ in (1 : ℝ)..m, g ((1 : ℝ) + y * Complex.I)) -
            Complex.I • (∫ y : ℝ in (1 : ℝ)..m, g ((0 : ℝ) + y * Complex.I)) = 0 := by
    simpa [g] using!
      (Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        (f := g) (z := (Complex.I : ℂ)) (w := (1 : ℂ) + m * Complex.I) (Hc := by
          simpa using! hC) (Hd := by
            simpa [hm] using! hD))
  have hVert :
      ∫ y : ℝ in (1 : ℝ)..m, g ((1 : ℝ) + y * Complex.I) =
        ∫ y : ℝ in (1 : ℝ)..m, g ((0 : ℝ) + y * Complex.I) := by
    refine intervalIntegral.integral_congr (μ := volume) ?_
    intro y hy
    have hy1 : (1 : ℝ) ≤ y := by
      have : y ∈ Set.Icc (1 : ℝ) m := by simpa [Set.uIcc_of_le hm] using! hy
      exact this.1
    have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy1
    have hyIm : 0 < (((y : ℂ) * Complex.I) : ℂ).im := by simpa [mul_assoc] using! hy0
    have hperφ : varphi₁' (((y : ℂ) * Complex.I) + 1) = varphi₁' ((y : ℂ) * Complex.I) :=
      varphi₁'_add_one (z := (y : ℂ) * Complex.I) hyIm
    have hperExp : expU u (((y : ℂ) * Complex.I) + 1) = expU u ((y : ℂ) * Complex.I) := by
      simpa [add_assoc] using! (expU_add_one (u := u) hu (z := (y : ℂ) * Complex.I))
    -- Reassociate to match `g`.
    have hzadd : (1 : ℂ) + (y : ℂ) * Complex.I = (y : ℂ) * Complex.I + 1 := by ring
    have hzadd0 : (0 : ℂ) + (y : ℂ) * Complex.I = (y : ℂ) * Complex.I := by ring
    simp [g, hzadd, hzadd0, hperφ, hperExp]
  grind only

end SpecialValuesAux

end

end SpherePacking.Dim24
