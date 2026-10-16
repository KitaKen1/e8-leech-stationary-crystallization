-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions


/-!
# Rectangle-domain regularity for `ψS'`

We prove differentiability for `ψS` on the upper half-plane (as a function of `z : ℂ`) and then
deduce continuity of the total extension `ψS'` on the closed rectangle
`Set.uIcc 0 1 ×ℂ Ici 1`.

These results are used both in the special-value computations for `bProfile` and in the
Laplace-profile analysis.

## Main statements
* `SpecialValuesAux.differentiableOn_ψS_ofComplex`
* `SpecialValuesAux.differentiableAt_ψS'_of_im_pos`
* `SpecialValuesAux.continuousOn_ψS'_rect`
-/
noncomputable section

namespace SpherePacking.Dim24.SpecialValuesAux

open Set
open scoped Topology

/-- Differentiability of `z ↦ ψS (ofComplex z)` on the upper half-plane, viewed as a subset of `ℂ`.
-/
public lemma differentiableOn_ψS_ofComplex :
    DifferentiableOn ℂ (fun z : ℂ => ψS (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  let zH : ℂ → UpperHalfPlane := UpperHalfPlane.ofComplex
  let H2c : ℂ → ℂ := fun z => H₂ (zH z)
  let H3c : ℂ → ℂ := fun z => H₃ (zH z)
  let H4c : ℂ → ℂ := fun z => H₄ (zH z)
  have hH2 : DifferentiableOn ℂ H2c U := by
    simpa [H2c, zH, U] using!
      (UpperHalfPlane.mdifferentiable_iff (f := H₂)).1 mdifferentiable_H₂
  have hH3 : DifferentiableOn ℂ H3c U := by
    simpa [H3c, zH, U] using!
      (UpperHalfPlane.mdifferentiable_iff (f := H₃)).1 mdifferentiable_H₃
  have hH4 : DifferentiableOn ℂ H4c U := by
    simpa [H4c, zH, U] using!
      (UpperHalfPlane.mdifferentiable_iff (f := H₄)).1 mdifferentiable_H₄
  have hden : ∀ z : ℂ, z ∈ U → (H3c z) ^ (4 : ℕ) * (H4c z) ^ (4 : ℕ) ≠ 0 := by
    intro z _
    exact mul_ne_zero (pow_ne_zero 4 (H₃_ne_zero (zH z))) (pow_ne_zero 4 (H₄_ne_zero (zH z)))
  have hnum :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          7 * (H2c z) * (H4c z) ^ 2 + 7 * (H2c z) ^ 2 * (H4c z) + 2 * (H2c z) ^ 3)
        U := by
    have hterm1 :
        DifferentiableOn ℂ
          (fun z : ℂ => (7 : ℂ) * (H2c z) * (H4c z) ^ 2) U := by
      simpa [mul_assoc] using! (DifferentiableOn.const_mul (hH2.mul (hH4.pow 2)) (7 : ℂ))
    have hterm2 :
        DifferentiableOn ℂ
          (fun z : ℂ => (7 : ℂ) * (H2c z) ^ 2 * (H4c z)) U := by
      simpa [mul_assoc] using! (DifferentiableOn.const_mul ((hH2.pow 2).mul hH4) (7 : ℂ))
    have hterm3 :
        DifferentiableOn ℂ
          (fun z : ℂ => (2 : ℂ) * (H2c z) ^ 3) U := by
      simpa [mul_assoc] using! (DifferentiableOn.const_mul (hH2.pow 3) (2 : ℂ))
    simpa [mul_assoc, add_assoc] using! (hterm1.add (hterm2.add hterm3))
  have hdenFun :
      DifferentiableOn ℂ
        (fun z : ℂ => (H3c z) ^ 4 * (H4c z) ^ 4) U := (hH3.pow 4).mul (hH4.pow 4)
  have hdiv := hnum.div hdenFun hden
  have hExpr :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          -((256 : ℂ) ^ (2 : ℕ)) *
            ((7 * (H2c z) * (H4c z) ^ 2 + 7 * (H2c z) ^ 2 * (H4c z) + 2 * (H2c z) ^ 3) /
              ((H3c z) ^ 4 * (H4c z) ^ 4)))
        U := by
    simpa [mul_assoc] using! (DifferentiableOn.const_mul hdiv (-((256 : ℂ) ^ (2 : ℕ))))
  refine DifferentiableOn.congr hExpr ?_
  intro z hz
  simpa [U, H2c, H3c, H4c, zH, mul_assoc, div_eq_mul_inv, mul_left_comm, mul_comm] using!
    (PsiRewrites.ψS_apply_eq_factor (zH z))

/-- Differentiability of the total extension `ψS'` at points with positive imaginary part. -/
public lemma differentiableAt_ψS'_of_im_pos (z : ℂ) (hz : 0 < z.im) : DifferentiableAt ℂ ψS' z := by
  have hAt : DifferentiableAt ℂ (fun w : ℂ => ψS (UpperHalfPlane.ofComplex w)) z :=
    (differentiableOn_ψS_ofComplex z hz).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  have hEq :
      (fun w : ℂ => ψS' w) =ᶠ[𝓝 z] fun w : ℂ => ψS (UpperHalfPlane.ofComplex w) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    have hw' : 0 < w.im := by
      simpa [UpperHalfPlane.upperHalfPlaneSet] using! hw
    simp [ψS', hw', UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  exact hAt.congr_of_eventuallyEq hEq

/-! ### Continuity on the closed rectangle -/

/-- Continuity of `ψS'` on the closed rectangle `Set.uIcc 0 1 ×ℂ Ici 1`. -/
public lemma continuousOn_ψS'_rect :
    ContinuousOn ψS' (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) := by
  have hcont0 :
      ContinuousOn (fun z : ℂ => ψS (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
    differentiableOn_ψS_ofComplex.continuousOn
  have hsubset : Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ)) ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have hzIm : z.im ∈ Ici (1 : ℝ) := (Complex.mem_reProdIm.1 hz).2
    exact lt_of_lt_of_le (by simp : (0 : ℝ) < (1 : ℝ)) hzIm
  refine (hcont0.mono hsubset).congr ?_
  intro z hz
  have hzpos : 0 < z.im := hsubset (a := z) hz
  have hof : UpperHalfPlane.ofComplex z = UpperHalfPlane.mk z hzpos :=
    UpperHalfPlane.ofComplex_apply_of_im_pos hzpos
  simp [ψS', hzpos, hof]

end SpherePacking.Dim24.SpecialValuesAux

end
