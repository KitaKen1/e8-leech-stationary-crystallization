-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgInnerMoments24Final


/-!
# Inner-product moments for `sphereAvg24`

This file derives formulas for the moments of `x ↦ ⟪x, v⟫` on `Ω₂₄` for an arbitrary vector `v`,
reducing to the unit-vector case proved in
`SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgInnerMoments24Final`.

## Main statements
* `SphereAvgMoments24.sphereAvg24_inner_pow_two`
* `SphereAvgMoments24.sphereAvg24_inner_pow_four`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Uniqueness.BS81.Thm14

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SphereAvgMoments24

private lemma sphereAvg24_const_mul (c : ℝ) (f : ℝ²⁴ → ℝ) :
    sphereAvg24 (fun x => c * f x) = c * sphereAvg24 f :=
  sphereAvg24_smul c f

private lemma sphereAvg24_inner_pow_of_norm (v : ℝ²⁴) (k : ℕ) (c : ℝ) (hk : k ≠ 0)
    (hunit : ∀ u : ℝ²⁴, ‖u‖ = (1 : ℝ) →
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ k) = c) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, v⟫ : ℝ) ^ k) = c * ‖v‖ ^ k := by
  by_cases hv : v = 0
  · subst hv
    simp [hk, sphereAvg24_const]
  · set r : ℝ := ‖v‖
    have hr : r ≠ (0 : ℝ) := by
      simp [r, hv]
    let u : ℝ²⁴ := r⁻¹ • v
    have hu : ‖u‖ = (1 : ℝ) := by
      simp [u, r, norm_smul, hr]
    have hvu : v = r • u := by
      simp [u, smul_smul, mul_inv_cancel₀ hr]
    have hcongr :
        (fun x : ℝ²⁴ => (⟪x, v⟫ : ℝ) ^ k) =
          fun x : ℝ²⁴ => (r ^ k) * (⟪x, u⟫ : ℝ) ^ k := by
      funext x
      simp [hvu, real_inner_smul_right, mul_pow]
    calc
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, v⟫ : ℝ) ^ k) =
          sphereAvg24 (fun x : ℝ²⁴ => (r ^ k) * (⟪x, u⟫ : ℝ) ^ k) := by
            simp [hcongr]
      _ = (r ^ k) * sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ k) := by
          simpa [mul_assoc] using!
            sphereAvg24_const_mul (r ^ k) (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ k)
      _ = (r ^ k) * c := by simp [hunit u hu]
      _ = c * ‖v‖ ^ k := by simp [mul_comm, r]

/-- The second moment satisfies
`sphereAvg24 (x ↦ ⟪x,v⟫^2) = (1/24) * ‖v‖^2`. -/
public theorem sphereAvg24_inner_pow_two (v : ℝ²⁴) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, v⟫ : ℝ) ^ 2) = (1 / 24 : ℝ) * ‖v‖ ^ 2 := by
  simpa using!
    (sphereAvg24_inner_pow_of_norm (v := v) (k := 2) (c := (1 / 24 : ℝ)) (hk := by simp)
      (hunit := fun u hu =>
        Uniqueness.BS81.Thm14.sphereAvg24_inner_pow_two_of_norm_one (u := u) hu))

/-- The fourth moment satisfies
`sphereAvg24 (x ↦ ⟪x,v⟫^4) = (1/208) * ‖v‖^4`. -/
public theorem sphereAvg24_inner_pow_four (v : ℝ²⁴) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, v⟫ : ℝ) ^ 4) = (1 / 208 : ℝ) * ‖v‖ ^ 4 := by
  simpa using!
    (sphereAvg24_inner_pow_of_norm (v := v) (k := 4) (c := (1 / 208 : ℝ)) (hk := by simp)
      (hunit := fun u hu =>
        Uniqueness.BS81.Thm14.sphereAvg24_inner_pow_four_of_norm_one (u := u) hu))


end SphereAvgMoments24

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16
