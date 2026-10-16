-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgMoments
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgFourthMoment24Final

/-!
# Inner-product moments for `sphereAvg24`

This file packages the second and fourth moments of `x ↦ ⟪x,u⟫` on the unit sphere `Ω₂₄`, in a form
convenient for deriving the BS81 distance distribution (equation (11)).

## Main statements
* `sphereAvg24_inner_pow_two_of_norm_one`
* `sphereAvg24_inner_pow_four_of_norm_one`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Existence of an isometry sending a unit vector to `e₀`

We use the orthonormal-basis extension lemma from
`SphereAvgFourthMoment24Final` (`exists_linearIsometryEquiv_map_unit_to_basis0`).
-/

lemma coord0_of_map_unit_to_e0
    {u : ℝ²⁴}
    {E : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴} (hEu : E u = (EuclideanSpace.single (0 : Fin 24) (1 : ℝ) : ℝ²⁴)) :
    ∀ x : ℝ²⁴, (E x) (0 : Fin 24) = (⟪x, u⟫ : ℝ) := by
  let bstd : OrthonormalBasis (Fin 24) ℝ ℝ²⁴ := EuclideanSpace.basisFun (Fin 24) ℝ
  let e0 : ℝ²⁴ := bstd (0 : Fin 24)
  have hEu0 : E u = e0 := by
    simpa [e0, bstd] using! hEu
  intro x
  have hx0 : (E x) (0 : Fin 24) = (⟪E x, e0⟫ : ℝ) := by
    simpa [e0, bstd] using!
      (EuclideanSpace.inner_basisFun_real (ι := Fin 24) (x := (E x)) (i := (0 : Fin 24))).symm
  have hx1 : (⟪E x, e0⟫ : ℝ) = (⟪E x, E u⟫ : ℝ) := by
    simp [hEu0]
  have hx2 : (⟪E x, E u⟫ : ℝ) = (⟪x, u⟫ : ℝ) :=
    LinearIsometryEquiv.inner_map_map E x u
  exact hx0.trans (hx1.trans hx2)

/-!
## Second and fourth inner moments
-/

/-- The second moment of `x ↦ ⟪x,u⟫` on `Ω₂₄` is `1 / 24` for any unit vector `u`. -/
public theorem sphereAvg24_inner_pow_two_of_norm_one
    {u : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 2) = (1 / 24 : ℝ) := by
  obtain ⟨E, hEu⟩ := exists_linearIsometryEquiv_map_unit_to_basis0 (u := u) hu
  have hcoord := coord0_of_map_unit_to_e0 (u := u) (E := E) hEu
  have hinv :=
    sphereAvg24_comp_linearIsometryEquiv (e := E) (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2)
  have hE :
      sphereAvg24 (fun x : ℝ²⁴ => ((E x) (0 : Fin 24)) ^ 2) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2) := by
    simpa using! hinv
  have hcongr :
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 2) =
        sphereAvg24 (fun x : ℝ²⁴ => ((E x) (0 : Fin 24)) ^ 2) :=
    Eq.symm (sphereAvg24_congr fun x => congrFun (congrArg HPow.hPow (hcoord ↑x)) 2)
  calc
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 2)
        = sphereAvg24 (fun x : ℝ²⁴ => ((E x) (0 : Fin 24)) ^ 2) := hcongr
    _ = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2) := hE
    _ = (1 / 24 : ℝ) := sphereAvg24_coord_sq (i := (0 : Fin 24))

/-- The fourth moment of `x ↦ ⟪x,u⟫` on `Ω₂₄` is `1 / 208` for any unit vector `u`. -/
public theorem sphereAvg24_inner_pow_four_of_norm_one
    {u : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) :
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4) = (1 / 208 : ℝ) := by
  obtain ⟨E, hEu⟩ := exists_linearIsometryEquiv_map_unit_to_basis0 (u := u) hu
  have hcoord := coord0_of_map_unit_to_e0 (u := u) (E := E) hEu
  have hinv :=
    sphereAvg24_comp_linearIsometryEquiv (e := E) (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4)
  have hE :
      sphereAvg24 (fun x : ℝ²⁴ => ((E x) (0 : Fin 24)) ^ 4) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) := by
    simpa using! hinv
  have hcongr :
      sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4) =
        sphereAvg24 (fun x : ℝ²⁴ => ((E x) (0 : Fin 24)) ^ 4) :=
    Eq.symm (sphereAvg24_congr fun x => congrFun (congrArg HPow.hPow (hcoord ↑x)) 4)
  calc
    sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4)
        = sphereAvg24 (fun x : ℝ²⁴ => ((E x) (0 : Fin 24)) ^ 4) := hcongr
    _ = sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) := hE
    _ = (1 / 208 : ℝ) := sphereAvg24_coord_pow_four

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
