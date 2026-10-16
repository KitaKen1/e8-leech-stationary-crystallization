module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.FromSharpness
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.DistanceDistribution.DeriveEq11FromMomentsFinal


/-!
# Distance distribution from sharpness

This file is Step C in the BS81 Theorem 14 pipeline: from optimality (sharpness) we derive the
explicit distance distribution (equation (11)) and assemble the equality-case package.

## Main statements
* `dist_eq11_of_optimal`
* `thm14_eqCase24Pkg_of_optimal`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Step C: from optimality, derive the BS81 distance distribution (equation (11)). -/
public theorem dist_eq11_of_optimal
    (C : Set ℝ²⁴)
    (hC : IsSphericalCode 24 C (1 / 2 : ℝ))
    (hcard : Set.ncard C = 196560) :
    ∀ ⦃u : ℝ²⁴⦄, u ∈ C →
      distCount (n := 24) C u (1 : ℝ) = 1 ∧
        distCount (n := 24) C u (-1 : ℝ) = 1 ∧
        distCount (n := 24) C u (1 / 2 : ℝ) = 4600 ∧
        distCount (n := 24) C u (-1 / 2 : ℝ) = 4600 ∧
        distCount (n := 24) C u (1 / 4 : ℝ) = 47104 ∧
        distCount (n := 24) C u (-1 / 4 : ℝ) = 47104 ∧
        distCount (n := 24) C u (0 : ℝ) = 93150 :=
  Uniqueness.BS81.Thm14.dist_eq11_of_design10_and_support
      (C := C) hC hcard (design10_of_optimal (C := C) hC hcard)
      (support_of_optimal (C := C) hC hcard)

/-!
## Assemble the package
-/

/-- Assemble `EqCase24Pkg` from optimality, using the design and distance-distribution steps. -/
public theorem thm14_eqCase24Pkg_of_optimal
    (C : Set ℝ²⁴)
    (hC : IsSphericalCode 24 C (1 / 2 : ℝ))
    (hcard : Set.ncard C = 196560) :
    EqCase24Pkg C := by
  refine ⟨?_, ?_⟩
  · exact ⟨hC, hcard, dist_eq11_of_optimal (C := C) hC hcard⟩
  · exact design11_of_optimal (C := C) hC hcard

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
