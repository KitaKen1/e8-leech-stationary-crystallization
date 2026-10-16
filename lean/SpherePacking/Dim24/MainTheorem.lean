-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Packing
public import SpherePacking.Basic.SpherePacking
public import SpherePacking.Dim24.Uniqueness.Defs
import SpherePacking.Dim24.MagicFunction.F.UpperBound
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.Rigidity

/-!
Main theorem in dimension 24.

We prove that the optimal sphere packing density in `R^24` is achieved by the Leech lattice packing:
`SpherePackingConstant 24 = LeechPacking.density`.

Moreover, any periodic sphere packing of the same density is isometric to a scaled copy of the Leech
packing.

Paper reference: `dim_24.tex`, Theorem 1.1 and Section 4.
-/

namespace SpherePacking.Dim24

open scoped ENNReal

/-- The optimal packing density in dimension 24 equals the density of the Leech lattice packing. -/
public theorem SpherePackingConstant_eq_leech_density :
    SpherePackingConstant 24 = LeechPacking.density := by
  refine le_antisymm ?_ LeechPacking_density_le_SpherePackingConstant
  rw [LeechPacking_density]
  exact SpherePackingConstant_le_leech_density

/--
Main theorem (dimension 24): optimality of the Leech packing,
with uniqueness among periodic packings.
-/
public theorem MainTheorem :
    SpherePackingConstant 24 = Dim24.LeechPacking.density ∧
      ∀ S : PeriodicSpherePacking 24,
        S.density = Dim24.LeechPacking.density → Dim24.IsometricToScaledLeech S := by
  refine ⟨SpherePackingConstant_eq_leech_density, fun S hS => ?_⟩
  simpa using! Uniqueness.RigidityClassify.CE.leech_unique_optimal_periodic (S := S) hS

end SpherePacking.Dim24
