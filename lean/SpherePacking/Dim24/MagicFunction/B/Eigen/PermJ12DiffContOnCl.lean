-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ12Regularity
import SpherePacking.ForMathlib.ScalarOneFormDiffContOnCl
import SpherePacking.ForMathlib.ScalarOneFormFDeriv
import SpherePacking.Contour.PermJ12DiffContOnCl

/-!
# `DiffContOnCl` for `Ψ₁'` on `wedgeSet`

This file supplies the `DiffContOnCl` hypotheses needed for the contour deformation argument for
`perm_J₁_J₂`. We show that `Ψ₁' r` and the associated one-form `scalarOneForm (Ψ₁' r)` are
`DiffContOnCl` on `wedgeSet`, and we record a symmetry identity for the resulting
`fderivWithin`.

## Main statements
* `diffContOnCl_Ψ₁'_wedgeSet`
* `diffContOnCl_ω_wedgeSet`
* `fderivWithin_ω_wedgeSet_symm`
-/

namespace SpherePacking.Dim24.BFourier
open Filter SpherePacking.ForMathlib
open scoped Topology

noncomputable section

open MagicFunction

section PermJ12

/-- The function `Ψ₁' r` is `DiffContOnCl` on `wedgeSet`. -/
public lemma diffContOnCl_Ψ₁'_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (Ψ₁' r) wedgeSet := by
  have hdiffC : DifferentiableOn ℂ (Ψ₁' r) UpperHalfPlane.upperHalfPlaneSet :=
    differentiableOn_Ψ₁'_upper (r := r)
  have htend : Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
    simpa using! (tendsto_Ψ₁'_one_within_closure_wedgeSet (r := r))
  have hval : (Ψ₁' r) (1 : ℂ) = 0 := by simp [Ψ₁', ψT']
  simpa using! (SpherePacking.Contour.diffContOnCl_wedgeSet_of (f := Ψ₁' r) hdiffC htend hval)

/-- The one-form `scalarOneForm (Ψ₁' r)` is `DiffContOnCl` on `wedgeSet`. -/
public lemma diffContOnCl_ω_wedgeSet (r : ℝ) :
    DiffContOnCl ℝ (scalarOneForm (Ψ₁' r)) wedgeSet :=
  diffContOnCl_scalarOneForm (s := wedgeSet) (diffContOnCl_Ψ₁'_wedgeSet (r := r))

/-- Symmetry of `fderivWithin` for `scalarOneForm (Ψ₁' r)` on `wedgeSet`. -/
public lemma fderivWithin_ω_wedgeSet_symm (r : ℝ) :
    ∀ x ∈ wedgeSet, ∀ u ∈ tangentConeAt ℝ wedgeSet x, ∀ v ∈ tangentConeAt ℝ wedgeSet x,
      fderivWithin ℝ (scalarOneForm (Ψ₁' r)) wedgeSet x u v =
        fderivWithin ℝ (scalarOneForm (Ψ₁' r)) wedgeSet x v u := by
  simpa using!
    (SpherePacking.Contour.fderivWithin_scalarOneForm_wedgeSet_symm_of
      (f := Ψ₁' r) (hdiffC := differentiableOn_Ψ₁'_upper (r := r)))

end PermJ12
end
end SpherePacking.Dim24.BFourier
