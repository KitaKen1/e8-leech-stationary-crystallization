-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.ThetaTransform
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.DualSelf
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Theta series on the upper half-plane

This is a lightweight bridge layer between the analytic theta series `thetaSeries L : ℂ → ℂ`
and the modular-forms framework, which is phrased over `UpperHalfPlane` (`ℍ`).

We only record the `T`-invariance (for even lattices) and the `S`-transformation law (for even
unimodular lattices), in the explicit `ℍ` terms that are convenient for later use.

## Main definitions
* `thetaSeriesUHP`

## Main statements
* `thetaSeries_transform_S_of_even_unimodular`
* `thetaSeriesUHP_vadd_one`
* `thetaSeriesUHP_mk_inv_neg`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify
noncomputable section

open scoped RealInnerProductSpace
open Complex UpperHalfPlane MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- For an even unimodular lattice `L` in rank `24`, the analytic theta series satisfies the usual
`S`-transformation law. -/
public theorem thetaSeries_transform_S_of_even_unimodular
    (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] [IsZLattice ℝ L]
    (hEven : EvenNormSq L) (hUnimod : Unimodular L) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaSeries L (-1 / τ) = (-(τ * Complex.I)) ^ (12 : ℂ) * thetaSeries L τ := by
  have hS := thetaSeries_transform_S (L := L) (τ := τ) hτ
  have hcov : ZLattice.covolume L volume = 1 := by simpa [Unimodular] using! hUnimod
  have hdual : DualLattice L = L := by
    simpa using!
      (dualLattice_eq_of_integral_unimodular (L := L)
        (integral_of_evenNormSq (L := L) hEven) hUnimod)
  simpa [hcov, hdual, mul_assoc, mul_left_comm, mul_comm] using! hS

/-- Theta series viewed as a function on `ℍ` by restriction. -/
@[expose]
public noncomputable def thetaSeriesUHP (L : Submodule ℤ ℝ²⁴) (z : ℍ) : ℂ :=
  thetaSeries L (z : ℂ)

/-- `T`-invariance of the theta series on `ℍ`, for even lattices. -/
public theorem thetaSeriesUHP_vadd_one
    (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] [IsZLattice ℝ L]
    (hEven : EvenNormSq L) (z : ℍ) :
    thetaSeriesUHP L ((1 : ℝ) +ᵥ z) = thetaSeriesUHP L z := by
  -- `((1 : ℝ) +ᵥ z : ℂ) = (1 : ℂ) + z`, then commute to match `τ + 1`.
  simpa [thetaSeriesUHP, UpperHalfPlane.coe_vadd, add_comm] using!
    (thetaSeries_add_one_of_even (L := L) hEven (τ := (z : ℂ)))

/-- `S`-transformation of the theta series on `ℍ`, for even unimodular lattices. -/
public theorem thetaSeriesUHP_mk_inv_neg
    (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] [IsZLattice ℝ L]
    (hEven : EvenNormSq L) (hUnimod : Unimodular L) (z : ℍ) :
    thetaSeriesUHP L (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) =
      (-(z : ℂ) * Complex.I) ^ (12 : ℂ) * thetaSeriesUHP L z := by
  -- `(-1 / z) = (-z)⁻¹`, and the `S`-action on `ℍ` is given by `z ↦ (-z)⁻¹`.
  simpa [thetaSeriesUHP, div_eq_mul_inv, UpperHalfPlane.coe_mk, inv_neg, mul_assoc] using!
    (thetaSeries_transform_S_of_even_unimodular (L := L) hEven hUnimod (τ := (z : ℂ)) z.2)

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
