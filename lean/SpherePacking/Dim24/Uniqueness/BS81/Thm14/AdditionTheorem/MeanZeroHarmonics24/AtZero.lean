-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DoubleSumsToHarmonics24

/-!
# Mean-zero bridge: evaluation at `0`

This step file isolates the algebraic fact that `evalPk24` at `0` vanishes for homogeneous pieces
of positive degree.

## Main statements
* `MeanZeroHarmonics24Steps.evalPk24_at_zero_eq_zero_of_degree_pos_step`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.LP

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace MeanZeroHarmonics24Steps

/-- Evaluation at the origin vanishes for homogeneous polynomials of positive degree. -/
public theorem evalPk24_at_zero_eq_zero_of_degree_pos_step
    (k : ℕ) (hk : 1 ≤ k)
    (p : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k) :
    evalPk24 (k := k) (y := (0 : ℝ²⁴)) p = 0 := by
  -- Evaluation at `0` is the constant coefficient, which vanishes for homogeneous degree `k > 0`.
  have hpHom :
      MvPolynomial.IsHomogeneous (p.1 : MvPolynomial (Fin 24) ℝ) k := by
    simpa using!
      (MvPolynomial.mem_homogeneousSubmodule (σ := Fin 24) (R := ℝ) k
            (p := (p.1 : MvPolynomial (Fin 24) ℝ))).1 p.2
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have hconst : MvPolynomial.constantCoeff (p.1 : MvPolynomial (Fin 24) ℝ) = 0 := by
    -- `constantCoeff` is the `0`-monomial coefficient.
    have hcoeff :
        MvPolynomial.coeff (0 : (Fin 24) →₀ ℕ) (p.1 : MvPolynomial (Fin 24) ℝ) = 0 := by
      refine hpHom.coeff_eq_zero ?_
      -- `degree 0 = 0 ≠ k` since `k > 0`.
      simpa using! (Ne.symm hk0)
    simpa [MvPolynomial.constantCoeff_eq] using! hcoeff
  -- Now compute the evaluation.
  simp [evalPk24, evalPoly24, hconst]

end MeanZeroHarmonics24Steps

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24
