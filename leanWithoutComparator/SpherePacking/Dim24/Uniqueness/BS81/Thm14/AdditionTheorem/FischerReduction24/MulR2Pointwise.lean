-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.FischerDecompositionFixed
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DoubleSumsToHarmonics24

/-!
# Fischer reduction: restriction of `r²`

This step file isolates the pointwise claim that on the unit sphere, `mulR2Pk` does not change
evaluation.

## Main statements
* `FischerReduction24Steps.evalPk24_mulR2Pk_of_norm_eq_one_step`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24.FischerReduction24Steps

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.LP Uniqueness.BS81.Thm14.AdditionTheorem Uniqueness.BS81.LP.Gegenbauer24.PSD

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- On the unit sphere, `mulR2Pk` does not change evaluation. -/
public theorem evalPk24_mulR2Pk_of_norm_eq_one_step
    (k : ℕ) (q : Fischer.Pk k) (x : ℝ²⁴) (hx : ‖x‖ = (1 : ℝ)) :
    evalPk24 (k := k + 2) (y := x) (Fischer.mulR2Pk (k := k) q) =
      evalPk24 (k := k) (y := x) q := by
  -- Expand `mulR2Pk` as `∑ i, X i * (X i * q)` and evaluate termwise.
  -- On the unit sphere, `∑ i, x i ^ 2 = ‖x‖^2 = 1`, so the factor cancels.
  have hmulX (j : Fin 24) (p : Fischer.Pk k) :
      (Fischer.mulXPk (k := k) j p).1 = (MvPolynomial.X j : MvPolynomial (Fin 24) ℝ) * p.1 := by
    simp [Fischer.mulXPk, LinearMap.codRestrict, LinearMap.comp_apply]
  have hmulX' (j : Fin 24) (p : Fischer.Pk (k + 1)) :
      (Fischer.mulXPk (k := k + 1) j p).1 =
        (MvPolynomial.X j : MvPolynomial (Fin 24) ℝ) * p.1 := by
    simp [Fischer.mulXPk, LinearMap.codRestrict, LinearMap.comp_apply]
  have hcoe :
      (Fischer.mulR2Pk (k := k) q).1 =
        (Finset.univ : Finset (Fin 24)).sum (fun j =>
          (MvPolynomial.X j : MvPolynomial (Fin 24) ℝ) *
            ((MvPolynomial.X j : MvPolynomial (Fin 24) ℝ) * q.1)) := by
    simp [Fischer.mulR2Pk, LinearMap.sum_apply, LinearMap.comp_apply, hmulX, hmulX']
  have hsumSq :
      (Finset.univ : Finset (Fin 24)).sum (fun j => (x j) ^ (2 : ℕ)) = (1 : ℝ) := by
    have hnorm :
        ‖x‖ ^ 2 = (Finset.univ : Finset (Fin 24)).sum (fun j => (x j) ^ (2 : ℕ)) := by
      -- `‖x‖^2` is the coordinate sum of squares in Euclidean space.
      -- `Real.norm_eq_abs` and `sq_abs` rewrite `‖x j‖^2` to `(x j)^2`.
      simpa [Real.norm_eq_abs, sq_abs] using!
        (EuclideanSpace.norm_sq_eq (𝕜 := ℝ) (n := Fin 24) x)
    calc
      (Finset.univ : Finset (Fin 24)).sum (fun j => (x j) ^ (2 : ℕ)) = ‖x‖ ^ 2 := by
        simpa using! hnorm.symm
      _ = (1 : ℝ) := by simp [hx]
  -- Evaluate the sum and factor out `evalPk24 k x q`.
  have heval :
      evalPk24 (k := k + 2) (y := x) (Fischer.mulR2Pk (k := k) q) =
        ((Finset.univ : Finset (Fin 24)).sum (fun j => (x j) ^ (2 : ℕ))) *
          evalPk24 (k := k) (y := x) q := by
    -- Unfold evaluation, rewrite the underlying polynomial, then use `eval_mul`/`eval_X`.
    simp [evalPk24, evalPoly24, hcoe, MvPolynomial.eval_mul, mul_assoc, pow_two, Finset.sum_mul]
  -- Now use `∑ x_j^2 = 1`.
  simp [heval, hsumSq]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24.FischerReduction24Steps
