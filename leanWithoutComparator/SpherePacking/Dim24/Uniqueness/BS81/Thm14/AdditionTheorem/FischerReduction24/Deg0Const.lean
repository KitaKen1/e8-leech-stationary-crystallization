-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DoubleSumsToHarmonics24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24

/-!
# Fischer reduction: degree `0`

This step file isolates the base case in the Fischer-reduction argument: a homogeneous polynomial
of degree `0` is constant, so its finite average equals its sphere average.

## Main statements
* `FischerReduction24Steps.finsetAvg_eq_sphereAvg_of_degree_zero_step`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24.FischerReduction24Steps

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.LP Uniqueness.BS81.Thm14.AdditionTheorem Uniqueness.BS81.LP.Gegenbauer24.PSD

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Base case for Fischer reduction: degree `0` homogeneous polynomials are constant. -/
public theorem finsetAvg_eq_sphereAvg_of_degree_zero_step
    (C : Finset ℝ²⁴) (hCne : C.Nonempty) (p : Fischer.Pk 0) :
    finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := 0) (y := x) p) =
      sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := 0) (y := x) p) := by
  -- A degree-`0` homogeneous polynomial is constant, i.e. lies in the `1`-submodule.
  have hmem0 :
      (p.1 : MvPolynomial (Fin 24) ℝ) ∈
        MvPolynomial.homogeneousSubmodule (Fin 24) ℝ 0 := by
    simpa [Fischer.Pk] using! p.2
  have hmem1 :
      (p.1 : MvPolynomial (Fin 24) ℝ) ∈
        (1 : Submodule ℝ (MvPolynomial (Fin 24) ℝ)) := by
    simpa [MvPolynomial.homogeneousSubmodule_zero] using! hmem0
  rcases (Submodule.mem_one.mp hmem1) with ⟨a, ha⟩
  have heval_const :
      (fun x : ℝ²⁴ => evalPk24 (k := 0) (y := x) p) = fun _ : ℝ²⁴ => a := by
    funext x
    unfold evalPk24 evalPoly24
    rw [← ha]
    simp [MvPolynomial.algebraMap_eq]
  have hfin : finsetAvg C (fun _ : ℝ²⁴ => a) = a := by
    have hcard_ne : (C.card : ℝ) ≠ 0 := by exact_mod_cast hCne.card_ne_zero
    simp [finsetAvg, Finset.sum_const, hcard_ne]
  have hsph : sphereAvg24 (fun _ : ℝ²⁴ => a) = a := by
    simpa using! (sphereAvg24_const (c := a))
  simpa [heval_const] using! hfin.trans hsph.symm

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24.FischerReduction24Steps
