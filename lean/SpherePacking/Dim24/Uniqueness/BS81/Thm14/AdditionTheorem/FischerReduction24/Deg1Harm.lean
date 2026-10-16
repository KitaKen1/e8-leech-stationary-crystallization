-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.FischerDecompositionFixed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Fischer reduction: degree `1` is harmonic

This step file records the low-degree fact used in the Fischer-reduction argument: every
homogeneous polynomial of degree `1` is harmonic.

## Main statements
* `FischerReduction24Steps.mem_Harm_of_degree_one_step`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24.FischerReduction24Steps

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.LP Uniqueness.BS81.LP.Gegenbauer24.PSD

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- A homogeneous polynomial of degree `1` lies in the harmonic subspace. -/
public theorem mem_Harm_of_degree_one_step
    (p : Fischer.Pk 1) : (p : Fischer.Pk 1) ∈ Harmonic.Harm 1 := by
  -- By definition, `Harm 1` is the kernel of the restricted Laplacian.
  change Harmonic.laplacianPk 1 p = 0
  -- Reduce equality in the subtype `Pk 0` to equality of underlying polynomials.
  apply Subtype.ext
  -- Unfold the restricted Laplacian: it is the sum of second partial derivatives.
  simp [Harmonic.laplacianPk, Harmonic.laplacian_apply]
  have hpHom : (p.1 : MvPolynomial (Fin 24) ℝ).IsHomogeneous 1 := by
    have hp : (p.1 : MvPolynomial (Fin 24) ℝ) ∈ Fischer.Pk 1 := p.2
    dsimp [Fischer.Pk] at hp
    exact hp
  have hterm (i : Fin 24) :
      MvPolynomial.pderiv i (MvPolynomial.pderiv i (p.1 : MvPolynomial (Fin 24) ℝ)) = 0 := by
    have hhom0 : (MvPolynomial.pderiv i (p.1 : MvPolynomial (Fin 24) ℝ)).IsHomogeneous 0 := by
      simpa using! (hpHom.pderiv (i := i))
    have hmem0 :
        MvPolynomial.pderiv i (p.1 : MvPolynomial (Fin 24) ℝ) ∈
          MvPolynomial.homogeneousSubmodule (Fin 24) ℝ 0 :=
      hhom0
    have hmem1 :
        (MvPolynomial.pderiv i (p.1 : MvPolynomial (Fin 24) ℝ)) ∈
          (1 : Submodule ℝ (MvPolynomial (Fin 24) ℝ)) := by
      simpa [MvPolynomial.homogeneousSubmodule_zero] using! hmem0
    rcases (Submodule.mem_one.mp hmem1) with ⟨a, ha⟩
    simp [ha.symm, MvPolynomial.algebraMap_eq]
  simp [hterm]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24.FischerReduction24Steps
