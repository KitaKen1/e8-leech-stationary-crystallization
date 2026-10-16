-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.R2AdjointFixed
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Fischer decomposition: orthogonal complement as the `r²`-range

This file records the orthogonal complement identity behind Fischer decomposition: the orthogonal
complement of the harmonic subspace is the range of multiplication by `r²`.

We use the adjointness results in `PSD/R2AdjointFixed.lean` and the general
adjoint/orthogonal-ker machinery from `Mathlib.Analysis.InnerProductSpace.Adjoint`.

## Main statements
* `Harm_orthogonal_eq_range_mulR2Pk`
* `isCompl_Harm_range_mulR2Pk`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
noncomputable section

open scoped BigOperators RealInnerProductSpace

open Harmonic

local notation "Pk" => Pk

/-!
Typeclass note.

`InnerProductSpace` in Mathlib only provides a `SeminormedAddCommGroup` by default; in order to use
`ContinuousLinearMap` and the finite-dimensional adjoint `LinearMap.adjoint` we equip `Pk k` with
the `NormedAddCommGroup`/`CompleteSpace` instances derived from the definite Fischer inner product.
-/

/-- The Fischer inner product induces a `NormedAddCommGroup` structure on `Pk k`. -/
public local instance (k : ℕ) : NormedAddCommGroup (Pk k) :=
  (show InnerProductSpace.Core ℝ (Pk k) from inferInstance).toNormedAddCommGroup

/-- Each `Pk k` is complete because it is finite dimensional. -/
public local instance (k : ℕ) : CompleteSpace (Pk k) := by
  simpa using! (FiniteDimensional.complete ℝ (Pk k))

/-- The adjoint of the degree-`k+2` Laplacian is multiplication by `r²`. -/
private lemma laplacianPk_adjoint_eq_mulR2Pk (k : ℕ) :
    (Harmonic.laplacianPk (k + 2)).adjoint = mulR2Pk (k := k) := by
  -- Use the characterizing property of adjoints.
  -- `LinearMap.eq_adjoint_iff` is phrased as `A = B.adjoint ↔ ...`, so apply it to `A := mulR2Pk`.
  symm
  refine (LinearMap.eq_adjoint_iff (A := mulR2Pk (k := k)) (B := Harmonic.laplacianPk (k + 2))).2 ?_
  intro p q
  -- This is exactly `inner_mulR2Pk_eq_inner_laplacianPk`.
  simpa using! (inner_mulR2Pk_eq_inner_laplacianPk (k := k) (p := p) (q := q))

/-- Orthogonal complement of the harmonic subspace: `(ker Δ)ᗮ = range (r²·)`.

This is the key orthogonality statement behind Fischer decomposition. -/
public lemma Harm_orthogonal_eq_range_mulR2Pk (k : ℕ) :
    Submodule.orthogonal (Harmonic.Harm (k + 2) : Submodule ℝ (Pk (k + 2))) =
      LinearMap.range (mulR2Pk (k := k)) := by
  -- Reduce to the general statement `(ker T)ᗮ = range (T†)`, noting that ranges are closed in
  -- finite-dimensional spaces.
  let T : Pk (k + 2) →ₗ[ℝ] Pk k := Harmonic.laplacianPk (k + 2)
  haveI : CompleteSpace (Pk (k + 2)) := FiniteDimensional.complete ℝ (Pk (k + 2))
  haveI : CompleteSpace (Pk k) := FiniteDimensional.complete ℝ (Pk k)
  -- Apply `orthogonal_ker` for continuous linear maps.
  have hker :
      Submodule.orthogonal (T.toContinuousLinearMap.ker) =
        (T.toContinuousLinearMap.adjoint.range).topologicalClosure := by
    simpa using! (ContinuousLinearMap.orthogonal_ker (T.toContinuousLinearMap))
  -- Rewrite the ker/range in terms of the underlying `LinearMap`.
  -- In finite-dimensional spaces, the range is closed, so the closure is redundant.
  have hrange_closed :
      IsClosed (T.toContinuousLinearMap.adjoint.range : Set (Pk (k + 2))) :=
    (T.toContinuousLinearMap.adjoint.range).closed_of_finiteDimensional
  have hclosure :
      (T.toContinuousLinearMap.adjoint.range).topologicalClosure =
        T.toContinuousLinearMap.adjoint.range :=
    hrange_closed.submodule_topologicalClosure_eq
  -- Transport to the statement on `LinearMap`s and substitute the adjoint computation.
  -- `Harm (k+2) = ker (laplacianPk (k+2))` by definition.
  have hker' :
      Submodule.orthogonal (LinearMap.ker T) = LinearMap.range (T.adjoint) := by
    -- Start from the continuous version and simplify.
    -- The coercions are a bit delicate; we use `show` to guide rewriting.
    -- `LinearMap.range` agrees definitionally on `toContinuousLinearMap.toLinearMap`.
    simpa [T, hclosure, LinearMap.adjoint_eq_toCLM_adjoint (A := T)] using! hker
  -- Rewrite `T.adjoint` using `laplacianPk_adjoint_eq_mulR2Pk`.
  have hker'' :
      Submodule.orthogonal (LinearMap.ker T) = LinearMap.range (mulR2Pk (k := k)) := by
    have hadj : T.adjoint = mulR2Pk (k := k) := by
      -- `T = laplacianPk (k+2)` by definition.
      simpa [T] using! (laplacianPk_adjoint_eq_mulR2Pk (k := k))
    simpa [hadj] using! hker'
  -- Unfold `Harm` and discharge.
  simpa [Harmonic.Harm, T] using! hker''

/-- Orthogonal decomposition: `Harm (k+2)` is a complement to the `r²`-range. -/
public lemma isCompl_Harm_range_mulR2Pk (k : ℕ) :
    IsCompl (Harmonic.Harm (k + 2)) (LinearMap.range (mulR2Pk (k := k))) := by
  -- Use the abstract fact that a submodule splits with its orthogonal complement,
  -- then rewrite the orthogonal complement via the adjoint/range computation.
  haveI : CompleteSpace (Harmonic.Harm (k + 2)) := by
    simpa using! (FiniteDimensional.complete ℝ (Harmonic.Harm (k + 2)))
  haveI : (Harmonic.Harm (k + 2)).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace (K := Harmonic.Harm (k + 2))
  have h :
      IsCompl (Harmonic.Harm (k + 2))
        (Submodule.orthogonal (Harmonic.Harm (k + 2) : Submodule ℝ (Pk (k + 2)))) := by
    simpa using!
      (Submodule.isCompl_orthogonal_of_hasOrthogonalProjection (K := Harmonic.Harm (k + 2)))
  simpa [Harm_orthogonal_eq_range_mulR2Pk (k := k)] using! h

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
