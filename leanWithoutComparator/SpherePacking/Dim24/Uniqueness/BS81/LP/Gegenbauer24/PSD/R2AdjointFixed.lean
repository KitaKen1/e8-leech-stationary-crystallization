-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.AdjointOpsFixed
import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.R2Laplacian
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Adjointness between `r²` and the Laplacian

We define multiplication by `r² = ∑ᵢ Xᵢ²` on the homogeneous pieces `Pk k` as an `ℝ`-linear map,
and similarly package the degree-`k+2` Laplacian on homogeneous pieces as a sum of second partial
derivatives. The main statement is the adjointness identity
`Fischer.inner_mulR2Pk_eq_inner_laplacianPk`, reduced to the degree-`1` adjointness proved in
`PSD/AdjointOpsFixed.lean`.

## Main definitions
* `Fischer.mulR2Pk`

## Main statements
* `Fischer.inner_mulR2Pk_eq_inner_laplacianPk`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer

noncomputable section

open scoped BigOperators RealInnerProductSpace
open Finset MvPolynomial
open Harmonic

local notation "Pk" => Fischer.Pk

/-- Multiply by `r² = ∑ᵢ Xᵢ²` as a degree-shifting map `Pk k →ₗ[ℝ] Pk (k+2)`.

We define this as a sum of the maps `p ↦ X i * (X i * p)`, so no homogeneity proof is needed. -/
@[expose] public noncomputable def mulR2Pk (k : ℕ) : Pk k →ₗ[ℝ] Pk (k + 2) :=
  (univ : Finset Var).sum (fun i =>
    (mulXPk (k := k + 1) i).comp (mulXPk (k := k) i))

/-- Second partial derivative `∂ᵢ²` as a degree-shifting map `Pk (k+2) →ₗ[ℝ] Pk k`. -/
private noncomputable def pderiv2Pk (k : ℕ) (i : Var) : Pk (k + 2) →ₗ[ℝ] Pk k :=
  (pderivPk (k := k) i).comp (pderivPk (k := k + 1) i)

private lemma laplacianPk_apply_eq_sum_pderiv2Pk (k : ℕ) (q : Pk (k + 2)) :
    Harmonic.laplacianPk (k + 2) q =
      (univ : Finset Var).sum (fun i => pderiv2Pk (k := k) i q) := by
  -- Compare the underlying polynomials.
  ext d
  -- Unfold the degree-restricted Laplacian and the `pderivPk` maps.
  simp [Harmonic.laplacianPk, Harmonic.laplacian, pderiv2Pk, pderivPk,
    LinearMap.codRestrict, LinearMap.sum_apply, LinearMap.comp_apply]

/-- Adjointness: multiplication by `r²` is adjoint to the Laplacian (between homogeneous pieces). -/
public lemma inner_mulR2Pk_eq_inner_laplacianPk (k : ℕ) (p : Pk k) (q : Pk (k + 2)) :
    ⟪mulR2Pk (k := k) p, q⟫ = ⟪p, Harmonic.laplacianPk (k + 2) q⟫ := by
  -- Reduce to adjointness of `X i` vs `pderiv i`, twice, then sum over `i`.
  have hterm (i : Var) :
      ⟪(mulXPk (k := k + 1) i) ((mulXPk (k := k) i) p), q⟫ =
        ⟪p, (pderiv2Pk (k := k) i) q⟫ := by
    -- Apply the degree-`1` adjointness twice.
    have h1 :
        ⟪(mulXPk (k := k + 1) i) ((mulXPk (k := k) i) p), q⟫ =
          ⟪(mulXPk (k := k) i) p, (pderivPk (k := k + 1) i) q⟫ := by
      -- This is `inner_mulXPk_eq_inner_pderivPk` at degree `k+1`.
      exact
        inner_mulXPk_eq_inner_pderivPk (k := k + 1) (i := i)
          (p := (mulXPk (k := k) i p)) (q := q)
    have h2 :
        ⟪(mulXPk (k := k) i) p, (pderivPk (k := k + 1) i) q⟫ =
          ⟪p, (pderivPk (k := k) i) ((pderivPk (k := k + 1) i) q)⟫ :=
      inner_mulXPk_eq_inner_pderivPk (k := k) (i := i) (p := p)
          (q := (pderivPk (k := k + 1) i q))
    -- Combine.
    simpa [pderiv2Pk, LinearMap.comp_apply] using! h1.trans h2
  -- Sum the termwise identities.
  -- Expand the `r²` sum on the left.
  have hsum :
      ⟪mulR2Pk (k := k) p, q⟫ =
        (univ : Finset Var).sum (fun i => ⟪p, (pderiv2Pk (k := k) i) q⟫) := by
    -- The sum is in the *left* argument, so use `sum_inner`.
    simp [mulR2Pk, sum_inner, hterm]
  -- Rewrite the Laplacian as the sum of second derivatives and expand using `inner_sum`.
  have hlap :
      ⟪p, Harmonic.laplacianPk (k + 2) q⟫ =
        (univ : Finset Var).sum (fun i => ⟪p, (pderiv2Pk (k := k) i) q⟫) := by
    -- First rewrite `laplacianPk` as a sum.
    have hq :
        Harmonic.laplacianPk (k + 2) q =
          (univ : Finset Var).sum (fun i => pderiv2Pk (k := k) i q) :=
      laplacianPk_apply_eq_sum_pderiv2Pk (k := k) (q := q)
    -- Then expand the inner product in the right argument.
    simp [hq, inner_sum]
  -- Finish.
  exact hsum.trans hlap.symm

/-- The `r²`-range is orthogonal to the harmonic subspace. -/
private lemma inner_mulR2Pk_eq_zero_of_mem_Harm (k : ℕ) (p : Pk k) (h : Pk (k + 2))
    (hh : h ∈ Harmonic.Harm (k + 2)) :
    ⟪mulR2Pk (k := k) p, h⟫ = 0 := by
  -- Use adjointness and `laplacianPk h = 0`.
  have : Harmonic.laplacianPk (k + 2) h = 0 := (Harmonic.mem_Harm_iff (k := k + 2) (p := h)).1 hh
  simp [inner_mulR2Pk_eq_inner_laplacianPk (k := k) (p := p) (q := h), this]

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
