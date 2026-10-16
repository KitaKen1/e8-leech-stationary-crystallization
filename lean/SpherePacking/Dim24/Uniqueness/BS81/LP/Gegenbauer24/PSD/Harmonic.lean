-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Harmonic homogeneous polynomials in 24 variables

We define the (Euclidean) Laplacian `Δ := ∑ i, ∂ᵢ^2` on `MvPolynomial (Fin 24) ℝ`, restrict it to
the degree-`k` homogeneous component, and define `Harm k` as the kernel.

## Main definitions
* `laplacian`, `laplacianPk`
* `Harm`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic
noncomputable section

open scoped BigOperators

open Finset Finsupp MvPolynomial

open Fischer

/-- The degree-`k` homogeneous component, as a shorthand for `Fischer.Pk k`. -/
public abbrev Pk (k : ℕ) : Submodule ℝ Poly := Fischer.Pk k

/-- The Laplacian on multivariate polynomials in `24` variables: `Δ = ∑ᵢ ∂ᵢ^2`. -/
@[expose]
public noncomputable def laplacian : Poly →ₗ[ℝ] Poly :=
  (Finset.univ : Finset Var).sum (fun i =>
    ((MvPolynomial.pderiv i).toLinearMap.comp (MvPolynomial.pderiv i).toLinearMap))

/-- Expanded formula for `laplacian`. -/
public lemma laplacian_apply (p : Poly) :
    laplacian p =
      ∑ i : Var, (MvPolynomial.pderiv i) (MvPolynomial.pderiv i p) := by
  simp [laplacian, LinearMap.sum_apply]

/-- The Laplacian lowers homogeneity degree by `2`. -/
public lemma isHomogeneous_laplacian {k : ℕ} {p : Poly} (hp : p.IsHomogeneous k) :
    (laplacian p).IsHomogeneous (k - 2) := by
  -- Each `∂ᵢ` lowers homogeneity by `1`, so `∂ᵢ^2` lowers by `2` (sums preserve homogeneity).
  have hsum :
      (∑ i : Var, (MvPolynomial.pderiv i) (MvPolynomial.pderiv i p)).IsHomogeneous (k - 2) := by
    refine MvPolynomial.IsHomogeneous.sum (s := (Finset.univ : Finset Var))
        (φ := fun i => (MvPolynomial.pderiv i) (MvPolynomial.pderiv i p)) (n := k - 2) ?_
    intro i hi
    have hp1 : (MvPolynomial.pderiv i p).IsHomogeneous (k - 1) := hp.pderiv (i := i)
    simpa [Nat.sub_sub] using! (hp1.pderiv (i := i))
  simpa [laplacian_apply] using! hsum

/-- The Laplacian restricted to the degree-`k` piece, landing in degree `k-2`. -/
@[expose]
public noncomputable def laplacianPk (k : ℕ) : Pk k →ₗ[ℝ] Pk (k - 2) :=
  LinearMap.codRestrict (Pk (k - 2)) (laplacian.comp (Submodule.subtype (Pk k))) (by
    intro p
    -- Use homogeneity preservation.
    have hp' : (p.1 : Poly).IsHomogeneous k := by
      -- `Pk k` is definitionally the homogeneous submodule.
      simpa [Pk] using!
        (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) k (p := (p.1 : Poly))).1 p.2
    -- Return membership in the degree-`k-2` homogeneous submodule.
    exact (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) (k - 2)
      (p := laplacian (p.1 : Poly))).2 (isHomogeneous_laplacian (k := k) (p := (p.1 : Poly)) hp'))

/-- Harmonic homogeneous polynomials of degree `k`: the kernel of the restricted Laplacian. -/
public abbrev Harm (k : ℕ) : Submodule ℝ (Pk k) :=
  LinearMap.ker (laplacianPk k)

/-- Membership in `Harm k` is equivalent to vanishing of `laplacianPk k`. -/
@[simp] public lemma mem_Harm_iff {k : ℕ} (p : Pk k) :
    p ∈ Harm k ↔ laplacianPk k p = 0 := Iff.rfl

attribute [grind =] mem_Harm_iff

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic
