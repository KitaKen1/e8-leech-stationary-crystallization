-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finsupp.Order
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Fischer adjointness: coefficient-level tools

For the Fischer inner product on the degree-`k` homogeneous piece `Pk k`, multiplication by `X i`
is adjoint to the partial derivative `∂ᵢ`. This file provides coefficient-level tools and defines
the degree-shifting maps `mulXPk` and `pderivPk`. The actual adjointness identity is proved in
`PSD/AdjointOpsFixed.lean`.

## Main definitions
* `mulXPk`, `pderivPk`

## Main statements
* `coeff_pderiv`
-/
namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
noncomputable section

open scoped BigOperators RealInnerProductSpace

open Finset Finsupp MvPolynomial

local notation "Pk" => Pk

/-!
### Coefficient formula for `pderiv`

`coeff d (∂ᵢ p) = (d i + 1) * coeff (d + eᵢ) p`.
-/

/-- Coefficient formula for `pderiv`: `coeff d (∂ᵢ p) = (d i + 1) * coeff (d + eᵢ) p`. -/
public lemma coeff_pderiv (i : Var) (p : Poly) (d : Var →₀ ℕ) :
    MvPolynomial.coeff d (MvPolynomial.pderiv i p) =
      ((d i + 1 : ℕ) : ℝ) * MvPolynomial.coeff (d + Finsupp.single i (1 : ℕ)) p := by
  -- This is linear in `p`, so it suffices to check it on monomials.
  have h :
      ∀ p : Poly, ∀ d : Var →₀ ℕ,
        MvPolynomial.coeff d (MvPolynomial.pderiv i p) =
          ((d i + 1 : ℕ) : ℝ) * MvPolynomial.coeff (d + Finsupp.single i (1 : ℕ)) p := by
    intro p
    -- `MvPolynomial.induction_on'` reduces to monomials + additivity.
    refine
      MvPolynomial.induction_on' (p := p)
        (P := fun p : Poly =>
          ∀ d : Var →₀ ℕ,
            MvPolynomial.coeff d (MvPolynomial.pderiv i p) =
              ((d i + 1 : ℕ) : ℝ) * MvPolynomial.coeff (d + Finsupp.single i (1 : ℕ)) p)
        (fun s a d => ?_)
        (fun p q hp hq d => by
          simp [hp d, hq d, mul_add, add_mul])
    -- Monomial case.
    by_cases hsi : s i = 0
    · have hsne : s ≠ d + Finsupp.single i (1 : ℕ) := by
        intro hs
        simp_all
      -- If `s i = 0`, then `pderiv i (monomial s a) = 0`.
      simp [MvPolynomial.pderiv_monomial, hsi, hsne]
    · -- If `s i ≠ 0`, then `s - eᵢ = d` forces `s = d + eᵢ`.
      by_cases hs : s = d + Finsupp.single i (1 : ℕ)
      · cases hs
        have hsub : (d + Finsupp.single i (1 : ℕ) : Var →₀ ℕ) - Finsupp.single i (1 : ℕ) = d := by
          exact add_tsub_cancel_right d (single i 1)
        -- Now `simp` reduces both sides to the same scalar multiple.
        simp [MvPolynomial.pderiv_monomial, hsub, mul_comm]
      · have hs' : s - Finsupp.single i (1 : ℕ) ≠ d := by
          intro hsd
          have :
              s - Finsupp.single i (1 : ℕ) + Finsupp.single i (1 : ℕ) =
                d + Finsupp.single i (1 : ℕ) := by
            simp [hsd]
          have :
              s = d + Finsupp.single i (1 : ℕ) := by
            simpa [Finsupp.sub_add_single_one_cancel (u := s) (i := i) hsi] using! this
          exact hs this
        simp [MvPolynomial.pderiv_monomial, hs, hs']
  exact h p d

/-!
### Degree-shifting maps: multiply by `X i` and `pderiv i`
-/

/-- Multiply by `X i`, shifting degree `k ↦ k+1`. -/
@[expose] public noncomputable def mulXPk (k : ℕ) (i : Var) : Pk k →ₗ[ℝ] Pk (k + 1) :=
  LinearMap.codRestrict (Pk (k + 1))
    ((LinearMap.mul ℝ Poly (X i)).comp (Submodule.subtype (Pk k))) (by
      intro p
      have hp : (p.1 : Poly).IsHomogeneous k :=
        (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) k (p := (p.1 : Poly))).1 p.2
      have hx : (X i : Poly).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X (R := ℝ) i
      have hmul : ((X i : Poly) * (p.1 : Poly)).IsHomogeneous (k + 1) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using! (hx.mul hp)
      assumption)

/-- Partial derivative `∂ᵢ`, shifting degree `k+1 ↦ k`. -/
@[expose] public noncomputable def pderivPk (k : ℕ) (i : Var) : Pk (k + 1) →ₗ[ℝ] Pk k :=
  LinearMap.codRestrict (Pk k)
    ((MvPolynomial.pderiv i).toLinearMap.comp (Submodule.subtype (Pk (k + 1)))) (by
      intro p
      have hp : (p.1 : Poly).IsHomogeneous (k + 1) :=
        (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) (k + 1) (p := p.1)).1 p.2
      refine
        (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) k
          (p := MvPolynomial.pderiv i p.1)).2 ?_
      simpa using! (hp.pderiv (i := i)))

end
end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
