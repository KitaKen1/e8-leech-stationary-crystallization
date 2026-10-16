-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.AdjointOpsFixed
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Linear operators for the Fischer inner product

This file sets up the basic operators needed for the zonal-kernel / Gegenbauer bridge:
* `lin y` as the polynomial `x ↦ ⟪x,y⟫`,
* multiplication by `lin y` on homogeneous pieces, and the corresponding directional derivative,
* adjointness with respect to the Fischer inner product, and
* the Laplacian identity `Δ (lin y * p) = 2 * D_y p + (lin y) * Δ p`.

Only `lin` and its basic properties are part of the public API; the remaining operators are kept
private to this file.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Finset Finsupp MvPolynomial

/-- A point in `ℝ^{24}` written as a coordinate function `Var → ℝ`. -/
public abbrev Point : Type := Var → ℝ

namespace LinOps

/-- The linear form `x ↦ ⟪x,y⟫` as a polynomial in the `x` variables. -/
@[expose]
public noncomputable def lin (y : Point) : Poly :=
  (univ : Finset Var).sum (fun i => C (y i) * X i)

/-- Unfolding lemma for `lin`. -/
public lemma lin_apply (y : Point) :
    lin y = (univ : Finset Var).sum (fun i => C (y i) * X i) :=
  rfl

/-- The linear form `lin y` is homogeneous of degree `1`. -/
public lemma isHomogeneous_lin (y : Point) : (lin y).IsHomogeneous 1 := by
  refine MvPolynomial.IsHomogeneous.sum (s := (univ : Finset Var))
      (φ := fun i => C (y i) * X i) (n := 1) ?_
  intro i hi
  simpa using! (MvPolynomial.isHomogeneous_C_mul_X (R := ℝ) (σ := Var) (y i) i)

/-- Differentiating `lin y` with respect to `X i` yields the constant polynomial `C (y i)`. -/
@[simp] public lemma pderiv_lin (y : Point) (i : Var) :
    MvPolynomial.pderiv i (lin y) = (C (y i) : Poly) := by
  -- Differentiate termwise; only the `i`-summand contributes.
  -- `∂ᵢ (C a * X j) = if j = i then C a else 0`.
  have hterm (j : Var) :
      MvPolynomial.pderiv i (C (y j) * (X j : Poly)) =
        if j = i then (C (y i) : Poly) else 0 := by
    by_cases h : j = i
    · subst h
      simp
    · have : MvPolynomial.pderiv i (X j : Poly) = 0 := by
        simpa using! (MvPolynomial.pderiv_X_of_ne (R := ℝ) (i := i) (j := j) h)
      simp [this, h]
  -- Push `pderiv` through the finite sum.
  simp [lin, hterm]

@[simp] private lemma pderiv_pderiv_lin (y : Point) (i : Var) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i (lin y)) = 0 := by
  -- Use `pderiv_lin` and `pderiv_C`.
  simp [pderiv_lin]

end LinOps

namespace Fischer

open Harmonic

local notation "Pk" => Fischer.Pk

open LinOps

/-- Multiply by the linear form `lin y`, shifting degree `k ↦ k+1`. -/
private noncomputable def mulLinPk (k : ℕ) (y : Point) : Pk k →ₗ[ℝ] Pk (k + 1) :=
  (univ : Finset Var).sum (fun i => (y i) • (mulXPk (k := k) i))

/-- Directional derivative `D_y := ∑ᵢ yᵢ ∂ᵢ`, shifting degree `k+1 ↦ k`. -/
private noncomputable def pderivLinPk (k : ℕ) (y : Point) : Pk (k + 1) →ₗ[ℝ] Pk k :=
  (univ : Finset Var).sum (fun i => (y i) • (pderivPk (k := k) i))

lemma mulLinPk_apply (k : ℕ) (y : Point) (p : Pk k) :
    mulLinPk (k := k) y p =
      (univ : Finset Var).sum (fun i => (y i) • (mulXPk (k := k) i p)) := by
  simp [mulLinPk, LinearMap.sum_apply]

lemma pderivLinPk_apply (k : ℕ) (y : Point) (q : Pk (k + 1)) :
    pderivLinPk (k := k) y q =
      (univ : Finset Var).sum (fun i => (y i) • (pderivPk (k := k) i q)) := by
  simp [pderivLinPk, LinearMap.sum_apply]

lemma inner_mulLinPk_eq_inner_pderivLinPk (k : ℕ) (y : Point) (p : Pk k) (q : Pk (k + 1)) :
    ⟪mulLinPk (k := k) y p, q⟫ = ⟪p, pderivLinPk (k := k) y q⟫ := by
  -- Expand the sum in `mulLinPk` and `pderivLinPk`, then reduce to the `Xᵢ ⟂ ∂ᵢ` adjointness.
  rw [mulLinPk_apply (k := k) (y := y) (p := p)]
  rw [pderivLinPk_apply (k := k) (y := y) (q := q)]
  -- Expand the inner products against the sums.
  rw [sum_inner]
  rw [inner_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Termwise: `⟪y i • (Xᵢ p), q⟫ = ⟪p, y i • (∂ᵢ q)⟫`.
  calc
    ⟪y i • (mulXPk (k := k) i p), q⟫
        = (y i) * ⟪mulXPk (k := k) i p, q⟫ := by
            simpa [smul_eq_mul] using!
              (inner_smul_left_eq_smul (x := (mulXPk (k := k) i p)) (y := q) (r := y i))
    _ = (y i) * ⟪p, pderivPk (k := k) i q⟫ := by
            have h :
                ⟪mulXPk (k := k) i p, q⟫ = ⟪p, pderivPk (k := k) i q⟫ := by
              simpa using! (inner_mulXPk_eq_inner_pderivPk (k := k) (i := i) (p := p) (q := q))
            simp [h]
    _ = ⟪p, y i • (pderivPk (k := k) i q)⟫ := by
            simpa [smul_eq_mul] using!
              (inner_smul_right_eq_smul (x := p) (y := (pderivPk (k := k) i q)) (r := y i)).symm

end Fischer

namespace LinOps

open Harmonic

open Fischer

local notation "Pk" => Fischer.Pk

lemma laplacian_lin_mul_aux (y : Point) (Q : Poly) :
    Harmonic.laplacian (LinOps.lin y * Q) =
      (C (2 : ℝ) : Poly) *
          (univ : Finset Var).sum (fun i => (C (y i) : Poly) * MvPolynomial.pderiv i Q) +
        (LinOps.lin y) * Harmonic.laplacian Q := by
  -- Termwise computation: `∂ᵢ² (lin y * Q) = 2 * C(y i) * ∂ᵢ Q + (lin y) * ∂ᵢ² Q`.
  have hC2 : (2 : Poly) = (C (2 : ℝ) : Poly) := by
    simpa using! (MvPolynomial.C_eq_coe_nat (σ := Var) (R := ℝ) 2).symm
  have hterm (i : Var) :
      (MvPolynomial.pderiv i) (MvPolynomial.pderiv i (LinOps.lin y * Q)) =
        (C (2 : ℝ) : Poly) * ((C (y i) : Poly) * MvPolynomial.pderiv i Q) +
          (LinOps.lin y) * (MvPolynomial.pderiv i) (MvPolynomial.pderiv i Q) := by
    -- Two Leibniz rules plus `pderiv_lin` (and `pderiv_C`).
    have :
        (MvPolynomial.pderiv i) (MvPolynomial.pderiv i (LinOps.lin y * Q)) =
          ((2 : Poly) * ((C (y i) : Poly) * MvPolynomial.pderiv i Q)) +
            (LinOps.lin y) * (MvPolynomial.pderiv i) (MvPolynomial.pderiv i Q) := by
      -- `simp` leaves the two identical terms as `t + t`; rewrite them as `2 * t`.
      simp [LinOps.pderiv_lin, add_left_comm, add_comm, mul_comm,
        (two_mul ((C (y i) : Poly) * MvPolynomial.pderiv i Q)).symm]
    simpa [hC2] using! this
  -- Expand the Laplacian as a sum of second partial derivatives and sum the termwise identity.
  rw [Harmonic.laplacian_apply]
  have hsum :
      (univ : Finset Var).sum (fun i =>
          (MvPolynomial.pderiv i) (MvPolynomial.pderiv i (LinOps.lin y * Q))) =
        (univ : Finset Var).sum (fun i =>
          (C (2 : ℝ) : Poly) * ((C (y i) : Poly) * MvPolynomial.pderiv i Q) +
            (LinOps.lin y) * (MvPolynomial.pderiv i) (MvPolynomial.pderiv i Q)) := by
    simp_all
  rw [hsum, Finset.sum_add_distrib]
  simp [Finset.mul_sum, Harmonic.laplacian_apply]

/-- Laplacian identity: `Δ (lin y * Q) = 2 * (∑ᵢ yᵢ ∂ᵢ Q) + (lin y) * Δ Q`. -/
lemma laplacian_lin_mul (y : Point) (Q : Poly) :
    Harmonic.laplacian (LinOps.lin y * Q) =
      (C (2 : ℝ) : Poly) *
          (univ : Finset Var).sum (fun i => (C (y i) : Poly) * MvPolynomial.pderiv i Q) +
        (LinOps.lin y) * Harmonic.laplacian Q :=
  laplacian_lin_mul_aux (y := y) (Q := Q)

end LinOps

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD
