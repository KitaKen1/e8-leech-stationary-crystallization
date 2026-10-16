-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.LinOps

/-!
# Laplacian of powers of the linear form `lin y`

For `t(x) = ⟪x,y⟫` viewed as an element of `MvPolynomial (Fin 24) ℝ` in the `x` variables, we show

`Δ (t^m) = m(m-1) (∑ i, y i ^ 2) t^(m-2)`.

The unit case `‖y‖ = 1` is obtained by rewriting `∑ i, y i ^ 2 = 1`.

## Main definitions
* `sumSq`

## Main statements
* `laplacian_lin_pow`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalProjector
noncomputable section

open scoped BigOperators RealInnerProductSpace

open Finset MvPolynomial

open LinOps Harmonic

/-- First partial derivative of `t^m` where `t = lin y`. -/
private lemma pderiv_lin_pow (y : Point) (i : Var) (m : ℕ) :
    MvPolynomial.pderiv i ((lin y : Poly) ^ m) =
      (C ((m : ℕ) : ℝ) : Poly) * (C (y i) : Poly) * (lin y : Poly) ^ (m - 1) := by
  -- `pderiv i (lin y) = C (y i)` from `LinOps`.
  simp [LinOps.pderiv_lin, mul_left_comm, mul_comm]

/-- Second partial derivative of `t^m` where `t = lin y`. -/
private lemma pderiv_pderiv_lin_pow (y : Point) (i : Var) (m : ℕ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i ((lin y : Poly) ^ m)) =
      (C ((m * (m - 1) : ℕ) : ℝ) : Poly) * (C ((y i) ^ (2 : ℕ)) : Poly) *
        (lin y : Poly) ^ (m - 2) := by
  -- Start from the first derivative and differentiate once more; only the power contributes.
  rw [pderiv_lin_pow (y := y) (i := i) (m := m)]
  simp [LinOps.pderiv_lin, Nat.cast_mul, Nat.sub_sub, pow_two, mul_assoc, mul_left_comm, mul_comm,
    MvPolynomial.C_mul]

/-- `∑ᵢ yᵢ^2` as an element of `ℝ`. -/
@[expose] public noncomputable def sumSq (y : Point) : ℝ :=
  (univ : Finset Var).sum (fun i => (y i) ^ (2 : ℕ))

/-- Unfolding lemma for `sumSq`. -/
@[simp] public lemma sumSq_def (y : Point) :
    sumSq y = (univ : Finset Var).sum (fun i => (y i) ^ (2 : ℕ)) :=
  rfl

/-- Laplacian of `t^m` where `t = lin y`. -/
public lemma laplacian_lin_pow (y : Point) (m : ℕ) :
    laplacian ((lin y : Poly) ^ m) =
      (C (((m * (m - 1) : ℕ) : ℝ) * sumSq y) : Poly) * (lin y : Poly) ^ (m - 2) := by
  rw [Harmonic.laplacian_apply]
  -- Rewrite each term using the second derivative formula.
  have hrewrite :
      (univ : Finset Var).sum (fun i =>
          (C ((m * (m - 1) : ℕ) : ℝ) : Poly) * (C ((y i) ^ (2 : ℕ)) : Poly) *
            (lin y : Poly) ^ (m - 2)) =
        (C ((m * (m - 1) : ℕ) : ℝ) : Poly) * (C (sumSq y) : Poly) * (lin y : Poly) ^ (m - 2) := by
    -- Factor out common terms and fold the sum into `sumSq`.
    simp [sumSq, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  -- Replace the summand with the closed form and then apply `hrewrite`.
  have hsum :
      (univ : Finset Var).sum (fun i =>
          MvPolynomial.pderiv i (MvPolynomial.pderiv i ((lin y : Poly) ^ m))) =
        (univ : Finset Var).sum (fun i =>
          (C ((m * (m - 1) : ℕ) : ℝ) : Poly) * (C ((y i) ^ (2 : ℕ)) : Poly) *
            (lin y : Poly) ^ (m - 2)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa using! (pderiv_pderiv_lin_pow (y := y) (i := i) (m := m))
  -- Assemble.
  rw [hsum, hrewrite]
  simp [sumSq, mul_assoc, mul_left_comm, mul_comm]

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalProjector
