-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Laplacian identities involving `r²`

This file provides a small algebraic toolkit for Laplacian computations in `24` variables,
centered on the polynomial `r² = ∑ᵢ X i ^ 2`. The main lemma `laplacian_r2_mul` expands the
Laplacian of `r2 * Q` in terms of `Q`, the Euler operator `∑ᵢ X i * ∂ᵢ Q`, and `laplacian Q`.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.R2Laplacian

noncomputable section

open scoped BigOperators
open Finset MvPolynomial
open Harmonic

-- Prevent expensive unfolding of the Laplacian definition during elaboration/reduction.
attribute [local irreducible] Harmonic.laplacian

/-- The polynomial `r² = ∑ᵢ X i ^ 2` in `24` variables. -/
@[expose] public noncomputable def r2 : Poly :=
  (univ : Finset Var).sum (fun i => (X i : Poly) ^ (2 : ℕ))

private lemma pderiv_r2 (i : Var) :
    MvPolynomial.pderiv i r2 = (C (2 : ℝ) : Poly) * (X i : Poly) := by
  -- Differentiate termwise; only the `i`-th term survives.
  have hterm (j : Var) :
      MvPolynomial.pderiv i ((X j : Poly) ^ (2 : ℕ)) =
        if j = i then (C (2 : ℝ) : Poly) * (X i : Poly) else 0 := by
    by_cases h : j = i
    · subst j
      -- `∂ᵢ (Xᵢ^2) = 2 * Xᵢ`.
      -- Use the product rule on `Xᵢ * Xᵢ`.
      calc
        MvPolynomial.pderiv i ((X i : Poly) ^ (2 : ℕ))
            = MvPolynomial.pderiv i ((X i : Poly) * (X i : Poly)) := by simp [pow_two]
        _ = MvPolynomial.pderiv i (X i : Poly) * (X i : Poly) +
              (X i : Poly) * MvPolynomial.pderiv i (X i : Poly) := by
                simp
        _ = (X i : Poly) + (X i : Poly) := by simp
        _ = (2 : Poly) * (X i : Poly) := by
              simpa using! (two_mul (X i : Poly)).symm
        _ = (C (2 : ℝ) : Poly) * (X i : Poly) := by
              -- Rewrite `2 : Poly` as `C (2:ℝ)`.
              simpa using! congrArg (fun t : Poly => t * (X i : Poly))
                (MvPolynomial.C_eq_coe_nat (σ := Var) (R := ℝ) 2).symm
        _ = if i = i then (C (2 : ℝ) : Poly) * (X i : Poly) else 0 := by simp
    · have hX : MvPolynomial.pderiv i (X j : Poly) = 0 := by
        simpa using! (MvPolynomial.pderiv_X_of_ne (R := ℝ) (i := i) (j := j) h)
      -- If `∂ᵢ(Xⱼ) = 0` then `∂ᵢ(Xⱼ^2) = 0`.
      simp [pow_two, hX, h]
  -- Push `pderiv` through the finite sum.
  simp [r2, hterm]

private lemma pderiv_pderiv_r2 (i : Var) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i r2) = (C (2 : ℝ) : Poly) := by
  rw [pderiv_r2 (i := i)]
  -- Differentiate `C 2 * X i`.
  simp

private lemma pderiv_pderiv_r2_mul_term (Q : Poly) (i : Var) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i (r2 * Q)) =
      (C (2 : ℝ) : Poly) * Q +
        (C (4 : ℝ) : Poly) * ((X i : Poly) * MvPolynomial.pderiv i Q) +
          r2 * MvPolynomial.pderiv i (MvPolynomial.pderiv i Q) := by
  have h1 : MvPolynomial.pderiv i (r2 * Q) =
      MvPolynomial.pderiv i r2 * Q + r2 * MvPolynomial.pderiv i Q := by
    simpa using! (MvPolynomial.pderiv_mul (i := i) (f := r2) (g := Q))
  rw [h1]
  have h2 :
      MvPolynomial.pderiv i (MvPolynomial.pderiv i r2 * Q + r2 * MvPolynomial.pderiv i Q) =
        (MvPolynomial.pderiv i (MvPolynomial.pderiv i r2) * Q +
            MvPolynomial.pderiv i r2 * MvPolynomial.pderiv i Q) +
          (MvPolynomial.pderiv i r2 * MvPolynomial.pderiv i Q +
            r2 * MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) := by
    simp [add_left_comm, add_comm, mul_comm]
  rw [h2, pderiv_pderiv_r2 (i := i), pderiv_r2 (i := i)]
  set D : Poly := MvPolynomial.pderiv i Q
  have hdouble :
      (X i : Poly) * ((C (2 : ℝ) : Poly) * D) + (X i : Poly) * ((C (2 : ℝ) : Poly) * D) =
              (X i : Poly) * ((C (4 : ℝ) : Poly) * D) := by
    calc
      (X i : Poly) * ((C (2 : ℝ) : Poly) * D) + (X i : Poly) * ((C (2 : ℝ) : Poly) * D)
          = (X i : Poly) * (((C (2 : ℝ) : Poly) * D) + ((C (2 : ℝ) : Poly) * D)) := by
              rw [← mul_add]
      _ = (X i : Poly) * (((C (2 : ℝ) : Poly) + (C (2 : ℝ) : Poly)) * D) := by
            grind only
      _ = (X i : Poly) * ((C (4 : ℝ) : Poly) * D) := by
            have hC : (C (2 : ℝ) : Poly) + (C (2 : ℝ) : Poly) = (C (4 : ℝ) : Poly) := by
              calc
                (C (2 : ℝ) : Poly) + (C (2 : ℝ) : Poly) = (C ((2 : ℝ) + (2 : ℝ)) : Poly) :=
                  (MvPolynomial.C_add (σ := Var) (R := ℝ) (a := (2 : ℝ)) (a' := (2 : ℝ))).symm
                _ = (C (4 : ℝ) : Poly) := by
                      norm_num
            simp [hC]
  simp [D, hdouble, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]

private lemma sum_pderiv_pderiv_r2_mul_split (Q : Poly) :
    (univ : Finset Var).sum (fun i => MvPolynomial.pderiv i (MvPolynomial.pderiv i (r2 * Q))) =
      (univ : Finset Var).sum (fun _i => (C (2 : ℝ) : Poly) * Q) +
        (univ : Finset Var).sum (fun i =>
          (C (4 : ℝ) : Poly) * ((X i : Poly) * MvPolynomial.pderiv i Q)) +
          (univ : Finset Var).sum (fun i =>
            r2 * MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) := by
  have hrewrite :
      (univ : Finset Var).sum (fun i => MvPolynomial.pderiv i (MvPolynomial.pderiv i (r2 * Q))) =
        (univ : Finset Var).sum (fun i =>
          (C (2 : ℝ) : Poly) * Q +
            ((C (4 : ℝ) : Poly) * ((X i : Poly) * MvPolynomial.pderiv i Q) +
              r2 * MvPolynomial.pderiv i (MvPolynomial.pderiv i Q))) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa [add_assoc] using! (pderiv_pderiv_r2_mul_term (Q := Q) (i := i))
  rw [hrewrite]
  simp [Finset.sum_add_distrib, add_assoc]

/-- Formula for `laplacian (r2 * Q)` in `24` variables. -/
public lemma laplacian_r2_mul (Q : Poly) :
    laplacian (r2 * Q) =
      (C (48 : ℝ) : Poly) * Q +
        (C (4 : ℝ) : Poly) *
          ((univ : Finset Var).sum (fun i => (X i : Poly) * MvPolynomial.pderiv i Q)) +
          r2 * laplacian Q := by
  -- Expand the Laplacian as a `Finset` sum of second derivatives.
  rw [laplacian_apply]
  -- Convert to a plain `univ`-sum and split it using `sum_pderiv_pderiv_r2_mul_split`.
  change
    (univ : Finset Var).sum (fun i => MvPolynomial.pderiv i (MvPolynomial.pderiv i (r2 * Q))) = _
  rw [sum_pderiv_pderiv_r2_mul_split (Q := Q)]
  -- Now simplify each of the three sums.
  have hcard : (univ : Finset Var).card = 24 := by simp
  -- Simplify the three sums produced by `sum_pderiv_pderiv_r2_mul_split`.
  -- Simplify the first sum (`24` copies of the same term).
  have hconst :
      (univ : Finset Var).sum (fun _i => (C (2 : ℝ) : Poly) * Q) = (C (48 : ℝ) : Poly) * Q := by
    have hNat : 24 * 2 = (48 : ℕ) := by decide
    have hReal : (24 : ℝ) * (2 : ℝ) = (48 : ℝ) := by
      norm_num
    have hCmul : (C (24 : ℝ) : Poly) * (C (2 : ℝ) : Poly) = (C (48 : ℝ) : Poly) := by
      calc
        (C (24 : ℝ) : Poly) * (C (2 : ℝ) : Poly) = (C ((24 : ℝ) * (2 : ℝ)) : Poly) := by
          simp
        _ = (C (48 : ℝ) : Poly) := by simp [hReal]
    have h24 : (24 : Poly) = (C (24 : ℝ) : Poly) := by
      simpa using! (MvPolynomial.C_eq_coe_nat (σ := Var) (R := ℝ) 24).symm
    calc
      (univ : Finset Var).sum (fun _i => (C (2 : ℝ) : Poly) * Q) =
          (24 : ℕ) • ((C (2 : ℝ) : Poly) * Q) := by
            simp [Finset.sum_const, hcard]
      _ = ((24 : Poly) * ((C (2 : ℝ) : Poly) * Q)) := by
            simp [nsmul_eq_mul]
      _ = ((C (24 : ℝ) : Poly) * ((C (2 : ℝ) : Poly) * Q)) := by
            simp [h24]
      _ = (((C (24 : ℝ) : Poly) * (C (2 : ℝ) : Poly)) * Q) := by
            simp [mul_assoc]
      _ = (C (48 : ℝ) : Poly) * Q := by
            simp [hCmul]
  rw [hconst]
  simp [Finset.mul_sum, laplacian_apply]

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.R2Laplacian
