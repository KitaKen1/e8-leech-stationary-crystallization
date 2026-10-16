-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.LaplacianLinPow
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.R2Laplacian
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring

/-!
# Laplacian of `r²^j * (lin y)^m` in 24 variables

This is the algebraic core for constructing zonal harmonic projections: the Laplacian maps the
`(j,m)` monomial to a linear combination of the two nearby monomials `(j-1,m)` and `(j,m-2)`.

## Main statements
* `laplacian_r2_pow_mul_lin_pow`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalProjector

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

open Harmonic R2Laplacian LinOps

private lemma isHomogeneous_r2 : (R2Laplacian.r2 : Poly).IsHomogeneous 2 := by
  -- Each summand is `X i ^ 2`.
  refine MvPolynomial.IsHomogeneous.sum (s := (univ : Finset Var))
      (φ := fun i => (X i : Poly) ^ (2 : ℕ)) (n := 2) ?_
  intro i hi
  simpa using! (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (σ := Var) i 2)

private lemma isHomogeneous_r2_pow (j : ℕ) :
    ((R2Laplacian.r2 : Poly) ^ j).IsHomogeneous (2 * j) := by
  simpa using! (isHomogeneous_r2).pow j

private lemma isHomogeneous_lin_pow (y : Point) (m : ℕ) :
    ((lin y : Poly) ^ m).IsHomogeneous m := by
  simpa using! (LinOps.isHomogeneous_lin (y := y)).pow m

private lemma isHomogeneous_r2_pow_mul_lin_pow (y : Point) (j m : ℕ) :
    ((R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m).IsHomogeneous (2 * j + m) := by
  simpa using! (isHomogeneous_r2_pow (j := j)).mul (isHomogeneous_lin_pow (y := y) (m := m))

private lemma sum_X_mul_pderiv_r2_pow_mul_lin_pow (y : Point) (j m : ℕ) :
    (univ : Finset Var).sum (fun i =>
        (X i : Poly) * MvPolynomial.pderiv i ((R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m)) =
      (2 * j + m) • ((R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m) := by
  -- Euler's identity for homogeneous polynomials.
  -- Avoid `simp` here: `pderiv` has many simp lemmas and we want to keep it unexpanded.
  simpa using!
    (MvPolynomial.IsHomogeneous.sum_X_mul_pderiv
      (φ := ((R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m)) (n := 2 * j + m)
      (isHomogeneous_r2_pow_mul_lin_pow (y := y) (j := j) (m := m)))

private lemma sum_X_mul_pderiv_r2_pow_mul_lin_pow_C (y : Point) (j m : ℕ) :
    (univ : Finset Var).sum (fun i => (X i : Poly) * MvPolynomial.pderiv i
        ((R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m)) =
      (C ((2 * j + m : ℕ) : ℝ) : Poly) * ((R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m) := by
  have hEuler := sum_X_mul_pderiv_r2_pow_mul_lin_pow (y := y) (j := j) (m := m)
  -- Rewrite `n • p` as multiplication by the constant polynomial `C n`.
  -- Using `calc` avoids triggering simp lemmas for `pderiv` on the LHS.
  calc
    (univ : Finset Var).sum (fun i => (X i : Poly) * MvPolynomial.pderiv i
        ((R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m))
        = (2 * j + m) • ((R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m) := hEuler
    _ = (((2 * j + m : ℕ) : ℝ) • ((R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m)) :=
          Eq.symm (Nat.cast_smul_eq_nsmul ℝ (2 * j + m) (r2 ^ j * lin y ^ m))
    _ = (C ((2 * j + m : ℕ) : ℝ) : Poly) * ((R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m) :=
          smul_eq_C_mul (r2 ^ j * lin y ^ m) ↑(2 * j + m)

/-- Laplacian of `r²^j * (lin y)^m` in `24` variables. -/
public lemma laplacian_r2_pow_mul_lin_pow (y : Point) (j m : ℕ) :
    laplacian (((R2Laplacian.r2 : Poly) ^ j) * (lin y : Poly) ^ m) =
      (C ((2 * j * (2 * m + 2 * j + 22) : ℕ) : ℝ) : Poly) *
          (R2Laplacian.r2 : Poly) ^ (j - 1) * (lin y : Poly) ^ m +
        (C (((m * (m - 1) : ℕ) : ℝ) * (ZonalProjector.sumSq y)) : Poly) *
          (R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ (m - 2) := by
  -- Induction on `j`.
  induction j with
  | zero =>
      -- `j = 0`: use `laplacian_lin_pow`.
      simp [ZonalProjector.laplacian_lin_pow (y := y) (m := m), ZonalProjector.sumSq]
  | succ j ih =>
      -- Write `r2^(j+1) * t^m = r2 * (r2^j * t^m)`.
      -- Abbreviate the base term `Q = r2^j * t^m`.
      set Q : Poly := ((R2Laplacian.r2 : Poly) ^ j) * (lin y : Poly) ^ m
      have hEuler : (univ : Finset Var).sum (fun i =>
          (X i : Poly) * MvPolynomial.pderiv i Q) =
            (C ((2 * j + m : ℕ) : ℝ) : Poly) * Q := by
        simpa [Q] using! sum_X_mul_pderiv_r2_pow_mul_lin_pow_C (y := y) (j := j) (m := m)
      -- Start from `Δ(r2*Q)` and rewrite using Euler + IH.
      have hΔ :
          laplacian ((R2Laplacian.r2 : Poly) * Q) =
            (C (48 : ℝ) : Poly) * Q +
              (C (4 : ℝ) : Poly) * ((univ : Finset Var).sum (fun i => (X i : Poly) *
                MvPolynomial.pderiv i Q)) +
                (R2Laplacian.r2 : Poly) * laplacian Q := by
        simpa using! (R2Laplacian.laplacian_r2_mul (Q := Q))
      -- A closed-form coefficient identity for the `j`-recurrence.
      have hcoeff :
          (48 : ℝ) + 4 * ((2 * j + m : ℕ) : ℝ) + ((2 * j * (2 * m + 2 * j + 22) : ℕ) : ℝ) =
            ((2 * (j + 1) * (2 * m + 2 * (j + 1) + 22) : ℕ) : ℝ) := by
        -- Push casts and use `ring`.
        simp [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] ; ring
      -- Main computation.
      calc
        laplacian (((R2Laplacian.r2 : Poly) ^ (j + 1)) * (lin y : Poly) ^ m)
            = laplacian ((R2Laplacian.r2 : Poly) * Q) := by
                simp [Q, pow_succ, mul_assoc, mul_comm]
        _ = (C (48 : ℝ) : Poly) * Q +
              (C (4 : ℝ) : Poly) *
                ((univ : Finset Var).sum (fun i => (X i : Poly) * MvPolynomial.pderiv i Q)) +
              (R2Laplacian.r2 : Poly) * laplacian Q := hΔ
        _ = (C (48 : ℝ) : Poly) * Q +
              (C (4 : ℝ) : Poly) * ((C ((2 * j + m : ℕ) : ℝ) : Poly) * Q) +
              (R2Laplacian.r2 : Poly) * laplacian Q := by
                simp [hEuler]
        _ = (C (48 : ℝ) : Poly) * Q +
              (C (4 * ((2 * j + m : ℕ) : ℝ) : ℝ) : Poly) * Q +
              (R2Laplacian.r2 : Poly) * laplacian Q := by
                simp [mul_left_comm, mul_comm]
        _ = (C (48 : ℝ) : Poly) * Q +
              (C (4 * ((2 * j + m : ℕ) : ℝ) : ℝ) : Poly) * Q +
              (R2Laplacian.r2 : Poly) *
                ((C ((2 * j * (2 * m + 2 * j + 22) : ℕ) : ℝ) : Poly) *
                    (R2Laplacian.r2 : Poly) ^ (j - 1) * (lin y : Poly) ^ m +
                  (C (((m * (m - 1) : ℕ) : ℝ) * (ZonalProjector.sumSq y)) : Poly) *
                    (R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ (m - 2)) := by
                simpa [Q] using! congrArg (fun T => (C (48 : ℝ) : Poly) * Q +
                  (C (4 * ((2 * j + m : ℕ) : ℝ) : ℝ) : Poly) * Q + (R2Laplacian.r2 : Poly) * T) ih
        _ = (C ((48 : ℝ) + 4 * ((2 * j + m : ℕ) : ℝ) +
                  ((2 * j * (2 * m + 2 * j + 22) : ℕ) : ℝ)) : Poly) *
                (R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m +
              (C (((m * (m - 1) : ℕ) : ℝ) * (ZonalProjector.sumSq y)) : Poly) *
                (R2Laplacian.r2 : Poly) ^ (j + 1) * (lin y : Poly) ^ (m - 2) := by
                -- Distribute and collect the two target monomials.
                -- The first term simplifies automatically when `j=0` since its coefficient is `0`.
                -- Avoid a large `simp` call (can hit recursion-depth); split on `j`.
                cases j with
                | zero =>
                    simp [Q, mul_add, add_mul, pow_succ]
                    ring
                | succ j =>
                    -- Prefer `ring` over `simp`-AC (avoids recursion-depth).
                    simp [Q, mul_add, add_mul, pow_succ]
                    ring
        _ = (C (((2 * (j + 1) * (2 * m + 2 * (j + 1) + 22) : ℕ) : ℝ)) : Poly) *
                (R2Laplacian.r2 : Poly) ^ j * (lin y : Poly) ^ m +
              (C (((m * (m - 1) : ℕ) : ℝ) * (ZonalProjector.sumSq y)) : Poly) *
                (R2Laplacian.r2 : Poly) ^ (j + 1) * (lin y : Poly) ^ (m - 2) := by
                grind only

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalProjector
