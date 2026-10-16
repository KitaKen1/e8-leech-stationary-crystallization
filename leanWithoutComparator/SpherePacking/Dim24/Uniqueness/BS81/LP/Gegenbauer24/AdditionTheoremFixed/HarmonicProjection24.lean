module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.ZonalKernelPSD
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.LaplacianR2PowLinPow
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.FischerDecompositionFixed

/-!
# Explicit harmonic projection in dimension 24

This file is the first algebraic step toward the addition-theorem bridge. We build an explicit
degree-`k` polynomial in the `x` variables that is congruent to `(⟪x,y⟫)^k / k!` modulo `r²`, and
use the Fischer decomposition
`Pk k = Harm k ⊕ range (mulR2Pk (k := k - 2))`
to identify it with the harmonic projection `Φ k y` defined in `ZonalKernelPSD.lean`.

No results from `AdditionTheorem/` are used.

## Main definitions
* `yPoint`, `t`, `r2`
* `aCoeff`, `harmApprox`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.Zonal
noncomputable section

open scoped RealInnerProductSpace

open Finset MvPolynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open PSD PSD.Harmonic PSD.LinOps PSD.R2Laplacian

/-- View `y : ℝ²⁴` as a coordinate function `Fin 24 → ℝ`. -/
@[expose] public def yPoint (y : ℝ²⁴) : Fin 24 → ℝ := fun i => y i

/-- The linear polynomial representing `x ↦ ⟪x, y⟫` in the `x` variables. -/
@[expose] public def t (y : ℝ²⁴) : MvPolynomial (Fin 24) ℝ := LinOps.lin (yPoint y)

/-- The quadratic polynomial `r² = ∑ i, X i ^ 2`. -/
@[expose] public def r2 : MvPolynomial (Fin 24) ℝ := (PSD.R2Laplacian.r2 : MvPolynomial (Fin 24) ℝ)

lemma t_eq (y : ℝ²⁴) :
    t y = (PSD.ZonalKernel.lin y) := rfl

/-!
### Coefficients for the harmonic correction

For fixed `k` we define coefficients `a k j` by the recursion that makes
`∑_{j≤k/2} a k j * r2^j * t^(k-2j)` harmonic (under the unit-sphere specialization `‖y‖=1`).

At this stage we only set up the recursion and the finite sum; the harmonicity proof is in the
next file.
-/

/-- The coefficient `A k j` in the Laplacian recursion for `r2^j * t^(k-2j)`. -/
@[expose] public def A (k j : ℕ) : ℕ :=
  2 * j * (2 * (k - 2 * j) + 2 * j + 22)

/-- The coefficient `B k j` in the Laplacian recursion for `r2^j * t^(k-2j)`. -/
@[expose] public def B (k j : ℕ) : ℕ :=
  (k - 2 * j) * ((k - 2 * j) - 1)

/-- Recursive coefficients for the harmonic correction of `t^k / k!`. -/
@[expose] public def aCoeff (k : ℕ) : ℕ → ℝ
  | 0 => (Nat.factorial k : ℝ)⁻¹
  | j + 1 =>
      -- `a_{j+1} = - a_j * B(k,j) / A(k, j+1)` (unit-sphere specialization).
      - (aCoeff k j) * ((B k j : ℕ) : ℝ) / ((A k (j + 1) : ℕ) : ℝ)

/-- Base value of the recursion defining `aCoeff`. -/
public lemma aCoeff_zero (k : ℕ) : aCoeff k 0 = (Nat.factorial k : ℝ)⁻¹ := rfl

/-- Recursive step for `aCoeff`. -/
public lemma aCoeff_succ (k j : ℕ) :
    aCoeff k (j + 1) =
      - (aCoeff k j) * ((B k j : ℕ) : ℝ) / ((A k (j + 1) : ℕ) : ℝ) := rfl

/-- The explicit correction `∑ aCoeff k j • r2^j * t^(k-2j)` used to build a harmonic element. -/
@[expose] public def harmApprox (k : ℕ) (y : ℝ²⁴) : MvPolynomial (Fin 24) ℝ :=
  (Finset.range (k / 2 + 1)).sum (fun j =>
    (aCoeff k j) • ((r2 ^ j) * (t y) ^ (k - 2 * j)))

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.Zonal
