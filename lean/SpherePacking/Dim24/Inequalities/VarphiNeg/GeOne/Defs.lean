/-
Negativity of `varphi(it)` for `t ≥ 1` (Appendix A, Lemma `phinonpos`, first case).
-/
module
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
public import SpherePacking.ModularForms.EisensteinBase
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.List.GetD
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order


/-!
# Coefficient model for `varphi_num`

This file defines the rational coefficient functions used to model the `q`-series of
`varphi_num(it t)` in the `t ≥ 1` part of Appendix A.

We use the standard `q`-expansions
`E₂ = 1 - 24 * ∑ σ₁(n) q^n`, `E₄ = 1 + 240 * ∑ σ₃(n) q^n`, `E₆ = 1 - 504 * ∑ σ₅(n) q^n`
and take products using Cauchy convolution (antidiagonals).

## Main definitions
* `varphi_num`
* `coeffVarphiNum`
-/

open scoped BigOperators
open scoped ArithmeticFunction.sigma
open UpperHalfPlane
open SlashInvariantFormClass ModularFormClass

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

namespace VarphiNegGeOne

/-- The numerator `varphi · Δ²` appearing in Appendix A (called `phinum` in `appendix.txt`). -/
@[expose]
public def varphi_num (z : ℍ) : ℂ :=
  (25 * (E₄ z) ^ 4 - 49 * (E₆ z) ^ 2 * (E₄ z))
      + 48 * (E₆ z) * (E₄ z) ^ 2 * (E₂ z)
      + ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2) * (E₂ z) ^ 2

/-- The identity `varphi_num = varphi * Δ^2`, obtained by unfolding the definition of `varphi`. -/
public lemma varphi_num_eq_varphi_mul_Delta_sq (z : ℍ) :
    varphi_num z = varphi z * (Δ z) ^ 2 := by
  -- This is just unfolding the definition of `varphi`.
  have hΔ : (Δ z) ≠ 0 := Δ_ne_zero z
  simp [Dim24.varphi, varphi_num, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hΔ]

/-!
## Eisenstein coefficients

We package the coefficients of the standard `q`-expansions of `E₂`, `E₄`, and `E₆` as rational
sequences.
-/
/-- Coefficients for the `q`-series of `E₂` (`1 - 24 * ∑ σ₁(n) q^n`). -/
@[expose] public def coeffE2 : ℕ → ℚ := fun n => if n = 0 then 1 else (-24 : ℚ) * (σ 1 n)

/-- Coefficients for the `q`-series of `E₄` (`1 + 240 * ∑ σ₃(n) q^n`). -/
@[expose] public def coeffE4 : ℕ → ℚ := fun n => if n = 0 then 1 else (240 : ℚ) * (σ 3 n)

/-- Coefficients for the `q`-series of `E₆` (`1 - 504 * ∑ σ₅(n) q^n`). -/
@[expose] public def coeffE6 : ℕ → ℚ := fun n => if n = 0 then 1 else (-504 : ℚ) * (σ 5 n)

/-- Cauchy convolution of coefficient sequences, encoding multiplication of `q`-series. -/
@[expose]
public def conv (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

/-- Coefficients for the `q`-series of `E₂^2`, computed via `conv`. -/
@[expose] public def coeffE2Sq : ℕ → ℚ := fun n => conv coeffE2 coeffE2 n

/-- Coefficients for the `q`-series of `E₄^2`, computed via `conv`. -/
@[expose] public def coeffE4Sq : ℕ → ℚ := fun n => conv coeffE4 coeffE4 n

/-- Coefficients for the `q`-series of `E₄^3`, computed via `conv`. -/
@[expose] public def coeffE4Cube : ℕ → ℚ := fun n => conv coeffE4Sq coeffE4 n

/-- Coefficients for the `q`-series of `E₄^4`, computed via `conv`. -/
@[expose] public def coeffE4Fourth : ℕ → ℚ := fun n => conv coeffE4Sq coeffE4Sq n

/-- Coefficients for the `q`-series of `E₆^2`, computed via `conv`. -/
@[expose] public def coeffE6Sq : ℕ → ℚ := fun n => conv coeffE6 coeffE6 n

/-- Helper linear combination of `E₄^3` and `E₆^2` coefficients used in `coeffVarphiNum`. -/
@[expose]
public def coeffLin : ℕ → ℚ :=
  fun m => -(49 * coeffE4Cube m) + (25 : ℚ) * coeffE6Sq m

/-- Rewrite `coeffLin` as a linear combination with coefficients `-49` and `25`. -/
public lemma coeffLin_eq_lincomb :
    coeffLin = fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m := by
  funext m
  simp [coeffLin]

/-- Coefficient function for the `q`-series of `varphi_num`, assembled from Eisenstein data. -/
@[expose]
public def coeffVarphiNum : ℕ → ℚ :=
  fun n =>
    (25 : ℚ) * coeffE4Fourth n
      - (49 : ℚ) * (conv coeffE6Sq coeffE4 n)
      + (48 : ℚ) * (conv (conv coeffE6 coeffE4Sq) coeffE2 n)
      + (conv coeffLin coeffE2Sq n)


end SpherePacking.Dim24.VarphiNegGeOne
