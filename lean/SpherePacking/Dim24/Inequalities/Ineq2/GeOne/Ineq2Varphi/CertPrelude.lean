-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
public import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.AbsBoundQ
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.List.GetD
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Conv
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.QSeriesHelpers
public import SpherePacking.Dim24.Inequalities.Certificate.ZVArith


/-!
# Certificate: first 50 coefficients of `coeffVarphiNum`

We rewrite `coeffVarphiNum n` (a `ℚ` coefficient) as the cast of an explicit `ℤ` formula and
compute the first `NVarphi = 50` coefficients using truncated list arithmetic in `ℤ`.

## Main definitions
* `coeffVarphiNumZV` and `coeffVarphiNum_eq_cast`
* the truncated coefficient lists `coeffE2ListZV`, ... used downstream in the certificate
-/

noncomputable section

namespace SpherePacking.Dim24

open SpherePacking.Dim24.CertificateZV

namespace Ineq2Varphi

open scoped ArithmeticFunction.sigma
open AppendixA


lemma conv_cast_eq_mulFunZV (a b : ℕ → ℤ) (n : ℕ) :
    AppendixA.conv (fun m => (a m : ℚ)) (fun m => (b m : ℚ)) n = (mulFunZV a b n : ℚ) := by
  simpa [AppendixA.conv, mulFunZV, Int.cast_mul] using!
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (a i : ℚ) * (b j : ℚ)) n)

-- Base Eisenstein coefficients, but in `ℤ`.
/-- Coefficient function for the `q`-expansion of `E₂`, valued in `ℤ`. -/
@[expose] public def coeffE2ZV (n : ℕ) : ℤ := if n = 0 then 1 else (-24 : ℤ) * (σ 1 n)
/-- Coefficient function for the `q`-expansion of `E₄`, valued in `ℤ`. -/
@[expose] public def coeffE4ZV (n : ℕ) : ℤ := if n = 0 then 1 else (240 : ℤ) * (σ 3 n)
/-- Coefficient function for the `q`-expansion of `E₆`, valued in `ℤ`. -/
@[expose] public def coeffE6ZV (n : ℕ) : ℤ := if n = 0 then 1 else (-504 : ℤ) * (σ 5 n)

lemma coeffE2_eq_cast (n : ℕ) : (AppendixA.coeffE2 n) = (coeffE2ZV n : ℚ) := by
  by_cases hn : n = 0 <;> simp [AppendixA.coeffE2, coeffE2ZV, hn]

lemma coeffE4_eq_cast (n : ℕ) : (AppendixA.coeffE4 n) = (coeffE4ZV n : ℚ) := by
  by_cases hn : n = 0 <;> simp [AppendixA.coeffE4, coeffE4ZV, hn]

lemma coeffE6_eq_cast (n : ℕ) : (AppendixA.coeffE6 n) = (coeffE6ZV n : ℚ) := by
  by_cases hn : n = 0 <;> simp [AppendixA.coeffE6, coeffE6ZV, hn]

lemma coeffE2_fun_eq_cast : (AppendixA.coeffE2) = fun n => (coeffE2ZV n : ℚ) := by
  funext n; simpa using! (coeffE2_eq_cast n)

lemma coeffE4_fun_eq_cast : (AppendixA.coeffE4) = fun n => (coeffE4ZV n : ℚ) := by
  funext n; simpa using! (coeffE4_eq_cast n)

lemma coeffE6_fun_eq_cast : (AppendixA.coeffE6) = fun n => (coeffE6ZV n : ℚ) := by
  funext n; simpa using! (coeffE6_eq_cast n)

-- Intermediate coefficient functions in `ℤ` mirroring the `ℚ` ones.
/-- Coefficients of `(E₂)^2`, computed in `ℤ` by convolution. -/
@[expose] public def coeffE2SqZV (n : ℕ) : ℤ := mulFunZV coeffE2ZV coeffE2ZV n
/-- Coefficients of `(E₄)^2`, computed in `ℤ` by convolution. -/
@[expose] public def coeffE4SqZV (n : ℕ) : ℤ := mulFunZV coeffE4ZV coeffE4ZV n
/-- Coefficients of `(E₄)^3`, computed in `ℤ` by convolution. -/
@[expose] public def coeffE4CubeZV (n : ℕ) : ℤ := mulFunZV coeffE4SqZV coeffE4ZV n
/-- Coefficients of `(E₄)^4`, computed in `ℤ` by convolution. -/
@[expose] public def coeffE4FourthZV (n : ℕ) : ℤ := mulFunZV coeffE4SqZV coeffE4SqZV n
/-- Coefficients of `(E₆)^2`, computed in `ℤ` by convolution. -/
@[expose] public def coeffE6SqZV (n : ℕ) : ℤ := mulFunZV coeffE6ZV coeffE6ZV n

/-- Coefficients of the auxiliary linear combination `-49 * E₄^3 + 25 * E₆^2`, valued in `ℤ`. -/
@[expose] public def coeffLinZV (n : ℕ) : ℤ :=
  (-49 : ℤ) * coeffE4CubeZV n + (25 : ℤ) * coeffE6SqZV n

/-- Rational-valued coefficients of `-49 * E₄^3 + 25 * E₆^2` (the `ℚ` analogue of `coeffLinZV`). -/
@[expose] public def coeffLin : ℕ → ℚ :=
  fun n => (-49 : ℚ) * coeffE4Cube n + (25 : ℚ) * coeffE6Sq n

/--
Integer formula for `coeffVarphiNum`: coefficients of the numerator polynomial expressed in terms
of Eisenstein series coefficients.
-/
@[expose] public def coeffVarphiNumZV (n : ℕ) : ℤ :=
  (25 : ℤ) * coeffE4FourthZV n +
    (-(49 : ℤ)) * (mulFunZV coeffE6SqZV coeffE4ZV n) +
      (48 : ℤ) * (mulFunZV (fun m => mulFunZV coeffE6ZV coeffE4SqZV m) coeffE2ZV n) +
        (mulFunZV coeffLinZV coeffE2SqZV n)

lemma coeffE2Sq_eq_cast (n : ℕ) : (coeffE2Sq n) = (coeffE2SqZV n : ℚ) := by
  simpa [coeffE2Sq, coeffE2SqZV, coeffE2_fun_eq_cast] using!
    (conv_cast_eq_mulFunZV (a := coeffE2ZV) (b := coeffE2ZV) (n := n))

lemma coeffE4Sq_eq_cast (n : ℕ) : (coeffE4Sq n) = (coeffE4SqZV n : ℚ) := by
  simpa [coeffE4Sq, coeffE4SqZV, coeffE4_fun_eq_cast] using!
    (conv_cast_eq_mulFunZV (a := coeffE4ZV) (b := coeffE4ZV) (n := n))

lemma coeffE4Cube_eq_cast (n : ℕ) : (coeffE4Cube n) = (coeffE4CubeZV n : ℚ) := by
  have hsq : (fun m => coeffE4Sq m) = fun m => (coeffE4SqZV m : ℚ) := by
    funext m; simpa using! (coeffE4Sq_eq_cast m)
  simpa [coeffE4Cube, coeffE4CubeZV, hsq, coeffE4_fun_eq_cast] using!
    (conv_cast_eq_mulFunZV (a := coeffE4SqZV) (b := coeffE4ZV) (n := n))

lemma coeffE4Fourth_eq_cast (n : ℕ) : (coeffE4Fourth n) = (coeffE4FourthZV n : ℚ) := by
  have hsq : (fun m => coeffE4Sq m) = fun m => (coeffE4SqZV m : ℚ) := by
    funext m; simpa using! (coeffE4Sq_eq_cast m)
  simpa [coeffE4Fourth, coeffE4FourthZV, hsq] using!
    (conv_cast_eq_mulFunZV (a := coeffE4SqZV) (b := coeffE4SqZV) (n := n))

lemma coeffE6Sq_eq_cast (n : ℕ) : (coeffE6Sq n) = (coeffE6SqZV n : ℚ) := by
  simpa [coeffE6Sq, coeffE6SqZV, coeffE6_fun_eq_cast] using!
    (conv_cast_eq_mulFunZV (a := coeffE6ZV) (b := coeffE6ZV) (n := n))

lemma coeffLin_eq_cast (n : ℕ) : (coeffLin n) = (coeffLinZV n : ℚ) := by
  simp [coeffLin, coeffLinZV, coeffE4Cube_eq_cast n, coeffE6Sq_eq_cast n]

/-! ## Casting `coeffVarphiNum` to `ℤ` -/

/--
Rewrite `AppendixA.coeffVarphiNum` as the cast of the explicit integer formula `coeffVarphiNumZV`.
-/
public lemma coeffVarphiNum_eq_cast (n : ℕ) :
    (AppendixA.coeffVarphiNum n) = (coeffVarphiNumZV n : ℚ) := by
  -- Function-level cast identities.
  have hE2Sq : (coeffE2Sq) = fun m => (coeffE2SqZV m : ℚ) := by
    funext m; simpa using! (coeffE2Sq_eq_cast m)
  have hE4Sq : (coeffE4Sq) = fun m => (coeffE4SqZV m : ℚ) := by
    funext m; simpa using! (coeffE4Sq_eq_cast m)
  have hE6Sq : (coeffE6Sq) = fun m => (coeffE6SqZV m : ℚ) := by
    funext m; simpa using! (coeffE6Sq_eq_cast m)
  have hLin : (coeffLin) = fun m => (coeffLinZV m : ℚ) := by
    funext m; simpa using! (coeffLin_eq_cast m)
  have hConvE6SqE4 :
      AppendixA.conv coeffE6Sq AppendixA.coeffE4 n = (mulFunZV coeffE6SqZV coeffE4ZV n : ℚ) := by
    simpa [hE6Sq, coeffE4_fun_eq_cast] using!
      (conv_cast_eq_mulFunZV (a := coeffE6SqZV) (b := coeffE4ZV) (n := n))
  have hConvE6E4Sq_fun :
      (AppendixA.conv AppendixA.coeffE6 coeffE4Sq) = fun m =>
        (mulFunZV coeffE6ZV coeffE4SqZV m : ℚ) :=
        by
    funext m
    simpa [coeffE6_fun_eq_cast, hE4Sq] using!
      (conv_cast_eq_mulFunZV (a := coeffE6ZV) (b := coeffE4SqZV) (n := m))
  have hConvE6E4SqE2 :
      AppendixA.conv (AppendixA.conv AppendixA.coeffE6 coeffE4Sq) AppendixA.coeffE2 n =
        (mulFunZV (fun m => mulFunZV coeffE6ZV coeffE4SqZV m) coeffE2ZV n : ℚ) := by
    simpa [hConvE6E4Sq_fun, coeffE2_fun_eq_cast] using!
      (conv_cast_eq_mulFunZV (a := fun m => mulFunZV coeffE6ZV coeffE4SqZV m) (b :=
        coeffE2ZV) (n :=
        n))
  have hConvLinE2Sq :
      AppendixA.conv coeffLin coeffE2Sq n = (mulFunZV coeffLinZV coeffE2SqZV n : ℚ) := by
    simpa [hLin, hE2Sq] using!
      (conv_cast_eq_mulFunZV (a := coeffLinZV) (b := coeffE2SqZV) (n := n))
  have hLinFun : (fun m ↦ -(49 * coeffE4Cube m) + 25 * coeffE6Sq m) = coeffLin := by
    funext m
    simp [coeffLin, neg_mul]
  -- Assemble the identity.
  simp [AppendixA.coeffVarphiNum, coeffVarphiNumZV, coeffE4Fourth_eq_cast n, hConvE6SqE4,
    hConvE6E4SqE2, hLinFun, hConvLinE2Sq, sub_eq_add_neg]

-- Truncated `ℤ` lists for the Eisenstein coefficients and their products.
/-- Truncated `ℤ` list for `coeffE2ZV` (first `NVarphi = 50` coefficients). -/
@[expose] public def coeffE2ListZV : List ℤ := truncZV coeffE2ZV
/-- Truncated `ℤ` list for `coeffE4ZV` (first `NVarphi = 50` coefficients). -/
@[expose] public def coeffE4ListZV : List ℤ := truncZV coeffE4ZV
/-- Truncated `ℤ` list for `coeffE6ZV` (first `NVarphi = 50` coefficients). -/
@[expose] public def coeffE6ListZV : List ℤ := truncZV coeffE6ZV
/-- Truncated `ℤ` list for `coeffE2SqZV`. -/
@[expose] public def coeffE2SqListZV : List ℤ := mulZV coeffE2ListZV coeffE2ListZV
/-- Truncated `ℤ` list for `coeffE4SqZV`. -/
@[expose] public def coeffE4SqListZV : List ℤ := mulZV coeffE4ListZV coeffE4ListZV
/-- Truncated `ℤ` list for `coeffE4CubeZV`. -/
@[expose] public def coeffE4CubeListZV : List ℤ := mulZV coeffE4SqListZV coeffE4ListZV
/-- Truncated `ℤ` list for `coeffE4FourthZV`. -/
@[expose] public def coeffE4FourthListZV : List ℤ := mulZV coeffE4SqListZV coeffE4SqListZV
/-- Truncated `ℤ` list for `coeffE6SqZV`. -/
@[expose] public def coeffE6SqListZV : List ℤ := mulZV coeffE6ListZV coeffE6ListZV

/-- Truncated `ℤ` list for `coeffLinZV`. -/
@[expose] public def coeffLinListZV : List ℤ :=
  addZV (smulZV (-49) coeffE4CubeListZV) (smulZV 25 coeffE6SqListZV)


end SpherePacking.Dim24.Ineq2Varphi
