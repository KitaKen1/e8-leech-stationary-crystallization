-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PhiDeltaQSeries.Identities
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ZVArith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Conv

/-!
# Integer coefficient model for Appendix A

This file provides an integer model for the coefficient functions used in Appendix A (truncated to
`n < 50`). We define integer Cauchy products (`mulFunZ`), integer versions of the Eisenstein
coefficients, and integer versions of the derived numerator coefficient functions.

We also record cast lemmas identifying the rational coefficient functions with `ℤ`-casts (up to a
fixed scaling factor for `coeffDeltaSq`), so that table certificates can be discharged by kernel
computation.

## Main definitions
* `mulFunZ`
* `coeffE2Z`, `coeffE4Z`, `coeffE6Z`
* `coeffVarphiNumZ`, `coeffPhi1CoreZ`, `coeffPhi2CoreZ`
* `coeffDeltaHatZ`, `coeffDeltaHatSqZ`

## Main statements
* `coeffVarphiNum_eq_cast`, `coeffPhi1Core_eq_cast`, `coeffPhi2Core_eq_cast`
* `coeffDeltaSq_eq_cast`
-/

namespace SpherePacking.Dim24.AppendixA

open scoped ArithmeticFunction.sigma

/-- Integer Cauchy product of two coefficient functions (the `conv` model over `ℤ`). -/
@[expose] public def mulFunZ (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n + 1)) fun j => a j * b (n - j)

/-- `mulZV` on truncated integer vectors computes `mulFunZ` at indices `n < QN`. -/
public lemma coeffZV_mulZV_truncZV (a b : ℕ → ℤ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV (mulZV (truncZV a) (truncZV b)) n = mulFunZ a b n := by
  refine (coeffZV_mulZV (a := truncZV a) (b := truncZV b) (n := n) hn).trans ?_
  simp only [mulFunZ]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hj' : j < BleadingCoeffs.QN :=
    lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hn
  have hnj' : n - j < BleadingCoeffs.QN :=
    lt_of_le_of_lt (Nat.sub_le n j) hn
  simp [coeffZV_truncZV (a := a) (n := j) hj', coeffZV_truncZV (a := b) (n := n - j) hnj']

lemma conv_eq_sum_range (a b : ℕ → ℚ) (n : ℕ) :
    conv a b n = Finset.sum (Finset.range (n + 1)) fun j => a j * b (n - j) := by
  simpa [conv, Nat.succ_eq_add_one] using!
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j) n)

lemma conv_cast_eq_mulFunZ (a b : ℕ → ℤ) (n : ℕ) :
    conv (fun m => (a m : ℚ)) (fun m => (b m : ℚ)) n = (mulFunZ a b n : ℚ) := by
  simp [conv_eq_sum_range, mulFunZ]

private lemma conv_eq_mulFunZ_of_eq_cast (a b : ℕ → ℚ) (aZ bZ : ℕ → ℤ) (n : ℕ)
    (ha : ∀ m, a m = (aZ m : ℚ)) (hb : ∀ m, b m = (bZ m : ℚ)) :
    conv a b n = (mulFunZ aZ bZ n : ℚ) := by
  have ha' : a = fun m => (aZ m : ℚ) := by
    funext m; simpa using! ha m
  have hb' : b = fun m => (bZ m : ℚ) := by
    funext m; simpa using! hb m
  simpa [ha', hb'] using! (conv_cast_eq_mulFunZ (a := aZ) (b := bZ) (n := n))

/-!
### Eisenstein coefficients as integers
-/

/-- Integer `q^n` coefficient of the Eisenstein series `E₂`. -/
@[expose] public def coeffE2Z (n : ℕ) : ℤ := if n = 0 then 1 else (-24 : ℤ) * (σ 1 n)
/-- Integer `q^n` coefficient of the Eisenstein series `E₄`. -/
@[expose] public def coeffE4Z (n : ℕ) : ℤ := if n = 0 then 1 else (240 : ℤ) * (σ 3 n)
/-- Integer `q^n` coefficient of the Eisenstein series `E₆`. -/
@[expose] public def coeffE6Z (n : ℕ) : ℤ := if n = 0 then 1 else (-504 : ℤ) * (σ 5 n)

lemma coeffE2_eq_cast (n : ℕ) : coeffE2 n = (coeffE2Z n : ℚ) := by
  cases n <;> simp [coeffE2, coeffE2Z]

lemma coeffE4_eq_cast (n : ℕ) : coeffE4 n = (coeffE4Z n : ℚ) := by
  cases n <;> simp [coeffE4, coeffE4Z]

lemma coeffE6_eq_cast (n : ℕ) : coeffE6 n = (coeffE6Z n : ℚ) := by
  cases n <;> simp [coeffE6, coeffE6Z]

lemma coeffE2_fun_eq_cast : coeffE2 = fun n => (coeffE2Z n : ℚ) := by
  funext n; exact coeffE2_eq_cast n

lemma coeffE4_fun_eq_cast : coeffE4 = fun n => (coeffE4Z n : ℚ) := by
  funext n; exact coeffE4_eq_cast n

lemma coeffE6_fun_eq_cast : coeffE6 = fun n => (coeffE6Z n : ℚ) := by
  funext n; exact coeffE6_eq_cast n

/-!
### Derived coefficients as integers + cast lemmas
-/

/-- Integer coefficients of `E₂^2` (Cauchy product model). -/
@[expose] public def coeffE2SqZ (n : ℕ) : ℤ := mulFunZ coeffE2Z coeffE2Z n
/-- Integer coefficients of `E₄^2` (Cauchy product model). -/
@[expose] public def coeffE4SqZ (n : ℕ) : ℤ := mulFunZ coeffE4Z coeffE4Z n
/-- Integer coefficients of `E₄^3` (Cauchy product model). -/
@[expose] public def coeffE4CubeZ (n : ℕ) : ℤ := mulFunZ coeffE4SqZ coeffE4Z n
/-- Integer coefficients of `E₄^4` (Cauchy product model). -/
@[expose] public def coeffE4FourthZ (n : ℕ) : ℤ := mulFunZ coeffE4SqZ coeffE4SqZ n
/-- Integer coefficients of `E₆^2` (Cauchy product model). -/
@[expose] public def coeffE6SqZ (n : ℕ) : ℤ := mulFunZ coeffE6Z coeffE6Z n

lemma coeffE2Sq_eq_cast (n : ℕ) : coeffE2Sq n = (coeffE2SqZ n : ℚ) := by
  simpa [coeffE2Sq, coeffE2SqZ] using!
    (conv_eq_mulFunZ_of_eq_cast (a := coeffE2) (b := coeffE2) (aZ := coeffE2Z) (bZ := coeffE2Z) n
      coeffE2_eq_cast coeffE2_eq_cast)

lemma coeffE4Sq_eq_cast (n : ℕ) : coeffE4Sq n = (coeffE4SqZ n : ℚ) := by
  simpa [coeffE4Sq, coeffE4SqZ] using!
    (conv_eq_mulFunZ_of_eq_cast (a := coeffE4) (b := coeffE4) (aZ := coeffE4Z) (bZ := coeffE4Z) n
      coeffE4_eq_cast coeffE4_eq_cast)

lemma coeffE6Sq_eq_cast (n : ℕ) : coeffE6Sq n = (coeffE6SqZ n : ℚ) := by
  simpa [coeffE6Sq, coeffE6SqZ] using!
    (conv_eq_mulFunZ_of_eq_cast (a := coeffE6) (b := coeffE6) (aZ := coeffE6Z) (bZ := coeffE6Z) n
      coeffE6_eq_cast coeffE6_eq_cast)

lemma coeffE4Cube_eq_cast (n : ℕ) : coeffE4Cube n = (coeffE4CubeZ n : ℚ) := by
  simpa [coeffE4Cube, coeffE4CubeZ] using!
    (conv_eq_mulFunZ_of_eq_cast
      (a := coeffE4Sq) (b := coeffE4)
      (aZ := coeffE4SqZ) (bZ := coeffE4Z)
      n coeffE4Sq_eq_cast coeffE4_eq_cast)

lemma coeffE4Fourth_eq_cast (n : ℕ) : coeffE4Fourth n = (coeffE4FourthZ n : ℚ) := by
  simpa [coeffE4Fourth, coeffE4FourthZ] using!
    (conv_eq_mulFunZ_of_eq_cast
      (a := coeffE4Sq) (b := coeffE4Sq)
      (aZ := coeffE4SqZ) (bZ := coeffE4SqZ)
      n coeffE4Sq_eq_cast coeffE4Sq_eq_cast)

/-- Integer model of `coeffPhi2Core`. -/
@[expose] public def coeffPhi2CoreZ (n : ℕ) : ℤ :=
  (-49 : ℤ) * coeffE4CubeZ n + (25 : ℤ) * coeffE6SqZ n

/-- Integer model of `coeffPhi1Core`. -/
@[expose] public def coeffPhi1CoreZ (n : ℕ) : ℤ :=
  (48 : ℤ) * (mulFunZ coeffE6Z coeffE4SqZ n) + (2 : ℤ) * (mulFunZ coeffE2Z coeffPhi2CoreZ n)

/-- Integer model of `coeffVarphiNum`. -/
@[expose] public def coeffVarphiNumZ (n : ℕ) : ℤ :=
  (25 : ℤ) * coeffE4FourthZ n +
    (-(49 : ℤ)) * (mulFunZ coeffE6SqZ coeffE4Z n) +
      (48 : ℤ) * (mulFunZ (fun m => mulFunZ coeffE6Z coeffE4SqZ m) coeffE2Z n) +
        (mulFunZ (fun m => -(49 * coeffE4CubeZ m) + (25 : ℤ) * coeffE6SqZ m) coeffE2SqZ n)

/-- `coeffPhi2Core` is the rational cast of the integer model `coeffPhi2CoreZ`. -/
public lemma coeffPhi2Core_eq_cast (n : ℕ) : coeffPhi2Core n = (coeffPhi2CoreZ n : ℚ) := by
  simp [coeffPhi2Core, coeffPhi2CoreZ, coeffE4Cube_eq_cast, coeffE6Sq_eq_cast]

private lemma conv_coeffE6_coeffE4Sq_eq_cast (n : ℕ) :
    conv coeffE6 coeffE4Sq n = (mulFunZ coeffE6Z coeffE4SqZ n : ℚ) :=
  conv_eq_mulFunZ_of_eq_cast (a := coeffE6) (b := coeffE4Sq) (aZ := coeffE6Z) (bZ := coeffE4SqZ) n
    coeffE6_eq_cast coeffE4Sq_eq_cast

private lemma conv_coeffE2_coeffPhi2Core_eq_cast (n : ℕ) :
    conv coeffE2 coeffPhi2Core n = (mulFunZ coeffE2Z coeffPhi2CoreZ n : ℚ) :=
  conv_eq_mulFunZ_of_eq_cast
    (a := coeffE2) (b := coeffPhi2Core) (aZ := coeffE2Z) (bZ := coeffPhi2CoreZ) n
    coeffE2_eq_cast coeffPhi2Core_eq_cast

private lemma conv_coeffE6Sq_coeffE4_eq_cast (n : ℕ) :
    conv coeffE6Sq coeffE4 n = (mulFunZ coeffE6SqZ coeffE4Z n : ℚ) :=
  conv_eq_mulFunZ_of_eq_cast (a := coeffE6Sq) (b := coeffE4) (aZ := coeffE6SqZ) (bZ := coeffE4Z) n
    coeffE6Sq_eq_cast coeffE4_eq_cast

public lemma coeffPhi1Core_eq_cast (n : ℕ) : coeffPhi1Core n = (coeffPhi1CoreZ n : ℚ) := by
  simp [coeffPhi1Core, coeffPhi1CoreZ, conv_coeffE6_coeffE4Sq_eq_cast,
    conv_coeffE2_coeffPhi2Core_eq_cast]

/-- `coeffVarphiNum` is the rational cast of the integer model `coeffVarphiNumZ`. -/
public lemma coeffVarphiNum_eq_cast (n : ℕ) : coeffVarphiNum n = (coeffVarphiNumZ n : ℚ) := by
  have hE6E4SqE2 :
      conv (conv coeffE6 coeffE4Sq) coeffE2 n =
        (mulFunZ (fun m => mulFunZ coeffE6Z coeffE4SqZ m) coeffE2Z n : ℚ) := by
    have hE6E4Sq : ∀ m, conv coeffE6 coeffE4Sq m = (mulFunZ coeffE6Z coeffE4SqZ m : ℚ) :=
      conv_coeffE6_coeffE4Sq_eq_cast
    exact
      (conv_eq_mulFunZ_of_eq_cast
        (a := fun m => conv coeffE6 coeffE4Sq m) (b := coeffE2)
        (aZ := fun m => mulFunZ coeffE6Z coeffE4SqZ m) (bZ := coeffE2Z) n
        hE6E4Sq coeffE2_eq_cast)
  have hLinE2Sq :
      conv (fun m => -(49 * coeffE4Cube m) + (25 : ℚ) * coeffE6Sq m) coeffE2Sq n =
        (mulFunZ
            (fun m => -(49 * coeffE4CubeZ m) + (25 : ℤ) * coeffE6SqZ m)
            coeffE2SqZ n : ℚ) := by
    let phi2Z : ℕ → ℤ := fun m => -(49 * coeffE4CubeZ m) + (25 : ℤ) * coeffE6SqZ m
    have hlin : ∀ m, (-(49 * coeffE4Cube m) + (25 : ℚ) * coeffE6Sq m) = (phi2Z m : ℚ) := by
      intro m
      simp [phi2Z, coeffE4Cube_eq_cast, coeffE6Sq_eq_cast]
    exact
      (conv_eq_mulFunZ_of_eq_cast (a := fun m => -(49 * coeffE4Cube m) + (25 : ℚ) * coeffE6Sq m)
        (b := coeffE2Sq) (aZ := phi2Z) (bZ := coeffE2SqZ) n hlin coeffE2Sq_eq_cast)
  simp [coeffVarphiNum, coeffVarphiNumZ, coeffE4Fourth_eq_cast n, conv_coeffE6Sq_coeffE4_eq_cast,
    hE6E4SqE2, hLinE2Sq,
    sub_eq_add_neg]

/-!
### Delta-square: keep the integer numerator table

We use `Δ = (E₄^3 - E₆^2) / 1728`, hence
`coeffDeltaSq n = (1/1728)^2 * (mulFunZ coeffDeltaHatZ coeffDeltaHatZ n : ℚ)`.
-/

/-- Integer coefficients of `Δ̂ := E₄^3 - E₆^2` (the numerator of `Δ`). -/
@[expose] public def coeffDeltaHatZ (n : ℕ) : ℤ :=
  coeffE4CubeZ n - coeffE6SqZ n

/-- Integer coefficients of `Δ̂^2`, used to model `Δ^2` up to a fixed rational scale. -/
@[expose] public def coeffDeltaHatSqZ (n : ℕ) : ℤ :=
  mulFunZ coeffDeltaHatZ coeffDeltaHatZ n

/--
Cast lemma for `coeffDeltaSq` in terms of the integer table `coeffDeltaHatSqZ`.

The scaling factor is `(1/1728)^2`.
-/
public lemma coeffDeltaSq_eq_cast (n : ℕ) :
    coeffDeltaSq n = ((coeffDeltaHatSqZ n : ℚ) * ((1 : ℚ) / (1728 ^ (2 : ℕ)))) := by
  -- First rewrite `coeffDelta` as a scaled integer cast.
  have hDelta : (fun m => coeffDelta m) =
      fun m => ((1 : ℚ) / 1728) * (coeffDeltaHatZ m : ℚ) := by
    funext m
    -- `coeffDelta m = (1/1728) * (coeffE4Cube m - coeffE6Sq m)`.
    simp [coeffDelta, coeffDeltaHatZ, coeffE4Cube_eq_cast m, coeffE6Sq_eq_cast m, sub_eq_add_neg]
  -- Cast-convolution for the integer numerator.
  have hconv :
      conv (fun m => (coeffDeltaHatZ m : ℚ)) (fun m => (coeffDeltaHatZ m : ℚ)) n =
        (coeffDeltaHatSqZ n : ℚ) := by
    simpa [coeffDeltaHatSqZ] using!
      (conv_cast_eq_mulFunZ (a := coeffDeltaHatZ) (b := coeffDeltaHatZ) (n := n))
  -- Expand `coeffDeltaSq` and reassociate scalars.
  have hconst : ((1 : ℚ) / 1728) * ((1 : ℚ) / 1728) = ((1 : ℚ) / (1728 ^ (2 : ℕ))) := by
    norm_num
  calc
    coeffDeltaSq n = conv coeffDelta coeffDelta n := by simp [coeffDeltaSq]
    _ = conv (fun m => ((1 : ℚ) / 1728) * (coeffDeltaHatZ m : ℚ))
          (fun m => ((1 : ℚ) / 1728) * (coeffDeltaHatZ m : ℚ)) n := by
          simp [hDelta]
    _ = (((1 : ℚ) / 1728) * ((1 : ℚ) / 1728)) *
          conv (fun m => (coeffDeltaHatZ m : ℚ)) (fun m => (coeffDeltaHatZ m : ℚ)) n := by
          -- Pull constants out of the convolution sum.
          simp [conv, mul_assoc, mul_left_comm, Finset.mul_sum]
    _ = ((1 : ℚ) / (1728 ^ (2 : ℕ))) * (coeffDeltaHatSqZ n : ℚ) := by
          have := congrArg (fun c : ℚ => c * (coeffDeltaHatSqZ n : ℚ)) hconst
          simpa [hconv, mul_assoc] using! this
    _ = ((coeffDeltaHatSqZ n : ℚ) * ((1 : ℚ) / (1728 ^ (2 : ℕ)))) := by
          ring

end SpherePacking.Dim24.AppendixA
