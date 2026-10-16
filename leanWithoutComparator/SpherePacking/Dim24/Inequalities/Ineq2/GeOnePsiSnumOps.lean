module
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn


/-!
# Truncated series operations for the `psiS_num` certificate

This file defines list-based operations on truncated integer power series of length `N = 100`,
together with the definitional computation `psiSnumCoeffs_calc` obtained from theta-series
arithmetic. These operations are used in the `t ≥ 1` case of Appendix A, Lemma `ineq2`, both for
constructing the coefficient function and for the kernel-checkable certificate against
`Ineq2GeOneCoeffs.psiSnumCoeffs`.

## Main definitions
* `mulZ`, `addZ`, `negZ`, `smulZ`, `powZ`, `shift1Z`
* `psiSnumCoeffs_calc`
-/

open scoped BigOperators

namespace SpherePacking.Dim24.Ineq2PsiSnum
/-- Turn a coefficient function `ℕ → ℤ` into a truncated coefficient list of length `N`. -/
@[expose] public def coeffList (a : ℕ → ℤ) : List ℤ :=
  List.ofFn fun i : Fin Ineq2GeOneCoeffs.N => a i.1

/-- Truncated convolution product of integer coefficient lists (Cauchy product, length `N`). -/
@[expose] public def mulZ (a b : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin Ineq2GeOneCoeffs.N =>
    let n := i.1
    ∑ k ∈ Finset.range (n + 1), a.getD k 0 * b.getD (n - k) 0

/-- Pointwise addition of truncated integer coefficient lists (length `N`). -/
@[expose] public def addZ (a b : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin Ineq2GeOneCoeffs.N => a.getD i.1 0 + b.getD i.1 0

/-- Pointwise negation of a truncated integer coefficient list (length `N`). -/
@[expose] public def negZ (a : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin Ineq2GeOneCoeffs.N => -a.getD i.1 0

/-- Scalar multiplication of a truncated integer coefficient list (length `N`). -/
@[expose] public def smulZ (c : ℤ) (a : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin Ineq2GeOneCoeffs.N => c * a.getD i.1 0

/-- Truncated power of an integer coefficient list, using `mulZ` (length `N`). -/
@[expose] public def powZ (a : List ℤ) : ℕ → List ℤ
  | 0 => List.ofFn fun i : Fin Ineq2GeOneCoeffs.N => if i.1 = 0 then (1 : ℤ) else 0
  | Nat.succ k => mulZ a (powZ a k)

/-- Shift a truncated coefficient list by one (multiply by `r`), dropping the last coefficient. -/
@[expose] public def shift1Z (a : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin Ineq2GeOneCoeffs.N =>
    match i.1 with
    | 0 => 0
    | n + 1 => a.getD n 0

/-- Truncated coefficient function for `theta01`, computed with cutoff `thetaCutoff`. -/
@[expose] public def theta01CoeffTrunc (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (AppendixA.BleadingCoeffs.thetaCutoff + 1),
    if k ^ (2 : ℕ) = n then (if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k)) else 0

/-- Truncated coefficient function for `theta10`, computed with cutoff `thetaCutoff`. -/
@[expose] public def theta10CoeffTrunc (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (AppendixA.BleadingCoeffs.thetaCutoff + 1),
    if k * (k + 1) = n then (2 : ℤ) else 0

/-- Definitional computation of the `psiS_num` numerator coefficient list (length `N = 100`). -/
@[expose] public def psiSnumCoeffs_calc : List ℤ :=
  let theta01Z : List ℤ := coeffList theta01CoeffTrunc
  let theta10Z : List ℤ := coeffList theta10CoeffTrunc
  let H₄Z : List ℤ := powZ theta01Z 4
  let H₂Z : List ℤ := shift1Z (powZ theta10Z 4)
  negZ <|
    addZ
        (addZ
          (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2)))
          (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z)))
        (smulZ 2 (powZ H₂Z 7))

end SpherePacking.Dim24.Ineq2PsiSnum
