module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Phi2CoreTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Phi1CoreTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.DeltaHatSqTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.VarphiTable
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic


/-!
# Coefficient model for the `ineq2` truncation (`t ≤ 1`)

For the `t ≤ 1` case of Appendix A, Lemma `ineq2`, we construct an explicit truncation of the
cleared numerator. The coefficients are assembled from precomputed integer tables and split into
three parts corresponding to the powers `t^2`, `t / pi`, and `1 / pi^2` in
`ExactTrunc.ineq2_exact_coeff`.

This file provides the basic rational coefficient functions (`A0`, `B0`, `C0`) and a small
decision procedure (`piChoice`) choosing which rational bound for `pi` to use in each coefficient.

## Main definitions
* `N`
* `A0`, `B0`, `C0`
-/

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux.CoeffModel

/-- Truncation length for the `ineq2` `t ≤ 1` coefficient tables (`N = 100`). -/
@[expose] public def N : ℕ := 100

/-- Coefficient function for `varphi_num`, read from the precomputed integer table. -/
@[expose] public def phinumCoeffQ (n : ℕ) : ℚ :=
  (AppendixA.varphiNumCoeffsZ_table.getD n 0 : ℚ)

/-- Coefficient function for the core polynomial used in `phi1_num`, from the integer table. -/
@[expose] public def phi1CoreCoeffQ (n : ℕ) : ℚ :=
  (AppendixA.phi1CoreCoeffsZ_table.getD n 0 : ℚ)

/-- Coefficient function for the core polynomial used in `phi2_num`, from the integer table. -/
@[expose] public def phi2CoreCoeffQ (n : ℕ) : ℚ :=
  (AppendixA.phi2CoreCoeffsZ_table.getD n 0 : ℚ)

/-- Coefficient function for `psiI_num`, read from the precomputed integer table. -/
@[expose] public def psiInumCoeffQ (n : ℕ) : ℚ :=
  (AppendixA.psiInumCoeffs_table.getD n 0 : ℚ)

/-- The coefficient list `A0` in `ExactTrunc.ineq2_exact_coeff`, coming from `varphi_num`.
Odd indices vanish because `varphi_num` is a polynomial in `q = r^2`. -/
@[expose] public def A0 (i : ℕ) : ℚ :=
  if i % 2 = 0 then phinumCoeffQ (i / 2) else 0

/-- The coefficient list `B0` in `ExactTrunc.ineq2_exact_coeff`, coming from `phi1_num`. -/
@[expose] public def B0 (i : ℕ) : ℚ :=
  if i % 2 = 0 then (-6) * phi1CoreCoeffQ (i / 2) else 0

/-- The coefficient list `C0` in `ExactTrunc.ineq2_exact_coeff`, combining the `phi2_num` and
`psiI_num` contributions. -/
@[expose] public def C0 (i : ℕ) : ℚ :=
  (if i % 2 = 0 then (36 : ℚ) * phi2CoreCoeffQ (i / 2) else 0) + (432 : ℚ) * psiInumCoeffQ i

def y (i : ℕ) : ℚ := A0 i + B0 i + C0 i

def use_tLower (i : ℕ) : Bool := 0 < y i

def piChoice (i : ℕ) : ℚ :=
  let degPiNonneg : Bool := A0 i ≠ 0
  if use_tLower i then
    if degPiNonneg then AppendixA.BleadingCoeffs.piLower10Q else AppendixA.BleadingCoeffs.piUpper10Q
  else
    if degPiNonneg then AppendixA.BleadingCoeffs.piUpper10Q else AppendixA.BleadingCoeffs.piLower10Q

def invPiChoice (i : ℕ) : ℚ := 1 / (piChoice i)

def invPiSqChoice (i : ℕ) : ℚ := 1 / ((piChoice i) ^ (2 : ℕ))

def Aterm (i : ℕ) : ℚ := A0 i

def Bterm (i : ℕ) : ℚ := B0 i * invPiChoice i

def Cterm (i : ℕ) : ℚ := C0 i * invPiSqChoice i

def coeff_same (i : ℕ) : ℚ :=
  if use_tLower i then Aterm i + Bterm i + Cterm i else Cterm i

def coeff_shift1 (i : ℕ) : ℚ :=
  if use_tLower i then 0 else AppendixA.BleadingCoeffs.cQ * Bterm i

def coeff_shift2 (i : ℕ) : ℚ :=
  if use_tLower i then 0 else (AppendixA.BleadingCoeffs.cQ ^ (2 : ℕ)) * Aterm i

def coeffP (n : ℕ) : ℚ :=
  coeff_same n
    + (if _ : n + 1 < N then coeff_shift1 (n + 1) else 0)
    + (if _ : n + 2 < N then coeff_shift2 (n + 2) else 0)

def ineq2_trunc_leOne_coeffs_expected : List ℚ :=
  List.ofFn fun i : Fin N => coeffP i.1

end SpherePacking.Dim24.Ineq2LeOneTruncAux.CoeffModel
