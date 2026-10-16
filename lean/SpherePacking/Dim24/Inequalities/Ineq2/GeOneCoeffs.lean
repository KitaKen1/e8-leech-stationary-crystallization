-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases


/-!
# Certified coefficient identities for `ineq2` (t ≥ 1)

This file implements truncated power-series arithmetic on coefficient lists of length `N = 100`
and uses it to build a computable certificate for the `t ≥ 1` case of Appendix A, Lemma `ineq2`.

The main result is that the hard-coded coefficient list `AppendixA.ineq2_trunc_geOne_coeffs`
agrees with the expected coefficients obtained from the theta-polynomial construction, written
here as `ineq2_trunc_geOne_coeffs_expected`.

## Main definitions
* `N`
* `psiSnumCoeffs`
* `ineq2_trunc_geOne_coeffs_expected`

## Main statements
* `ineq2_trunc_geOne_coeffs_eq_expected`
-/

open scoped BigOperators


namespace SpherePacking.Dim24.Ineq2GeOneCoeffs
/-- The truncation length used throughout the `t ≥ 1` coefficient certificate. -/
@[expose] public def N : ℕ := 100

def coeffZ (l : List ℤ) (n : ℕ) : ℤ :=
  l.getD n 0

def addZ (a b : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin N => coeffZ a i.1 + coeffZ b i.1

def negZ (a : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin N => -coeffZ a i.1

def smulZ (c : ℤ) (a : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin N => c * coeffZ a i.1

def mulZ (a b : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin N =>
    let n := i.1
    Finset.sum (Finset.range (n + 1)) fun j => coeffZ a j * coeffZ b (n - j)

def powZ (a : List ℤ) : ℕ → List ℤ
  | 0 => List.ofFn fun i : Fin N => if i.1 = 0 then (1 : ℤ) else 0
  | Nat.succ k => mulZ a (powZ a k)

def shift1Z (a : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin N =>
    match i.1 with
    | 0 => 0
    | n + 1 => coeffZ a n

/-!
### Truncated theta coefficient lists

We only need coefficients up to `r^99`, so it suffices to truncate:
- squares `k^2` to `k ≤ 10` (`11^2 = 121 > 99`),
- triangular numbers `k(k+1)` to `k ≤ 9` (`10·11 = 110 > 99`).
-/

def theta01Coeff (M : ℕ) (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (M + 1)) fun k =>
    if k ^ 2 = n then (if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k)) else 0

def theta10Coeff (M : ℕ) (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (M + 1)) fun k => if k * (k + 1) = n then (2 : ℤ) else 0

def theta01Z (M : ℕ) : List ℤ :=
  List.ofFn fun i : Fin N => theta01Coeff M i.1

def theta10Z (M : ℕ) : List ℤ :=
  List.ofFn fun i : Fin N => theta10Coeff M i.1

def H₄Z (M : ℕ) : List ℤ :=
  powZ (theta01Z M) 4

def H₂Z (M : ℕ) : List ℤ :=
  shift1Z (powZ (theta10Z M) 4)

def psiSnumZ (M : ℕ) : List ℤ :=
  negZ <|
    addZ
        (addZ
          (smulZ 7 (mulZ (powZ (H₂Z M) 5) (powZ (H₄Z M) 2)))
          (smulZ 7 (mulZ (powZ (H₂Z M) 6) (H₄Z M))))
        (smulZ 2 (powZ (H₂Z M) 7))

/-- The coefficient table used in the `psiS_num` certificate, given explicitly to avoid kernel
reduction of the underlying theta-series computation. -/
@[expose] public def psiSnumCoeffs_table : List ℤ :=
  [
    0, 0, 0,
    0, 0, -7340032,
    0, -566231040, 0,
    -14900264960, 0, -202291281920,
    0, -1774709637120, 0,
    -11404383879168, 0, -58038146826240,
    0, -246418086297600, 0,
    -905169579540480, 0, -2953520097525760,
    0, -8731672090509312, 0,
    -23746909873111040, 0, -60124559766978560,
    0, -143080273729290240, 0,
    -322521943328686080, 0, -693046512510304256,
    0, -1427250586095452160, 0,
    -2829553893522800640, 0, -5420856710224936960,
    0, -10068568410842726400, 0,
    -18181962338896183296, 0, -31999998313134817280,
    0, -55008125592356782080, 0,
    -92531661538307604480, 0, -152568228756549795840,
    0, -246940752003018522624, 0,
    -392872109573564006400, 0, -615111652741658705920,
    0, -948780293830009159680, 0,
    -1443129207234337177600, 0, -2166463810273676361728,
    0, -3212552522736976527360, 0,
    -4708865160502994534400, 0, -6827101114637620346880,
    0, -9796591133693470310400, 0,
    -13921130305392463577088, 0, -19600052244084152074240,
    0, -27354576079271535575040, 0,
    -37860236246239548538880, 0, -51986790059192877056000,
    0, -70847386888714862985216, 0,
    -95857998800067955261440, 0, -128809498140507698626560,
    0, -171955432966082883747840, 0,
    -228116345471750646005760, 0, -300804736853001812049920,
    0, -394375881451937778892800, 0,
    -514204181457552675962880
  ]

/-!
### `ψS` numerator coefficients

The list `psiSnumCoeffs_table` is the coefficient table used in the certificate below.
We also keep a definitional computation `psiSnumCoeffs_calc` from theta-series arithmetic,
but we avoid proving `psiSnumCoeffs_calc = psiSnumCoeffs_table` here because it is too
expensive to compute in the kernel.
-/

def psiSnumCoeffs_calc : List ℤ :=
  psiSnumZ AppendixA.BleadingCoeffs.thetaCutoff

/-- The coefficient table for the first `N` terms of the `psiS_num` numerator, exposed as a public
constant for the rest of the `ineq2` `t ≥ 1` development. -/
@[expose] public def psiSnumCoeffs : List ℤ :=
  psiSnumCoeffs_table

/-- A rational upper bound for `π` (with denominator `10^10`), used to define `cPiLower10Q`. -/
@[expose] public def piUpper10Q : ℚ := 31415926536 / 10000000000

/-- The rational constant `432 / piUpper10Q^2`, serving as the rational version of `cPiLower10`. -/
@[expose] public def cPiLower10Q : ℚ := 432 / (piUpper10Q ^ (2 : ℕ))

/-- The "expected" truncation coefficients for `ineq2_trunc_geOne`: the even part comes from
`varphi_trunc_geOne_coeffs`, and we subtract `cPiLower10Q` times the `psiSnumCoeffs` table. -/
@[expose] public def ineq2_trunc_geOne_coeffs_expected : List ℚ :=
  List.ofFn fun i : Fin N =>
    let n : ℕ := i.1
    let varphiPart : ℚ :=
      if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0
    varphiPart - cPiLower10Q * (psiSnumCoeffs.getD n 0 : ℚ)

/-- The expected coefficient list `ineq2_trunc_geOne_coeffs_expected` has length `N`. -/
public lemma ineq2_trunc_geOne_coeffs_expected_length :
    ineq2_trunc_geOne_coeffs_expected.length = N := by
  trivial

/-- Closed form for `ineq2_trunc_geOne_coeffs_expected.getD n 0` for `n < N`. -/
public lemma ineq2_trunc_geOne_coeffs_expected_getD (n : ℕ) (hn : n < N) :
    ineq2_trunc_geOne_coeffs_expected.getD n 0 =
      (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0) -
        cPiLower10Q * (psiSnumCoeffs.getD n 0 : ℚ) := by
  have hnlen : n < ineq2_trunc_geOne_coeffs_expected.length := by
    simpa [ineq2_trunc_geOne_coeffs_expected_length] using! hn
  have hgetD :
      ineq2_trunc_geOne_coeffs_expected.getD n 0 = ineq2_trunc_geOne_coeffs_expected[n] := by
    simpa using!
      (List.getD_eq_getElem (l := ineq2_trunc_geOne_coeffs_expected) (d := (0 : ℚ)) hnlen)
  have hgetElem :
      ineq2_trunc_geOne_coeffs_expected[n] =
        (if n % 2 = 0 then AppendixA.varphi_trunc_geOne_coeffs.getD (n / 2) 0 else 0) -
          cPiLower10Q * (psiSnumCoeffs.getD n 0 : ℚ) := by
    dsimp [ineq2_trunc_geOne_coeffs_expected]
    exact List.getElem_ofFn hnlen
  exact hgetD.trans hgetElem

set_option maxHeartbeats 1000000 in
-- Lean 4.33: the 25-case table evaluation needs more than the default 200000 heartbeats.
set_option backward.isDefEq.respectTransparency false in
lemma ineq2_trunc_geOne_coeffs_eq_expected_get_0_24 (n : ℕ)
    (hn1 : n < AppendixA.ineq2_trunc_geOne_coeffs.length)
    (hn2 : n < ineq2_trunc_geOne_coeffs_expected.length) (hn : n < 25) :
      AppendixA.ineq2_trunc_geOne_coeffs.get ⟨n, hn1⟩ =
      ineq2_trunc_geOne_coeffs_expected.get ⟨n, hn2⟩ := by
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n using hn0, hn
  all_goals
    simp only [
      AppendixA.ineq2_trunc_geOne_coeffs,
      ineq2_trunc_geOne_coeffs_expected,
      psiSnumCoeffs,
      psiSnumCoeffs_table,
      cPiLower10Q,
      piUpper10Q,
      N,
      AppendixA.varphi_trunc_geOne_coeffs,
      List.get_ofFn
    ]
    norm_num

lemma ineq2_trunc_geOne_coeffs_eq_expected_get_25_49 (n : ℕ)
    (hn1 : n < AppendixA.ineq2_trunc_geOne_coeffs.length)
    (hn2 : n < ineq2_trunc_geOne_coeffs_expected.length) (hn1' : 25 ≤ n) (hn2' : n < 50) :
      AppendixA.ineq2_trunc_geOne_coeffs.get ⟨n, hn1⟩ =
      ineq2_trunc_geOne_coeffs_expected.get ⟨n, hn2⟩ := by
  interval_cases n using hn1', hn2'
  all_goals
    simp only [
      AppendixA.ineq2_trunc_geOne_coeffs,
      ineq2_trunc_geOne_coeffs_expected,
      psiSnumCoeffs,
      psiSnumCoeffs_table,
      cPiLower10Q,
      piUpper10Q,
      N,
      AppendixA.varphi_trunc_geOne_coeffs,
      List.get_ofFn
    ]
    norm_num

lemma ineq2_trunc_geOne_coeffs_eq_expected_get_50_74 (n : ℕ)
    (hn1 : n < AppendixA.ineq2_trunc_geOne_coeffs.length)
    (hn2 : n < ineq2_trunc_geOne_coeffs_expected.length) (hn1' : 50 ≤ n) (hn2' : n < 75) :
      AppendixA.ineq2_trunc_geOne_coeffs.get ⟨n, hn1⟩ =
      ineq2_trunc_geOne_coeffs_expected.get ⟨n, hn2⟩ := by
  interval_cases n using hn1', hn2'
  all_goals
    simp only [
      AppendixA.ineq2_trunc_geOne_coeffs,
      ineq2_trunc_geOne_coeffs_expected,
      psiSnumCoeffs,
      psiSnumCoeffs_table,
      cPiLower10Q,
      piUpper10Q,
      N,
      AppendixA.varphi_trunc_geOne_coeffs,
      List.get_ofFn
    ]
    norm_num

lemma ineq2_trunc_geOne_coeffs_eq_expected_get_75_99 (n : ℕ)
    (hn1 : n < AppendixA.ineq2_trunc_geOne_coeffs.length)
    (hn2 : n < ineq2_trunc_geOne_coeffs_expected.length) (hn1' : 75 ≤ n) (hn2' : n < 100) :
      AppendixA.ineq2_trunc_geOne_coeffs.get ⟨n, hn1⟩ =
      ineq2_trunc_geOne_coeffs_expected.get ⟨n, hn2⟩ := by
  interval_cases n using hn1', hn2'
  all_goals
    simp only [
      AppendixA.ineq2_trunc_geOne_coeffs,
      ineq2_trunc_geOne_coeffs_expected,
      psiSnumCoeffs,
      psiSnumCoeffs_table,
      cPiLower10Q,
      piUpper10Q,
      N,
      AppendixA.varphi_trunc_geOne_coeffs,
      List.get_ofFn
    ]
    norm_num

/-- Certificate that the hard-coded truncation coefficients `AppendixA.ineq2_trunc_geOne_coeffs`
agree with the expected coefficients `ineq2_trunc_geOne_coeffs_expected`. -/
public theorem ineq2_trunc_geOne_coeffs_eq_expected :
    AppendixA.ineq2_trunc_geOne_coeffs = ineq2_trunc_geOne_coeffs_expected := by
  refine List.ext_get ?_ ?_
  · -- Both lists have length `N = 100`.
    decide
  · intro n hn1 hn2
    have hn : n < N := by simpa using! hn1
    have hn100 : n < 100 := by simpa [N] using! hn
    by_cases h25 : n < 25
    · exact ineq2_trunc_geOne_coeffs_eq_expected_get_0_24 n hn1 hn2 h25
    have h25' : 25 ≤ n := Nat.le_of_not_gt h25
    by_cases h50 : n < 50
    · exact ineq2_trunc_geOne_coeffs_eq_expected_get_25_49 n hn1 hn2 h25' h50
    have h50' : 50 ≤ n := Nat.le_of_not_gt h50
    by_cases h75 : n < 75
    · exact ineq2_trunc_geOne_coeffs_eq_expected_get_50_74 n hn1 hn2 h50' h75
    have h75' : 75 ≤ n := Nat.le_of_not_gt h75
    exact ineq2_trunc_geOne_coeffs_eq_expected_get_75_99 n hn1 hn2 h75' hn100

end SpherePacking.Dim24.Ineq2GeOneCoeffs
