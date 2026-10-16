/-
Verified integer numerator coefficient table for `coeffDeltaSq` (first `50` coefficients).

We tabulate `coeffDeltaHatSqZ n = (E4^3 - E6^2)^2` coefficients (integer), and then
`coeffDeltaSq n = (coeffDeltaHatSqZ n : ℚ) * (1 / 1728^2)`.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffZModel
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ZVArith
public import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn


/-!
# `Δ̂^2` coefficient table

This file provides a verified coefficient table for the integer coefficients of
`Δ̂^2 = (E₄^3 - E₆^2)^2`, truncated to `QN = 50` as used in Appendix A.

We compute the truncated list once using list arithmetic over `ℤ`, compare it to the hardcoded
list `deltaHatSqCoeffsZ_table` by kernel computation (`decide`), and then derive the
coefficientwise table lemma for `coeffDeltaSq`.

## Main definitions
* `deltaHatSqCoeffsZ_table`

## Main statements
* `coeffDeltaSq_eq_table`
-/

namespace SpherePacking.Dim24.AppendixA

/-- Hardcoded table for `coeffDeltaHatSqZ n` at indices `n < QN`. -/
@[expose] public def deltaHatSqCoeffsZ_table : List ℤ :=
  [0, 0, 2985984, -143327232, 3224862720, -44909199360, 429444218880, -2943654690816,
    14505671393280, -48656728719360, 84840494653440, 115472778854400, -1267611552055296,
    3787273618587648, -3618824968765440, -12859277690142720, 54622879544770560,
    -70237006676361216, -78528449003139072, 409732527142010880, -450881142420602880,
    -402251878304317440, 1341553784783781888, -317511753465987072, -1082219795510722560,
    -3281471186219827200, 8578623962998333440, 7742471243875614720, -39468056419124379648,
    20316698457015582720, 56325018133275770880, -44235935463230668800,
    -68362980295679410176, -41801177758969626624, 341334008532711383040,
    -77025040144863068160, -672590235914535075840, 517800494732977373184,
    227616607834958315520, 329244005988939202560, -580624973538066432000,
    -1669793748347702476800, 2371679348582922190848, -717061664309642330112,
    2843804036643329802240, -991752356924687646720, -12331447816126781030400,
    10851363160911671721984, 8128180893360511254528, 4000969534743930470400]


namespace DeltaHatSqCalc

-- List arithmetic utilities are shared in `BLeadingNumLowerBound.ZVArith`.

def deltaHatSqCoeffsZ_computed : List ℤ :=
  let e4 : List ℤ := truncZV coeffE4Z
  let e6 : List ℤ := truncZV coeffE6Z
  let e4Sq : List ℤ := mulZV e4 e4
  let e4Cube : List ℤ := mulZV e4Sq e4
  let e6Sq : List ℤ := mulZV e6 e6
  let deltaHat : List ℤ := subZV e4Cube e6Sq
  mulZV deltaHat deltaHat

lemma deltaHatSqCoeffsZ_computed_eq_table :
    deltaHatSqCoeffsZ_computed = deltaHatSqCoeffsZ_table := by
  set_option maxRecDepth 20000 in
  decide

lemma coeffDeltaHatSqZ_eq_getD (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffDeltaHatSqZ n = deltaHatSqCoeffsZ_table.getD n 0 := by
  have htab := congrArg (fun l : List ℤ => l.getD n 0) deltaHatSqCoeffsZ_computed_eq_table
  have hcomp : deltaHatSqCoeffsZ_computed.getD n 0 = coeffDeltaHatSqZ n := by
    let e4 : List ℤ := truncZV coeffE4Z
    let e6 : List ℤ := truncZV coeffE6Z
    let e4Sq : List ℤ := mulZV e4 e4
    let e4Cube : List ℤ := mulZV e4Sq e4
    let e6Sq : List ℤ := mulZV e6 e6
    let deltaHat : List ℤ := subZV e4Cube e6Sq
    have hE4Sq (m : ℕ) (hm : m < BleadingCoeffs.QN) : coeffZV e4Sq m = coeffE4SqZ m := by
      simpa [e4Sq, e4, coeffE4SqZ] using!
        (coeffZV_mulZV_truncZV (a := coeffE4Z) (b := coeffE4Z) (n := m) hm)
    have hE6Sq (m : ℕ) (hm : m < BleadingCoeffs.QN) : coeffZV e6Sq m = coeffE6SqZ m := by
      simpa [e6Sq, e6, coeffE6SqZ] using!
        (coeffZV_mulZV_truncZV (a := coeffE6Z) (b := coeffE6Z) (n := m) hm)
    have hE4Cube (m : ℕ) (hm : m < BleadingCoeffs.QN) : coeffZV e4Cube m = coeffE4CubeZ m := by
      have hmul :
          coeffZV e4Cube m =
            Finset.sum (Finset.range (m + 1)) fun j => coeffZV e4Sq j * coeffZV e4 (m - j) := by
        simpa [e4Cube] using! (coeffZV_mulZV (a := e4Sq) (b := e4) (n := m) hm)
      refine hmul.trans ?_
      simp only [coeffE4CubeZ, mulFunZ]
      simpa using! (Finset.sum_congr rfl (fun j hj => by
        have hjle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hjlt : j < BleadingCoeffs.QN := lt_of_le_of_lt hjle hm
        have hsublt : m - j < BleadingCoeffs.QN := lt_of_le_of_lt (Nat.sub_le _ _) hm
        simp [hE4Sq j hjlt, e4, coeffZV_truncZV (a := coeffE4Z) (n := m - j) hsublt]))
    have hdeltaHat (m : ℕ) (hm : m < BleadingCoeffs.QN) :
        coeffZV deltaHat m = coeffDeltaHatZ m := by
      simpa [deltaHat, coeffDeltaHatZ, hE4Cube m hm, hE6Sq m hm] using!
        (coeffZV_subZV (a := e4Cube) (b := e6Sq) (n := m) hm)
    have hmul :
        coeffZV (mulZV deltaHat deltaHat) n =
          Finset.sum (Finset.range (n + 1)) fun j =>
            coeffZV deltaHat j * coeffZV deltaHat (n - j) := by
      simpa using! (coeffZV_mulZV (a := deltaHat) (b := deltaHat) (n := n) hn)
    have hmul' : coeffZV (mulZV deltaHat deltaHat) n = coeffDeltaHatSqZ n := by
      have :
          coeffZV (mulZV deltaHat deltaHat) n =
            Finset.sum (Finset.range (n + 1)) fun j =>
              coeffDeltaHatZ j * coeffDeltaHatZ (n - j) := by
        refine hmul.trans ?_
        simpa using! (Finset.sum_congr rfl (fun j hj => by
          have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hjlt : j < BleadingCoeffs.QN := lt_of_le_of_lt hjle hn
          have hsublt : n - j < BleadingCoeffs.QN := lt_of_le_of_lt (Nat.sub_le _ _) hn
          simp [hdeltaHat j hjlt, hdeltaHat (n - j) hsublt]))
      simpa [coeffDeltaHatSqZ, mulFunZ] using! this
    -- Convert `coeffZV` to `getD` and fold back the `let`-definitions.
    simpa [coeffZV, deltaHatSqCoeffsZ_computed, e4, e6, e4Sq, e4Cube, e6Sq, deltaHat] using! hmul'
  simpa using! hcomp.symm.trans htab

lemma coeffDeltaHatSqZ_eq_getD_fin (i : Fin BleadingCoeffs.QN) :
    coeffDeltaHatSqZ i.1 = deltaHatSqCoeffsZ_table.getD i.1 0 :=
  by simpa using! coeffDeltaHatSqZ_eq_getD (n := i.1) (hn := i.2)

end DeltaHatSqCalc

/-- Table lemma for `coeffDeltaSq` at indices `n < QN`. -/
public lemma coeffDeltaSq_eq_table (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffDeltaSq n =
      ((deltaHatSqCoeffsZ_table.getD n 0 : ℚ) * ((1 : ℚ) / (1728 ^ (2 : ℕ)))) :=
  by simp [coeffDeltaSq_eq_cast, DeltaHatSqCalc.coeffDeltaHatSqZ_eq_getD n hn]

end SpherePacking.Dim24.AppendixA
