/-
Verified integer coefficient table for `coeffPhi1Core` (first `50` coefficients).
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffZModel
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ZVArith

/-!
# `phi1` core coefficient table

This file contains the verified integer table for `coeffPhi1CoreZ` at indices `n < QN = 50`.

We compute the coefficients using truncated list arithmetic (so base arithmetic-function
coefficients are reused across convolutions), compare with the hardcoded list
`phi1CoreCoeffsZ_table` by kernel computation (`decide`), and then derive a table lemma for the
rational coefficients `coeffPhi1Core`.

## Main definitions
* `phi1CoreCoeffsZ_table`

## Main statements
* `coeffPhi1Core_eq_table`
-/

namespace SpherePacking.Dim24.AppendixA

/-- Hardcoded table for `coeffPhi1CoreZ n` at indices `n < QN`. -/
@[expose] public def phi1CoreCoeffsZ_table : List ℤ :=
  [0, -120960, -13063680, -2506775040, -75710315520, -1113972652800, -9907895531520,
    -62982440801280, -312995583129600, -1285314526500480, -4553404407014400,
    -14284666779102720, -40599534078996480, -106036095002423040, -258158610547568640,
    -590522175402163200, -1281709499830824960, -2651684786771892480, -5267712557697891840,
    -10073521247511052800, -18651285061132953600, -33478880991617617920,
    -58535726240725493760, -99740451150985559040, -166297873521746534400,
    -271279560338572464000, -434539542160916075520, -683131881009081369600,
    -1057415318597983887360, -1610323647070570387200, -2419951063221799833600,
    -3584902773855891640320, -5249873847740242452480, -7591137159588671969280,
    -10866660917423924874240, -15379903508476402022400, -21576533070696120437760,
    -29961100141793954138880, -41281192307317710182400, -56352710452113976642560,
    -76395733319346835968000, -102693596919266238117120, -137196497069165804175360,
    -181868944157631891095040, -239762522378800461680640, -313826563070443574726400,
    -408736161867112899563520, -528824279128974738094080, -681155847716159429591040,
    -871946892993894462702720]


private def E2ZV : List ℤ := truncZV coeffE2Z
private def E4ZV : List ℤ := truncZV coeffE4Z
private def E6ZV : List ℤ := truncZV coeffE6Z

private def E4SqZV : List ℤ := mulZV E4ZV E4ZV
private def E4CubeZV : List ℤ := mulZV E4SqZV E4ZV
private def E6SqZV : List ℤ := mulZV E6ZV E6ZV

private def phi2CoreZV : List ℤ :=
  addZV (smulZV (-49) E4CubeZV) (smulZV 25 E6SqZV)

private def E6E4SqZV : List ℤ := mulZV E6ZV E4SqZV
private def E2Phi2CoreZV : List ℤ := mulZV E2ZV phi2CoreZV

private def phi1CoreZV : List ℤ :=
  addZV (smulZV 48 E6E4SqZV) (smulZV 2 E2Phi2CoreZV)

private lemma coeffZV_E6E4SqZV (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV E6E4SqZV n = mulFunZ coeffE6Z coeffE4SqZ n := by
  have hmul :
      coeffZV E6E4SqZV n =
        Finset.sum (Finset.range (n + 1)) fun j => coeffZV E6ZV j * coeffZV E4SqZV (n - j) := by
    simpa [E6E4SqZV] using! (coeffZV_mulZV (a := E6ZV) (b := E4SqZV) (n := n) hn)
  refine hmul.trans ?_
  simp only [mulFunZ]
  simpa using! (Finset.sum_congr rfl (fun j hj => by
    have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hjlt : j < BleadingCoeffs.QN := lt_of_le_of_lt hjle hn
    have hsublt : n - j < BleadingCoeffs.QN := lt_of_le_of_lt (Nat.sub_le _ _) hn
    simp [E6ZV, coeffZV_truncZV (a := coeffE6Z) (n := j) hjlt, E4SqZV, E4ZV, coeffE4SqZ,
      coeffZV_mulZV_truncZV (a := coeffE4Z) (b := coeffE4Z) (n := n - j) hsublt]))

private lemma coeffZV_E2Phi2CoreZV (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV E2Phi2CoreZV n = mulFunZ coeffE2Z coeffPhi2CoreZ n := by
  have hphi2 : ∀ m < BleadingCoeffs.QN, coeffZV phi2CoreZV m = coeffPhi2CoreZ m := by
    intro m hm
    have hE4sq (k : ℕ) (hk : k < BleadingCoeffs.QN) : coeffZV E4SqZV k = coeffE4SqZ k := by
      simpa [E4SqZV, E4ZV, coeffE4SqZ] using!
        (coeffZV_mulZV_truncZV (a := coeffE4Z) (b := coeffE4Z) (n := k) hk)
    have hE4cube : coeffZV E4CubeZV m = coeffE4CubeZ m := by
      have hmul :
          coeffZV E4CubeZV m =
            Finset.sum (Finset.range (m + 1)) fun j => coeffZV E4SqZV j * coeffZV E4ZV (m - j) := by
        simpa [E4CubeZV] using! (coeffZV_mulZV (a := E4SqZV) (b := E4ZV) (n := m) hm)
      refine hmul.trans ?_
      simp only [coeffE4CubeZ, mulFunZ]
      simpa using! (Finset.sum_congr rfl (fun j hj => by
        have hjle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hjlt : j < BleadingCoeffs.QN := lt_of_le_of_lt hjle hm
        have hsublt : m - j < BleadingCoeffs.QN := lt_of_le_of_lt (Nat.sub_le _ _) hm
        simp [hE4sq j hjlt, E4ZV, coeffZV_truncZV (a := coeffE4Z) (n := m - j) hsublt]))
    have hE6sq : coeffZV E6SqZV m = coeffE6SqZ m := by
      simpa [E6SqZV, E6ZV, coeffE6SqZ] using!
        (coeffZV_mulZV_truncZV (a := coeffE6Z) (b := coeffE6Z) (n := m) hm)
    simp [phi2CoreZV, coeffZV_addZV, coeffZV_smulZV, hm, coeffPhi2CoreZ, hE4cube, hE6sq]
  have hmul :
      coeffZV E2Phi2CoreZV n =
        Finset.sum (Finset.range (n + 1)) fun j => coeffZV E2ZV j * coeffZV phi2CoreZV (n - j) := by
    simpa [E2Phi2CoreZV] using! (coeffZV_mulZV (a := E2ZV) (b := phi2CoreZV) (n := n) hn)
  refine hmul.trans ?_
  simp only [mulFunZ]
  simpa using! (Finset.sum_congr rfl (fun j hj => by
    have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hjlt : j < BleadingCoeffs.QN := lt_of_le_of_lt hjle hn
    have hsublt : n - j < BleadingCoeffs.QN := lt_of_le_of_lt (Nat.sub_le _ _) hn
    simp [E2ZV, coeffZV_truncZV (a := coeffE2Z) (n := j) hjlt, hphi2 (n - j) hsublt]))

private lemma coeffZV_phi1CoreZV (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV phi1CoreZV n = coeffPhi1CoreZ n := by
  have hE6E4 : coeffZV E6E4SqZV n = mulFunZ coeffE6Z coeffE4SqZ n :=
    coeffZV_E6E4SqZV (n := n) hn
  have hE2phi2 : coeffZV E2Phi2CoreZV n = mulFunZ coeffE2Z coeffPhi2CoreZ n :=
    coeffZV_E2Phi2CoreZV (n := n) hn
  simp [phi1CoreZV, coeffZV_addZV, coeffZV_smulZV, hn, coeffPhi1CoreZ, hE6E4, hE2phi2]

private lemma phi1CoreZV_eq_table : phi1CoreZV = phi1CoreCoeffsZ_table := by
  -- The `decide` proof can hit the default recursion-depth limit.
  set_option maxRecDepth 20000 in
  decide

lemma coeffPhi1CoreZ_eq_getD_fin (i : Fin BleadingCoeffs.QN) :
    coeffPhi1CoreZ i.1 = phi1CoreCoeffsZ_table.getD i.1 0 := by
  have htab := congrArg (fun l : List ℤ => l.getD i.1 0) phi1CoreZV_eq_table
  simpa [coeffZV] using! (coeffZV_phi1CoreZV (n := i.1) i.2).symm.trans htab

lemma coeffPhi1CoreZ_eq_getD (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffPhi1CoreZ n = phi1CoreCoeffsZ_table.getD n 0 := by
  simpa using! coeffPhi1CoreZ_eq_getD_fin (i := ⟨n, hn⟩)

/-- Table lemma for `coeffPhi1Core` at indices `n < QN`. -/
public lemma coeffPhi1Core_eq_table (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffPhi1Core n = (phi1CoreCoeffsZ_table.getD n 0 : ℚ) := by
  simpa [coeffPhi1Core_eq_cast] using!
    congrArg (fun z : ℤ => (z : ℚ)) (coeffPhi1CoreZ_eq_getD n hn)

end SpherePacking.Dim24.AppendixA
