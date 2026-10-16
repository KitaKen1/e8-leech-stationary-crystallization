-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffZModel


/-!
# `phi2` core coefficient table

This file contains the verified integer table for `coeffPhi2CoreZ` at indices `n < QN = 50`.

We compute the coefficients using truncated list arithmetic, compare with the hardcoded list
`phi2CoreCoeffsZ_table` by kernel computation (`decide`), and then derive the rational table lemma
`coeffPhi2Core_eq_table`.

## Main definitions
* `phi2CoreCoeffsZ_table`

## Main statements
* `coeffPhi2Core_eq_table`
-/

namespace SpherePacking.Dim24.AppendixA

/-- Hardcoded table for `coeffPhi2CoreZ n` at indices `n < QN`. -/
@[expose] public def phi2CoreCoeffsZ_table : List ℤ :=
  [-24, -60480, -3265920, -417795840, -9463789440, -111397265280, -825657960960, -4498745771520,
    -19562223945600, -71406362583360, -227670220350720, -649303035413760, -1691647253291520,
    -4078311346247040, -9219950376698880, -19684072513405440, -40053421869713280,
    -77990729022702720, -146325348824941440, -265092664408185600, -466282126528323840,
    -797116214086133760, -1330357414561943040, -2168270677195338240, -3464539031703052800,
    -5425591206771449280, -8356529656940693760, -12650590389057062400, -18882416403535426560,
    -27764200811561558400, -40332517720363330560, -57821012481546639360,
    -82029278870941288320, -115017229690737454080, -159803837020940071680,
    -219712907263948600320, -299674070426335006080, -404879731645864245120,
    -543173582991022502400, -722470646821974059520, -954946666491835449600,
    -1252360938039832172160, -1633291631775783383040, -2114755164623626640640,
    -2724574117940914337280, -3486961811893817496960, -4442784368120792386560,
    -5625790203499731256320, -7095373413709994058240, -8897417275447902680640]

private def E4ZV : List ℤ := truncZV coeffE4Z
private def E6ZV : List ℤ := truncZV coeffE6Z

private def E4SqZV : List ℤ := mulZV E4ZV E4ZV
private def E4CubeZV : List ℤ := mulZV E4SqZV E4ZV
private def E6SqZV : List ℤ := mulZV E6ZV E6ZV

private def phi2CoreZV : List ℤ :=
  addZV (smulZV (-49) E4CubeZV) (smulZV 25 E6SqZV)

private lemma coeffZV_E4SqZV (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV E4SqZV n = coeffE4SqZ n := by
  simpa [E4SqZV, E4ZV, coeffE4SqZ] using!
    (coeffZV_mulZV_truncZV (a := coeffE4Z) (b := coeffE4Z) (n := n) hn)

private lemma coeffZV_E6SqZV (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV E6SqZV n = coeffE6SqZ n := by
  simpa [E6SqZV, E6ZV, coeffE6SqZ] using!
    (coeffZV_mulZV_truncZV (a := coeffE6Z) (b := coeffE6Z) (n := n) hn)

private lemma coeffZV_E4CubeZV (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV E4CubeZV n = coeffE4CubeZ n := by
  have hmul :
      coeffZV E4CubeZV n =
        Finset.sum (Finset.range (n + 1)) fun j => coeffZV E4SqZV j * coeffZV E4ZV (n - j) := by
    simpa [E4CubeZV] using! (coeffZV_mulZV (a := E4SqZV) (b := E4ZV) (n := n) hn)
  refine hmul.trans ?_
  simp only [coeffE4CubeZ, mulFunZ]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjlt : j < BleadingCoeffs.QN := lt_of_le_of_lt hjle hn
  have hsublt : n - j < BleadingCoeffs.QN := lt_of_le_of_lt (Nat.sub_le _ _) hn
  simp [coeffZV_E4SqZV (n := j) hjlt, E4ZV,
    coeffZV_truncZV (a := coeffE4Z) (n := n - j) hsublt]

private lemma coeffZV_phi2CoreZV (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV phi2CoreZV n = coeffPhi2CoreZ n := by
  have hE4cube : coeffZV E4CubeZV n = coeffE4CubeZ n := coeffZV_E4CubeZV (n := n) hn
  have hE6sq : coeffZV E6SqZV n = coeffE6SqZ n := coeffZV_E6SqZV (n := n) hn
  simp [phi2CoreZV, coeffZV_addZV, coeffZV_smulZV, hn, coeffPhi2CoreZ, hE4cube, hE6sq]

private lemma phi2CoreZV_eq_table : phi2CoreZV = phi2CoreCoeffsZ_table := by
  -- The `decide` proof can hit the default recursion-depth limit.
  set_option maxRecDepth 20000 in
  decide

lemma coeffPhi2CoreZ_eq_getD_fin (i : Fin BleadingCoeffs.QN) :
    coeffPhi2CoreZ i.1 = phi2CoreCoeffsZ_table.getD i.1 0 := by
  have htab := congrArg (fun l : List ℤ => l.getD i.1 0) phi2CoreZV_eq_table
  simpa [coeffZV] using! (coeffZV_phi2CoreZV (n := i.1) i.2).symm.trans htab

lemma coeffPhi2CoreZ_eq_getD (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffPhi2CoreZ n = phi2CoreCoeffsZ_table.getD n 0 := by
  simpa using! coeffPhi2CoreZ_eq_getD_fin (i := ⟨n, hn⟩)

/-- Table lemma for `coeffPhi2Core` at indices `n < QN`. -/
public lemma coeffPhi2Core_eq_table (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffPhi2Core n = (phi2CoreCoeffsZ_table.getD n 0 : ℚ) := by
  simpa [coeffPhi2Core_eq_cast] using!
    congrArg (fun z : ℤ => (z : ℚ)) (coeffPhi2CoreZ_eq_getD n hn)

end SpherePacking.Dim24.AppendixA
