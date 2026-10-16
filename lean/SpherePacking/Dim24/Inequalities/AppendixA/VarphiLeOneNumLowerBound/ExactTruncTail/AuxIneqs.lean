-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.CoeffModel


/-!
Auxiliary inequalities for the `t ≤ 1` exact truncation comparison.

These lemmas bound the "keep/shift" decompositions of the coefficient model against the original
expressions involving `t` and `1/π` (or `1/π^2`). They are used in
`VarphiLeOneNumLowerBound.ExactTruncTail.ExactTruncation` to show that the PARI/GP truncation
polynomial is dominated by the exact finite head.
-/

namespace SpherePacking.Dim24.AppendixA

noncomputable section

namespace VarphiLeOne

open BleadingCoeffs

/--
Bound the sum of the `B`-part keep/shift terms by the corresponding exact `Bcoeff` sum.

This is the inequality used to justify replacing a `1/π` approximation by `1/π` itself, while
handling negative coefficients via the "shift" term and the constraint `t * x ≤ 1/23`.
-/
public lemma Bpart_sum_le (t x : ℝ) (ht : 1 ≤ t) (hx0 : 0 ≤ x) (htr : t * x ≤ (1 / 23 : ℝ))
    (htr0 : 0 ≤ t * x) (hinvPi_lo : (BleadingCoeffs.invPiLower10Q : ℝ) ≤ (1 / Real.pi))
    (hinvPi_hi : (1 / Real.pi) ≤ (BleadingCoeffs.invPiUpper10Q : ℝ)) :
    Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Bkeep n : ℝ) * x ^ n) +
        Finset.sum (Finset.range BleadingCoeffs.N) (fun i =>
          if 1 ≤ i then (Bshift i : ℝ) * x ^ (i - 1) else 0) ≤
      Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
        (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n) := by
  -- Combine keep+shift into a single sum and prove termwise by cases on the sign of `Bcoeff`.
  have hL :
      (Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Bkeep n : ℝ) * x ^ n) +
            Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
              if 1 ≤ n then (Bshift n : ℝ) * x ^ (n - 1) else 0)) =
          Finset.sum (Finset.range BleadingCoeffs.N)
            (fun n =>
              (Bkeep n : ℝ) * x ^ n +
                (if 1 ≤ n then (Bshift n : ℝ) * x ^ (n - 1) else 0)) :=
    Eq.symm Finset.sum_add_distrib
  rw [hL]
  refine Finset.sum_le_sum ?_
  intro n hn
  by_cases hsign : 0 ≤ Bcoeff n
  · -- Nonnegative coefficient: `Bshift` vanishes and we use the lower bound for `1/pi` and `1 ≤ t`.
    have hneg : ¬Bcoeff n < 0 := not_lt_of_ge hsign
    have hB0 : 0 ≤ (Bcoeff n : ℝ) := by exact_mod_cast hsign
    have hinv : (invPiForB n : ℝ) ≤ (1 / Real.pi) := by
      dsimp [invPiForB, chooseInvPi]
      simp [hsign]
      simpa [one_div] using! hinvPi_lo
    have ht1 : (1 / Real.pi) ≤ t * (1 / Real.pi) := by
      have : (1 : ℝ) ≤ t := ht
      have hpi0 : 0 ≤ (1 / Real.pi) := by positivity [Real.pi_pos.le]
      simpa [mul_assoc] using! mul_le_mul_of_nonneg_right this hpi0
    have hinv' : (invPiForB n : ℝ) ≤ t * (1 / Real.pi) := hinv.trans ht1
    have hxpow : 0 ≤ x ^ n := by positivity
    have hmul :
          (invPiForB n : ℝ) * (Bcoeff n : ℝ) * x ^ n ≤
            (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n := by
        have hfac : 0 ≤ (Bcoeff n : ℝ) * x ^ n := mul_nonneg hB0 hxpow
        have := mul_le_mul_of_nonneg_right hinv' hfac
        simpa [mul_assoc, mul_left_comm, mul_comm] using! this
    simpa [
      Bkeep,
      Bshift,
      hsign,
      hneg,
      one_div,
      add_assoc,
      mul_assoc,
      mul_left_comm,
      mul_comm
    ] using! hmul
  · -- Negative coefficient: `Bkeep` vanishes and `Bshift` handles it using `t*x ≤ cQ`.
    have hneg : Bcoeff n < 0 := lt_of_not_ge hsign
    have hnegR : (Bcoeff n : ℝ) < 0 := by exact_mod_cast hneg
    by_cases hn1 : 1 ≤ n
    · have hxpow : 0 ≤ x ^ (n - 1) := pow_nonneg hx0 (n - 1)
      have htx : t * x ≤ (cQ : ℝ) := by simpa [cQ] using! htr
      have hinv : (1 / Real.pi) ≤ (invPiForB n : ℝ) := by
        dsimp [invPiForB, chooseInvPi]
        have hleQ : ¬0 ≤ Bcoeff n := not_le_of_gt hneg
        simp [hleQ]
        simpa [one_div] using! hinvPi_hi
      have hinv0 : 0 ≤ (invPiForB n : ℝ) := by
        have hpi0 : 0 ≤ (1 / Real.pi) := by positivity [Real.pi_pos.le]
        exact le_trans hpi0 hinv
      have hprod : (1 / Real.pi) * (t * x) ≤ (invPiForB n : ℝ) * (cQ : ℝ) := by
        have := mul_le_mul hinv htx htr0 hinv0
        simpa [mul_assoc, mul_left_comm, mul_comm] using! this
      have htxpow :
          t * (1 / Real.pi) * x ^ n ≤ (cQ : ℝ) * (invPiForB n : ℝ) * x ^ (n - 1) := by
        have hn' : (n - 1) + 1 = n := Nat.sub_add_cancel hn1
        have hxsplit : x ^ n = x ^ (n - 1) * x := by
          calc
            x ^ n = x ^ ((n - 1) + 1) := by simp [hn']
            _ = x ^ (n - 1) * x := by simp [pow_add, pow_one]
        calc
          t * (1 / Real.pi) * x ^ n = t * (1 / Real.pi) * (x ^ (n - 1) * x) := by simp [hxsplit]
          _ = (1 / Real.pi) * (t * x) * x ^ (n - 1) := by ring_nf
          _ ≤ (invPiForB n : ℝ) * (cQ : ℝ) * x ^ (n - 1) := by
              have := mul_le_mul_of_nonneg_right hprod hxpow
              simpa [mul_assoc, mul_left_comm, mul_comm] using! this
          _ = (cQ : ℝ) * (invPiForB n : ℝ) * x ^ (n - 1) := by ring_nf
      have hmul := mul_le_mul_of_nonpos_left htxpow (le_of_lt hnegR)
      have hmul' :
          (Bshift n : ℝ) * x ^ (n - 1) ≤ (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n := by
        have : (cQ : ℝ) * (invPiForB n : ℝ) * (Bcoeff n : ℝ) * x ^ (n - 1) ≤
            (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using! hmul
        simpa [Bshift, hneg, mul_assoc, mul_left_comm, mul_comm] using! this
      simpa [
        Bkeep,
        Bshift,
        hsign,
        hneg,
        hn1,
        add_assoc,
        mul_assoc,
        mul_left_comm,
        mul_comm
      ] using! hmul'
    · -- `n = 0` would force `Bcoeff n ≥ 0`, contradiction.
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn1
      subst hn0
      have : 0 ≤ Bcoeff 0 := by
        -- `phi1CoreCoeffsZ_table[0] = 0`, hence `Bcoeff 0 = 0`.
        simp [
          Bcoeff,
          BleadingCoeffs.coeffQ_phi1CoreQ_eq_table,
          BleadingCoeffs.QN,
          phi1CoreCoeffsZ_table
        ]
      exact (not_le_of_gt hneg this).elim

/--
Bound the sum of the `C`-part keep terms by the corresponding exact `Ccoeff` sum.

This replaces the chosen `1/π^2` approximation by `1/π^2` itself, using sign-dependent bounds.
-/
public lemma Ckeep_sum_le (x : ℝ) (hx0 : 0 ≤ x)
    (hinvPi_lo : (BleadingCoeffs.invPiLower10Q : ℝ) ≤ (1 / Real.pi))
    (hinvPi_hi : (1 / Real.pi) ≤ (BleadingCoeffs.invPiUpper10Q : ℝ)) :
    Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Ckeep n : ℝ) * x ^ n) ≤
      Finset.sum (Finset.range BleadingCoeffs.N)
        (fun n => (Ccoeff n : ℝ) * (1 / (Real.pi ^ 2)) * x ^ n) := by
  refine Finset.sum_le_sum ?_
  intro n hn
  dsimp [Ckeep, invPiSqForC]
  by_cases hsign : 0 ≤ Ccoeff n
  · have hC0 : 0 ≤ (Ccoeff n : ℝ) := by exact_mod_cast hsign
    have hinv : ((chooseInvPi (Ccoeff n)) : ℝ) ≤ (1 / Real.pi) := by
      dsimp [chooseInvPi]
      simp [hsign]
      simpa [one_div] using! hinvPi_lo
    have hchoose0 : 0 ≤ ((chooseInvPi (Ccoeff n)) : ℝ) := by
      dsimp [chooseInvPi]
      simp [hsign]
      norm_num [invPiLower10Q, piUpper10Q]
    have hsq :
        ((chooseInvPi (Ccoeff n)) : ℝ) ^ (2 : ℕ) ≤ (1 / Real.pi) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hchoose0 hinv 2
    have hsq' : ((chooseInvPi (Ccoeff n)) : ℝ) ^ (2 : ℕ) ≤ (1 / (Real.pi ^ 2)) := by
      simpa [pow_two, one_div, mul_assoc] using! hsq
    have hxpow : 0 ≤ x ^ n := pow_nonneg hx0 n
    have hmul :
        (((chooseInvPi (Ccoeff n)) : ℝ) ^ (2 : ℕ)) * (Ccoeff n : ℝ) * x ^ n ≤
          (Ccoeff n : ℝ) * (1 / (Real.pi ^ 2)) * x ^ n := by
      have hfac : 0 ≤ (Ccoeff n : ℝ) * x ^ n := mul_nonneg hC0 hxpow
      have := mul_le_mul_of_nonneg_right hsq' hfac
      simpa [mul_assoc, mul_left_comm, mul_comm] using! this
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hmul
  · have hneg : Ccoeff n < 0 := lt_of_not_ge hsign
    have hnegR : (Ccoeff n : ℝ) < 0 := by exact_mod_cast hneg
    have hinv : (1 / Real.pi) ≤ ((chooseInvPi (Ccoeff n)) : ℝ) := by
      dsimp [chooseInvPi]
      have hleQ : ¬0 ≤ Ccoeff n := not_le_of_gt hneg
      simp [hleQ]
      simpa [one_div] using! hinvPi_hi
    have hsq :
        (1 / Real.pi) ^ (2 : ℕ) ≤ ((chooseInvPi (Ccoeff n)) : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hinv 2
    have hsq' : (1 / (Real.pi ^ 2)) ≤ ((chooseInvPi (Ccoeff n)) : ℝ) ^ (2 : ℕ) := by
      simpa [pow_two, one_div, mul_assoc] using! hsq
    have hxpow : 0 ≤ x ^ n := pow_nonneg hx0 n
    have hmul :
        (((chooseInvPi (Ccoeff n)) : ℝ) ^ (2 : ℕ)) * (Ccoeff n : ℝ) * x ^ n ≤
          (Ccoeff n : ℝ) * (1 / (Real.pi ^ 2)) * x ^ n := by
      have hfac : 0 ≤ x ^ n := hxpow
      have h := mul_le_mul_of_nonpos_left hsq' (le_of_lt hnegR)
      have h' := mul_le_mul_of_nonneg_right h hfac
      simpa [mul_assoc, mul_left_comm, mul_comm] using! h'
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hmul

end VarphiLeOne

end

end SpherePacking.Dim24.AppendixA
