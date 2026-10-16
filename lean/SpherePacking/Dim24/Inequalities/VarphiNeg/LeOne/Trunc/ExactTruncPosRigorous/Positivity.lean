-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Trunc.ExactTruncPosRigorous.Term4LowerBound


/-!
# Positivity

Positivity of the exact truncation head used in the `t ≤ 1` case of Appendix A.

## Main statements
* `varphi_exact_trunc_sub_eps_pos`
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.VarphiNeg.LeOne.Trunc

open AppendixA
open AppendixA.VarphiLeOne

/-- Lower bound `exactTrunc t` by the partial sum of the `i = 0,2,4` terms. -/
lemma exactTrunc_ge_sel024 (t : ℝ) (ht : 1 ≤ t) :
    (∑ i ∈ ({0, 2, 4} : Finset ℕ),
        exactCoeff t i * (AppendixA.r t) ^ i) ≤ exactTrunc t := by
  let N : ℕ := BleadingCoeffs.N
  let s : Finset ℕ := Finset.range N
  let tset : Finset ℕ := ({0, 2, 4} : Finset ℕ)
  have htset : tset ⊆ s := by
    trivial
  have hnonneg :
      ∀ i, i ∈ s \ tset → 0 ≤ exactCoeff t i * (AppendixA.r t) ^ i := by
    intro i hi
    have hiN : i < N := by
      have : i ∈ s := (Finset.mem_sdiff.1 hi).1
      simpa [s] using! (Finset.mem_range.1 this)
    have hir : 0 ≤ (AppendixA.r t) ^ i := pow_nonneg (Real.exp_pos _).le _
    have himem : i ∉ tset := (Finset.mem_sdiff.1 hi).2
    have hodd_or_even : i % 2 = 0 ∨ i % 2 = 1 := Nat.mod_two_eq_zero_or_one i
    rcases hodd_or_even with hEven | hOdd
    · have hi6 : 6 ≤ i := by
        -- With `i ∉ {0,2,4}` and `i` even, necessarily `6 ≤ i`.
        grind only [= Finset.mem_insert, = Finset.mem_singleton]
      have hcoeff : 0 ≤ exactCoeff t i :=
        exactCoeff_nonneg_even_ge6 (t := t) ht i hiN hi6 hEven
      exact mul_nonneg hcoeff hir
    · -- odd: coefficient is exactly 0
      simp [exactCoeff_odd (t := t) (i := i) hOdd]
  -- Apply the `Finset` lemma.
  have hsum :
      Finset.sum tset (fun i => exactCoeff t i * (AppendixA.r t) ^ i) ≤
        Finset.sum s (fun i => exactCoeff t i * (AppendixA.r t) ^ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg htset (by
      intro i _hi hi_not
      have : i ∈ s \ tset := by
        refine Finset.mem_sdiff.2 ?_
        exact ⟨_hi, hi_not⟩
      exact hnonneg i this)
  -- Keep the small sum expanded, then simplify `r(t)^0`.
  assumption

/-- Positivity of the exact truncation head with tail error term for all `t ≥ 1`. -/
public theorem varphi_exact_trunc_sub_eps_pos (t : ℝ) (ht : 1 ≤ t) :
    0 < exactTrunc t - eps * (AppendixA.r t) ^ (12 : ℕ) := by
  -- Lower bound `exactTrunc` by the `i = 0,2,4` terms.
  have hsel := exactTrunc_ge_sel024 (t := t) ht
  have h0pow : (AppendixA.r t) ^ (0 : ℕ) = 1 := by simp
  -- Termwise lower bounds for `i=0,2,4`.
  have hterm0 :
      exactCoeff t 0 * (AppendixA.r t) ^ (0 : ℕ) ≥ (Ccoeff 0 : ℝ) * uLoSq := by
    have hC0 : 0 ≤ (Ccoeff 0 : ℝ) := by
      have : (0 : ℚ) ≤ Ccoeff 0 := by
        have hQN0 : (0 : ℕ) < BleadingCoeffs.QN := by decide
        simp [Ccoeff, BleadingCoeffs.coeffQ_phi2CoreQ_eq_table, hQN0, phi2CoreCoeffsZ_table]
      exact_mod_cast this
    have hu2 : uLoSq ≤ (1 / Real.pi) ^ (2 : ℕ) := by
      have huLo0 : (0 : ℝ) ≤ uLo := by
        have : (0 : ℚ) ≤ uLoQ := by
          dsimp [uLoQ, AppendixA.BleadingCoeffs.invPiLower10Q, AppendixA.BleadingCoeffs.piUpper10Q]
          norm_num
        have : (0 : ℝ) ≤ (uLoQ : ℝ) := by exact_mod_cast this
        simpa [uLo] using! this
      have := pow_le_pow_left₀ huLo0 uLo_le_inv_pi 2
      simpa [uLoSq, uLo, uLoSqQ, uLoQ, one_div, pow_two] using! this
    have hx : (Ccoeff 0 : ℝ) * uLoSq ≤ (Ccoeff 0 : ℝ) * (1 / (Real.pi ^ 2)) := by
      have : (Ccoeff 0 : ℝ) * uLoSq ≤ (Ccoeff 0 : ℝ) * ((1 / Real.pi) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hu2 hC0
      simpa [one_div, pow_two, mul_assoc] using! this
    -- `exactCoeff t 0 = C0/pi^2` and `r^0 = 1`.
    have hA0 : (Acoeff 0 : ℚ) = 0 := by
      have hQN0 : (0 : ℕ) < BleadingCoeffs.QN := by decide
      simp [Acoeff, BleadingCoeffs.coeffQ_phinumQ_eq_table, hQN0, varphiNumCoeffsZ_table]
    have hB0 : (Bcoeff 0 : ℚ) = 0 := by
      have hQN0 : (0 : ℕ) < BleadingCoeffs.QN := by decide
      simp [Bcoeff, BleadingCoeffs.coeffQ_phi1CoreQ_eq_table, hQN0, phi1CoreCoeffsZ_table]
    have hA0R : (Acoeff 0 : ℝ) = 0 := by exact_mod_cast hA0
    have hB0R : (Bcoeff 0 : ℝ) = 0 := by exact_mod_cast hB0
    simp [exactCoeff, hA0R, hB0R] at *
    linarith
  have hterm2 := term2_lower_bound (t := t) ht
  have hterm4 := term4_lower_bound (t := t) ht
  -- Coarse bound: `eps * r(t)^12 ≤ 1`.
  have heps_le_one : eps ≤ (1 : ℝ) := by
    dsimp [eps]
    norm_num
  have hr_le_one : AppendixA.r t ≤ 1 := by
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    have : (-Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, ht0]
    simpa [AppendixA.r] using! (Real.exp_le_one_iff.2 this)
  have hr0 : 0 ≤ AppendixA.r t := (Real.exp_pos _).le
  have hr12_le_one : (AppendixA.r t) ^ (12 : ℕ) ≤ 1 := pow_le_one₀ hr0 hr_le_one
  have hepsr12_le_one : eps * (AppendixA.r t) ^ (12 : ℕ) ≤ (1 : ℝ) := by
    have := mul_le_mul heps_le_one hr12_le_one (by positivity) (by norm_num)
    simpa using! this
  -- Convert the selected-sum lower bound into a single rational margin and finish by `decide`.
  set mQ : ℚ :=
    (Ccoeff 0) * uLoSqQ +
      (Bcoeff 2) * (uHiSqQ / 2) * (1 / 1000) +
      (Bcoeff 4) * uHiQ *
        (1 - 3 / (2 * AppendixA.BleadingCoeffs.piUpper10Q)) *
        (1 / (535 : ℚ) ^ (2 : ℕ)) -
      1
  have hmQ_pos : (0 : ℚ) < mQ := by
    -- Fully concrete rational margin.
    have hQN0 : (0 : ℕ) < BleadingCoeffs.QN := by decide
    have hQN1 : (1 : ℕ) < BleadingCoeffs.QN := by decide
    have hQN2 : (2 : ℕ) < BleadingCoeffs.QN := by decide
    simp [mQ, uLoQ, uHiQ, uLoSqQ, uHiSqQ,
      AppendixA.BleadingCoeffs.piLower10Q, AppendixA.BleadingCoeffs.piUpper10Q,
      AppendixA.BleadingCoeffs.invPiLower10Q, AppendixA.BleadingCoeffs.invPiUpper10Q,
      Bcoeff, Ccoeff,
      BleadingCoeffs.coeffQ_phi1CoreQ_eq_table, BleadingCoeffs.coeffQ_phi2CoreQ_eq_table,
      hQN0, hQN1, hQN2, phi1CoreCoeffsZ_table, phi2CoreCoeffsZ_table]
    norm_num
  have hm_pos : (0 : ℝ) < (mQ : ℝ) := by exact_mod_cast hmQ_pos
  have hsel_ge :
      (mQ : ℝ) + 1 ≤
        (∑ i ∈ ({0, 2, 4} : Finset ℕ), exactCoeff t i * (AppendixA.r t) ^ i) := by
    -- Expand the small `Finset` sum and apply the three termwise bounds.
    -- Note: the algebraic identity for `mQ + 1` is handled by `simp`.
    have : (mQ : ℝ) + 1 =
        (Ccoeff 0 : ℝ) * uLoSq +
          (Bcoeff 2 : ℝ) * (uHiSq / 2) * ((1 : ℝ) / 1000) +
          (Bcoeff 4 : ℝ) * uHi *
            (1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ))) *
            ((1 : ℝ) / (535 : ℝ) ^ (2 : ℕ)) := by
      -- unfold and clear the `-1`.
      simp [mQ, uLoSq, uHiSq, uHi, uLoQ, uHiQ, uLoSqQ, uHiSqQ, sub_eq_add_neg]
    -- Evaluate the sum over `{0,2,4}`.
    have hsum :
        (Ccoeff 0 : ℝ) * uLoSq +
            (Bcoeff 2 : ℝ) * (uHiSq / 2) * ((1 : ℝ) / 1000) +
            (Bcoeff 4 : ℝ) * uHi *
                (1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ))) *
                ((1 : ℝ) / (535 : ℝ) ^ (2 : ℕ))
          ≤
          ∑ i ∈ ({0, 2, 4} : Finset ℕ), exactCoeff t i * (AppendixA.r t) ^ i := by
      -- Use the termwise lower bounds.
      have h0 : (Ccoeff 0 : ℝ) * uLoSq ≤ exactCoeff t 0 := by
        have : (Ccoeff 0 : ℝ) * uLoSq ≤ exactCoeff t 0 * (AppendixA.r t) ^ (0 : ℕ) := by
          simpa [ge_iff_le] using! hterm0
        simpa [h0pow] using! this
      have h2 :
          (Bcoeff 2 : ℝ) * (uHiSq / 2) * ((1 : ℝ) / 1000) ≤
            exactCoeff t 2 * (AppendixA.r t) ^ (2 : ℕ) := by
        simpa [ge_iff_le, mul_assoc, mul_left_comm, mul_comm] using! hterm2
      have h4 :
          (Bcoeff 4 : ℝ) * uHi *
              (1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ))) *
              ((1 : ℝ) / (535 : ℝ) ^ (2 : ℕ))
            ≤ exactCoeff t 4 * (AppendixA.r t) ^ (4 : ℕ) :=
        by simpa [ge_iff_le, mul_assoc, mul_left_comm, mul_comm] using! hterm4
      have h24 :
          (Bcoeff 2 : ℝ) * (uHiSq / 2) * ((1 : ℝ) / 1000) +
              (Bcoeff 4 : ℝ) * uHi *
                  (1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ))) *
                  ((1 : ℝ) / (535 : ℝ) ^ (2 : ℕ))
            ≤ exactCoeff t 2 * (AppendixA.r t) ^ (2 : ℕ) +
                exactCoeff t 4 * (AppendixA.r t) ^ (4 : ℕ) :=
        add_le_add h2 h4
      have h024 :
          (Ccoeff 0 : ℝ) * uLoSq +
              ((Bcoeff 2 : ℝ) * (uHiSq / 2) * ((1 : ℝ) / 1000) +
                (Bcoeff 4 : ℝ) * uHi *
                    (1 - (3 : ℝ) / (2 * (AppendixA.BleadingCoeffs.piUpper10Q : ℝ))) *
                    ((1 : ℝ) / (535 : ℝ) ^ (2 : ℕ)))
            ≤ exactCoeff t 0 +
                (exactCoeff t 2 * (AppendixA.r t) ^ (2 : ℕ) +
                  exactCoeff t 4 * (AppendixA.r t) ^ (4 : ℕ)) :=
        add_le_add h0 h24
      -- Rearrange to match the `{0,2,4}` finset-sum normal form.
      simpa [Finset.sum_insert, Finset.sum_singleton, pow_zero, mul_one,
        add_assoc, add_left_comm, add_comm] using! h024
    nlinarith [this, hsum]
  have hmain :
      (mQ : ℝ) ≤ exactTrunc t - eps * (AppendixA.r t) ^ (12 : ℕ) := by
    linarith
  exact lt_of_lt_of_le hm_pos hmain

end SpherePacking.Dim24.VarphiNeg.LeOne.Trunc
