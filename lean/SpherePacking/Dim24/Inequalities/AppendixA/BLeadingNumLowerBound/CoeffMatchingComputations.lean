-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffMatchingLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ShiftSums
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import
  SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PiBoundsAndTruncCompare

/-!
# Coefficient matching computations for Appendix A

This file contains explicit computations used to compare the computable truncation polynomial
`Bleading_trunc` with the analytic expression `Bleading_exact_trunc` for `t ≥ 1`.

## Main statements
* `Bleading_trunc_eval₂_le_exact_trunc`
* `re_ge_sub_of_norm_sub_le`
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.AppendixA

lemma coeffQ_phi2CoreQ_zero : BleadingCoeffs.coeffQ BleadingCoeffs.phi2CoreQ 0 = (-24 : ℚ) := by
  have hE4Cube : BleadingCoeffs.coeffQ BleadingCoeffs.E4CubeQ 0 = 1 := by
    simpa [BleadingCoeffs.E4CubeQ, coeffQ_E4Q_zero] using!
      (coeffQ_powQ_zero (a := BleadingCoeffs.E4Q) 3)
  have hE6Sq : BleadingCoeffs.coeffQ BleadingCoeffs.E6SqQ 0 = 1 := by
    simpa [BleadingCoeffs.E6SqQ, coeffQ_E6Q_zero] using!
      (coeffQ_powQ_zero (a := BleadingCoeffs.E6Q) 2)
  simp only [BleadingCoeffs.phi2CoreQ, coeffQ_addQ_zero, coeffQ_smulQ_zero, hE4Cube, hE6Sq]
  norm_num

lemma coeffQ_phi1CoreQ_zero : BleadingCoeffs.coeffQ BleadingCoeffs.phi1CoreQ 0 = 0 := by
  have hE4Sq : BleadingCoeffs.coeffQ BleadingCoeffs.E4SqQ 0 = 1 := by
    simpa [BleadingCoeffs.E4SqQ, coeffQ_E4Q_zero] using!
      (coeffQ_powQ_zero (a := BleadingCoeffs.E4Q) 2)
  calc
    BleadingCoeffs.coeffQ BleadingCoeffs.phi1CoreQ 0 =
        48 *
            BleadingCoeffs.coeffQ
              (BleadingCoeffs.mulQ BleadingCoeffs.E6Q BleadingCoeffs.E4SqQ) 0 +
          2 *
            BleadingCoeffs.coeffQ
              (BleadingCoeffs.mulQ BleadingCoeffs.E2Q BleadingCoeffs.phi2CoreQ) 0 := by
          simp only [BleadingCoeffs.phi1CoreQ, coeffQ_addQ_zero, coeffQ_smulQ_zero]
    _ =
        48 *
            (BleadingCoeffs.coeffQ BleadingCoeffs.E6Q 0 *
              BleadingCoeffs.coeffQ BleadingCoeffs.E4SqQ 0) +
          2 *
            (BleadingCoeffs.coeffQ BleadingCoeffs.E2Q 0 *
              BleadingCoeffs.coeffQ BleadingCoeffs.phi2CoreQ 0) := by
          simp only [coeffQ_mulQ_zero]
    _ = 0 := by
          rw [coeffQ_E6Q_zero, coeffQ_E2Q_zero, coeffQ_phi2CoreQ_zero, hE4Sq]
          norm_num

lemma coeffQ_DeltaQ_zero : BleadingCoeffs.coeffQ BleadingCoeffs.DeltaQ 0 = 0 := by
  have hE4Cube : BleadingCoeffs.coeffQ BleadingCoeffs.E4CubeQ 0 = 1 := by
    simpa [BleadingCoeffs.E4CubeQ, coeffQ_E4Q_zero] using!
      (coeffQ_powQ_zero (a := BleadingCoeffs.E4Q) 3)
  have hE6Sq : BleadingCoeffs.coeffQ BleadingCoeffs.E6SqQ 0 = 1 := by
    simpa [BleadingCoeffs.E6SqQ, coeffQ_E6Q_zero] using!
      (coeffQ_powQ_zero (a := BleadingCoeffs.E6Q) 2)
  simp only [BleadingCoeffs.DeltaQ, coeffQ_smulQ_zero, coeffQ_subQ_zero, hE4Cube, hE6Sq]
  norm_num

lemma coeffQ_DeltaSqQ_one : BleadingCoeffs.coeffQ BleadingCoeffs.DeltaSqQ 1 = 0 := by
  have h0 : BleadingCoeffs.coeffQ BleadingCoeffs.DeltaQ 0 = 0 := coeffQ_DeltaQ_zero
  dsimp [BleadingCoeffs.DeltaSqQ]
  change
    BleadingCoeffs.coeffQ
        (BleadingCoeffs.mulQ BleadingCoeffs.DeltaQ
          (BleadingCoeffs.powQ BleadingCoeffs.DeltaQ 1)) 1 = 0
  rw [coeffQ_mulQ_one]
  have hpow0 : BleadingCoeffs.coeffQ (BleadingCoeffs.powQ BleadingCoeffs.DeltaQ 1) 0 = 0 := by
    simpa [h0] using! (coeffQ_powQ_zero (a := BleadingCoeffs.DeltaQ) 1)
  rw [h0, hpow0]
  simp

lemma coeffQ_phinumQ_zero : BleadingCoeffs.coeffQ BleadingCoeffs.phinumQ 0 = 0 := by
  have hcoeff0 : coeffVarphiNum 0 = 0 := by
    simp [coeffVarphiNum, coeffE4Fourth, coeffE4Cube, coeffE4Sq, coeffE6Sq, coeffE2Sq, conv,
      coeffE2, coeffE4, coeffE6]
    norm_num
  simpa [hcoeff0] using! (coeffQ_phinumQ_eq (n := 0) (hn := by decide))

lemma BleadingCoeffs_Acoeff_zero : BleadingCoeffs.Acoeff 0 = 0 := by
  simp only [BleadingCoeffs.Acoeff, BleadingCoeffs.isEven, BleadingCoeffs.qIdx]
  rw [coeffQ_phinumQ_zero]
  simp

lemma BleadingCoeffs_Bcoeff_zero : BleadingCoeffs.Bcoeff 0 = 0 := by
  simp only [BleadingCoeffs.Bcoeff, BleadingCoeffs.isEven, BleadingCoeffs.qIdx,
    BleadingCoeffs.deltaIdx]
  rw [coeffQ_phi1CoreQ_zero, coeffQ_DeltaSqQ_one]
  simp

/-- The truncation polynomial underestimates `Bleading_exact_trunc` for `t ≥ 1`. -/
public lemma Bleading_trunc_eval₂_le_exact_trunc (t : ℝ) (ht : 1 ≤ t) :
    (Bleading_trunc.eval₂ (algebraMap ℚ ℝ) (r t)) ≤ Bleading_exact_trunc t := by
  set x : ℝ := r t
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have ht0 : 0 ≤ t := le_trans (by simp : (0 : ℝ) ≤ 1) ht
  have ht2 : 1 ≤ t ^ (2 : ℕ) := by
    -- For `t ≥ 1`, we have `1 ≤ t*t = t^2`.
    exact (one_le_sq_iff₀ ht0).mpr ht
  have htr : t * x ≤ (1 / 23 : ℝ) := by
    simpa [x] using! (AppendixA.t_mul_r_le_one_div_23 (t := t) ht)
  have htr0 : 0 ≤ t * x := mul_nonneg ht0 hx0
  have htr_sq : (t * x) ^ (2 : ℕ) ≤ (1 / 23 : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ htr0 htr 2
  have hpiLower_le : (BleadingCoeffs.piLower10Q : ℝ) ≤ Real.pi :=
    (le_of_lt piLower10Q_lt_pi)
  have hpi_le_piUpper : Real.pi ≤ (BleadingCoeffs.piUpper10Q : ℝ) :=
    (le_of_lt pi_lt_piUpper10Q)
  -- Expand the polynomial evaluation into the coefficient sum.
  have hpoly := Bleading_trunc_eval₂_eq_sum_range_formula (t := t)
  rw [hpoly]
  dsimp [Bleading_exact_trunc, Bleading_exact_coeff]
  -- Split the LHS sum into the five coefficient parts and reindex the shifts.
  have hterm :
      ∀ n : ℕ,
        (Bleading_trunc_coeff_formula n : ℝ) * x ^ n =
          (BleadingCoeffs.Akeep n : ℝ) * x ^ n +
            (if n + 2 < BleadingCoeffs.N then
              (BleadingCoeffs.Ashift (n + 2) : ℝ) * x ^ n
            else 0) +
            (BleadingCoeffs.Bkeep n : ℝ) * x ^ n +
              (if n + 1 < BleadingCoeffs.N then
                (BleadingCoeffs.Bshift (n + 1) : ℝ) * x ^ n
              else 0) +
              (BleadingCoeffs.Ckeep n : ℝ) * x ^ n := by
    intro n
    -- Split on the two `if`-conditions to avoid expensive `simp` on casts of `ite`.
    by_cases hA : n + 2 < BleadingCoeffs.N <;> by_cases hB : n + 1 < BleadingCoeffs.N <;>
      simp [Bleading_trunc_coeff_formula, hA, hB, x] <;> ring
  have hsplit :
      Finset.sum (Finset.range BleadingCoeffs.N)
          (fun n => (Bleading_trunc_coeff_formula n : ℝ) * x ^ n) =
        Finset.sum (Finset.range BleadingCoeffs.N)
            (fun n => (BleadingCoeffs.Akeep n : ℝ) * x ^ n) +
          Finset.sum (Finset.range BleadingCoeffs.N)
              (fun n =>
                if n + 2 < BleadingCoeffs.N then
                  (BleadingCoeffs.Ashift (n + 2) : ℝ) * x ^ n
                else 0) +
          Finset.sum (Finset.range BleadingCoeffs.N)
              (fun n => (BleadingCoeffs.Bkeep n : ℝ) * x ^ n) +
            Finset.sum (Finset.range BleadingCoeffs.N)
                (fun n =>
                  if n + 1 < BleadingCoeffs.N then
                    (BleadingCoeffs.Bshift (n + 1) : ℝ) * x ^ n
                  else 0) +
            Finset.sum (Finset.range BleadingCoeffs.N)
                (fun n => (BleadingCoeffs.Ckeep n : ℝ) * x ^ n) := by
    -- Rewrite each summand using `hterm`, then split the sum of additions.
    have hrewrite :
        Finset.sum (Finset.range BleadingCoeffs.N)
            (fun n => (Bleading_trunc_coeff_formula n : ℝ) * x ^ n) =
          Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
              (BleadingCoeffs.Akeep n : ℝ) * x ^ n +
                (if n + 2 < BleadingCoeffs.N then
                  (BleadingCoeffs.Ashift (n + 2) : ℝ) * x ^ n
                else 0) +
                (BleadingCoeffs.Bkeep n : ℝ) * x ^ n +
                  (if n + 1 < BleadingCoeffs.N then
                    (BleadingCoeffs.Bshift (n + 1) : ℝ) * x ^ n
                  else 0) +
                  (BleadingCoeffs.Ckeep n : ℝ) * x ^ n) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      exact hterm n
    -- Split the nested sum of additions into five sums.
    -- `simp` is fast here since it only reassociates and uses `sum_add_distrib`.
    simp [hrewrite, Finset.sum_add_distrib, add_assoc]
  -- Reindex the shifted sums.
  have hAshift :
      (∑ n ∈ Finset.range BleadingCoeffs.N,
          if n + 2 < BleadingCoeffs.N then (BleadingCoeffs.Ashift (n + 2) : ℝ) * x ^ n else 0) =
        ∑ i ∈ Finset.range BleadingCoeffs.N,
          (if 2 ≤ i then (BleadingCoeffs.Ashift i : ℝ) * x ^ (i - 2) else 0) := by
    simpa using!
      (sum_shift2_eq
        (N := BleadingCoeffs.N)
        (x := x)
        (f := fun i => (BleadingCoeffs.Ashift i : ℝ)))
  have hBshift :
      (∑ n ∈ Finset.range BleadingCoeffs.N,
          if n + 1 < BleadingCoeffs.N then (BleadingCoeffs.Bshift (n + 1) : ℝ) * x ^ n else 0) =
        ∑ i ∈ Finset.range BleadingCoeffs.N,
          (if 1 ≤ i then (BleadingCoeffs.Bshift i : ℝ) * x ^ (i - 1) else 0) := by
    simpa using!
      (sum_shift1_eq
        (N := BleadingCoeffs.N)
        (x := x)
        (f := fun i => (BleadingCoeffs.Bshift i : ℝ)))
  -- Put the LHS into a single sum with the shifted terms reindexed.
  rw [hsplit, hAshift, hBshift]
  -- Now compare term-by-term against the exact coefficients.
  -- We do this as three independent bounds (A/B/C), then add them.
  have hA :
      (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Akeep i : ℝ) * x ^ i) +
          (∑ i ∈ Finset.range BleadingCoeffs.N,
              if 2 ≤ i then (BleadingCoeffs.Ashift i : ℝ) * x ^ (i - 2) else 0)
        ≤
          ∑ i ∈ Finset.range BleadingCoeffs.N,
            (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) * x ^ i := by
    have hconst0 : (0 : ℝ) < Real.pi := Real.pi_pos
    -- Termwise comparison.
    have htermA :
        ∀ i : ℕ, i ∈ Finset.range BleadingCoeffs.N →
          (BleadingCoeffs.Akeep i : ℝ) * x ^ i +
              (if 2 ≤ i then (BleadingCoeffs.Ashift i : ℝ) * x ^ (i - 2) else 0)
            ≤
              (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) * x ^ i := by
      intro i hi
      by_cases hAi : 0 ≤ BleadingCoeffs.Acoeff i
      · -- Nonnegative A-coefficient: keep term only.
        have hAshift0 : BleadingCoeffs.Ashift i = 0 := by
          have : ¬ BleadingCoeffs.Acoeff i < 0 := not_lt_of_ge hAi
          simp [BleadingCoeffs.Ashift, this]
        have hAshift0Num : BleadingCoeffs.AshiftNum i = 0 := by
          simpa using! hAshift0
        have hpiFor : BleadingCoeffs.piForA i = BleadingCoeffs.piLower10Q := by
          simp [BleadingCoeffs.piForA, BleadingCoeffs.choosePi, hAi]
        have hAkeep :
            (BleadingCoeffs.Akeep i : ℝ) ≤ (BleadingCoeffs.Acoeff i : ℝ) * Real.pi := by
          -- `Akeep i = piLower10Q * Acoeff i` and `piLower10Q ≤ π`.
          have hAkeep' : (BleadingCoeffs.Akeep i : ℝ) =
              (BleadingCoeffs.piLower10Q : ℝ) * (BleadingCoeffs.Acoeff i : ℝ) := by
            simp [BleadingCoeffs.Akeep, hAi, hpiFor, Rat.cast_mul]
          rw [hAkeep']
          -- Multiply `piLower10Q ≤ π` by the nonnegative `Acoeff i`.
          have hAiR : (0 : ℝ) ≤ (BleadingCoeffs.Acoeff i : ℝ) := by exact_mod_cast hAi
          have := mul_le_mul_of_nonneg_right hpiLower_le hAiR
          simpa [mul_assoc, mul_left_comm, mul_comm] using! this
        have hxpow : 0 ≤ x ^ i := pow_nonneg hx0 _
        have hbase :
            (BleadingCoeffs.Akeep i : ℝ) * x ^ i ≤
              (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * x ^ i :=
          mul_le_mul_of_nonneg_right hAkeep hxpow
        have hscale :
            (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * x ^ i ≤
              (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) * x ^ i := by
          have hnonneg :
              0 ≤ (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * x ^ i := by
            have hAiR : (0 : ℝ) ≤ (BleadingCoeffs.Acoeff i : ℝ) := by exact_mod_cast hAi
            have : 0 ≤ (BleadingCoeffs.Acoeff i : ℝ) * Real.pi :=
              mul_nonneg hAiR (Real.pi_pos.le)
            exact mul_nonneg this hxpow
          -- Multiply by `1 ≤ t^2`.
          have := mul_le_mul_of_nonneg_left ht2 hnonneg
          -- `a * 1 = a`.
          simpa [mul_assoc, mul_left_comm, mul_comm] using! this
        -- Finish; shift term vanishes.
        have hmain :
            (BleadingCoeffs.Akeep i : ℝ) * x ^ i ≤
              (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) * x ^ i :=
          hbase.trans hscale
        simpa [hAshift0Num, add_assoc] using! hmain
      · -- Negative A-coefficient: shift term dominates.
        have hAi' : BleadingCoeffs.Acoeff i < 0 := lt_of_not_ge hAi
        have hAkeep0 : BleadingCoeffs.Akeep i = 0 := by
          simp [BleadingCoeffs.Akeep, hAi]
        have hAkeep0Num : BleadingCoeffs.AkeepNum i = 0 := by
          simpa using! hAkeep0
        have hpiFor : BleadingCoeffs.piForA i = BleadingCoeffs.piUpper10Q := by
          have : ¬ 0 ≤ BleadingCoeffs.Acoeff i := hAi
          simp [BleadingCoeffs.piForA, BleadingCoeffs.choosePi, this]
        have hi2 : 2 ≤ i := by
          -- `Acoeff 0 = Acoeff 1 = 0`, so negativity forces `i ≥ 2`.
          cases i with
          | zero =>
              exfalso
              have hA0 : BleadingCoeffs.Acoeff 0 = 0 := BleadingCoeffs_Acoeff_zero
              simp [hA0] at hAi'
          | succ i =>
              cases i with
              | zero =>
                  exfalso
                  -- `Acoeff 1 = 0`.
                  have : BleadingCoeffs.Acoeff 1 = 0 := by
                    simp [BleadingCoeffs.Acoeff, BleadingCoeffs.isEven]
                  simp [this] at hAi'
              | succ i =>
                  exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le i))
        have hAshift_def :
            BleadingCoeffs.Ashift i =
              (BleadingCoeffs.cQ ^ (2 : ℕ)) *
                (BleadingCoeffs.piForA i * BleadingCoeffs.Acoeff i) := by
          simp [BleadingCoeffs.Ashift, hAi']
        have hpiFor_le : Real.pi ≤ (BleadingCoeffs.piForA i : ℝ) := by
          -- Here `piForA i = piUpper10Q`.
          simpa [hpiFor] using! hpi_le_piUpper
        have hpi_mul_le :
            Real.pi * (t * x) ^ (2 : ℕ) ≤
              (BleadingCoeffs.piForA i : ℝ) * (1 / 23 : ℝ) ^ (2 : ℕ) := by
          have h1 : Real.pi ≤ (BleadingCoeffs.piForA i : ℝ) := hpiFor_le
          have h2 : (t * x) ^ (2 : ℕ) ≤ (1 / 23 : ℝ) ^ (2 : ℕ) := htr_sq
          have htx0 : 0 ≤ (t * x) ^ (2 : ℕ) :=
            pow_nonneg htr0 2
          have hpiFor0 : 0 ≤ (BleadingCoeffs.piForA i : ℝ) := by
            -- Here `piForA i = piUpper10Q`, which is positive.
            have : (0 : ℝ) < (BleadingCoeffs.piUpper10Q : ℝ) := by
              norm_num [BleadingCoeffs.piUpper10Q]
            simpa [hpiFor] using! this.le
          have := mul_le_mul h1 h2 htx0 hpiFor0
          simpa [mul_assoc, mul_left_comm, mul_comm] using! this
        have hAiR : (BleadingCoeffs.Acoeff i : ℝ) ≤ 0 := by
          exact_mod_cast (le_of_lt hAi')
        have hmul_neg :
            (BleadingCoeffs.Acoeff i : ℝ) *
                ((BleadingCoeffs.piForA i : ℝ) * (1 / 23 : ℝ) ^ (2 : ℕ)) ≤
              (BleadingCoeffs.Acoeff i : ℝ) * (Real.pi * (t * x) ^ (2 : ℕ)) := by
          -- Multiply `hpi_mul_le` by the nonpositive `Acoeff i` (reverses inequality).
          simpa [mul_assoc, mul_left_comm, mul_comm] using!
            (mul_le_mul_of_nonpos_left hpi_mul_le hAiR)
        have hxpow : 0 ≤ x ^ (i - 2) := pow_nonneg hx0 _
        have hmul_neg' :
            (BleadingCoeffs.Acoeff i : ℝ) *
                  ((BleadingCoeffs.piForA i : ℝ) * (1 / 23 : ℝ) ^ (2 : ℕ)) *
                  x ^ (i - 2) ≤
                (BleadingCoeffs.Acoeff i : ℝ) *
                    (Real.pi * (t * x) ^ (2 : ℕ)) *
                    x ^ (i - 2) :=
          mul_le_mul_of_nonneg_right hmul_neg hxpow
        -- Rewrite the RHS into the desired `t^2 * x^i` shape.
        have hxsplit : x ^ i = x ^ (2 : ℕ) * x ^ (i - 2) :=
          Eq.symm (pow_mul_pow_sub x hi2)
        have htsplit : (t * x) ^ (2 : ℕ) = t ^ (2 : ℕ) * x ^ (2 : ℕ) := by
          simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
        have hAsh_le :
            (BleadingCoeffs.Ashift i : ℝ) * x ^ (i - 2) ≤
              (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) * x ^ i := by
          -- Start from `hmul_neg'` and rewrite constants to match `Ashift`.
          have hcQ : (BleadingCoeffs.cQ : ℝ) = (1 / 23 : ℝ) := by
            norm_num [BleadingCoeffs.cQ]
          -- `Ashift` is `cQ^2 * (piForA * Acoeff)`; rewrite `cQ` and reassociate.
          have hAsh_cast :
              (BleadingCoeffs.Ashift i : ℝ) =
                (BleadingCoeffs.Acoeff i : ℝ) *
                  ((BleadingCoeffs.piForA i : ℝ) * (1 / 23 : ℝ) ^ (2 : ℕ)) := by
            -- Rewrite `Ashift` first to avoid the global simp rewrite `Ashift = AshiftNum`.
            rw [hAshift_def]
            simp [hcQ, mul_left_comm, mul_comm]
          -- Rewrite `Real.pi * (t*x)^2 * x^(i-2)` into `Real.pi * t^2 * x^i`.
          have hR :
              (BleadingCoeffs.Acoeff i : ℝ) * (Real.pi * (t * x) ^ (2 : ℕ)) * x ^ (i - 2) =
                (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) * x ^ i := by
            -- Expand `(t*x)^2` and `x^i`.
            simp [htsplit, hxsplit, mul_assoc, mul_left_comm, mul_comm]
          -- Conclude.
          calc
            (BleadingCoeffs.Ashift i : ℝ) * x ^ (i - 2)
                = (BleadingCoeffs.Acoeff i : ℝ) *
                    ((BleadingCoeffs.piForA i : ℝ) * (1 / 23 : ℝ) ^ (2 : ℕ)) *
                    x ^ (i - 2) := by
                      simpa using! congrArg (fun z => z * x ^ (i - 2)) hAsh_cast
            _ ≤
                (BleadingCoeffs.Acoeff i : ℝ) *
                  (Real.pi * (t * x) ^ (2 : ℕ)) *
                  x ^ (i - 2) := hmul_neg'
            _ = (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) * x ^ i := by simp [hR]
        -- Assemble LHS: `Akeep` vanishes and `if 2≤i` selects `Ashift`.
        simpa [hAkeep0Num, hi2, add_assoc] using! hAsh_le
    -- Sum the termwise bounds.
    have hsumA :=
      Finset.sum_le_sum (s := Finset.range BleadingCoeffs.N) (fun i hi => htermA i hi)
    simpa [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm] using! hsumA
  have hB :
      (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bkeep i : ℝ) * x ^ i) +
          (∑ i ∈ Finset.range BleadingCoeffs.N,
              if 1 ≤ i then (BleadingCoeffs.Bshift i : ℝ) * x ^ (i - 1) else 0)
        ≤
          ∑ i ∈ Finset.range BleadingCoeffs.N,
            (BleadingCoeffs.Bcoeff i : ℝ) * t * x ^ i := by
    have htermB :
        ∀ i : ℕ, i ∈ Finset.range BleadingCoeffs.N →
          (BleadingCoeffs.Bkeep i : ℝ) * x ^ i +
              (if 1 ≤ i then (BleadingCoeffs.Bshift i : ℝ) * x ^ (i - 1) else 0)
            ≤ (BleadingCoeffs.Bcoeff i : ℝ) * t * x ^ i := by
      intro i hi
      by_cases hBi : 0 ≤ BleadingCoeffs.Bcoeff i
      · have hBshift0 : BleadingCoeffs.Bshift i = 0 := by
          have : ¬ BleadingCoeffs.Bcoeff i < 0 := not_lt_of_ge hBi
          simp [BleadingCoeffs.Bshift, this]
        have hBshift0Num : BleadingCoeffs.BshiftNum i = 0 := by
          simpa using! hBshift0
        have hBkeep : BleadingCoeffs.Bkeep i = BleadingCoeffs.Bcoeff i := by
          simp [BleadingCoeffs.Bkeep, hBi]
        have hBkeepNum : BleadingCoeffs.BkeepNum i = BleadingCoeffs.Bcoeff i := by
          simpa using! hBkeep
        have hxpow : 0 ≤ x ^ i := pow_nonneg hx0 _
        have hbase :
            (BleadingCoeffs.Bkeep i : ℝ) * x ^ i ≤ (BleadingCoeffs.Bcoeff i : ℝ) * x ^ i := by
          simp [hBkeepNum]
        have hscale :
            (BleadingCoeffs.Bcoeff i : ℝ) * x ^ i ≤
              (BleadingCoeffs.Bcoeff i : ℝ) * t * x ^ i := by
          have hBiR : (0 : ℝ) ≤ (BleadingCoeffs.Bcoeff i : ℝ) := by exact_mod_cast hBi
          have hnonneg : 0 ≤ (BleadingCoeffs.Bcoeff i : ℝ) * x ^ i := mul_nonneg hBiR hxpow
          have := mul_le_mul_of_nonneg_left ht hnonneg
          simpa [mul_assoc, mul_left_comm, mul_comm] using! this
        -- After simplification, this is exactly `hscale`.
        -- simpa [hBshift0, hBkeep] using! hscale
        have hmain :
            (BleadingCoeffs.Bkeep i : ℝ) * x ^ i ≤
              (BleadingCoeffs.Bcoeff i : ℝ) * t * x ^ i :=
          hbase.trans hscale
        simpa [hBshift0Num, hBkeepNum, add_assoc] using! hmain
      · have hBi' : BleadingCoeffs.Bcoeff i < 0 := lt_of_not_ge hBi
        have hBkeep0 : BleadingCoeffs.Bkeep i = 0 := by simp [BleadingCoeffs.Bkeep, hBi]
        have hBkeep0Num : BleadingCoeffs.BkeepNum i = 0 := by
          simpa using! hBkeep0
        have hi1 : 1 ≤ i := by
          -- `Bcoeff 0 = 0`, so negativity forces `i ≥ 1`.
          cases i with
          | zero =>
              exfalso
              have hB0 : BleadingCoeffs.Bcoeff 0 = 0 := BleadingCoeffs_Bcoeff_zero
              simp [hB0] at hBi'
          | succ i => exact Nat.succ_le_succ (Nat.zero_le i)
        have hBshift_def :
            BleadingCoeffs.Bshift i = BleadingCoeffs.cQ * BleadingCoeffs.Bcoeff i := by
          simp [BleadingCoeffs.Bshift, hBi']
        have hcQ : (BleadingCoeffs.cQ : ℝ) = (1 / 23 : ℝ) := by
          norm_num [BleadingCoeffs.cQ]
        have hmul_neg :
            (BleadingCoeffs.Bcoeff i : ℝ) * (BleadingCoeffs.cQ : ℝ) ≤
              (BleadingCoeffs.Bcoeff i : ℝ) * (t * x) := by
          -- Use `t*x ≤ cQ` and the negativity of `Bcoeff i`.
          have htx : t * x ≤ (BleadingCoeffs.cQ : ℝ) := by simpa [hcQ] using! htr
          have hBiR : (BleadingCoeffs.Bcoeff i : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hBi')
          -- Multiply by nonpositive `Bcoeff` reverses.
          simpa [mul_assoc, mul_left_comm, mul_comm] using!
            (mul_le_mul_of_nonpos_left htx hBiR)
        have hxpow : 0 ≤ x ^ (i - 1) := pow_nonneg hx0 _
        have hmul_neg' :
            (BleadingCoeffs.Bcoeff i : ℝ) * (BleadingCoeffs.cQ : ℝ) * x ^ (i - 1) ≤
              (BleadingCoeffs.Bcoeff i : ℝ) * (t * x) * x ^ (i - 1) :=
          mul_le_mul_of_nonneg_right hmul_neg hxpow
        have hxsplit : x ^ i = x ^ (1 : ℕ) * x ^ (i - 1) :=
          Eq.symm (pow_mul_pow_sub x hi1)
        have hBshift_le :
            (BleadingCoeffs.Bshift i : ℝ) * x ^ (i - 1) ≤
              (BleadingCoeffs.Bcoeff i : ℝ) * t * x ^ i := by
          have hBshift_cast :
              (BleadingCoeffs.Bshift i : ℝ) =
                (BleadingCoeffs.Bcoeff i : ℝ) * (BleadingCoeffs.cQ : ℝ) := by
            rw [hBshift_def]
            simp [Rat.cast_mul, mul_comm]
          calc
            (BleadingCoeffs.Bshift i : ℝ) * x ^ (i - 1)
                = (BleadingCoeffs.Bcoeff i : ℝ) * (BleadingCoeffs.cQ : ℝ) * x ^ (i - 1) := by
                      rw [hBshift_cast]
            _ ≤ (BleadingCoeffs.Bcoeff i : ℝ) * (t * x) * x ^ (i - 1) := hmul_neg'
            _ = (BleadingCoeffs.Bcoeff i : ℝ) * t * x ^ i := by
                  simp [hxsplit, pow_one, mul_assoc, mul_left_comm, mul_comm]
        simpa [hBkeep0Num, hi1, add_assoc] using! hBshift_le
    have hsumB :=
      Finset.sum_le_sum (s := Finset.range BleadingCoeffs.N) (fun i hi => htermB i hi)
    simpa [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm] using! hsumB
  have hC :
      (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Ckeep i : ℝ) * x ^ i) ≤
        ∑ i ∈ Finset.range BleadingCoeffs.N,
          (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi) * x ^ i := by
    have htermC :
        ∀ i : ℕ, i ∈ Finset.range BleadingCoeffs.N →
          (BleadingCoeffs.Ckeep i : ℝ) * x ^ i ≤
            (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi) * x ^ i := by
      intro i hi
      by_cases hCi : 0 ≤ BleadingCoeffs.Ccoeff i
      · have hinvFor : BleadingCoeffs.invPiForC i = BleadingCoeffs.invPiLower10Q := by
          simp [BleadingCoeffs.invPiForC, BleadingCoeffs.chooseInvPi, hCi]
        have hinv_le : (BleadingCoeffs.invPiForC i : ℝ) ≤ (1 / Real.pi) := by
          -- `invPiLower10Q ≤ 1/π`.
          simpa [hinvFor] using! invPiLower10Q_le_inv_pi
        have hCiR : (0 : ℝ) ≤ (BleadingCoeffs.Ccoeff i : ℝ) := by exact_mod_cast hCi
        have hmul :
            (BleadingCoeffs.invPiForC i : ℝ) * (BleadingCoeffs.Ccoeff i : ℝ) ≤
              (1 / Real.pi) * (BleadingCoeffs.Ccoeff i : ℝ) := by
          exact mul_le_mul_of_nonneg_right hinv_le hCiR
        have hxpow : 0 ≤ x ^ i := pow_nonneg hx0 _
        -- `Ckeep = invPiForC * Ccoeff`.
        have hCkeep :
            (BleadingCoeffs.Ckeep i : ℝ) =
              (BleadingCoeffs.invPiForC i : ℝ) * (BleadingCoeffs.Ccoeff i : ℝ) := by
          simp [BleadingCoeffs.Ckeep, Rat.cast_mul]
        calc
          (BleadingCoeffs.Ckeep i : ℝ) * x ^ i
              = ((BleadingCoeffs.invPiForC i : ℝ) * (BleadingCoeffs.Ccoeff i : ℝ)) * x ^ i := by
                    simpa using! congrArg (fun z => z * x ^ i) hCkeep
          _ ≤ ((1 / Real.pi) * (BleadingCoeffs.Ccoeff i : ℝ)) * x ^ i := by
                exact mul_le_mul_of_nonneg_right hmul hxpow
          _ = (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi) * x ^ i := by
                ring_nf
      · have hCi' : BleadingCoeffs.Ccoeff i < 0 := lt_of_not_ge hCi
        have hinvFor : BleadingCoeffs.invPiForC i = BleadingCoeffs.invPiUpper10Q := by
          have : ¬ 0 ≤ BleadingCoeffs.Ccoeff i := hCi
          simp [BleadingCoeffs.invPiForC, BleadingCoeffs.chooseInvPi, this]
        have hinv_ge : (1 / Real.pi) ≤ (BleadingCoeffs.invPiForC i : ℝ) := by
          simpa [hinvFor] using! inv_pi_le_invPiUpper10Q
        have hCiR : (BleadingCoeffs.Ccoeff i : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hCi')
        have hmul :
            (BleadingCoeffs.invPiForC i : ℝ) * (BleadingCoeffs.Ccoeff i : ℝ) ≤
              (1 / Real.pi) * (BleadingCoeffs.Ccoeff i : ℝ) := by
          -- Multiply `1/pi ≤ invPiForC` by a nonpositive `Ccoeff`.
          simpa [mul_assoc, mul_left_comm, mul_comm] using!
            (mul_le_mul_of_nonpos_right hinv_ge hCiR)
        have hxpow : 0 ≤ x ^ i := pow_nonneg hx0 _
        have hCkeep :
            (BleadingCoeffs.Ckeep i : ℝ) =
              (BleadingCoeffs.invPiForC i : ℝ) * (BleadingCoeffs.Ccoeff i : ℝ) := by
          simp [BleadingCoeffs.Ckeep, Rat.cast_mul]
        calc
          (BleadingCoeffs.Ckeep i : ℝ) * x ^ i
              = ((BleadingCoeffs.invPiForC i : ℝ) * (BleadingCoeffs.Ccoeff i : ℝ)) * x ^ i := by
                    simpa using! congrArg (fun z => z * x ^ i) hCkeep
          _ ≤ ((1 / Real.pi) * (BleadingCoeffs.Ccoeff i : ℝ)) * x ^ i := by
                exact mul_le_mul_of_nonneg_right hmul hxpow
          _ = (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi) * x ^ i := by
                ring_nf
    exact Finset.sum_le_sum htermC
  -- Combine the three bounds.
  have hBC :
      (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bkeep i : ℝ) * x ^ i) +
          (∑ i ∈ Finset.range BleadingCoeffs.N,
            if 1 ≤ i then
              (BleadingCoeffs.Bshift i : ℝ) * x ^ (i - 1)
            else 0) +
          (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Ckeep i : ℝ) * x ^ i)
        ≤ (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bcoeff i : ℝ) * t * x ^ i) +
          (∑ i ∈ Finset.range BleadingCoeffs.N,
            (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi) * x ^ i) := by
    -- Add the `B` and `C` inequalities.
    simpa [add_assoc] using! (add_le_add hB hC)
  have hABC :
      (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Akeep i : ℝ) * x ^ i) +
          (∑ i ∈ Finset.range BleadingCoeffs.N,
            if 2 ≤ i then
              (BleadingCoeffs.Ashift i : ℝ) * x ^ (i - 2)
            else 0) +
          ((∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bkeep i : ℝ) * x ^ i) +
            (∑ i ∈ Finset.range BleadingCoeffs.N,
              if 1 ≤ i then
                (BleadingCoeffs.Bshift i : ℝ) * x ^ (i - 1)
              else 0) +
            (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Ckeep i : ℝ) * x ^ i))
        ≤ (∑ i ∈ Finset.range BleadingCoeffs.N,
              (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) * x ^ i) +
          ((∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bcoeff i : ℝ) * t * x ^ i) +
            (∑ i ∈ Finset.range BleadingCoeffs.N,
              (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi) * x ^ i)) := by
    simpa [add_assoc] using! (add_le_add hA hBC)
  -- Rewrite the RHS into a single sum using distributivity, and discharge the final goal.
  have hRsplit :
      (∑ i ∈ Finset.range BleadingCoeffs.N,
          ((BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) +
              (BleadingCoeffs.Bcoeff i : ℝ) * t +
              (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi)) *
            x ^ i) =
        (∑ i ∈ Finset.range BleadingCoeffs.N,
          (BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) * x ^ i) +
          (∑ i ∈ Finset.range BleadingCoeffs.N, (BleadingCoeffs.Bcoeff i : ℝ) * t * x ^ i) +
          (∑ i ∈ Finset.range BleadingCoeffs.N,
            (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi) * x ^ i) := by
    -- Expand `(*)` over `+` inside the sum, then split using `sum_add_distrib`.
    simp [add_mul, Finset.sum_add_distrib, add_assoc, mul_assoc]
  -- Reassociate `hABC` and rewrite the RHS using `hRsplit`.
  grind only


/-- If `‖z - a‖ ≤ δ` with `a ∈ ℝ`, then `a - δ ≤ re z`. -/
public lemma re_ge_sub_of_norm_sub_le (z : ℂ) (a δ : ℝ) (h : ‖z - (a : ℂ)‖ ≤ δ) :
    a - δ ≤ z.re := by
  have h' : |z.re - a| ≤ δ := by
    simpa [Complex.sub_re, Complex.ofReal_re] using! (Complex.abs_re_le_norm (z - (a : ℂ))).trans h
  have h'' : -δ ≤ z.re - a := (abs_le.1 h').1
  linarith


end SpherePacking.Dim24.AppendixA
