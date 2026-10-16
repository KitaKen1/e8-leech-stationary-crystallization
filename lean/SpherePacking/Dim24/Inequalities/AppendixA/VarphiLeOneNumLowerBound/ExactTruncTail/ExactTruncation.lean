-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.CoeffModel
import SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.ExactTruncTail.AuxIneqs
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PiBoundsAndTruncCompare


/-!
Exact truncation sum and comparison with the PARI/GP truncation polynomial.

We define the exact finite head `exactTrunc t` obtained by summing the modeled coefficients against
`r(t)^i`, and prove that the PARI/GP truncation polynomial evaluation is bounded above by this
exact head (using the keep/shift inequalities from `AuxIneqs`).
-/

open scoped BigOperators

namespace SpherePacking.Dim24.AppendixA

noncomputable section

namespace VarphiLeOne

open BleadingCoeffs

/-
### Exact truncation and tail bound

We compare the PARI/GP truncation polynomial against the exact finite head of the `q`-series, and
bound the remaining tails by `eps * r(t)^12`.
-/

/-- The exact coefficient of `r(t)^i` in the modeled head (as a real number). -/
@[expose] public def exactCoeff (t : ℝ) (i : ℕ) : ℝ :=
  (Acoeff i : ℝ) * t ^ (2 : ℕ) +
    (Bcoeff i : ℝ) * t * (1 / Real.pi) +
      (Ccoeff i : ℝ) * (1 / (Real.pi ^ 2))

/-- The exact finite head `∑ exactCoeff t i * r(t)^i` used in the `t ≤ 1` comparison. -/
@[expose] public def exactTrunc (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range BleadingCoeffs.N, exactCoeff t i * (r t) ^ i

/-- Comparison between the truncation polynomial evaluation and the exact head `exactTrunc t`. -/
public lemma trunc_eval₂_le_exactTrunc (t : ℝ) (ht : 1 ≤ t) :
    ((-varphi_trunc_leOne).eval₂ (algebraMap ℚ ℝ) (r t)) ≤ exactTrunc t := by
  set x : ℝ := r t
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have ht2 : 1 ≤ t ^ (2 : ℕ) := by
    have : (1 : ℝ) * (1 : ℝ) ≤ t * t := mul_le_mul ht ht (by positivity) ht0
    simpa [pow_two] using! this
  have htr : t * x ≤ (1 / 23 : ℝ) := by simpa [x] using! (t_mul_r_le_one_div_23 (t := t) ht)
  have htr0 : 0 ≤ t * x := mul_nonneg ht0 hx0
  have htr_sq : (t * x) ^ (2 : ℕ) ≤ (1 / 23 : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ htr0 htr 2
  have hinvPi_lo : (BleadingCoeffs.invPiLower10Q : ℝ) ≤ (1 / Real.pi) := invPiLower10Q_le_inv_pi
  have hinvPi_hi : (1 / Real.pi) ≤ (BleadingCoeffs.invPiUpper10Q : ℝ) := inv_pi_le_invPiUpper10Q
  -- Expand the polynomial evaluation as a coefficient sum.
  have hpoly := trunc_eval₂_eq_sum_range_formula (t := t)
  rw [hpoly]
  dsimp [exactTrunc, exactCoeff]
  -- Split each summand into its five pieces.
  have hterm :
      ∀ n : ℕ,
        (truncCoeffFormula n : ℝ) * x ^ n =
          ((Akeep n : ℝ) * x ^ n) +
          (if n + 2 < BleadingCoeffs.N then (Ashift (n + 2) : ℝ) * x ^ n else 0) +
          ((Bkeep n : ℝ) * x ^ n) +
            (if n + 1 < BleadingCoeffs.N then (Bshift (n + 1) : ℝ) * x ^ n else 0) +
            ((Ckeep n : ℝ) * x ^ n) := by
    intro n
    by_cases hA : n + 2 < BleadingCoeffs.N <;> by_cases hB : n + 1 < BleadingCoeffs.N <;>
      simp [truncCoeffFormula, hA, hB, add_mul, x, add_assoc, add_comm]
  have hsplit :
      Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (truncCoeffFormula n : ℝ) * x ^ n) =
        Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Akeep n : ℝ) * x ^ n) +
          Finset.sum (Finset.range BleadingCoeffs.N)
              (fun n => if n + 2 < BleadingCoeffs.N then (Ashift (n + 2) : ℝ) * x ^ n else 0) +
            Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Bkeep n : ℝ) * x ^ n) +
              Finset.sum (Finset.range BleadingCoeffs.N)
                  (fun n => if n + 1 < BleadingCoeffs.N then (Bshift (n + 1) : ℝ) * x ^ n else 0) +
                Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Ckeep n : ℝ) * x ^ n) := by
    have hrewrite :
        Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (truncCoeffFormula n : ℝ) * x ^ n) =
          Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
              ((Akeep n : ℝ) * x ^ n) +
                (if n + 2 < BleadingCoeffs.N then (Ashift (n + 2) : ℝ) * x ^ n else 0) +
                ((Bkeep n : ℝ) * x ^ n) +
                  (if n + 1 < BleadingCoeffs.N then (Bshift (n + 1) : ℝ) * x ^ n else 0) +
                    ((Ckeep n : ℝ) * x ^ n)) :=
        Finset.sum_congr rfl fun x a => hterm x
    -- Split sums of additions.
    -- We reassociate/commute additions to match the desired grouping.
    -- `simp` with `Finset.sum_add_distrib` handles the bookkeeping.
    -- NOTE: explicit `simp` avoids `ring` on large expressions.
    simp [hrewrite, Finset.sum_add_distrib, add_assoc]
  -- Reindex the shift sums into `i - 2` and `i - 1` forms.
  have hshiftA :
      Finset.sum (Finset.range BleadingCoeffs.N)
          (fun n => if n + 2 < BleadingCoeffs.N then (Ashift (n + 2) : ℝ) * x ^ n else 0) =
        Finset.sum (Finset.range BleadingCoeffs.N)
          (fun i => if 2 ≤ i then (Ashift i : ℝ) * x ^ (i - 2) else 0) := by
    simpa using! (sum_shift2_eq (N := BleadingCoeffs.N) (x := x) (f := fun i => (Ashift i : ℝ)))
  have hshiftB :
      Finset.sum (Finset.range BleadingCoeffs.N)
          (fun n => if n + 1 < BleadingCoeffs.N then (Bshift (n + 1) : ℝ) * x ^ n else 0) =
        Finset.sum (Finset.range BleadingCoeffs.N)
          (fun i => if 1 ≤ i then (Bshift i : ℝ) * x ^ (i - 1) else 0) := by
    simpa using! (sum_shift1_eq (N := BleadingCoeffs.N) (x := x) (f := fun i => (Bshift i : ℝ)))
  -- Now prove termwise bounds for each part.
  have hAkeep :
        Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Akeep n : ℝ) * x ^ n) ≤
          Finset.sum (Finset.range BleadingCoeffs.N)
            (fun n => (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have hn' : n < BleadingCoeffs.N := Finset.mem_range.1 hn
    have hsign : 0 ≤ Acoeff n := by
      simpa using! (Acoeff_nonneg_fin ⟨n, hn'⟩)
    have hn0 : 0 ≤ (Acoeff n : ℝ) := by exact_mod_cast hsign
    -- Positive: keep the coefficient and use `1 ≤ t^2`.
    have hmul :
        (Acoeff n : ℝ) * x ^ n ≤ (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n := by
      have hxpow : 0 ≤ x ^ n := by positivity
      have := mul_le_mul_of_nonneg_right ht2 (mul_nonneg hn0 hxpow)
      simpa [mul_assoc, mul_left_comm, mul_comm] using! this
    simpa [Akeep, hsign, mul_assoc, mul_left_comm, mul_comm] using! hmul
  have hAshift :
        Finset.sum (Finset.range BleadingCoeffs.N)
            (fun i => if 2 ≤ i then (Ashift i : ℝ) * x ^ (i - 2) else 0) ≤
          Finset.sum (Finset.range BleadingCoeffs.N)
            (fun n => (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    by_cases hn2 : 2 ≤ n
    · -- In-range shifted term.
      dsimp [Ashift]
      by_cases hneg : Acoeff n < 0
      · have hneg' : (Acoeff n : ℝ) < 0 := by exact_mod_cast hneg
        have hxpow : 0 ≤ x ^ (n - 2) := by positivity
        have hxpow' : 0 ≤ x ^ n := by positivity
        -- Use `(t*x)^2 ≤ c^2`.
        have htx_sq : (t * x) ^ (2 : ℕ) ≤ (cQ : ℝ) ^ (2 : ℕ) := by
          -- `t*x ≤ 1/23 = cQ`.
          have htx : t * x ≤ (cQ : ℝ) := by
            -- `t*x ≤ 1/23`, rewrite `cQ`.
            simpa [cQ] using! htr
          exact pow_le_pow_left₀ htr0 htx 2
          -- Rewrite the target inequality into an inequality on positive scalars, then flip using
          -- `Acoeff n < 0`.
        have hscalar :
            (t ^ (2 : ℕ)) * x ^ n ≤ (cQ : ℝ) ^ (2 : ℕ) * x ^ (n - 2) := by
          -- `t^2 * x^n = (t*x)^2 * x^(n-2)`.
          have hrew : (t ^ (2 : ℕ)) * x ^ n = (t * x) ^ (2 : ℕ) * x ^ (n - 2) := by
            -- `x^n = x^(n-2) * x^2` and `t^2*x^2 = (t*x)^2`.
            have hn' : (n - 2) + 2 = n := Nat.sub_add_cancel hn2
            -- `x^n = x^(n-2) * x^2`
            have hxsplit : x ^ n = x ^ (n - 2) * x ^ (2 : ℕ) := by
              -- Avoid `simp` loops by rewriting `n` first, then using `pow_add`.
              exact Eq.symm (pow_sub_mul_pow x hn2)
            -- assemble
            calc
              (t ^ (2 : ℕ)) * x ^ n
                  = (t ^ (2 : ℕ)) * (x ^ (n - 2) * x ^ (2 : ℕ)) := by simp [hxsplit]
              _ = (t ^ (2 : ℕ)) * x ^ (2 : ℕ) * x ^ (n - 2) := by ring_nf
              _ = (t * x) ^ (2 : ℕ) * x ^ (n - 2) := by
                    -- `t^2 * x^2 = (t*x)^2`.
                    simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
              _ = (t * x) ^ (2 : ℕ) * x ^ (n - 2) := rfl
          -- Apply `htx_sq` and multiply by `x^(n-2)`.
          have h := mul_le_mul_of_nonneg_right htx_sq hxpow
          simpa [hrew, mul_assoc, mul_left_comm, mul_comm] using! h
        have hmul :
            (cQ : ℝ) ^ (2 : ℕ) * (Acoeff n : ℝ) * x ^ (n - 2) ≤
              (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n := by
          have hscalar' :
              (Acoeff n : ℝ) * ((cQ : ℝ) ^ (2 : ℕ) * x ^ (n - 2)) ≤
                (Acoeff n : ℝ) * ((t ^ (2 : ℕ)) * x ^ n) :=
            mul_le_mul_of_nonpos_left hscalar (le_of_lt hneg')
          simpa [mul_assoc, mul_left_comm, mul_comm] using! hscalar'
        -- Finish the termwise estimate (just reassociation/commutation).
        simpa [Ashift, hn2, hneg, mul_assoc, mul_left_comm, mul_comm] using! hmul
      · -- If not negative, `Ashift = 0`.
        have hAn0 : 0 ≤ (Acoeff n : ℝ) := by
          have : 0 ≤ Acoeff n := le_of_not_gt hneg
          exact_mod_cast this
        have ht2' : 0 ≤ t ^ (2 : ℕ) := by positivity
        have hxpow' : 0 ≤ x ^ n := by positivity
        have hR : 0 ≤ (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n :=
          mul_nonneg (mul_nonneg hAn0 ht2') hxpow'
        -- Reduce to `0 ≤ RHS`.
        simpa [hn2, hneg, mul_assoc, mul_left_comm, mul_comm] using! hR
    · -- `n < 2`: shift term is zero.
      have hn' : n < BleadingCoeffs.N := Finset.mem_range.1 hn
      have hAn0 : 0 ≤ (Acoeff n : ℝ) := by
        have : 0 ≤ Acoeff n := Acoeff_nonneg_fin ⟨n, hn'⟩
        exact_mod_cast this
      have ht2' : 0 ≤ t ^ (2 : ℕ) := by positivity
      have hxpow' : 0 ≤ x ^ n := by positivity
      have hR : 0 ≤ (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n :=
        mul_nonneg (mul_nonneg hAn0 ht2') hxpow'
      simpa [hn2, mul_assoc, mul_left_comm, mul_comm] using! hR
  have hBpart :
      Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Bkeep n : ℝ) * x ^ n) +
          Finset.sum (Finset.range BleadingCoeffs.N)
              (fun i => if 1 ≤ i then (Bshift i : ℝ) * x ^ (i - 1) else 0) ≤
        Finset.sum (Finset.range BleadingCoeffs.N)
          (fun n => (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n) :=
    Bpart_sum_le (t := t) (x := x) ht hx0 htr htr0 hinvPi_lo hinvPi_hi
  have hCkeep :
      Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Ckeep n : ℝ) * x ^ n) ≤
        Finset.sum (Finset.range BleadingCoeffs.N)
          (fun n => (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) := by
    simpa [one_div] using! Ckeep_sum_le (x := x) hx0 hinvPi_lo hinvPi_hi
  -- Assemble: group all five parts and compare with the exact coefficient sum.
  have hmain :
      Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (truncCoeffFormula n : ℝ) * x ^ n) ≤
        Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
          (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n +
            (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n +
              (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) := by
    -- Rewrite the LHS into the split form.
    rw [hsplit]
    -- Rewrite the shift sums.
    rw [hshiftA, hshiftB]
    -- Bound each part, then add.
    have hA :
        Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Akeep n : ℝ) * x ^ n) +
            Finset.sum (Finset.range BleadingCoeffs.N)
                (fun i => if 2 ≤ i then (Ashift i : ℝ) * x ^ (i - 2) else 0)
          ≤
            Finset.sum (Finset.range BleadingCoeffs.N)
              (fun n => (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n) := by
      have hAshift0 :
          Finset.sum (Finset.range BleadingCoeffs.N)
              (fun i => if 2 ≤ i then (Ashift i : ℝ) * x ^ (i - 2) else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        by_cases hi2 : 2 ≤ i
        · have hi_lt : i < BleadingCoeffs.N := Finset.mem_range.1 hi
          have hnonneg : 0 ≤ Acoeff i := Acoeff_nonneg_fin ⟨i, hi_lt⟩
          have hnotneg : ¬Acoeff i < 0 := not_lt_of_ge hnonneg
          simp [hi2, Ashift, hnotneg]
        · simp [hi2]
      simpa [hAshift0] using! hAkeep
    have hB :
        Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Bkeep n : ℝ) * x ^ n) +
            Finset.sum (Finset.range BleadingCoeffs.N)
                (fun i => if 1 ≤ i then (Bshift i : ℝ) * x ^ (i - 1) else 0)
          ≤
            Finset.sum (Finset.range BleadingCoeffs.N)
              (fun n => (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n) :=
      hBpart
    have hC :
        Finset.sum (Finset.range BleadingCoeffs.N) (fun n => (Ckeep n : ℝ) * x ^ n) ≤
          Finset.sum (Finset.range BleadingCoeffs.N)
            (fun n => (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) :=
      hCkeep
    -- Add the three inequalities, then rewrite the single RHS sum into three sums.
    have hABC := add_le_add (add_le_add hA hB) hC
    have hsum :
          Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
              (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n +
                (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n +
                  (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) =
            (Finset.sum (Finset.range BleadingCoeffs.N)
                  (fun n => (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n) +
                Finset.sum (Finset.range BleadingCoeffs.N)
                  (fun n => (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n)) +
              Finset.sum (Finset.range BleadingCoeffs.N)
                (fun n => (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) := by
      -- Use `Finset.sum_add_distrib` twice; keep the rewriting very explicit to avoid timeouts.
      have h1 :
          Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
              ((Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n +
                  (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n) +
                (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) =
            Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
                (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n +
                  (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n) +
              Finset.sum (Finset.range BleadingCoeffs.N)
                (fun n => (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) := by
        -- `sum (f+g) = sum f + sum g`
        exact Finset.sum_add_distrib
      have h2 :
          Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
                (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n +
                  (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n) =
              Finset.sum (Finset.range BleadingCoeffs.N)
                  (fun n => (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n) +
                Finset.sum (Finset.range BleadingCoeffs.N)
                  (fun n => (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n) :=
        Finset.sum_add_distrib
      calc
        Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
              (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n +
                (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n +
                  (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n)
            =
            Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
              ((Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n +
                  (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n) +
                (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) := by
              simp [add_assoc]
        _ = Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
                (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n +
                  (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n) +
              Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
                (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) :=
              h1
        _ =
            (Finset.sum (Finset.range BleadingCoeffs.N)
                  (fun n => (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n) +
                Finset.sum (Finset.range BleadingCoeffs.N)
                  (fun n => (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n)) +
              Finset.sum (Finset.range BleadingCoeffs.N)
                (fun n => (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) := by
          rw [h2]
    -- Rewrite the goal RHS and close with `hABC`.
    rw [hsum]
    simpa [add_assoc, add_left_comm, add_comm] using! hABC
  -- The RHS is exactly `exactTrunc`.
  have hR :
      Finset.sum (Finset.range BleadingCoeffs.N) (fun n =>
          (Acoeff n : ℝ) * (t ^ (2 : ℕ)) * x ^ n +
            (Bcoeff n : ℝ) * t * (1 / Real.pi) * x ^ n +
              (Ccoeff n : ℝ) * (Real.pi ^ (2 : ℕ))⁻¹ * x ^ n) =
        Finset.sum (Finset.range BleadingCoeffs.N) (fun n => exactCoeff t n * x ^ n) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      -- Expand `exactCoeff` and distribute over `x^n`.
      simp [exactCoeff, add_mul, mul_assoc, add_assoc]
  -- Conclude.
  have h := le_trans hmain (le_of_eq hR)
  simpa [x, exactTrunc, exactCoeff, mul_add, add_mul, add_assoc, mul_assoc] using! h


end VarphiLeOne

end

end SpherePacking.Dim24.AppendixA
