-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.ZonalPolynomial24
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bridge from harmonic projection to Gegenbauer polynomials (dimension 24)

This file relates the explicit univariate polynomial `harmPoly24Raw k` extracted from the harmonic
feature map to the recurrence-defined Gegenbauer polynomial `(gegenbauer 11 k)`. Concretely, we
show

`(harmPoly24Raw k).eval t = (scale24 k)⁻¹ * (gegenbauer 11 k).eval t`,

where `scale24 k = 2^k * (11).ascFactorial k`.

## Main definitions
* `scale24`

## Main statements
* `harmPoly24Raw_eval_eq_inv_scale_mul_gegenbauer_eval`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.ZonalPolynomial24
noncomputable section

open scoped BigOperators

open Finset Polynomial

open Gegenbauer24.AdditionTheoremFixed.Zonal

lemma natFactorial_cast_ne_zero (n : ℕ) : (Nat.factorial n : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.factorial_ne_zero n)

/-!
### Simplifying the `aCoeff` recursion denominators in dimension `24`

In dimension `24`, the `A`-coefficient simplifies to `4*j*(k-j+11)` (provided `2*j ≤ k`), so
`aCoeff` satisfies a simpler recursion that matches a closed-form factorial expression after
scaling.
-/

lemma A_simp (k j : ℕ) (hj : 2 * j ≤ k) :
    Zonal.A k j = 4 * j * (k - j + 11) := by
  have hj' : j ≤ k - j := Nat.le_sub_of_add_le (by simpa [two_mul] using! hj)
  have hsub : k - 2 * j + j = k - j := by
    calc
      k - 2 * j + j = (k - j - j) + j := by
        -- `k - 2*j = k - (j+j)`.
        simp [two_mul, Nat.sub_sub]
      _ = k - j := Nat.sub_add_cancel hj'
  calc
    Zonal.A k j = 2 * j * (2 * (k - 2 * j) + 2 * j + 22) := rfl
    _ = 2 * j * (2 * ((k - 2 * j) + j) + 22) := by
          simp [Nat.mul_add, Nat.add_assoc]
    _ = 2 * j * (2 * (k - j) + 22) := by simp [hsub]
    _ = 2 * j * (2 * (k - j + 11)) := by
          simp [Nat.mul_add, Nat.add_assoc, Nat.two_mul]
    _ = 4 * j * (k - j + 11) := by
          ring

lemma A_simp_succ (k j : ℕ) (hj : 2 * (j + 1) ≤ k) :
    Zonal.A k (j + 1) = 4 * (j + 1) * (k - j + 10) := by
  have hjle : j + 1 ≤ k := by
    lia
  have hk_j : 1 ≤ k - j :=
    Nat.le_sub_of_add_le' hjle
  have hsub : k - (j + 1) + 11 = k - j + 10 := by
    grind only
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hsub] using!
    (A_simp (k := k) (j := j + 1) hj)

lemma B_simp (k j : ℕ) :
    Zonal.B k j = (k - 2 * j) * ((k - 2 * j) - 1) := rfl

lemma aCoeff_succ_simp (k j : ℕ) (hj : 2 * (j + 1) ≤ k) :
    aCoeff k (j + 1) =
      - (aCoeff k j) * ((Zonal.B k j : ℕ) : ℝ) / ((4 * (j + 1) * (k - j + 10) : ℕ) : ℝ) := by
  simp [Zonal.aCoeff_succ, A_simp_succ (k := k) (j := j) hj]

/-!
### Scaling: `harmPoly24Raw` vs `gegenbauer 11`

We scale `harmPoly24Raw` by `scale24 k = 2^k * (11).ascFactorial k` and show the resulting
polynomial satisfies the defining Gegenbauer recurrence with parameter `λ = 11`.
-/

-- The scaling factor used to normalize `harmPoly24Raw` into the Gegenbauer basis.
/-- The scaling factor `2^k * (11).ascFactorial k` used in the Gegenbauer normalization. -/
@[expose]
public noncomputable def scale24 (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * (Nat.ascFactorial 11 k : ℝ)

/-- The scaling factor `scale24 k` is nonzero. -/
public lemma scale24_ne_zero (k : ℕ) : scale24 k ≠ 0 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k h2
  have hasc : (Nat.ascFactorial 11 k : ℝ) ≠ 0 := by
    positivity
  exact mul_ne_zero hpow hasc

noncomputable def scaledHarmPoly24Raw (k : ℕ) : Polynomial ℝ :=
  (C (scale24 k)) * (harmPoly24Raw k)

def gCoeff (k j : ℕ) : ℝ :=
  ((-1 : ℝ) ^ j) *
    (2 : ℝ) ^ (k - 2 * j) *
      (Nat.factorial (k + 10 - j) : ℝ) /
        ((Nat.factorial j : ℝ) * (Nat.factorial (k - 2 * j) : ℝ) * (Nat.factorial 10 : ℝ))

noncomputable def gPoly (k : ℕ) : Polynomial ℝ :=
  (Finset.range (k / 2 + 1)).sum (fun j => (C (gCoeff k j)) * (X ^ (k - 2 * j)))

lemma gPoly_eval (k : ℕ) (t : ℝ) :
    (gPoly k).eval t =
      (Finset.range (k / 2 + 1)).sum (fun j => (gCoeff k j) * t ^ (k - 2 * j)) := by
  let φ : Polynomial ℝ →+* ℝ := Polynomial.eval₂RingHom (RingHom.id ℝ) t
  have hφ : (gPoly k).eval t = φ (gPoly k) := rfl
  calc
    (gPoly k).eval t = φ (gPoly k) := hφ
    _ =
        (Finset.range (k / 2 + 1)).sum (fun j =>
          φ ((C (gCoeff k j)) * (X ^ (k - 2 * j)))) := by
          simp [gPoly, φ, map_sum]
    _ = (Finset.range (k / 2 + 1)).sum (fun j => (gCoeff k j) * t ^ (k - 2 * j)) := by
          simp [φ]

lemma scale_mul_aCoeff_eq_gCoeff (k j : ℕ) (hj : 2 * j ≤ k) :
    (scale24 k) * (aCoeff k j) = gCoeff k j := by
  induction j with
  | zero =>
      -- Base case: `aCoeff k 0 = (k!)⁻¹`.
      have h10 : (Nat.factorial 10 : ℝ) ≠ 0 := natFactorial_cast_ne_zero 10
      have hkfac : (Nat.factorial k : ℝ) ≠ 0 := natFactorial_cast_ne_zero k
      have hmul : (Nat.factorial 10 : ℝ) * (Nat.ascFactorial 11 k : ℝ) =
          (Nat.factorial (k + 10) : ℝ) := by
        -- `10! * 11.ascFactorial k = (10+k)!`.
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
          (show (Nat.factorial 10 : ℝ) * (Nat.ascFactorial 11 k : ℝ) =
                (Nat.factorial (10 + k) : ℝ) by
            exact_mod_cast (Nat.factorial_mul_ascFactorial 10 k))
      have hasc : (Nat.ascFactorial 11 k : ℝ) =
          (Nat.factorial (k + 10) : ℝ) / (Nat.factorial 10 : ℝ) :=
        (eq_div_iff h10).2 (by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! hmul)
      simp [scale24, gCoeff, Zonal.aCoeff_zero, hasc, div_eq_mul_inv, mul_assoc, mul_comm]
  | succ j ih =>
      have hj' : 2 * j ≤ k := le_trans (Nat.mul_le_mul_left 2 (Nat.le_succ j)) hj
      have ha :
          aCoeff k (j + 1) =
            - (aCoeff k j) * ((Zonal.B k j : ℕ) : ℝ) /
              ((4 * (j + 1) * (k - j + 10) : ℕ) : ℝ) := by
        simpa [Nat.succ_eq_add_one] using! (aCoeff_succ_simp (k := k) (j := j) (hj := hj))
      have hden : ((4 * (j + 1) * (k - j + 10) : ℕ) : ℝ) ≠ 0 := by
        have : 0 < 4 * (j + 1) * (k - j + 10) := by
          positivity
        exact_mod_cast (Nat.ne_of_gt this)
      have hgj :
          gCoeff k (j + 1) =
            - (gCoeff k j) * ((Zonal.B k j : ℕ) : ℝ) /
              ((4 * (j + 1) * (k - j + 10) : ℕ) : ℝ) := by
        -- Closed-form ratio computation. Clear the external denominator first, then clear factorial
        -- denominators via `field_simp`.
        have hfj : (Nat.factorial j : ℝ) ≠ 0 := natFactorial_cast_ne_zero j
        have hfj1 : (Nat.factorial (j + 1) : ℝ) ≠ 0 := natFactorial_cast_ne_zero (j + 1)
        have hf10 : (Nat.factorial 10 : ℝ) ≠ 0 := natFactorial_cast_ne_zero 10
        have hfkj : (Nat.factorial (k - j * 2) : ℝ) ≠ 0 := natFactorial_cast_ne_zero (k - j * 2)
        have hfkj1 : (Nat.factorial (k - j * 2 - 1) : ℝ) ≠ 0 :=
          natFactorial_cast_ne_zero (k - j * 2 - 1)
        have hfkj2 : (Nat.factorial (k - (2 + j * 2)) : ℝ) ≠ 0 :=
          natFactorial_cast_ne_zero (k - (2 + j * 2))
        have hsub10 : k + 10 - (j + 1) = k + 9 - j := by omega
        have hsub2 : k - 2 * (j + 1) = k - 2 * j - 2 := by omega
        apply (eq_div_iff hden).2
        simp only [gCoeff, pow_succ, mul_neg, mul_one, neg_mul, hsub10, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.reduceAdd, zero_add, Nat.factorial_zero,
          Nat.reduceMul, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev, B_simp, neg_inj]
        have hkge : 2 + j * 2 ≤ k := by
          have : 2 * j + 2 ≤ k := by
            simpa [Nat.mul_add, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using! hj
          simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using! this
        have hk2 : 2 ≤ k - j * 2 := Nat.le_sub_of_add_le hkge
        have hk1 : 1 ≤ k - j * 2 := le_trans (by decide : (1 : ℕ) ≤ 2) hk2
        have hk1' : 1 ≤ k - j * 2 - 1 := by
          exact Nat.le_sub_of_add_le hk2
        have hk2ne : ((k - j * 2 : ℕ) : ℝ) ≠ 0 := by
          have : 0 < k - j * 2 := lt_of_lt_of_le (by decide : 0 < 2) hk2
          exact_mod_cast (Nat.ne_of_gt this)
        have hk1ne : ((k - j * 2 - 1 : ℕ) : ℝ) ≠ 0 := by
          have : 0 < k - j * 2 - 1 := Nat.lt_of_lt_of_le (by decide : 0 < 1) hk1'
          exact_mod_cast (Nat.ne_of_gt this)
        -- Clear the remaining denominators; `field_simp` can leave auxiliary goals in the form of
        -- disjunctions recording the (impossible) denominator-zero cases, so we close all goals in
        -- one block.
        field_simp [hden, hk2ne, hk1ne, hfj, hfj1, hf10, hfkj, hfkj1, hfkj2]
        have hsubk : k - (2 + j * 2) = k - j * 2 - 2 := by
          -- `k - (2 + j*2) = k - (j*2 + 2) = k - j*2 - 2`.
          exact Nat.Simproc.sub_add_eq_comm k 2 (j * 2)
        have hfac_k : (Nat.factorial (k - j * 2) : ℝ) =
            ((k - j * 2 : ℕ) : ℝ) * ((k - j * 2 - 1 : ℕ) : ℝ) *
              (Nat.factorial (k - (2 + j * 2)) : ℝ) := by
          -- Expand `factorial (k - j*2)` twice.
          have hfac1_nat :
              Nat.factorial (k - j * 2) = (k - j * 2) * Nat.factorial (k - j * 2 - 1) := by
            have hn : (k - j * 2 - 1) + 1 = k - j * 2 := by
              simpa [Nat.sub_sub] using! (Nat.sub_add_cancel hk1)
            simpa [hn, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using!
              (Nat.factorial_succ (k - j * 2 - 1))
          have hfac2_nat :
              Nat.factorial (k - j * 2 - 1) = (k - j * 2 - 1) * Nat.factorial (k - j * 2 - 2) := by
            have hn : (k - j * 2 - 2) + 1 = k - j * 2 - 1 := by omega
            simpa [hn, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using!
              (Nat.factorial_succ (k - j * 2 - 2))
          have hfac1 : (Nat.factorial (k - j * 2) : ℝ) =
              ((k - j * 2 : ℕ) : ℝ) * (Nat.factorial (k - j * 2 - 1) : ℝ) := by
            exact_mod_cast hfac1_nat
          have hfac2 : (Nat.factorial (k - j * 2 - 1) : ℝ) =
              ((k - j * 2 - 1 : ℕ) : ℝ) * (Nat.factorial (k - j * 2 - 2) : ℝ) := by
            exact_mod_cast hfac2_nat
          -- Reassociate and rewrite `k - j*2 - 2` as `k - (2 + j*2)`.
          calc
            (Nat.factorial (k - j * 2) : ℝ)
                =
                  ((k - j * 2 : ℕ) : ℝ) *
                    (((k - j * 2 - 1 : ℕ) : ℝ) * (Nat.factorial (k - j * 2 - 2) : ℝ)) := by
                        simp [hfac1, hfac2]
            _ =
                  ((k - j * 2 : ℕ) : ℝ) * ((k - j * 2 - 1 : ℕ) : ℝ) *
                    (Nat.factorial (k - (2 + j * 2)) : ℝ) := by
                      simp [mul_assoc, hsubk]
        have hfac_10 : (Nat.factorial (k + 10 - j) : ℝ) =
            ((k - j + 10 : ℕ) : ℝ) * (Nat.factorial (k + 9 - j) : ℝ) := by
          have hn : (k + 9 - j) + 1 = k + 10 - j := by omega
          -- `factorial (n+1) = (n+1) * factorial n`.
          have hnat : Nat.factorial (k + 10 - j) = (k + 10 - j) * Nat.factorial (k + 9 - j) := by
            simpa [hn, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using!
              (Nat.factorial_succ (k + 9 - j))
          -- Cast and rewrite the scalar.
          have hkj : k + 10 - j = k - j + 10 := by omega
          simpa [hkj] using! (show (Nat.factorial (k + 10 - j) : ℝ) =
              ((k + 10 - j : ℕ) : ℝ) * (Nat.factorial (k + 9 - j) : ℝ) from
            (by exact_mod_cast hnat))
        have hpow2 : (2 : ℝ) ^ (k - j * 2) = (2 : ℝ) ^ (k - (2 + j * 2)) * 4 := by
          -- `k - j*2 = (k - (2 + j*2)) + 2`, using `2 ≤ k - j*2`.
          have hs : k - j * 2 - 2 + 2 = k - j * 2 := Nat.sub_add_cancel hk2
          have hs' : k - j * 2 - 2 = k - (2 + j * 2) := hsubk.symm
          calc
            (2 : ℝ) ^ (k - j * 2) = (2 : ℝ) ^ (k - j * 2 - 2 + 2) := by simp [hs]
            _ = (2 : ℝ) ^ (k - j * 2 - 2) * (2 : ℝ) ^ 2 := by
                  simp [pow_add, mul_comm]
            _ = (2 : ℝ) ^ (k - (2 + j * 2)) * 4 := by
                  -- `2^2 = 4`.
                  simp [hs', (show (2 : ℝ) ^ 2 = 4 by norm_num)]
        grind only
      grind only

lemma scaledHarmPoly24Raw_eq_gPoly (k : ℕ) : scaledHarmPoly24Raw k = gPoly k := by
  have hk (j : ℕ) (hj : j ∈ Finset.range (k / 2 + 1)) : 2 * j ≤ k := by
    have hj' : j < k / 2 + 1 := Finset.mem_range.1 hj
    have hjle : j ≤ k / 2 := Nat.lt_succ_iff.1 hj'
    exact (Nat.mul_le_mul_left 2 hjle).trans (Nat.mul_div_le k 2)
  unfold scaledHarmPoly24Raw harmPoly24Raw gPoly
  -- Distribute `C (scale24 k)` over the sum and rewrite the coefficients termwise.
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjk : 2 * j ≤ k := hk j hj
  have hsc : scale24 k * aCoeff k j = gCoeff k j := scale_mul_aCoeff_eq_gCoeff (k := k) (j := j) hjk
  -- `C s * (C a * X^n) = C (s*a) * X^n`.
  -- Avoid `simp` recursion by rewriting in two explicit steps.
  grind only [= map_mul]

/-!
### The `gPoly` recurrence and identification with `gegenbauer 11`
-/

abbrev lam : ℝ := (11 : ℝ)

def recA (n : ℕ) : ℝ :=
  (2 * ((n : ℝ) + 1 + lam)) / ((n + 2 : ℕ) : ℝ)

def recB (n : ℕ) : ℝ :=
  (((n : ℝ) + 2 * lam)) / ((n + 2 : ℕ) : ℝ)

@[simp] lemma gPoly_zero : gPoly 0 = (1 : Polynomial ℝ) := by
  have h10 : (Nat.factorial 10 : ℝ) ≠ 0 := natFactorial_cast_ne_zero 10
  have hcoeff : gCoeff 0 0 = 1 := by
    simp [gCoeff, h10]
  unfold gPoly
  simp [hcoeff]

@[simp] lemma gPoly_one : gPoly 1 = (C (2 * lam) : Polynomial ℝ) * X := by
  have h10 : (Nat.factorial 10 : ℝ) ≠ 0 := natFactorial_cast_ne_zero 10
  have hcoeff : gCoeff 1 0 = 2 * lam := by
    have h11_nat : Nat.factorial 11 = 11 * Nat.factorial 10 := by
      simpa using! (Nat.factorial_succ 10)
    have h11 : (Nat.factorial 11 : ℝ) = (11 : ℝ) * (Nat.factorial 10 : ℝ) := by
      exact_mod_cast h11_nat
    simp [gCoeff, lam, h11, div_eq_mul_inv, h10, mul_left_comm, mul_comm]
  unfold gPoly
  simp_all

lemma gCoeff_recurrence_core (n j : ℕ) (hj : 1 ≤ j) (h2 : 2 * j ≤ n + 1) :
    gCoeff (n + 2) j =
      (recA n) * gCoeff (n + 1) j - (recB n) * gCoeff n (j - 1) := by
  have hfj : (Nat.factorial j : ℝ) ≠ 0 := natFactorial_cast_ne_zero j
  have hfj1 : (Nat.factorial (j - 1) : ℝ) ≠ 0 := natFactorial_cast_ne_zero (j - 1)
  have hf10 : (Nat.factorial 10 : ℝ) ≠ 0 := natFactorial_cast_ne_zero 10
  have hfn2 : (Nat.factorial (n + 2 - 2 * j) : ℝ) ≠ 0 :=
    natFactorial_cast_ne_zero (n + 2 - 2 * j)
  have hfn1 : (Nat.factorial (n + 1 - 2 * j) : ℝ) ≠ 0 :=
    natFactorial_cast_ne_zero (n + 1 - 2 * j)
  have hden : ((n + 2 - 2 * j : ℕ) : ℝ) ≠ 0 := by
    have : 0 < n + 2 - 2 * j := by
      have : 2 * j < n + 2 := lt_of_le_of_lt h2 (Nat.lt_succ_self (n + 1))
      exact Nat.sub_pos_of_lt this
    exact_mod_cast (Nat.ne_of_gt this)
  have hsubDen : 2 + n - j * 2 = n + 2 - 2 * j := by omega
  have hsubDen1 : 1 + n - j * 2 = n + 1 - 2 * j := by omega
  have hden' : ((2 + n - j * 2 : ℕ) : ℝ) ≠ 0 := by simpa [hsubDen] using! hden
  have hfn2' : (Nat.factorial (2 + n - j * 2) : ℝ) ≠ 0 := by simpa [hsubDen] using! hfn2
  have hfn1' : (Nat.factorial (1 + n - j * 2) : ℝ) ≠ 0 := by simpa [hsubDen1] using! hfn1
  have hstep1 :
      gCoeff (n + 2) j =
        ((2 : ℝ) * ((n + 12 - j : ℕ) : ℝ) / ((n + 2 - 2 * j : ℕ) : ℝ)) * gCoeff (n + 1) j := by
    have hsub1 : n + 12 - j = (n + 11 - j) + 1 := by omega
    have hsub2 : n + 2 - 2 * j = (n + 1 - 2 * j) + 1 := by omega
    simp [gCoeff, hsub1, Nat.factorial_succ, mul_assoc, mul_comm, add_comm]
    field_simp [hden, hden', hfj, hf10, hfn2, hfn1, hfn2', hfn1']
    -- Normalize the remaining factorial/power fragments and clear the last denominator.
    have hfacA :
        (Nat.factorial (1 + (n + 11 - j)) : ℝ) =
          (((n + 11 - j) + 1 : ℕ) : ℝ) * (Nat.factorial (n + 11 - j) : ℝ) := by
      have h : 1 + (n + 11 - j) = (n + 11 - j) + 1 := by omega
      simpa [h] using!
        (show (Nat.factorial ((n + 11 - j) + 1) : ℝ) =
            (((n + 11 - j) + 1 : ℕ) : ℝ) * (Nat.factorial (n + 11 - j) : ℝ) from
          (by exact_mod_cast (Nat.factorial_succ (n + 11 - j))))
    have hfacB :
        (Nat.factorial (n + 2 - j * 2) : ℝ) =
          ((n + 2 - j * 2 : ℕ) : ℝ) * (Nat.factorial (n + 1 - j * 2) : ℝ) := by
      have h : n + 2 - j * 2 = (n + 1 - j * 2) + 1 := by omega
      simpa [h] using!
        (show (Nat.factorial ((n + 1 - j * 2) + 1) : ℝ) =
            (((n + 1 - j * 2) + 1 : ℕ) : ℝ) * (Nat.factorial (n + 1 - j * 2) : ℝ) from
          (by exact_mod_cast (Nat.factorial_succ (n + 1 - j * 2))))
    grind only
  have hstep2 :
      gCoeff n (j - 1) =
        (-(2 : ℝ) * (j : ℝ) / ((n + 2 - 2 * j : ℕ) : ℝ)) * gCoeff (n + 1) j := by
    have hsub : n + 2 - 2 * j = (n + 1 - 2 * j) + 1 := by omega
    have hjfac : Nat.factorial j = j * Nat.factorial (j - 1) := by
      cases j with
      | zero =>
          cases (Nat.not_succ_le_zero 0 hj)
      | succ j =>
          simp [Nat.factorial_succ]
    simp [gCoeff, hjfac, Nat.factorial_succ, mul_assoc, mul_comm, add_comm]
    field_simp [hden, hden', hfj, hfj1, hf10, hfn2, hfn1, hfn2', hfn1']
    have hsub10 : 10 + n - (j - 1) = n + 11 - j := by omega
    have hsubk : n - (j - 1) * 2 = n + 2 - j * 2 := by omega
    have hpow2 :
        (2 : ℝ) ^ (n - (j - 1) * 2) = (2 : ℝ) ^ (n + 1 - j * 2) * (2 : ℝ) := by
      have h : n - (j - 1) * 2 = (n + 1 - j * 2) + 1 := by omega
      simp [h, pow_succ]
    have hpowNeg1 :
        ((-1 : ℝ) ^ (j - 1)) = ((-1 : ℝ) ^ j) * (-1 : ℝ) := by
      have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
      grind only
    simp [hsubk, hpowNeg1, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_comm] at *
    field_simp [hden']
    -- Finish by rewriting the remaining factorial/power fragments.
    have hsub10' : 10 + n - (j - 1) = 11 + n - j := by omega
    have hfac2 :
        (Nat.factorial (2 + n - j * 2) : ℝ) =
          ((2 + n - j * 2 : ℕ) : ℝ) * (Nat.factorial (1 + n - j * 2) : ℝ) := by
      have h : 2 + n - j * 2 = (1 + n - j * 2) + 1 := by omega
      simpa [h] using!
        (show (Nat.factorial ((1 + n - j * 2) + 1) : ℝ) =
            (((1 + n - j * 2) + 1 : ℕ) : ℝ) * (Nat.factorial (1 + n - j * 2) : ℝ) from
          (by exact_mod_cast (Nat.factorial_succ (1 + n - j * 2))))
    grind only
  calc
    gCoeff (n + 2) j
        =
          ((2 : ℝ) * ((n + 12 - j : ℕ) : ℝ) / ((n + 2 - 2 * j : ℕ) : ℝ)) *
            gCoeff (n + 1) j := hstep1
    _ = (recA n) * gCoeff (n + 1) j - (recB n) * gCoeff n (j - 1) := by
      rw [hstep2]
      have hn2 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero (n + 1))
      -- At this point the goal is an identity in `ℝ` with only the denominators
      -- `↑(n+2-2*j)` and `↑(n+2)`.
      dsimp [recA, recB, lam]
      field_simp [hden, hn2]
      have hle : 2 * j ≤ n + 2 := by
        -- From `2*j ≤ n+1` and `n+1 ≤ n+2`.
        exact le_trans h2 (Nat.le_succ (n + 1))
      have hcast :
          ((n + 2 - 2 * j : ℕ) : ℝ) = (n : ℝ) + 2 - (2 * j : ℝ) := by
        have h' : ((n + 2 - 2 * j : ℕ) : ℝ) = (n + 2 : ℝ) - (2 * j : ℝ) := by
          simpa using! (Nat.cast_sub (R := ℝ) hle)
        -- Rewrite `↑(n+2)` as `↑n + 2` so later `simp` can expand `↑(2*j)` as `2*↑j`.
        simpa [Nat.cast_add, Nat.cast_ofNat, add_assoc, add_left_comm, add_comm] using! h'
      have hjle : j ≤ n + 12 := by
        -- `j ≤ 2*j ≤ n+1 ≤ n+12`.
        have hj2 : j ≤ 2 * j := by
          have h : j ≤ j + j := Nat.le_add_right j j
          convert (postTransparency := .instances) h using 1
          simp [two_mul]
        have hjn1 : j ≤ n + 1 := le_trans hj2 h2
        exact le_trans hjn1 (by omega)
      have hcast12N :
          ((n + 12 - j : ℕ) : ℝ) = (n : ℝ) + 12 - (j : ℝ) := by
        -- Same as above, but in the `n + 12 - j` form (this is what appears after `field_simp`).
        have h' : ((n + 12 - j : ℕ) : ℝ) = (n + 12 : ℝ) - (j : ℝ) := by
          simpa using! (Nat.cast_sub (R := ℝ) hjle)
        simpa [Nat.cast_add, Nat.cast_ofNat, add_assoc, add_left_comm, add_comm] using! h'
      -- Replace the remaining `ℕ` subtraction casts by `ℝ` subtraction so `ring_nf` can close.
      grind only

lemma gCoeff_recurrence_zero (n : ℕ) :
    gCoeff (n + 2) 0 = recA n * gCoeff (n + 1) 0 := by
  have hf10 : (Nat.factorial 10 : ℝ) ≠ 0 := natFactorial_cast_ne_zero 10
  have hfn2 : (Nat.factorial (n + 2) : ℝ) ≠ 0 := natFactorial_cast_ne_zero (n + 2)
  have hfn1 : (Nat.factorial (n + 1) : ℝ) ≠ 0 := natFactorial_cast_ne_zero (n + 1)
  have hden : ((n + 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero (n + 1))
  -- Unfold `gCoeff` at `j = 0` and use `factorial_succ` to simplify the ratio.
  simp [gCoeff, recA, lam, div_eq_mul_inv, Nat.factorial_succ, pow_succ, mul_assoc]
  -- Clear the remaining factorial denominators.
  grind only

lemma gCoeff_recurrence_even_last (m : ℕ) :
    gCoeff (2 * m + 2) (m + 1) = - (recB (2 * m)) * gCoeff (2 * m) m := by
  have hf10 : (Nat.factorial 10 : ℝ) ≠ 0 := natFactorial_cast_ne_zero 10
  have hfm : (Nat.factorial m : ℝ) ≠ 0 := natFactorial_cast_ne_zero m
  have hfm1 : (Nat.factorial (m + 1) : ℝ) ≠ 0 := natFactorial_cast_ne_zero (m + 1)
  have hden : ((2 * m + 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero (2 * m + 1))
  have hsubL : 2 * m + 2 - 2 * (m + 1) = 0 := by omega
  have hsubR : 2 * m - 2 * m = 0 := by omega
  have hkL : 2 * m + 2 + 10 - (m + 1) = m + 11 := by omega
  have hkR : 2 * m + 10 - m = m + 10 := by omega
  have hfacL :
      (Nat.factorial (m + 11) : ℝ) = ((m + 11 : ℕ) : ℝ) * (Nat.factorial (m + 10) : ℝ) := by
    exact_mod_cast (Nat.factorial_succ (m + 10))
  have hfacM : (Nat.factorial (m + 1) : ℝ) = ((m + 1 : ℕ) : ℝ) * (Nat.factorial m : ℝ) := by
    exact_mod_cast (Nat.factorial_succ m)
  have hpowsign : ((-1 : ℝ) ^ (m + 1)) = ((-1 : ℝ) ^ m) * (-1 : ℝ) := by
    simp [pow_succ]
  -- Unfold both sides at the boundary indices (`k-2*j = 0`) and reduce to a factorial identity.
  simp [gCoeff, recB, lam, div_eq_mul_inv, hfacM, hpowsign, Nat.factorial_zero, pow_zero,
    mul_assoc, mul_left_comm, mul_comm, add_assoc, add_comm]
  field_simp [hden, hf10, hfm, hfm1]
  -- `field_simp` can leave a disjunction corresponding to the (impossible) `denominator = 0` case.
  refine Or.inl ?_
  have hsubA : 2 + m * 2 - (m + 1) * 2 = 0 := by omega
  have hsubB : 2 + (m * 2 + 10) - (m + 1) = m + 11 := by omega
  have hsubC : m * 2 + 10 - m = m + 10 := by omega
  -- Reduce all remaining arithmetic indices, then use `hfacL` to rewrite `factorial (m+11)`.
  rw [hsubA, hsubB, hsubC]
  simp [Nat.factorial_zero, pow_zero, mul_assoc, mul_comm, add_comm]
  simp [hfacL]
  ring_nf

-- From this point on, `gCoeff` is used abstractly (via proved recurrences).
-- Mark it irreducible to prevent expensive unfolding during elaboration/`whnf`.
attribute [irreducible] gCoeff

-- Odd branch of `gPoly_recurrence` extracted as its own lemma (even case is huge).
-- in the main recurrence proof (the even branch is already large).
lemma gPoly_recurrence_odd_eval (m : ℕ) (t : ℝ) :
    (gPoly (2 * m + 3)).eval t =
      ((C (recA (2 * m + 1)) : Polynomial ℝ) * X * gPoly (2 * m + 2) -
        (C (recB (2 * m + 1)) : Polynomial ℝ) * gPoly (2 * m + 1)).eval t := by
  -- `n = 2m+1` (odd).
  -- Odd case: no last-coefficient correction is needed, but we still split off `j=0` to
  -- avoid the `j-1` boundary issue.
  simp only [gPoly_eval,mul_assoc,sub_eq_add_neg,eval_add,eval_mul,eval_C,eval_X,mul_sum,eval_neg]
  have hpos2 : (0 : ℕ) < 2 := by decide
  have hdiv3 : (2 * m + 3) / 2 + 1 = m + 2 := by
    lia
  have hdiv2 : (2 * m + 2) / 2 + 1 = m + 2 := by
    norm_num
  have hdiv1 : (2 * m + 1) / 2 + 1 = m + 1 := by
    grind only
  simp only [hdiv3, hdiv2, hdiv1]
  have sum_range_succ_start {α : Type} [AddCommMonoid α] (f : ℕ → α) (r : ℕ) :
      (Finset.range (r + 1)).sum f = f 0 + (Finset.range r).sum (fun j => f (j + 1)) := by
    induction r with
    | zero => simp
    | succ r ih =>
        simp [Finset.sum_range_succ, ih, add_assoc]
  have hL0 :
      (Finset.range (m + 2)).sum (fun j => gCoeff (2 * m + 3) j * t ^ (2 * m + 3 - 2 * j)) =
        gCoeff (2 * m + 3) 0 * t ^ (2 * m + 3) +
          (Finset.range (m + 1)).sum (fun j =>
            gCoeff (2 * m + 3) (j + 1) * t ^ (2 * m + 3 - 2 * (j + 1))) := by
    grind only
  have hterm (j : ℕ) (hj : j ∈ range (m + 1)) :
      gCoeff (2 * m + 3) (j + 1) =
        recA (2 * m + 1) * gCoeff (2 * m + 2) (j + 1) -
          recB (2 * m + 1) * gCoeff (2 * m + 1) j := by
    have hj1 : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
    have h2 : 2 * (j + 1) ≤ 2 * m + 2 := by
      have : j + 1 ≤ m + 1 := by
        have : j < m + 1 := Finset.mem_range.1 hj
        exact Nat.succ_le_succ (Nat.lt_succ_iff.1 this)
      exact Nat.mul_le_mul_left 2 this
    simpa using! (gCoeff_recurrence_core (n := 2 * m + 1) (j := j + 1) hj1 h2)
  rw [hL0]
  -- Rewrite the interior sum using `hterm` pointwise.
  have hinterior :
      (range (m + 1)).sum (fun j =>
          gCoeff (2 * m + 3) (j + 1) * t ^ (2 * m + 3 - 2 * (j + 1))) =
        (range (m + 1)).sum (fun j =>
          (recA (2 * m + 1) * gCoeff (2 * m + 2) (j + 1) -
              recB (2 * m + 1) * gCoeff (2 * m + 1) j) *
            t ^ (2 * m + 3 - 2 * (j + 1))) := by
    refine Finset.sum_congr rfl ?_
    grind only
  rw [hinterior]
  -- Keep simplification targeted: commutativity lemmas are too expensive here.
  simp only [gCoeff_recurrence_zero,add_assoc,Nat.reduceAdd,mul_assoc,sub_eq_add_neg,mul_add,
    mul_one,Nat.reduceSubDiff,add_mul,neg_mul,sum_add_distrib,sum_neg_distrib]
  -- Split the RHS `recA`-sum at `i=0`; rewrite `t * t^a` as one power.
  have hsplit :
      (∑ i ∈ range (m + 2),
          recA (2 * m + 1) * (t * (gCoeff (2 * m + 2) i * t ^ (2 * m + 2 - 2 * i)))) =
        recA (2 * m + 1) * (t * (gCoeff (2 * m + 2) 0 * t ^ (2 * m + 2))) +
          ∑ j ∈ range (m + 1),
            recA (2 * m + 1) *
              (t * (gCoeff (2 * m + 2) (j + 1) * t ^ (2 * m + 2 - 2 * (j + 1)))) := by
    grind only
  -- Rewrite the RHS `recA`-sum using this split.
  rw [hsplit]
  -- Boundary term `i = 0`: use the coefficient recurrence and `t * t^(2m+2) = t^(2m+3)`.
  have hgc0 : gCoeff (2 * m + 2) 0 = recA (2 * m) * gCoeff (2 * m + 1) 0 := by
    simpa using! (gCoeff_recurrence_zero (n := 2 * m))
  have hpow0 : t * (gCoeff (2 * m + 2) 0 * t ^ (2 * m + 2)) =
      recA (2 * m) * (gCoeff (2 * m + 1) 0 * t ^ (2 * m + 3)) := by
    grind only
  -- Interior terms: rewrite `t * t^(2m+2-2*(j+1)) = t^(2m+1-2*j)`.
  have hmulPow (j : ℕ) (hj : j ∈ range (m + 1)) :
      t * t ^ (2 * m + 2 - 2 * (j + 1)) = t ^ (2 * m + 1 - 2 * j) := by
    have hjle : j ≤ m := by
      have : j < m + 1 := Finset.mem_range.1 hj
      exact Nat.lt_succ_iff.1 this
    have hsub : 2 * m + 2 - 2 * (j + 1) + 1 = 2 * m + 1 - 2 * j := by
      omega
    calc
      t * t ^ (2 * m + 2 - 2 * (j + 1))
          = t ^ (2 * m + 2 - 2 * (j + 1)) * t := by
                ac_rfl
      _ = t ^ (2 * m + 2 - 2 * (j + 1) + 1) := by
            -- `t^a * t = t^(a+1)`.
            exact (pow_succ t (2 * m + 2 - 2 * (j + 1))).symm
      _ = t ^ (2 * m + 1 - 2 * j) :=
            congrArg (fun n : ℕ => t ^ n) hsub
  -- Define the interior summands to keep elaboration fast.
  let f1 : ℕ → ℝ :=
    fun j =>
      recA (2 * m + 1) *
        (t * (gCoeff (2 * m + 2) (j + 1) * t ^ (2 * m + 2 - 2 * (j + 1))))
  let f2 : ℕ → ℝ :=
    fun j =>
      recA (2 * m + 1) *
        (gCoeff (2 * m + 2) (j + 1) * t ^ (2 * m + 1 - 2 * j))
  have htail : (∑ j ∈ range (m + 1), f1 j) = ∑ j ∈ range (m + 1), f2 j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    dsimp [f1, f2]
    -- commute `t` past the coefficient, then apply `hmulPow`.
    calc
      recA (2 * m + 1) *
            (t * (gCoeff (2 * m + 2) (j + 1) * t ^ (2 * m + 2 - 2 * (j + 1)))) =
          recA (2 * m + 1) *
            (gCoeff (2 * m + 2) (j + 1) * (t * t ^ (2 * m + 2 - 2 * (j + 1)))) := by
              ac_rfl
      _ = recA (2 * m + 1) *
            (gCoeff (2 * m + 2) (j + 1) * t ^ (2 * m + 1 - 2 * j)) := by
              simp [hmulPow j hj]
  -- Apply the boundary and tail rewrites and finish.
  -- (The `recB`-sum already matches on both sides.)
  -- Keep the final normalization as a `ring_nf`, avoiding large commutativity simp calls.
  rw [hpow0, htail]
  simp [f2, add_assoc]

lemma gPoly_recurrence (n : ℕ) :
    gPoly (n + 2) =
      (C (recA n) : Polynomial ℝ) * X * gPoly (n + 1) - (C (recB n) : Polynomial ℝ) * gPoly n := by
  refine Polynomial.funext ?_
  intro t
  cases Nat.even_or_odd n with
  | inl hn =>
      rcases hn with ⟨m, rfl⟩
      -- `n = 2m` (even).
      -- Expand the polynomial evaluation on both sides into explicit finite sums.
      -- We avoid heavy `simp` on nested sums by splitting off boundary terms explicitly.
      simp only [gPoly_eval,sub_eq_add_neg,eval_add,eval_mul,eval_C,eval_X,mul_sum,eval_neg]
      -- Normalize the arithmetic shapes produced by `Even` (which gives `n = m + m`) so our
      -- `range (m+2)`/`range (m+1)` splits match syntactically.
      have hk2 : m + (m + 2) = 2 * m + 2 := by omega
      have hk1 : m + (m + 1) = 2 * m + 1 := by omega
      have hk0 : m + m = 2 * m := by omega
      have hpos2 : (0 : ℕ) < 2 := by decide
      have hdiv2 : (2 * m + 2) / 2 + 1 = m + 2 := by
        lia
      have hdiv1 : (2 * m + 1) / 2 + 1 = m + 1 := by
        grind only
      have hdiv0 : (2 * m) / 2 + 1 = m + 1 := by
        norm_num
      -- Apply the rewrites to the goal.
      simp only [hk0, hdiv2, hdiv1, hdiv0]
      -- Helper: split the range sum at the first index.
      have sum_range_succ_start {α : Type} [AddCommMonoid α] (f : ℕ → α) (r : ℕ) :
          (Finset.range (r + 1)).sum f = f 0 + (Finset.range r).sum (fun j => f (j + 1)) := by
        induction r with
        | zero =>
            simp
        | succ r ih =>
            -- `range (r+2) = insert 0 (image Nat.succ (range (r+1)))`.
            -- Use the induction hypothesis after rewriting as a `sum_range_succ`.
            simp [Finset.sum_range_succ, ih, add_assoc]
      -- Split off the `j=0` term and the `j=m+1` boundary term from the LHS sum.
      have hL0 :
          (range (m+2)).sum (fun j => gCoeff (2*m+2) j * t ^ (2*m+2 - 2*j)) =
            gCoeff (2 * m + 2) 0 * t ^ (2 * m + 2) +
              (range (m+1)).sum (fun j =>
                gCoeff (2 * m + 2) (j + 1) * t ^ (2 * m + 2 - 2 * (j + 1))) := by
        simp_all
      have hLlast :
          (range (m+1)).sum (fun j => gCoeff (2*m+2) (j+1) * t ^ (2*m+2 - 2*(j+1))) =
            (range m).sum (fun j => gCoeff (2*m+2) (j+1) * t ^ (2*m+2 - 2*(j+1))) +
              gCoeff (2 * m + 2) (m + 1) * t ^ (2 * m + 2 - 2 * (m + 1)) := by
        -- `sum_range_succ` splits off the last index `m`.
        exact sum_range_succ (fun x => gCoeff (2 * m + 2) (x + 1) * t ^ (2 * m + 2 - 2 * (x + 1))) m
      have hpow0 : t ^ (2 * m + 2 - 2 * (m + 1)) = (1 : ℝ) := by
        have : 2 * m + 2 - 2 * (m + 1) = 0 := by omega
        simp [this]
      -- Main recurrence on the interior coefficients `j+1` for `j < m`.
      have hterm (j : ℕ) (hj : j ∈ range m) :
          gCoeff (2 * m + 2) (j + 1) =
            recA (2 * m) * gCoeff (2 * m + 1) (j + 1) - recB (2 * m) * gCoeff (2 * m) j := by
        have hj1 : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
        have h2 : 2 * (j + 1) ≤ 2 * m + 1 := by
          have : j + 1 ≤ m := by
            have : j < m := Finset.mem_range.1 hj
            exact Nat.succ_le_iff.2 this
          exact (Nat.mul_le_mul_left 2 this).trans (by omega)
        -- Use the core coefficient recurrence with `n = 2*m`.
        simpa [Nat.sub_eq] using! (gCoeff_recurrence_core (n := 2 * m) (j := j + 1) hj1 h2)
      -- Assemble and finish by linearity of sums.
      -- (We keep the final algebra as a `ring_nf` after rewriting the boundary identities.)
      rw [hL0, hLlast]
      -- Rewrite the interior sum using `hterm` pointwise (simp cannot use `hterm` automatically).
      have hinterior :
          (Finset.range m).sum (fun j =>
              gCoeff (2 * m + 2) (j + 1) * t ^ (2 * m + 2 - 2 * (j + 1))) =
            (Finset.range m).sum (fun j =>
              (recA (2 * m) * gCoeff (2 * m + 1) (j + 1) - recB (2 * m) * gCoeff (2 * m) j) *
                t ^ (2 * m + 2 - 2 * (j + 1))) := by
        refine Finset.sum_congr rfl ?_
        exact fun x a =>
          Real.ext_cauchy <|
            congrArg Real.cauchy <|
              congrFun (congrArg HMul.hMul (hterm x a)) (t ^ (2 * m + 2 - 2 * (x + 1)))
      simp only [mul_comm, add_comm, add_mul, one_mul, tsub_self, pow_zero, mul_assoc]
      -- Split the `recA`/`recB` sums into `x = 0` and `x = j+1`.
      have hsumA :
          (∑ x ∈ range (m + 1),
              t ^ (1 + m * 2 - x * 2) * (gCoeff (1 + m * 2) x * (t * recA (m * 2)))) =
            t ^ (1 + m * 2) * (gCoeff (1 + m * 2) 0 * (t * recA (m * 2))) +
              ∑ j ∈ range m,
                t ^ (1+m*2 - (j+1)*2) * (gCoeff (1+m*2) (j+1) * (t * recA (m*2))) := by
        grind only
      have hsumB :
          (∑ x ∈ range (m + 1), t ^ (m * 2 - x * 2) * (gCoeff (m * 2) x * recB (m * 2))) =
            t ^ (m * 2) * (gCoeff (m * 2) 0 * recB (m * 2)) +
              ∑ j ∈ range m, t ^ (m*2 - (j+1)*2) * (gCoeff (m*2) (j+1) * recB (m*2)) := by
        grind only
      -- Rewrite the RHS using these decompositions.
      rw [hsumA, hsumB]
      -- Normalize products back into a flat form for the algebraic rewrite steps below.
      simp only [neg_add_rev]
      -- Rewrite the LHS coefficients using the recurrences.
      have hk2 : 2 + m * 2 = m * 2 + 2 := by omega
      have hk1 : 1 + m * 2 = m * 2 + 1 := by omega
      have hgc0 : gCoeff (2 + m * 2) 0 = recA (m * 2) * gCoeff (1 + m * 2) 0 := by
        -- Avoid `simp` loops on `Nat.add_comm`: use the precomputed arithmetic rewrites only.
        simpa [hk2.symm, hk1.symm] using!
          (gCoeff_recurrence_zero (n := m * 2))
      have hlast : gCoeff (2 + m * 2) (m + 1) = -recB (m * 2) * gCoeff (m * 2) m := by
        simpa [hk2, Nat.mul_comm] using! (gCoeff_recurrence_even_last (m := m))
      have hsumL :
          (∑ x ∈ range m, t ^ (2 + m * 2 - (2 + x * 2)) * gCoeff (2 + m * 2) (x + 1)) =
            ∑ x ∈ range m,
              t ^ (2 + m * 2 - (2 + x * 2)) *
                (recA (m * 2) * gCoeff (1 + m * 2) (x + 1) - recB (m * 2) * gCoeff (m * 2) x) := by
        refine Finset.sum_congr rfl ?_
        grind only
      -- Simplify the shifted `recA` terms: `t * t^(1+m*2-(j+1)*2) = t^(2+m*2-(2+j*2))`.
      have hmulA (j : ℕ) (hj : j ∈ range m) :
          t * t ^ (1 + m * 2 - (j + 1) * 2) = t ^ (2 + m * 2 - (2 + j * 2)) := by
        -- `t * t^a = t^(a+1)` and the exponent arithmetic is valid because `j < m`.
        have hj' : j + 1 ≤ m := by
          have : j < m := Finset.mem_range.1 hj
          exact Nat.succ_le_iff.2 this
        have hle : (j + 1) * 2 ≤ m * 2 := Nat.mul_le_mul_right 2 hj'
        have hsub : 1 + m * 2 - (j + 1) * 2 + 1 = 2 + m * 2 - (2 + j * 2) := by
          -- With non-underflow, `Nat` subtraction behaves like integer subtraction here.
          omega
        calc
          t * t ^ (1 + m * 2 - (j + 1) * 2)
              = t ^ (1 + m * 2 - (j + 1) * 2) * t := by
                    simp [mul_comm]
          _ = t ^ (1 + m * 2 - (j + 1) * 2 + 1) := by
                simp [pow_succ]
          _ = t ^ (2 + m * 2 - (2 + j * 2)) := by simp [hsub]
      -- Finish by rewriting and `ring_nf`.
      -- (After rewriting with the recurrences, both sides are the same split sum expression.)
      rw [hgc0, hlast, hsumL]
      -- Keep simplification targeted; commutativity simp is too expensive here.
      simp only [neg_mul,sub_eq_add_neg,mul_add,mul_neg,sum_add_distrib,sum_neg_distrib,add_mul,
        one_mul,add_assoc]
      -- Rewrite the shifted `recA` sum terms.
      have hshiftA :
          (∑ j ∈ range m,
              t ^ (1 + m * 2 - (j * 2 + 2)) * (gCoeff (1 + m * 2) (j + 1) * (t * recA (m * 2)))) =
            ∑ j ∈ range m,
              t ^ (2 + m * 2 - (2 + j * 2)) * gCoeff (1 + m * 2) (j + 1) * recA (m * 2) := by
        refine Finset.sum_congr rfl ?_
        grind only
      rw [hshiftA]
      -- Put the goal into commutative-ring normal form; then the `recB` shift works by congruence.
      ring_nf
      -- The remaining goal is a shift identity for the `recB`-sum.
      have hrecB :
          recB (m * 2) * gCoeff (m * 2) m +
              ∑ x ∈ range m, t ^ (2 + m * 2 - (2 + x * 2)) * recB (m * 2) * gCoeff (m * 2) x =
            t ^ (m * 2) * recB (m * 2) * gCoeff (m * 2) 0 +
              ∑ x ∈ range m, t ^ (m * 2 - (2 + x * 2)) * recB (m * 2) * gCoeff (m * 2) (1 + x) := by
        -- Both sides are equal to the full sum `∑ x < m+1, t^(m*2-x*2) * recB * gCoeff x`,
        -- split once at the last index and once at the first index.
        let f : ℕ → ℝ := fun x => t ^ (m * 2 - x * 2) * recB (m * 2) * gCoeff (m * 2) x
        have hsplit0 :
            (∑ x ∈ range (m + 1), f x) = f 0 + ∑ j ∈ range m, f (j + 1) := by
          simpa using! (sum_range_succ_start (f := f) (r := m))
        have hsplitLast :
            (∑ x ∈ range (m + 1), f x) = (∑ j ∈ range m, f j) + f m := by
          simpa using! (Finset.sum_range_succ (f := fun j => f j) (n := m))
        grind only
      -- Use `hrecB` to replace the combined `recB` boundary+sum, keeping the rest fixed.
      let A : ℝ := t ^ 2 * t ^ (m * 2) * recA (m * 2) * gCoeff (1 + m * 2) 0
      let SA : ℝ :=
        ∑ x ∈ range m, t ^ (2 + m * 2 - (2 + x * 2)) * recA (m * 2) * gCoeff (1 + m * 2) (1 + x)
      let B0 : ℝ := recB (m * 2) * gCoeff (m * 2) m
      let SB : ℝ :=
        ∑ x ∈ range m, t ^ (2 + m * 2 - (2 + x * 2)) * recB (m * 2) * gCoeff (m * 2) x
      let B0' : ℝ := t ^ (m * 2) * recB (m * 2) * gCoeff (m * 2) 0
      let SB' : ℝ :=
        ∑ x ∈ range m, t ^ (m * 2 - (2 + x * 2)) * recB (m * 2) * gCoeff (m * 2) (1 + x)
      let common : ℝ := A + SA
      have hlhs : A - B0 + (SA - SB) = common - (B0 + SB) := by
        dsimp [common, A, SA, B0, SB]
        ring_nf
      have hrhs : A - B0' + (SA - SB') = common - (B0' + SB') := by
        dsimp [common, A, SA, B0', SB']
        ring_nf
      have hmid : common - (B0 + SB) = common - (B0' + SB') := by
        simpa [B0, SB, B0', SB'] using! congrArg (fun z : ℝ => common - z) hrecB
      show A - B0 + SA - SB = A - B0' + SA - SB'
      linarith [hlhs, hrhs, hmid]
  | inr hn =>
      rcases hn with ⟨m, rfl⟩
      simpa using! (gPoly_recurrence_odd_eval (m := m) (t := t))

theorem gPoly_eq_gegenbauer (k : ℕ) : gPoly k = gegenbauer lam k := by
  refine Nat.twoStepInduction (motive := fun n => gPoly n = gegenbauer lam n) ?_ ?_ ?_ k
  · simp [gPoly_zero, gegenbauer]
  · simp [gPoly_one, gegenbauer, lam, mul_assoc]
  · intro n hn hn1
    calc
      gPoly (n + 2)
          = (C (recA n) : Polynomial ℝ) * X * gPoly (n + 1) -
              (C (recB n) : Polynomial ℝ) * gPoly n := gPoly_recurrence (n := n)
      _ = (C (recA n) : Polynomial ℝ) * X * gegenbauer lam (n + 1) -
              (C (recB n) : Polynomial ℝ) * gegenbauer lam n := by
            simp [hn, hn1]
      _ = gegenbauer lam (n + 2) := by
            simp [gegenbauer, recA, recB, lam, div_eq_mul_inv, sub_eq_add_neg,
              mul_left_comm, mul_comm, add_assoc]

theorem scaledHarmPoly24Raw_eq_gegenbauer (k : ℕ) :
    scaledHarmPoly24Raw k = gegenbauer (11 : ℝ) k := by
  simpa [lam, scaledHarmPoly24Raw_eq_gPoly (k := k)] using! (gPoly_eq_gegenbauer (k := k))

theorem harmPoly24Raw_eq_C_inv_scale_mul_gegenbauer (k : ℕ) :
    harmPoly24Raw k = (C ((scale24 k)⁻¹) : Polynomial ℝ) * gegenbauer (11 : ℝ) k := by
  have h := scaledHarmPoly24Raw_eq_gegenbauer (k := k)
  have hs : scale24 k ≠ 0 := scale24_ne_zero (k := k)
  -- Multiply by `C (scale⁻¹)` on the left and cancel `C (scale)`.
  have h' := congrArg (fun p : Polynomial ℝ => (C ((scale24 k)⁻¹) : Polynomial ℝ) * p) h
  -- Simplify the LHS: `C inv * (C scale * p) = (C (inv*scale)) * p = p`.
  have hL :
      (C ((scale24 k)⁻¹) : Polynomial ℝ) * scaledHarmPoly24Raw k = harmPoly24Raw k := by
    calc
      (C ((scale24 k)⁻¹) : Polynomial ℝ) * scaledHarmPoly24Raw k
          = (C ((scale24 k)⁻¹) : Polynomial ℝ) * (C (scale24 k) * harmPoly24Raw k) := by
              simp [scaledHarmPoly24Raw]
      _ = ((C ((scale24 k)⁻¹) : Polynomial ℝ) * C (scale24 k)) * harmPoly24Raw k := by
            simp [mul_assoc]
      _ = (C (((scale24 k)⁻¹) * (scale24 k)) : Polynomial ℝ) * harmPoly24Raw k := by
            simp [Polynomial.C_mul, mul_assoc]
      _ = harmPoly24Raw k := by
            simp [hs]
  simpa [hL] using! h'

/-- Evaluate `harmPoly24Raw` as an inverse-scaled Gegenbauer polynomial (parameter `11`). -/
public theorem harmPoly24Raw_eval_eq_inv_scale_mul_gegenbauer_eval (k : ℕ) (t : ℝ) :
    (harmPoly24Raw k).eval t = ((scale24 k)⁻¹) * (gegenbauer (11 : ℝ) k).eval t := by
  -- Evaluate the polynomial identity at `t`.
  have := congrArg (fun p : Polynomial ℝ => p.eval t)
    (harmPoly24Raw_eq_C_inv_scale_mul_gegenbauer (k := k))
  simpa [mul_assoc] using! this

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.ZonalPolynomial24
