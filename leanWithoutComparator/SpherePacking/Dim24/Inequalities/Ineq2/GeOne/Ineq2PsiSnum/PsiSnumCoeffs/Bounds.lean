-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.SparseCoeffs
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2PsiSnum.RSeries
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coefficients for the `ψS_num` truncation (`1 ≤ t` case)

We express `psiS_num (it t)` as an `r`-series with integer coefficients and relate its first
`Ineq2GeOneCoeffs.N = 100` coefficients to the certificate list `Ineq2GeOneCoeffs.psiSnumCoeffs`.

For the tail bound, we use a coarse coefficient-growth estimate with exponent `27` and constant
`16^8` (matching the "backup" bound in `appendix.txt`).

## Main definitions
* `H4CoeffFun`, `H2CoeffFun`, `psiSnumCoeffFun`
-/

noncomputable section

namespace SpherePacking.Dim24

open AppendixA
namespace Ineq2PsiSnum

/-- Shift a coefficient function: `shift1Fun a 0 = 0` and `shift1Fun a (n+1) = a n`. -/
@[expose] public def shift1Fun (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => a n

/-- Pointwise addition of coefficient functions. -/
@[expose] public def addFun (a b : ℕ → ℤ) : ℕ → ℤ := fun n => a n + b n

/-- Pointwise negation of a coefficient function. -/
@[expose] public def negFun (a : ℕ → ℤ) : ℕ → ℤ := fun n => -a n

/-- Pointwise scalar multiplication of a coefficient function. -/
@[expose] public def smulFun (c : ℤ) (a : ℕ → ℤ) : ℕ → ℤ := fun n => c * a n

/-- Convolution of coefficient functions (Cauchy product coefficients). -/
@[expose] public def mulFun (a b : ℕ → ℤ) : ℕ → ℤ := convZ a b

/-- The delta coefficient function supported at `0`. -/
@[expose] public def oneFun : ℕ → ℤ := fun n => if n = 0 then 1 else 0

/-- Convolution powers of a coefficient function (`powFun a m` is the `m`-fold Cauchy product). -/
@[expose] public def powFun (a : ℕ → ℤ) : ℕ → (ℕ → ℤ)
  | 0 => oneFun
  | Nat.succ k => mulFun a (powFun a k)

/-- Coefficient function for `H₄(it t)` as an `r`-series (fourth power of `theta01CoeffFun`). -/
@[expose] public def H4CoeffFun : ℕ → ℤ := powFun theta01CoeffFun 4

/--
Coefficient function for `H₂(it t)` as an `r`-series.

This is the shifted fourth power of `theta10CoeffFun`.
-/
@[expose] public def H2CoeffFun : ℕ → ℤ := shift1Fun (powFun theta10CoeffFun 4)

/-- Coefficient function for the `r`-series expansion of `psiS_num (it t)`. -/
@[expose] public def psiSnumCoeffFun : ℕ → ℤ :=
  negFun <|
    addFun
      (addFun
        (smulFun 7 (mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2)))
        (smulFun 7 (mulFun (powFun H2CoeffFun 6) H4CoeffFun)))
      (smulFun 2 (powFun H2CoeffFun 7))

/-- Uniform bound on the integer coefficients `theta01CoeffFun`. -/
public lemma abs_theta01CoeffFun_le_two (n : ℕ) : |(theta01CoeffFun n : ℝ)| ≤ 2 := by
  exact_mod_cast (AppendixA.abs_theta01CoeffFun_le_two (n := n))

/-- Uniform bound on the integer coefficients `theta10CoeffFun`. -/
public lemma abs_theta10CoeffFun_le_two (n : ℕ) : |(theta10CoeffFun n : ℝ)| ≤ 2 := by
  exact_mod_cast (AppendixA.abs_theta10CoeffFun_le_two (n := n))

/--
Coefficient bound for `mulFun`: convolution preserves polynomial coefficient bounds (up to a
degree shift).
-/
public lemma abs_mulFun_le (a b : ℕ → ℤ) (Ca Cb : ℝ) (ka kb : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ Ca * (((n + 1 : ℕ) : ℝ) ^ ka))
    (hb : ∀ n : ℕ, |(b n : ℝ)| ≤ Cb * (((n + 1 : ℕ) : ℝ) ^ kb)) :
    ∀ n : ℕ, |((mulFun a b n : ℤ) : ℝ)| ≤ (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb + 1)) := by
  intro n
  simpa [mulFun, convZ, AppendixA.convZ] using!
    (AppendixA.abs_convZ_le (a := a) (b := b) (Ca := Ca) (Cb := Cb) (ka := ka) (kb := kb)
      ha hb n)

/-- Coefficient-growth bound for convolution powers `powFun a m`. -/
public lemma abs_powFun_le (a : ℕ → ℤ) (Ca : ℝ) (ka : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ Ca * (((n + 1 : ℕ) : ℝ) ^ ka)) :
    ∀ m n : ℕ, |((powFun a m) n : ℝ)| ≤ (Ca ^ m) * (((n + 1 : ℕ) : ℝ) ^ (m * ka + Nat.pred m)) := by
  have mulFun_oneFun_right (n : ℕ) : mulFun a oneFun n = a n := by
    -- Delta series: `oneFun` is supported at `0`.
    dsimp [mulFun, convZ, oneFun]
    let p0 : ℕ × ℕ := (n, 0)
    have hp0 : p0 ∈ Finset.antidiagonal n := by
      simp [p0, Finset.mem_antidiagonal]
    refine (Finset.sum_eq_single_of_mem (s := Finset.antidiagonal n)
      (f := fun p : ℕ × ℕ => a p.1 * if p.2 = 0 then (1 : ℤ) else 0) (a := p0) hp0 ?_).trans ?_
    · intro p hp hpne
      rcases p with ⟨i, j⟩
      have hij : i + j = n := by simpa [Finset.mem_antidiagonal] using! hp
      have hj0 : j ≠ 0 := by
        intro hj0
        apply hpne
        have hi : i = n := by simpa [hj0] using! hij
        simp [p0, hi, hj0]
      simp [hj0]
    · simp [p0]
  have powFun_one : powFun a 1 = a := by
    funext n
    simp [powFun, mulFun_oneFun_right n]
  have hsucc :
      ∀ m n : ℕ,
        |((powFun a (Nat.succ m)) n : ℝ)| ≤
          (Ca ^ (Nat.succ m)) * (((n + 1 : ℕ) : ℝ) ^ ((Nat.succ m) * ka + m)) := by
    intro m
    induction m with
    | zero =>
        intro n
        -- `powFun a 1 = a` and `Nat.pred 1 = 0`.
        simpa [powFun_one, Nat.mul_zero, Nat.zero_add] using! (ha n)
    | succ m hm =>
        intro n
        have hb :
            ∀ k : ℕ,
              |((powFun a (Nat.succ m)) k : ℝ)| ≤ (Ca ^ (Nat.succ m)) *
                (((k + 1 : ℕ) : ℝ) ^ ((Nat.succ m) * ka + m)) := hm
        have hconv :=
          (abs_mulFun_le (a := a) (b := powFun a (Nat.succ m)) (Ca := Ca) (Cb := Ca ^ (Nat.succ m))
            (ka := ka) (kb := (Nat.succ m) * ka + m) ha hb n)
        have hC : Ca * Ca ^ (Nat.succ m) = Ca ^ (Nat.succ (Nat.succ m)) := by
          simp [pow_succ, mul_comm]
        have hexp : ka + (ka * (m + 1) + m) + 1 = ka * (m + 1 + 1) + (m + 1) := by
          ring
        -- Unfold `powFun`.
        simpa [powFun, mulFun, hC, hexp, mul_assoc, mul_left_comm, mul_comm] using! hconv
  intro m n
  cases m with
  | zero =>
      by_cases hn : n = 0 <;> simp [powFun, oneFun, hn]
  | succ m =>
      -- `Nat.pred (Nat.succ m) = m`.
      simpa [Nat.pred] using! (hsucc m n)

/--
If a coefficient function satisfies a polynomial bound, then the shifted function `shift1Fun a`
satisfies the same bound.
-/
public lemma abs_shift1Fun_le (a : ℕ → ℤ) (C : ℝ) (k : ℕ) (hC : 0 ≤ C)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    ∀ n : ℕ, |(shift1Fun a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k) := by
  intro n
  cases n with
  | zero =>
      simpa [shift1Fun] using! (mul_nonneg hC (by positivity : (0 : ℝ) ≤ (((0 + 1 : ℕ) : ℝ) ^ k)))
  | succ n =>
      have h := ha n
      -- `((n+1) : ℝ)^k ≤ ((n+2) : ℝ)^k`.
      have hmono :
          (((n + 1 : ℕ) : ℝ) ^ k) ≤ (((Nat.succ n + 1 : ℕ) : ℝ) ^ k) := by
        have : ((n + 1 : ℕ) : ℝ) ≤ ((Nat.succ n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.le_succ n)
        exact pow_le_pow_left₀ (by positivity) this _
      -- Transport the bound.
      have := le_trans h (by
        have := mul_le_mul_of_nonneg_left hmono hC
        simpa [mul_assoc] using! this)
      simpa [shift1Fun] using! this

/-- Coefficient-growth bound for `H4CoeffFun` (constant `16` and exponent `3`). -/
public lemma abs_H4CoeffFun_le (n : ℕ) :
    |(H4CoeffFun n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 3) := by
  have hθ : ∀ m : ℕ, |(theta01CoeffFun m : ℝ)| ≤ (2 : ℝ) * (((m + 1 : ℕ) : ℝ) ^ 0) := by
    intro m
    simpa using! (show |(theta01CoeffFun m : ℝ)| ≤ (2 : ℝ) from abs_theta01CoeffFun_le_two (n := m))
  have hpow : ∀ m : ℕ, |((powFun theta01CoeffFun 4) m : ℝ)| ≤ (2 : ℝ) ^ 4 * (((m +
    1 : ℕ) : ℝ) ^ 3) := by
    intro m
    simpa using! (abs_powFun_le (a := theta01CoeffFun) (Ca := (2 : ℝ)) (ka := 0) hθ 4 m)
  have h4 : (2 : ℝ) ^ 4 = 16 := by norm_num
  simpa [H4CoeffFun, h4] using! hpow n

/-- Coefficient-growth bound for `H2CoeffFun` (constant `16` and exponent `3`). -/
public lemma abs_H2CoeffFun_le (n : ℕ) :
    |(H2CoeffFun n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 3) := by
  have hθ : ∀ n : ℕ, |(theta10CoeffFun n : ℝ)| ≤ (2 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 0) := by
    intro m
    -- `|theta10CoeffFun m| ≤ 2`.
    simpa using! (show |(theta10CoeffFun m : ℝ)| ≤ (2 : ℝ) from abs_theta10CoeffFun_le_two (n := m))
  have hpow : ∀ m : ℕ, |((powFun theta10CoeffFun 4) m : ℝ)| ≤ (2 : ℝ) ^ 4 * (((m +
    1 : ℕ) : ℝ) ^ 3) := by
    intro m
    simpa using! (abs_powFun_le (a := theta10CoeffFun) (Ca := (2 : ℝ)) (ka := 0) hθ 4 m)
  have hshift :=
      abs_shift1Fun_le (a := powFun theta10CoeffFun 4) (C := (2 : ℝ) ^ 4) (k :=
        3) (by positivity) hpow n
  -- Simplify `2^4 = 16`.
  have h4 : (2 : ℝ) ^ 4 = 16 := by norm_num
  simpa [H2CoeffFun, h4] using! hshift

/--
Crude coefficient-growth bound for `psiSnumCoeffFun`, used for the tail estimate.

The bound has constant `16^8` and polynomial exponent `27`.
-/
public lemma abs_psiSnumCoeffFun_le (n : ℕ) :
    |(psiSnumCoeffFun n : ℝ)| ≤ (16 : ℝ) ^ (8 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ 27) := by
  -- Bound each of the three degree-7 terms separately, then add.
  have hH2 : ∀ n : ℕ, |(H2CoeffFun n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 3) :=
    abs_H2CoeffFun_le
  have hH4 : ∀ n : ℕ, |(H4CoeffFun n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 3) :=
    abs_H4CoeffFun_le
  have hpowH2 : ∀ m n : ℕ, |((powFun H2CoeffFun m) n : ℝ)| ≤ (16 : ℝ) ^ m * (((n +
    1 : ℕ) : ℝ) ^ (m *
    3 + Nat.pred m)) :=
    abs_powFun_le (a := H2CoeffFun) (Ca := (16 : ℝ)) (ka := 3) hH2
  have hpowH4 : ∀ m n : ℕ, |((powFun H4CoeffFun m) n : ℝ)| ≤ (16 : ℝ) ^ m * (((n +
    1 : ℕ) : ℝ) ^ (m *
    3 + Nat.pred m)) :=
    abs_powFun_le (a := H4CoeffFun) (Ca := (16 : ℝ)) (ka := 3) hH4
  -- Term 1: `7 * H2^5 * H4^2` gives constant `7*16^7` and exponent `27`.
  have hterm1 :
      |((smulFun 7 (mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2)) n : ℤ) : ℝ)| ≤
        (7 : ℝ) * (16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ 27) := by
    have hmul :
        |((mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2) n : ℤ) : ℝ)| ≤
          ((16 : ℝ) ^ (5 : ℕ) * (16 : ℝ) ^ (2 : ℕ)) * (((n + 1 : ℕ) : ℝ) ^ 27) := by
      -- Coefficient bound for the convolution term.
      simpa [Nat.pred, pow_add, mul_assoc, mul_left_comm, mul_comm] using!
        (abs_mulFun_le (a := powFun H2CoeffFun 5) (b := powFun H4CoeffFun 2)
          (Ca := (16 : ℝ) ^ (5 : ℕ)) (Cb := (16 : ℝ) ^ (2 : ℕ))
          (ka := 5 * 3 + Nat.pred 5) (kb := 2 * 3 + Nat.pred 2)
          (fun k => by simpa using! hpowH2 5 k) (fun k => by simpa using! hpowH4 2 k) n)
    have h7 : (0 : ℝ) ≤ (7 : ℝ) := by norm_num
    have hmul' :
        |((mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2) n : ℤ) : ℝ)| ≤
          (16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ 27) := by
      have hpow : (16 : ℝ) ^ (5 : ℕ) * (16 : ℝ) ^ (2 : ℕ) = (16 : ℝ) ^ (7 : ℕ) := by
        simpa [pow_add] using! (pow_add (16 : ℝ) 5 2).symm
      simpa [hpow, mul_assoc] using! hmul
    -- Now scale by `7`.
    simpa [smulFun, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7), mul_assoc] using!
      (mul_le_mul_of_nonneg_left hmul' h7)
  -- Term 2: `7 * H2^6 * H4` gives constant `7*16^7` and exponent `27`.
  have hterm2 :
      |((smulFun 7 (mulFun (powFun H2CoeffFun 6) H4CoeffFun) n : ℤ) : ℝ)| ≤
        (7 : ℝ) * (16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ 27) := by
    have hmul :
        |((mulFun (powFun H2CoeffFun 6) H4CoeffFun n : ℤ) : ℝ)| ≤
          ((16 : ℝ) ^ (6 : ℕ) * (16 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ 27) := by
      simpa [Nat.pred, pow_add, mul_assoc, mul_left_comm, mul_comm] using!
        (abs_mulFun_le (a := powFun H2CoeffFun 6) (b := H4CoeffFun)
          (Ca := (16 : ℝ) ^ (6 : ℕ)) (Cb := (16 : ℝ))
          (ka := 6 * 3 + Nat.pred 6) (kb := 3)
          (fun k => by simpa using! hpowH2 6 k) hH4 n)
    have h7 : (0 : ℝ) ≤ (7 : ℝ) := by norm_num
    have hmul' :
        |((mulFun (powFun H2CoeffFun 6) H4CoeffFun n : ℤ) : ℝ)| ≤
          (16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ 27) := by
      -- Rewrite `16^7` as `16^6 * 16`.
      simpa [pow_succ, mul_assoc] using! hmul
    simpa [smulFun, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7), mul_assoc] using!
      (mul_le_mul_of_nonneg_left hmul' h7)
  -- Term 3: `2 * H2^7` gives constant `2*16^7` and exponent `27`.
  have hterm3 :
      |((smulFun 2 (powFun H2CoeffFun 7) n : ℤ) : ℝ)| ≤
        (2 : ℝ) * (16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ 27) := by
    have hpow' := hpowH2 7 n
    have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    simpa [smulFun, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc] using!
      (mul_le_mul_of_nonneg_left hpow' h2)
  -- Combine by triangle inequality and sum the constants.
  let P : ℝ := (((n + 1 : ℕ) : ℝ) ^ 27)
  have hP : 0 ≤ P := by positivity [P]
  let A : ℝ :=
    ((smulFun 7 (mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2)) n : ℤ) : ℝ)
  let B : ℝ :=
    ((smulFun 7 (mulFun (powFun H2CoeffFun 6) H4CoeffFun) n : ℤ) : ℝ)
  let C : ℝ := ((smulFun 2 (powFun H2CoeffFun 7) n : ℤ) : ℝ)
  have hA : |A| ≤ (7 : ℝ) * (16 : ℝ) ^ (7 : ℕ) * P := by
    simpa [A, P] using! hterm1
  have hB : |B| ≤ (7 : ℝ) * (16 : ℝ) ^ (7 : ℕ) * P := by
    simpa [B, P] using! hterm2
  have hC : |C| ≤ (2 : ℝ) * (16 : ℝ) ^ (7 : ℕ) * P := by
    simpa [C, P] using! hterm3
  have habc : |(A + B) + C| ≤ |A| + |B| + |C| :=
    abs_add_three A B C
  have hdef : (psiSnumCoeffFun n : ℝ) = -((A + B) + C) := by
    simp [psiSnumCoeffFun, A, B, C, addFun, negFun, smulFun, mulFun, add_assoc]
  have habs : |(psiSnumCoeffFun n : ℝ)| ≤ |A| + |B| + |C| := by
      have heq : |(psiSnumCoeffFun n : ℝ)| = |(A + B) + C| := by
        calc
          |(psiSnumCoeffFun n : ℝ)| = |(-((A + B) + C))| := by simp [hdef]
          _ = |(A + B) + C| := by simpa using! (abs_neg ((A + B) + C))
      simpa [heq] using! habc
  grind only


end SpherePacking.Dim24.Ineq2PsiSnum
