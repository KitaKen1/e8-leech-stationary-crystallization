-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.DenomReduction.Numerators
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2PsiSnum.RSeries
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2PsiSnum.PsiSnumCoeffs.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2PsiSnum.SummabilityReindex
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ThetaRSeriesSpecialize
public import SpherePacking.ForMathlib.CancelDenomsCompat

/-!
# Operations on `rseries` for the `ψS_num` truncation

We prove basic identities for `rseries` (linearity, scaling, shifting, and convolution power
compatibility) for the coefficient functions used in the `ψS_num` truncation argument.

## Main statements
* `psiS_num_it_eq_rseries_psiSnumCoeffFun`
-/

open UpperHalfPlane
noncomputable section
namespace SpherePacking.Dim24
open AppendixA
namespace Ineq2PsiSnum
open scoped BigOperators

private lemma rseries_oneFun (t : ℝ) : rseries oneFun t = 1 := by
  -- Only the `n = 0` term contributes.
  simp [rseries, oneFun, tsum_ite_eq]

private lemma rseries_addFun (t : ℝ) (a b : ℕ → ℤ)
    (ha : Summable (fun n : ℕ => (a n : ℂ) * ((r t : ℂ) ^ n)))
    (hb : Summable (fun n : ℕ => (b n : ℂ) * ((r t : ℂ) ^ n))) :
    rseries (addFun a b) t = rseries a t + rseries b t := by
  simpa [rseries, addFun, add_mul] using! (ha.tsum_add hb)

private lemma rseries_negFun (t : ℝ) (a : ℕ → ℤ) :
    rseries (negFun a) t = -rseries a t := by
  simp [rseries, negFun, tsum_neg]

private lemma rseries_smulFun (t : ℝ) (c : ℤ) (a : ℕ → ℤ) :
    rseries (smulFun c a) t = (c : ℂ) * rseries a t := by
  simp [rseries, smulFun, Int.cast_mul, mul_assoc, tsum_mul_left]

private lemma rseries_shift1Fun (t : ℝ) (a : ℕ → ℤ)
    (ha : Summable (fun n : ℕ => (a n : ℂ) * ((r t : ℂ) ^ n))) :
    rseries (shift1Fun a) t = (r t : ℂ) * rseries a t := by
  let f : ℕ → ℂ := fun n => ((shift1Fun a n : ℤ) : ℂ) * ((r t : ℂ) ^ n)
  have hf_succ :
      (fun n : ℕ => f (n + 1)) = fun n : ℕ => (r t : ℂ) * ((a n : ℂ) * ((r t : ℂ) ^ n)) := by
    funext n
    simp [f, shift1Fun, pow_succ, mul_left_comm, mul_comm]
  have hs_succ : Summable (fun n : ℕ => f (n + 1)) := by
    -- `fun n => (r t : ℂ) * ((a n)*r^n)` is summable.
    simpa [hf_succ] using! ha.mul_left (r t : ℂ)
  have hs : Summable f :=
    (summable_nat_add_iff 1 (f := f)).1 hs_succ
  have hsplit :
      (∑' n : ℕ, f n) = (∑ n ∈ Finset.range 1, f n) + ∑' n : ℕ, f (n + 1) := by
    simpa using! (Summable.sum_add_tsum_nat_add 1 hs).symm
  have hf0 : f 0 = 0 := by simp [f, shift1Fun]
  have hsum1 : (∑ n ∈ Finset.range 1, f n) = 0 := by
    simp [Finset.range, hf0]
  -- Now compute the `tsum`.
  calc
    rseries (shift1Fun a) t = ∑' n : ℕ, f n := by simp [rseries, f]
    _ = ∑' n : ℕ, f (n + 1) := by simpa [hsum1, hsplit]
    _ = ∑' n : ℕ, (r t : ℂ) * ((a n : ℂ) * ((r t : ℂ) ^ n)) := by
        simp [hf_succ]
    _ = (r t : ℂ) * (∑' n : ℕ, (a n : ℂ) * ((r t : ℂ) ^ n)) := by
        simp [tsum_mul_left]
    _ = (r t : ℂ) * rseries a t := by simp [rseries]

private lemma summable_norm_rseries_of_const_bound (t : ℝ) (ht : 1 ≤ t) (a : ℕ → ℤ) (C : ℝ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C) :
    Summable (fun n : ℕ => ‖((a n : ℂ) * ((r t : ℂ) ^ n))‖) := by
  refine summable_norm_rseries_of_coeffBound (t := t) ht a C 0 ?_
  intro n
  simpa using! (ha n)

private lemma rseries_powFun_eq (t : ℝ) (ht : 1 ≤ t) (a : ℕ → ℤ) (C : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    ∀ m : ℕ, (rseries a t) ^ m = rseries (powFun a m) t := by
  intro m
  induction m with
  | zero =>
      simp [powFun, rseries_oneFun]
  | succ m ih =>
      -- Use `pow_succ` and convert (postTransparency := .instances) multiplication of `rseries` to convolution of coefficients.
      have hsA_norm :
          Summable (fun n : ℕ => ‖((a n : ℂ) * ((r t : ℂ) ^ n))‖) :=
        summable_norm_rseries_of_coeffBound (t := t) ht a C k ha
      have hpowBound :
          ∀ n : ℕ, |((powFun a m) n : ℝ)| ≤
            (C ^ m) * (((n + 1 : ℕ) : ℝ) ^ (m * k + Nat.pred m)) := by
        simpa using! (abs_powFun_le (a := a) (Ca := C) (ka := k) ha m)
      have hsPow_norm :
          Summable (fun n : ℕ => ‖(((powFun a m) n : ℂ) * ((r t : ℂ) ^ n))‖) :=
        summable_norm_rseries_of_coeffBound (t := t) ht (powFun a m) (C ^ m) (m * k +
          Nat.pred m) hpowBound
      have hmul :
          (rseries a t) * rseries (powFun a m) t = rseries (mulFun a (powFun a m)) t := by
        simpa [mulFun] using! (rseries_mul_cast (t := t) (a := a) (b :=
          powFun a m) hsA_norm hsPow_norm)
      calc
        (rseries a t) ^ Nat.succ m = (rseries a t) * (rseries a t) ^ m := by
          simp [pow_succ, mul_comm]
        _ = (rseries a t) * rseries (powFun a m) t := by simp [ih]
        _ = rseries (powFun a (Nat.succ m)) t := by
          simpa [powFun] using! hmul

private lemma H4_it_eq_rseries_H4CoeffFun (t : ℝ) (ht : 1 ≤ t) :
    H₄ (it t (lt_of_lt_of_le (by norm_num) ht)) = rseries H4CoeffFun t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hit : it t (lt_of_lt_of_le (by norm_num) ht) = it t ht0 := by
    ext
    rfl
  have hθ01 (n : ℕ) : AppendixA.theta01CoeffFun n = theta01CoeffFun n := by
    simp [AppendixA.theta01CoeffFun, theta01CoeffFun]
  have hTheta : Θ₄ (it t ht0) = rseries theta01CoeffFun t := by
    simpa [hit, AppendixA.rseries, AppendixA.rC, rseries, hθ01] using!
      (AppendixA.Theta4_it_eq_rseries_theta01CoeffFun (t := t) ht)
  have hbound : ∀ n : ℕ, |(theta01CoeffFun n : ℝ)| ≤ (2 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 0) := by
    intro n
    simpa using! (show |(theta01CoeffFun n : ℝ)| ≤ (2 : ℝ) from abs_theta01CoeffFun_le_two (n := n))
  -- `H₄ = Θ₄^4`.
  dsimp [H₄]
  -- Use the `rseries` power lemma.
  simpa [H4CoeffFun, hTheta] using! (rseries_powFun_eq (t := t) ht theta01CoeffFun 2 0 hbound 4)

private lemma exp_quarter_pow_four_eq_r (t : ℝ) :
    (((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) ^ (4 : ℕ)) = (r t : ℂ) := by
  -- `exp(x)^4 = exp(4x)`.
  have hR₁ : (Real.exp (-Real.pi * t / 4) : ℝ) ^ (4 : ℕ) = Real.exp (4 * (-Real.pi * t / 4)) := by
    simpa using! (Real.exp_nat_mul (-Real.pi * t / 4) 4).symm
  have hR₂ : Real.exp (4 * (-Real.pi * t / 4)) = Real.exp (-Real.pi * t) := by
    congr 1
    ring
  have hR : (Real.exp (-Real.pi * t / 4) : ℝ) ^ (4 : ℕ) = Real.exp (-Real.pi * t) :=
    hR₁.trans hR₂
  -- Cast to `ℂ` and rewrite the real power as a complex power.
  have hR' :
      (((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) ^ (4 : ℕ)) = (Real.exp (-Real.pi * t) : ℂ) := by
    calc
      (((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) ^ (4 : ℕ)) =
          (((Real.exp (-Real.pi * t / 4) : ℝ) ^ (4 : ℕ)) : ℂ) := by
            simp
      _ = (Real.exp (-Real.pi * t) : ℂ) :=
          by
            simpa [Complex.ofReal_pow] using! congrArg (fun x : ℝ => (x : ℂ)) hR
  dsimp [r, AppendixA.r]
  exact hR'

private lemma H2_it_eq_rseries_H2CoeffFun (t : ℝ) (ht : 1 ≤ t) :
    H₂ (it t (lt_of_lt_of_le (by norm_num) ht)) = rseries H2CoeffFun t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hit : it t (lt_of_lt_of_le (by norm_num) ht) = it t ht0 := by
    ext
    rfl
  have hθ10 (n : ℕ) : AppendixA.theta10CoeffFun n = theta10CoeffFun n := by
    simp [AppendixA.theta10CoeffFun, theta10CoeffFun]
  have hTheta :
      Θ₂ (it t ht0) =
        ((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) * rseries theta10CoeffFun t := by
    simpa [hit, AppendixA.rseries, AppendixA.rC, rseries, hθ10] using!
      (AppendixA.Theta2_it_eq_rseries_theta10CoeffFun (t := t) ht)
  have hbound : ∀ n : ℕ, |(theta10CoeffFun n : ℝ)| ≤ (2 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 0) := by
    intro n
    simpa using! (show |(theta10CoeffFun n : ℝ)| ≤ (2 : ℝ) from abs_theta10CoeffFun_le_two (n := n))
  have hsθ10 : Summable (fun n : ℕ => (powFun theta10CoeffFun 4 n : ℂ) * ((r t : ℂ) ^ n)) := by
    -- Summability of `powFun theta10CoeffFun 4` via the coefficient bound.
    have hpowBound :
        ∀ n : ℕ, |((powFun theta10CoeffFun 4) n : ℝ)| ≤ (2 : ℝ) ^ 4 * (((n + 1 : ℕ) : ℝ) ^ (4 * 0 +
          Nat.pred 4)) := by
      simpa using! (abs_powFun_le (a := theta10CoeffFun) (Ca := (2 : ℝ)) (ka := 0) hbound 4)
    exact
      summable_rseries_of_coeffBound t ht (powFun theta10CoeffFun 4)
        (2 ^ 4) (4 * 0 + Nat.pred 4) hpowBound
  -- `H₂ = Θ₂^4`.
  dsimp [H₂]
  -- Expand using `Θ₂(it)` and rewrite the scalar fourth power.
  have hpow : (Θ₂ (it t ht0)) ^ (4 : ℕ) =
      (r t : ℂ) * (rseries theta10CoeffFun t) ^ (4 : ℕ) := by
    -- `(c * s)^4 = c^4 * s^4` and `c^4 = (r t : ℂ)`.
    calc
      (Θ₂ (it t ht0)) ^ (4 : ℕ) =
          (((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) * rseries theta10CoeffFun t) ^ (4 : ℕ) := by
              simp [hTheta]
      _ = (((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) ^ (4 : ℕ)) *
        (rseries theta10CoeffFun t) ^ (4 : ℕ) := by
            simp [mul_pow]
      _ = (r t : ℂ) * (rseries theta10CoeffFun t) ^ (4 : ℕ) := by
            rw [exp_quarter_pow_four_eq_r]
  -- Convert the power of `rseries theta10` to `rseries (powFun theta10 4)`.
  have hpowSeries :
      (rseries theta10CoeffFun t) ^ (4 : ℕ) = rseries (powFun theta10CoeffFun 4) t := by
    -- Use the general power lemma.
    simpa using! (rseries_powFun_eq (t := t) ht theta10CoeffFun 2 0 hbound 4)
  -- Shift by one power of `r` and match `H2CoeffFun`.
  have hshift :
      rseries (shift1Fun (powFun theta10CoeffFun 4)) t = (r t : ℂ) *
        rseries (powFun theta10CoeffFun 4) t := by
    simpa using! (rseries_shift1Fun (t := t) (a := powFun theta10CoeffFun 4) hsθ10)
  -- Finish.
  calc
    (Θ₂ (it t ht0)) ^ (4 : ℕ) = (r t : ℂ) * rseries (powFun theta10CoeffFun 4) t := by
      simpa [hpowSeries] using! hpow
    _ = rseries H2CoeffFun t := by
      -- `H2CoeffFun = shift1Fun (powFun theta10CoeffFun 4)`.
      simpa [H2CoeffFun] using! hshift.symm

/--
For `1 ≤ t`, evaluating `psiS_num` at `z = it t` agrees with the power series
`rseries psiSnumCoeffFun t`.

This is the bridge from the polynomial definition of `psiS_num` (in `H₂` and `H₄`)
to the coefficientwise bounds proved for `psiSnumCoeffFun`.
-/
public lemma psiS_num_it_eq_rseries_psiSnumCoeffFun (t : ℝ) (ht : 1 ≤ t) :
    psiS_num (it t (lt_of_lt_of_le (by norm_num) ht)) = rseries psiSnumCoeffFun t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  set z : ℍ := it t ht0
  have hH2 : H₂ z = rseries H2CoeffFun t := by
    simpa [z] using! (H2_it_eq_rseries_H2CoeffFun (t := t) ht)
  have hH4 : H₄ z = rseries H4CoeffFun t := by
    simpa [z] using! (H4_it_eq_rseries_H4CoeffFun (t := t) ht)
  -- Rewrite `psiS_num` and use the `rseries` homomorphism properties.
  -- Summability assumptions for the small algebraic steps are discharged using the coefficient
  -- bounds
  -- already present in this namespace.
  have hsH2 : Summable (fun n : ℕ => (H2CoeffFun n : ℂ) * ((r t : ℂ) ^ n)) :=
    summable_rseries_of_coeffBound (t := t) ht H2CoeffFun 16 3 (by
      intro n; simpa using! (abs_H2CoeffFun_le (n := n)))
  have hsH4 : Summable (fun n : ℕ => (H4CoeffFun n : ℂ) * ((r t : ℂ) ^ n)) :=
    summable_rseries_of_coeffBound (t := t) ht H4CoeffFun 16 3 (by
      intro n; simpa using! (abs_H4CoeffFun_le (n := n)))
  have hpowH2 : ∀ m : ℕ, (rseries H2CoeffFun t) ^ m = rseries (powFun H2CoeffFun m) t :=
    rseries_powFun_eq (t := t) ht H2CoeffFun 16 3 (by
      intro n; simpa using! (abs_H2CoeffFun_le (n := n)))
  have hpowH4 : ∀ m : ℕ, (rseries H4CoeffFun t) ^ m = rseries (powFun H4CoeffFun m) t :=
    rseries_powFun_eq (t := t) ht H4CoeffFun 16 3 (by
      intro n; simpa using! (abs_H4CoeffFun_le (n := n)))
  -- Now expand the polynomial defining `psiS_num`.
  -- We work at the `rseries` level and then translate back using `hH2,hH4`.
  have hsPowH2_norm (m : ℕ) :
      Summable (fun n : ℕ => ‖(((powFun H2CoeffFun m) n : ℂ) * ((r t : ℂ) ^ n))‖) := by
    have hpowBound :
        ∀ n : ℕ, |((powFun H2CoeffFun m) n : ℝ)| ≤ (16 : ℝ) ^ m *
          (((n + 1 : ℕ) : ℝ) ^ (m * 3 + Nat.pred m)) := by
      simpa using! (abs_powFun_le (a := H2CoeffFun) (Ca := (16 : ℝ)) (ka := 3) (abs_H2CoeffFun_le) m)
    exact summable_norm_rseries_of_coeffBound (t := t) ht (powFun H2CoeffFun m) ((16 : ℝ) ^ m)
      (m * 3 + Nat.pred m) hpowBound
  have hsPowH4_norm (m : ℕ) :
      Summable (fun n : ℕ => ‖(((powFun H4CoeffFun m) n : ℂ) * ((r t : ℂ) ^ n))‖) := by
    have hpowBound :
        ∀ n : ℕ, |((powFun H4CoeffFun m) n : ℝ)| ≤ (16 : ℝ) ^ m *
          (((n + 1 : ℕ) : ℝ) ^ (m * 3 + Nat.pred m)) := by
      simpa using! (abs_powFun_le (a := H4CoeffFun) (Ca := (16 : ℝ)) (ka := 3) (abs_H4CoeffFun_le) m)
    exact summable_norm_rseries_of_coeffBound (t := t) ht (powFun H4CoeffFun m) ((16 : ℝ) ^ m)
      (m * 3 + Nat.pred m) hpowBound
  have hsH4_norm : Summable (fun n : ℕ => ‖((H4CoeffFun n : ℂ) * ((r t : ℂ) ^ n))‖) :=
    summable_norm_rseries_of_coeffBound (t := t) ht H4CoeffFun 16 3 (by
      intro n; simpa using! (abs_H4CoeffFun_le (n := n)))
  have hsMul1 :
      (rseries (powFun H2CoeffFun 5) t) * rseries (powFun H4CoeffFun 2) t =
        rseries (mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2)) t := by
    simpa [mulFun] using!
      rseries_mul_cast (t := t) (a := powFun H2CoeffFun 5) (b := powFun H4CoeffFun 2)
        (hsPowH2_norm 5) (hsPowH4_norm 2)
  have hsMul2 :
      (rseries (powFun H2CoeffFun 6) t) * rseries H4CoeffFun t =
        rseries (mulFun (powFun H2CoeffFun 6) H4CoeffFun) t := by
    -- For `H4CoeffFun` use the norm-summability lemma.
    have hsH4' : Summable (fun n : ℕ => ‖((H4CoeffFun n : ℂ) * ((r t : ℂ) ^ n))‖) := hsH4_norm
    simpa [mulFun] using!
      rseries_mul_cast (t := t) (a := powFun H2CoeffFun 6) (b := H4CoeffFun)
        (hsPowH2_norm 6) hsH4'
  -- Assemble the expression for `rseries psiSnumCoeffFun`.
  have hseries :
      rseries psiSnumCoeffFun t =
        -((7 : ℂ) * (rseries H2CoeffFun t) ^ 5 * (rseries H4CoeffFun t) ^ 2 +
            (7 : ℂ) * (rseries H2CoeffFun t) ^ 6 * (rseries H4CoeffFun t) +
            (2 : ℂ) * (rseries H2CoeffFun t) ^ 7) := by
    -- Rewrite the coefficient function `psiSnumCoeffFun` using `rseries_*` lemmas.
    have hsPow7 : Summable (fun n : ℕ => ((powFun H2CoeffFun 7) n : ℂ) * ((r t : ℂ) ^ n)) :=
      Summable.of_norm (hsPowH2_norm 7)
    have hsMul1' : Summable (fun n : ℕ =>
        ((mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2)) n : ℂ) * ((r t : ℂ) ^ n)) := by
      -- Coefficient growth implies summability, but reuse `summable_rseries_of_coeffBound`.
      -- We use a crude bound from `abs_mulFun_le` + `abs_powFun_le`.
      have hA : ∀ n : ℕ, |((powFun H2CoeffFun 5) n : ℝ)| ≤ (16 : ℝ) ^ 5 * (((n + 1 : ℕ) : ℝ) ^ (5 *
        3 +
        Nat.pred 5)) := by
        simpa using! (abs_powFun_le (a := H2CoeffFun) (Ca := (16 : ℝ)) (ka :=
          3) (abs_H2CoeffFun_le) 5)
      have hB : ∀ n : ℕ, |((powFun H4CoeffFun 2) n : ℝ)| ≤ (16 : ℝ) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (2 *
        3 +
        Nat.pred 2)) := by
        simpa using! (abs_powFun_le (a := H4CoeffFun) (Ca := (16 : ℝ)) (ka :=
          3) (abs_H4CoeffFun_le) 2)
      exact summable_rseries_of_coeffBound (t := t) ht
        (mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2))
        ((16 : ℝ) ^ 5 * (16 : ℝ) ^ 2) ((5 * 3 + Nat.pred 5) + (2 * 3 + Nat.pred 2) + 1) (by
          intro n
          exact
            abs_mulFun_le (powFun H2CoeffFun 5) (powFun H4CoeffFun 2)
              (16 ^ 5) (16 ^ 2) (5 * 3 + Nat.pred 5) (2 * 3 + Nat.pred 2) hA hB n)
    -- Use algebraic rewrites.
    -- This is a straightforward but verbose `simp`-based calculation on `rseries`.
    -- (We keep it local to avoid polluting the global simp set.)
    have hsMul2' : Summable (fun n : ℕ =>
        ((mulFun (powFun H2CoeffFun 6) H4CoeffFun) n : ℂ) * ((r t : ℂ) ^ n)) := by
      have hA : ∀ n : ℕ, |((powFun H2CoeffFun 6) n : ℝ)| ≤ (16 : ℝ) ^ 6 * (((n + 1 : ℕ) : ℝ) ^ (6 *
        3 +
        Nat.pred 6)) := by
        simpa using! (abs_powFun_le (a := H2CoeffFun) (Ca := (16 : ℝ)) (ka :=
          3) (abs_H2CoeffFun_le) 6)
      have hB : ∀ n : ℕ, |(H4CoeffFun n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 3) :=
        abs_H4CoeffFun_le
      exact summable_rseries_of_coeffBound (t := t) ht
        (mulFun (powFun H2CoeffFun 6) H4CoeffFun)
        ((16 : ℝ) ^ 6 * (16 : ℝ)) ((6 * 3 + Nat.pred 6) + 3 + 1) (by
          intro n
          exact
            abs_mulFun_le (powFun H2CoeffFun 6) H4CoeffFun (16 ^ 6) 16
              (6 * 3 + Nat.pred 6) 3 hA hB n)
    -- Now compute.
    -- Rewrite each occurrence of a power series power/product into the corresponding `rseries` of
    -- coefficient ops.
    have hpow5' : (rseries H2CoeffFun t) ^ 5 = rseries (powFun H2CoeffFun 5) t := hpowH2 5
    have hpow6' : (rseries H2CoeffFun t) ^ 6 = rseries (powFun H2CoeffFun 6) t := hpowH2 6
    have hpow7' : (rseries H2CoeffFun t) ^ 7 = rseries (powFun H2CoeffFun 7) t := hpowH2 7
    have hpow2' : (rseries H4CoeffFun t) ^ 2 = rseries (powFun H4CoeffFun 2) t := hpowH4 2
    -- Use linearity and multiplication, but keep the rewriting steps small (to avoid heartbeat
    -- timeouts).
    let A : ℕ → ℤ := mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2)
    let B : ℕ → ℤ := mulFun (powFun H2CoeffFun 6) H4CoeffFun
    let C : ℕ → ℤ := powFun H2CoeffFun 7
    let term1 : ℕ → ℤ := smulFun 7 A
    let term2 : ℕ → ℤ := smulFun 7 B
    let term3 : ℕ → ℤ := smulFun 2 C
    let sumTerms : ℕ → ℤ := addFun (addFun term1 term2) term3
    have hdef : psiSnumCoeffFun = negFun sumTerms := by
      funext n
      simp [psiSnumCoeffFun, sumTerms, term1, term2, term3, A, B, C, addFun, negFun, smulFun]
    have hsTerm1 : Summable (fun n : ℕ => (term1 n : ℂ) * ((r t : ℂ) ^ n)) := by
      have hs : Summable (fun n : ℕ => (7 : ℂ) * (((A n : ℂ) * ((r t : ℂ) ^ n)))) :=
        (hsMul1'.mul_left (7 : ℂ))
      simpa [term1, A, smulFun, mul_assoc] using! hs
    have hsTerm2 : Summable (fun n : ℕ => (term2 n : ℂ) * ((r t : ℂ) ^ n)) := by
      have hs : Summable (fun n : ℕ => (7 : ℂ) * (((B n : ℂ) * ((r t : ℂ) ^ n)))) :=
        (hsMul2'.mul_left (7 : ℂ))
      simpa [term2, B, smulFun, mul_assoc] using! hs
    have hsTerm3 : Summable (fun n : ℕ => (term3 n : ℂ) * ((r t : ℂ) ^ n)) := by
      have hs : Summable (fun n : ℕ => (2 : ℂ) * (((C n : ℂ) * ((r t : ℂ) ^ n)))) :=
        (hsPow7.mul_left (2 : ℂ))
      simpa [term3, C, smulFun, mul_assoc] using! hs
    have hs12 : Summable (fun n : ℕ => ((addFun term1 term2) n : ℂ) * ((r t : ℂ) ^ n)) := by
      have hs := hsTerm1.add hsTerm2
      have h :
          (fun n : ℕ => ((addFun term1 term2) n : ℂ) * ((r t : ℂ) ^ n)) =
            fun n : ℕ => (term1 n : ℂ) * ((r t : ℂ) ^ n) + (term2 n : ℂ) * ((r t : ℂ) ^ n) := by
        funext n
        simp [addFun, add_mul]
      simpa [h] using! hs
    have hsSum : Summable (fun n : ℕ => (sumTerms n : ℂ) * ((r t : ℂ) ^ n)) := by
      have hs := hs12.add hsTerm3
      have h :
          (fun n : ℕ => (sumTerms n : ℂ) * ((r t : ℂ) ^ n)) =
            fun n : ℕ =>
              ((addFun term1 term2) n : ℂ) * ((r t : ℂ) ^ n) + (term3 n : ℂ) * ((r t : ℂ) ^ n) := by
        funext n
        simp [sumTerms, addFun, add_mul]
      simpa [h] using! hs
    have haddInner :
        rseries (addFun term1 term2) t = rseries term1 t + rseries term2 t :=
      rseries_addFun (t := t) term1 term2 hsTerm1 hsTerm2
    have haddOuter :
        rseries sumTerms t = rseries (addFun term1 term2) t + rseries term3 t := by
      simpa [sumTerms] using!
        (rseries_addFun (t := t) (a := addFun term1 term2) (b := term3) hs12 hsTerm3)
    have hterm1 :
        rseries term1 t =
          (7 : ℂ) * (rseries H2CoeffFun t) ^ 5 * (rseries H4CoeffFun t) ^ 2 := by
      have hsmul : rseries term1 t = (7 : ℂ) * rseries A t := by
        simpa [term1, A] using! (rseries_smulFun (t := t) (c := 7) (a := A))
      have hmul :
          rseries A t = rseries (powFun H2CoeffFun 5) t * rseries (powFun H4CoeffFun 2) t := by
        simpa [A] using! hsMul1.symm
      calc
        rseries term1 t = (7 : ℂ) * rseries A t := hsmul
        _ = (7 : ℂ) * (rseries (powFun H2CoeffFun 5) t * rseries (powFun H4CoeffFun 2) t) := by
              simp [hmul]
        _ = (7 : ℂ) * ((rseries H2CoeffFun t) ^ 5 * (rseries H4CoeffFun t) ^ 2) := by
              simp [hpow5'.symm, hpow2'.symm]
        _ = (7 : ℂ) * (rseries H2CoeffFun t) ^ 5 * (rseries H4CoeffFun t) ^ 2 := by
              simp [mul_assoc]
    have hterm2 :
        rseries term2 t =
          (7 : ℂ) * (rseries H2CoeffFun t) ^ 6 * (rseries H4CoeffFun t) := by
      have hsmul : rseries term2 t = (7 : ℂ) * rseries B t := by
        simpa [term2, B] using! (rseries_smulFun (t := t) (c := 7) (a := B))
      have hmul : rseries B t = rseries (powFun H2CoeffFun 6) t * rseries H4CoeffFun t := by
        simpa [B] using! hsMul2.symm
      calc
        rseries term2 t = (7 : ℂ) * rseries B t := hsmul
        _ = (7 : ℂ) * (rseries (powFun H2CoeffFun 6) t * rseries H4CoeffFun t) := by
              simp [hmul]
        _ = (7 : ℂ) * ((rseries H2CoeffFun t) ^ 6 * rseries H4CoeffFun t) := by
              simp [hpow6'.symm]
        _ = (7 : ℂ) * (rseries H2CoeffFun t) ^ 6 * rseries H4CoeffFun t := by
              simp [mul_assoc]
    have hterm3 :
        rseries term3 t = (2 : ℂ) * (rseries H2CoeffFun t) ^ 7 := by
      have hsmul : rseries term3 t = (2 : ℂ) * rseries C t := by
        simpa [term3, C] using! (rseries_smulFun (t := t) (c := 2) (a := C))
      exact Eq.symm (CancelDenoms.derive_trans (hpowH2 7) (id (Eq.symm hsmul)))
    -- Put the pieces together.
    have hsum :
        rseries psiSnumCoeffFun t = -((rseries term1 t + rseries term2 t) + rseries term3 t) := by
      rw [hdef]
      -- `negFun` pulls out a negation of the whole series.
      have hneg : rseries (negFun sumTerms) t = -rseries sumTerms t :=
        rseries_negFun (t := t) (a := sumTerms)
      -- Expand the nested `addFun`.
      have hadd :
          rseries sumTerms t = (rseries term1 t + rseries term2 t) + rseries term3 t := by
        -- outer add
        have hadd' : rseries sumTerms t = rseries (addFun term1 term2) t + rseries term3 t :=
          haddOuter
        -- inner add
        have hadd'' : rseries (addFun term1 term2) t = rseries term1 t + rseries term2 t :=
          haddInner
        calc
          rseries sumTerms t = rseries (addFun term1 term2) t + rseries term3 t := hadd'
          _ = (rseries term1 t + rseries term2 t) + rseries term3 t := by
                simp [hadd'', add_assoc]
      -- Finish.
      calc
        rseries (negFun sumTerms) t = -rseries sumTerms t := hneg
        _ = -((rseries term1 t + rseries term2 t) + rseries term3 t) := by
              simp [hadd]
    -- Final simplification to match the statement.
    -- (Use associativity rather than `ring` to keep elaboration fast.)
    simp [hsum, hterm1, hterm2, hterm3, add_assoc, mul_assoc]
  -- Finish by substituting the `H₂,H₄` series identities.
  have hnum : psiS_num z =
        -((7 : ℂ) * (H₂ z) ^ 5 * (H₄ z) ^ 2 + (7 : ℂ) * (H₂ z) ^ 6 * (H₄ z) + (2 : ℂ) *
          (H₂ z) ^ 7) := by
    simp [psiS_num, z, add_assoc, mul_assoc]
  -- Rewrite everything.
  simp [z, hnum, hH2, hH4, hseries]

end SpherePacking.Dim24.Ineq2PsiSnum
