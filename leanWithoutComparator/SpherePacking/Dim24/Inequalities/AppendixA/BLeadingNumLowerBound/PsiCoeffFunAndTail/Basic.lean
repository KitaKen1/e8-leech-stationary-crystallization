-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.Basic
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.SparseCoeffs


/-!
### Convolution tools for `psiCoeffFun`

This file defines the "shift by one" operation `shift1Fun` on coefficient functions `ℕ → ℤ` and
proves the corresponding identity on `rseries`. It also records basic algebraic facts about
`powConvZ` (power via repeated `convZ`) and polynomial growth bounds for the resulting coefficients.
-/


open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.AppendixA


/-! ## Shift and `rseries` -/

/-- Shift a coefficient function by one place: `shift1Fun a 0 = 0` and `shift1Fun a (n+1) = a n`. -/
@[expose] public def shift1Fun (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => a n

/-- `rseries (shift1Fun a)` is `rC * rseries a`, assuming a polynomial coefficient bound. -/
public lemma rseries_shift1Fun_eq_mul (t : ℝ) (ht0 : 0 < t)
    (a : ℕ → ℤ) (C : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    rseries (shift1Fun a) t = (rC t) * rseries a t := by
  let f : ℕ → ℂ := fun n => (shift1Fun a n : ℂ) * (rC t) ^ n
  let g : ℕ → ℂ := fun n => (a n : ℂ) * (rC t) ^ n
  have hsG_norm : Summable (fun n : ℕ => ‖g n‖) := by
    simpa [g] using!
      summable_norm_rseries_of_coeffBound (t := t) (ht0 := ht0) (a := a) (C := C) (k := k) ha
  have hsG : Summable g := Summable.of_norm hsG_norm
  have hsSucc : Summable (fun n : ℕ => f (n + 1)) := by
    have hsMul : Summable (fun n : ℕ => g n * (rC t)) := hsG.mul_right (rC t)
    refine hsMul.congr ?_
    intro n
    simp [f, g, shift1Fun, pow_succ, mul_assoc]
  have hf : Summable f := (summable_nat_add_iff 1 (f := f)).1 hsSucc
  have hzero : ∀ n : ℕ, n ∉ Set.range Nat.succ → f n = 0 := by
    intro n hn
    cases n with
    | zero => simp [f, shift1Fun]
    | succ n => exact (hn ⟨n, rfl⟩).elim
  have hreindex : (∑' n : ℕ, f n) = ∑' m : ℕ, f (Nat.succ m) :=
    tsum_eq_tsum_comp_of_eq_zero_off_range (f := f) hf (g := Nat.succ) Nat.succ_injective hzero
  have hsucc :
      (∑' m : ℕ, f (Nat.succ m)) =
        (rC t) * ∑' m : ℕ, (a m : ℂ) * (rC t) ^ m := by
    have hterm :
        (fun m : ℕ => f (Nat.succ m)) =
          fun m : ℕ => (rC t) * ((a m : ℂ) * (rC t) ^ m) := by
      funext m
      simp [f, shift1Fun, pow_succ, mul_left_comm, mul_comm]
    rw [hterm]
    simpa [mul_assoc] using!
      (tsum_mul_left (a := (rC t)) (f := fun m : ℕ => (a m : ℂ) * (rC t) ^ m))
  simpa [rseries, f] using! (hreindex.trans hsucc)

lemma convZ_eq_sum_range (a b : ℕ → ℤ) (n : ℕ) :
    convZ a b n = ∑ k ∈ Finset.range (n + 1), a k * b (n - k) := by
  simpa [convZ, Nat.succ_eq_add_one] using!
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j => a i * b j) n)

lemma convZ_oneCoeffFun_right (a : ℕ → ℤ) (n : ℕ) : convZ a oneCoeffFun n = a n := by
  rw [convZ_eq_sum_range]
  have hn : n ∈ Finset.range (n + 1) := by simp
  refine
    (Finset.sum_eq_single_of_mem (s := Finset.range (n + 1))
      (f := fun k : ℕ => a k * oneCoeffFun (n - k)) (a := n) hn ?_).trans ?_
  · intro k hk hkne
    have hk' : k ≤ n := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using! hk)
    have hklt : k < n := lt_of_le_of_ne hk' hkne
    have hsub : n - k ≠ 0 := Nat.sub_ne_zero_of_lt hklt
    simp [oneCoeffFun, hsub]
  · simp [oneCoeffFun]

lemma convZ_oneCoeffFun_left (a : ℕ → ℤ) (n : ℕ) : convZ oneCoeffFun a n = a n := by
  rw [convZ_eq_sum_range]
  have h0 : 0 ∈ Finset.range (n + 1) := by simp
  refine
    (Finset.sum_eq_single_of_mem (s := Finset.range (n + 1))
      (f := fun k : ℕ => oneCoeffFun k * a (n - k)) (a := 0) h0 ?_).trans ?_
  · intro k hk hkne
    have hk0 : k ≠ 0 := hkne
    simp [oneCoeffFun, hk0]
  · simp [oneCoeffFun]

/-- The first convolution power is the identity: `powConvZ a 1 = a`. -/
public lemma powConvZ_one (a : ℕ → ℤ) : powConvZ a 1 = a := by
  ext n
  simpa [powConvZ] using! (convZ_oneCoeffFun_right (a := a) n)

lemma abs_oneCoeffFun_le (n : ℕ) : |(oneCoeffFun n : ℝ)| ≤ (1 : ℝ) := by
  cases n <;> simp [oneCoeffFun]

lemma rseries_oneCoeffFun (t : ℝ) : rseries oneCoeffFun t = 1 := by
  -- Only the `n = 0` term contributes.
  simp [rseries, oneCoeffFun, tsum_ite_eq]

/--
Coefficient growth bound for convolution powers `powConvZ a m`,
assuming a polynomial bound on `a`. -/
public lemma abs_powConvZ_le {a : ℕ → ℤ} (C : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    ∀ m n : ℕ,
      |(powConvZ a m n : ℝ)| ≤ (C ^ m) * (((n + 1 : ℕ) : ℝ) ^ (m * k + (m - 1))) := by
  have hsucc :
      ∀ m n : ℕ,
        |(powConvZ a (Nat.succ m) n : ℝ)| ≤
          (C ^ (Nat.succ m)) * (((n + 1 : ℕ) : ℝ) ^ ((Nat.succ m) * k + m)) := by
    intro m
    induction m with
    | zero =>
        intro n
        simpa [powConvZ_one, Nat.mul_zero, Nat.zero_add] using! (ha n)
    | succ m hm =>
        intro n
        have hconv :=
          abs_convZ_le (a := a) (b := powConvZ a (Nat.succ m))
            (Ca := C) (Cb := C ^ (Nat.succ m)) (ka := k) (kb := (Nat.succ m * k + m))
            ha hm n
        have hC : C * (C ^ (Nat.succ m)) = C ^ (Nat.succ (Nat.succ m)) := by
          simp [pow_succ, mul_comm]
        have hexp :
            k + (Nat.succ m * k + m) + 1 = Nat.succ (Nat.succ m) * k + Nat.succ m := by
          simp [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        simpa [powConvZ, hC, hexp] using! hconv
  intro m n
  cases m with
  | zero => simpa [powConvZ] using! (abs_oneCoeffFun_le n)
  | succ m => simpa [Nat.succ_sub_one] using! (hsucc m n)

/-- Under the usual coefficient bound, `rseries (powConvZ a m)` equals `(rseries a)^m`. -/
public lemma rseries_powConvZ_eq_pow (t : ℝ) (ht0 : 0 < t)
    (a : ℕ → ℤ) (C : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    ∀ m : ℕ, rseries (powConvZ a m) t = (rseries a t) ^ m := by
  intro m
  induction m with
  | zero =>
      -- `powConvZ a 0 = oneCoeffFun` and `rseries oneCoeffFun = 1`.
      simp [powConvZ, rseries_oneCoeffFun]
  | succ m hm =>
      have hsA :
          Summable (fun n : ℕ => ‖((a n : ℂ) * (rC t) ^ n)‖) :=
        summable_norm_rseries_of_coeffBound (t := t) (ht0 := ht0)
          (a := a) (C := C) (k := k) ha
      have hsPow :
          Summable (fun n : ℕ => ‖(((powConvZ a m) n : ℂ) * (rC t) ^ n)‖) := by
        refine summable_norm_rseries_of_coeffBound (t := t) (ht0 := ht0)
          (a := powConvZ a m) (C := C ^ m) (k := m * k + (m - 1)) ?_
        intro n
        simpa using! (abs_powConvZ_le (a := a) (C := C) (k := k) ha m n)
      have hmul := rseries_mul_cast (t := t) (a := a) (b := powConvZ a m) hsA hsPow
      calc
        rseries (powConvZ a (Nat.succ m)) t
            = rseries a t * rseries (powConvZ a m) t := by
              simpa [powConvZ] using! hmul.symm
        _ = rseries a t * (rseries a t) ^ m := by simp [hm]
        _ = (rseries a t) ^ (Nat.succ m) := by simp [pow_succ, mul_comm]

end SpherePacking.Dim24.AppendixA
