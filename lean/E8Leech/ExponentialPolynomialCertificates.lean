import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Exact Taylor certificates for exponential polynomials

Finite integer checks certify the initial coefficients; a linear threshold
certifies the entire tail. The analytic step uses the actual exponential series.
The example is the mathematical coefficient data of inequality (41) in
Seewoo Lee, arXiv:2602.10536v1, Lemma 3.5. This is an independent series proof,
not an import of a Ramanujan-identity axiom or of the upstream derivative proof.
-/

noncomputable section

namespace E8Leech

open scoped BigOperators

def exponentialPolynomialCoefficient {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, (b i * c i ^ n + (n : ℝ) * a i * c i ^ (n - 1))

theorem hasSum_linear_mul_exp (a c t : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * a * c ^ (n - 1) * t ^ n / (n.factorial : ℝ))
      (a * t * Real.exp (c * t)) := by
  let g := fun n : ℕ => (n : ℝ) * a * c ^ (n - 1) * t ^ n / (n.factorial : ℝ)
  have he : HasSum (fun n : ℕ => (c * t) ^ n / (n.factorial : ℝ))
      (Real.exp (c * t)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (c * t)
  have hshift : HasSum (fun n : ℕ => g (n + 1)) (a * t * Real.exp (c * t)) := by
    apply (he.mul_left (a * t)).congr_fun
    intro n
    dsimp [g]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, pow_succ, mul_pow]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hzero : ∑ i ∈ Finset.range 1, g i = 0 := by simp [g]
  change HasSum g (a * t * Real.exp (c * t))
  apply (hasSum_nat_add_iff' (f := g) 1).mp
  rw [hzero, sub_zero]
  exact hshift

theorem hasSum_exponentialPolynomial {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (t : ℝ) :
    HasSum (fun n : ℕ => exponentialPolynomialCoefficient a b c n *
      t ^ n / (n.factorial : ℝ))
      (∑ i, (a i * t + b i) * Real.exp (c i * t)) := by
  classical
  have hi : ∀ i : ι, HasSum
      (fun n : ℕ => (b i * c i ^ n + (n : ℝ) * a i * c i ^ (n - 1)) *
        t ^ n / (n.factorial : ℝ))
      ((a i * t + b i) * Real.exp (c i * t)) := by
    intro i
    have he : HasSum (fun n : ℕ => (c i * t) ^ n / (n.factorial : ℝ))
        (Real.exp (c i * t)) := by
      simpa only [Real.exp_eq_exp_ℝ] using
        NormedSpace.expSeries_div_hasSum_exp (c i * t)
    rw [show (a i * t + b i) * Real.exp (c i * t) =
      b i * Real.exp (c i * t) + a i * t * Real.exp (c i * t) by ring]
    apply ((he.mul_left (b i)).add (hasSum_linear_mul_exp (a i) (c i) t)).congr_fun
    intro n
    simp only [mul_pow]
    ring
  apply (hasSum_sum (s := Finset.univ) (fun i _ => hi i)).congr_fun
  intro n
  simp only [exponentialPolynomialCoefficient, Finset.sum_mul, Finset.sum_div]

theorem exponentialPolynomial_pos_of_coefficients {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (t : ℝ) (ht : 0 < t)
    (hcoeff : ∀ n, 0 ≤ exponentialPolynomialCoefficient a b c n)
    (m : ℕ) (hm : 0 < exponentialPolynomialCoefficient a b c m) :
    0 < ∑ i, (a i * t + b i) * Real.exp (c i * t) := by
  have hs := hasSum_exponentialPolynomial a b c t
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos
    (fun n => div_nonneg (mul_nonneg (hcoeff n) (pow_nonneg ht.le n))
      (Nat.cast_nonneg _)) m
    (div_pos (mul_pos hm (pow_pos ht m)) (by positivity))

def modular41Linear : Fin 9 → ℤ :=
  ![1, 502, 14608, 88234, 156190, 88234, 14608, 502, 1]

def modular41Constant : Fin 9 → ℤ :=
  ![8, 1968, 32368, 90608, 0, -90608, -32368, -1968, -8]

def modular41Coefficient (n : ℕ) : ℤ :=
  ∑ i : Fin 9, ((i.val : ℤ) ^ n * modular41Constant i +
    (n : ℤ) * (i.val : ℤ) ^ (n - 1) * modular41Linear i)

theorem modular41Coefficient_zero : modular41Coefficient 0 = 0 := by
  norm_num [modular41Coefficient, modular41Constant, Fin.sum_univ_succ]

theorem modular41Coefficient_initial_pos :
    ∀ n : Fin 64, 0 < n.val → 0 < modular41Coefficient n.val := by
  decide

theorem modular41Coefficient_pos (n : ℕ) (hn : 0 < n) :
    0 < modular41Coefficient n := by
  by_cases hsmall : n < 64
  · exact modular41Coefficient_initial_pos ⟨n, hsmall⟩ hn
  have hn64 : (64 : ℤ) ≤ n := by exact_mod_cast (show 64 ≤ n by omega)
  have hlin : ∀ i : Fin 9,
      0 ≤ (i.val : ℤ) * modular41Constant i + (n : ℤ) * modular41Linear i := by
    intro i
    fin_cases i <;> norm_num [modular41Constant, modular41Linear] <;> omega
  have hpow (i : Fin 9) : (i.val : ℤ) ^ n = (i.val : ℤ) ^ (n - 1) * i.val := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
  unfold modular41Coefficient
  apply Finset.sum_pos'
  · intro i _
    rw [hpow]
    have heq : (i.val : ℤ) ^ (n - 1) * i.val * modular41Constant i +
        (n : ℤ) * (i.val : ℤ) ^ (n - 1) * modular41Linear i =
        (i.val : ℤ) ^ (n - 1) *
          ((i.val : ℤ) * modular41Constant i + (n : ℤ) * modular41Linear i) := by ring
    rw [heq]
    exact mul_nonneg (pow_nonneg (Int.natCast_nonneg _) _) (hlin i)
  · refine ⟨1, Finset.mem_univ _, ?_⟩
    norm_num [modular41Constant, modular41Linear]
    positivity

theorem exponentialPolynomialCoefficient_modular41 (n : ℕ) :
    exponentialPolynomialCoefficient (fun i => (modular41Linear i : ℝ))
      (fun i => (modular41Constant i : ℝ)) (fun i : Fin 9 => (i.val : ℝ)) n =
      (modular41Coefficient n : ℝ) := by
  simp only [exponentialPolynomialCoefficient, modular41Coefficient, Int.cast_sum,
    Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem modular_exponential_polynomial_41_pos (t : ℝ) (ht : 0 < t) :
    0 < ∑ i : Fin 9, ((modular41Linear i : ℝ) * t + modular41Constant i) *
      Real.exp ((i.val : ℝ) * t) := by
  have hcoeff : ∀ n, 0 ≤ exponentialPolynomialCoefficient
      (fun i => (modular41Linear i : ℝ)) (fun i => (modular41Constant i : ℝ))
      (fun i : Fin 9 => (i.val : ℝ)) n := by
    intro n
    rw [exponentialPolynomialCoefficient_modular41]
    by_cases hn : n = 0
    · simp [hn, modular41Coefficient_zero]
    · exact_mod_cast (modular41Coefficient_pos n (by omega)).le
  apply exponentialPolynomial_pos_of_coefficients _ _ _ t ht hcoeff 1
  rw [exponentialPolynomialCoefficient_modular41]
  exact_mod_cast modular41Coefficient_pos 1 (by norm_num)

theorem modular_polynomial_inequality_41 (t : ℝ) (ht : 0 < t) :
    0 < t * ((Real.exp t) ^ 8 + 1 + 502 * ((Real.exp t) ^ 7 + Real.exp t) +
      14608 * ((Real.exp t) ^ 6 + (Real.exp t) ^ 2) +
      88234 * ((Real.exp t) ^ 5 + (Real.exp t) ^ 3) + 156190 * (Real.exp t) ^ 4) -
      8 * ((Real.exp t) ^ 8 - 1 + 246 * ((Real.exp t) ^ 7 - Real.exp t) +
        4046 * ((Real.exp t) ^ 6 - (Real.exp t) ^ 2) +
        11326 * ((Real.exp t) ^ 5 - (Real.exp t) ^ 3)) := by
  have h := modular_exponential_polynomial_41_pos t ht
  norm_num [modular41Linear, modular41Constant, Fin.sum_univ_succ] at h
  have he2 := Real.exp_nat_mul t 2
  have he3 := Real.exp_nat_mul t 3
  have he4 := Real.exp_nat_mul t 4
  have he5 := Real.exp_nat_mul t 5
  have he6 := Real.exp_nat_mul t 6
  have he7 := Real.exp_nat_mul t 7
  have he8 := Real.exp_nat_mul t 8
  norm_num only [Nat.cast_ofNat] at he2 he3 he4 he5 he6 he7 he8
  rw [he2, he3, he4, he5, he6, he7, he8] at h
  nlinarith only [h]

end E8Leech
