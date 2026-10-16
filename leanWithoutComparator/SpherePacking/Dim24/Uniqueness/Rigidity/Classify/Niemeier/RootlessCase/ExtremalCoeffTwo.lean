-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.ModularForms.DimensionFormulas
public import SpherePacking.ModularForms.EisensteinBase
public import SpherePacking.ModularForms.QExpansionLemmas.QExpansionAlgebra
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Coefficient computations for an extremal weight-12 modular form

This file computes the `q^2` coefficient of the weight-12 modular form `E₄^3 - 720 • Δ`.

Using the standard `q`-expansions of `E₄`, `E₆`, and `Δ`, we obtain the classical value
`196560`. These are purely modular-form computations; later files relate this coefficient to
theta-series shell counts.

## Main statements
* `E4_sq_q_exp_one`
* `extremal_weight12_q_exp_two`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

open scoped BigOperators
open scoped ArithmeticFunction.sigma

open ArithmeticFunction
open ModularFormClass
open UpperHalfPlane hiding I
open scoped CongruenceSubgroup MatrixGroups ModularForm

private lemma prime_two : Nat.Prime 2 := by decide

lemma sigma3_two : σ 3 2 = 9 := by
  have h := sigma_apply_prime_pow (k := 3) (p := 2) (i := 1) prime_two
  simpa [pow_one, Finset.sum_range_succ] using! h

lemma sigma5_two : σ 5 2 = 33 := by
  have h := sigma_apply_prime_pow (k := 5) (p := 2) (i := 1) prime_two
  simpa [pow_one, Finset.sum_range_succ] using! h

lemma E4_q_exp_two : (qExpansion 1 E₄).coeff 2 = 2160 := by
  have h := congr_fun E4_q_exp 2
  -- `2 ≠ 0`, so we are in the nonzero branch.
  simp [sigma3_two] at h
  simpa [show (240 : ℂ) * 9 = (2160 : ℂ) by norm_num] using! h

lemma E6_q_exp_two : (qExpansion 1 E₆).coeff 2 = -16632 := by
  have h : (qExpansion 1 E₆).coeff 2 = (-(504 : ℂ)) * 33 := by
    simpa [sigma5_two] using! congr_fun E6_q_exp 2
  simpa using! h.trans (by norm_num)

lemma antidiagonal_two :
    Finset.antidiagonal 2 = {(2, 0), (1, 1), (0, 2)} := by
  trivial

/-- The `q`-expansion coefficient at `q^1` of `E₄^2` is `480`. -/
public lemma E4_sq_q_exp_one :
    (qExpansion 1 (E₄.mul E₄)).coeff 1 = 480 := by
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff]
  rw [PowerSeries.coeff_mul, antidiagonal_one]
  have h0 := E4_q_exp_zero
  have h1 := E4_q_exp_one
  simp [h0, h1]
  ring

lemma E4_sq_q_exp_two :
    (qExpansion 1 (E₄.mul E₄)).coeff 2 = 61920 := by
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff]
  rw [PowerSeries.coeff_mul, antidiagonal_two]
  have h0 := E4_q_exp_zero
  have h1 := E4_q_exp_one
  have h2 := E4_q_exp_two
  simp [h0, h1, h2]
  ring

lemma E4_cubed_q_exp_two :
    (qExpansion 1 (E₄.mul (E₄.mul E₄))).coeff 2 = 179280 := by
  -- `(E₄) * (E₄ * E₄)` and use the already-computed square coefficients.
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff]
  rw [PowerSeries.coeff_mul, antidiagonal_two]
  have h0 := E4_q_exp_zero
  have h1 := E4_q_exp_one
  have h2 := E4_q_exp_two
  have hs0 : (qExpansion 1 (E₄.mul E₄)).coeff 0 = 1 := by
    -- constant term of a product is the product of constant terms
    rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff, PowerSeries.coeff_mul]
    simp [E4_q_exp_zero]
  have hs1 := E4_sq_q_exp_one
  have hs2 := E4_sq_q_exp_two
  simp [h0, h1, h2, hs0, hs1, hs2]
  ring

lemma E6_squared_q_exp_two :
    (qExpansion 1 (E₆.mul E₆)).coeff 2 = 220752 := by
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff]
  rw [PowerSeries.coeff_mul, antidiagonal_two]
  have h0 := E6_q_exp_zero
  have h1 := E6_q_exp_one
  have h2 := E6_q_exp_two
  simp [h0, h1, h2]
  ring

/-- The `q^2` coefficient of the form `E₄^3 - 720 • Δ` is `196560`. -/
public lemma extremal_weight12_q_exp_two :
    (qExpansion 1
        (let F : ModularForm Γ(1) 12 := E₄.mul (E₄.mul E₄)
         let G : ModularForm Γ(1) 12 := ModForm_mk Γ(1) 12 Delta
         F - (720 : ℂ) • G)).coeff 2 = 196560 := by
  let F : ModularForm Γ(1) 12 := E₄.mul (E₄.mul E₄)
  let G : ModularForm Γ(1) 12 := ModForm_mk Γ(1) 12 Delta
  have hGq : qExpansion 1 G = qExpansion 1 Delta := by
    apply qExpansion_ext2 G Delta
    rfl
  have hG2 : (qExpansion 1 G).coeff 2 = (-24 : ℂ) := by
    simpa [hGq] using! (Delta_q_exp_two : (qExpansion 1 Delta).coeff 2 = (-24 : ℂ))
  have hF2 : (qExpansion 1 F).coeff 2 = 179280 := by
    simpa [F] using! (E4_cubed_q_exp_two : (qExpansion 1 (E₄.mul (E₄.mul E₄))).coeff 2 = 179280)
  -- `E₄^3` contributes `179280`, and `-720 * Δ` contributes `-720 * (-24)`.
  -- Use `qExpansion_sub` and `qExpansion_smul2` to reduce to coefficient arithmetic.
  have : (qExpansion 1 (F - (720 : ℂ) • G)).coeff 2 = 196560 := by
    -- Expand `qExpansion` through subtraction and scalar multiplication.
    have hsub :
        qExpansion 1 (F - (720 : ℂ) • G) =
          qExpansion 1 F - qExpansion 1 ((720 : ℂ) • G) := by
      simpa using! (qExpansion_sub1 (f := F) (g := (720 : ℂ) • G))
    have hsmul : qExpansion 1 ((720 : ℂ) • G) = (720 : ℂ) • qExpansion 1 G := by
      simpa using!
        (qExpansion_smul2 (n := 1) (k := (12 : ℤ)) (a := (720 : ℂ)) (f := G)).symm
    -- Now take the `q^2`-coefficient.
    -- `PowerSeries.coeff` is linear and respects scalar multiplication.
    -- The remaining goal is arithmetic in `ℂ`.
    simp [hsub, hsmul, hF2, hG2]
    ring
  simpa [F, G] using! this

end SpherePacking.Dim24.Uniqueness.RigidityClassify
