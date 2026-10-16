-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Defs
import SpherePacking.Dim24.MagicFunction.PureImagCommon


/-!
# Pure imaginary values of `a`

This file proves that the magic function `a` takes values in `iℝ`, i.e. `Re (a x) = 0` for all
`x : ℝ²⁴`. The proof conjugates the contour decomposition of `aProfile`.
-/

open Complex Real
open MeasureTheory
open scoped ComplexConjugate

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

open UpperHalfPlane
open MagicFunction.Parametrisations

lemma conj_E₂ (z : ℍ) : conj (E₂ z) = E₂ (negConjH z) := by
  -- Use the q-expansion formula for `E₂` and compare termwise under conjugation.
  let f : ℍ → ℕ+ → ℂ :=
    fun w n => (n : ℂ) * cexp (2 * π * Complex.I * (n : ℂ) * (w : ℂ)) /
      (1 - cexp (2 * π * Complex.I * (n : ℂ) * (w : ℂ)))
  have hterm : ∀ n : ℕ+, conj (f z n) = f (negConjH z) n := by
    intro n
    have hArg :
        conj (2 * π * Complex.I * (n : ℂ) * (z : ℂ)) =
          2 * π * Complex.I * (n : ℂ) * (negConjH z : ℂ) := by
      simp [negConjH_coe, conj_two, mul_assoc, mul_left_comm, mul_comm]
    -- Push conjugation through the rational expression, then rewrite the exponential argument.
    simp [f, div_eq_mul_inv, conj_cexp, negConjH_coe, conj_two, mul_assoc]
  have htsum :
      conj (∑' n : ℕ+, f z n) = ∑' n : ℕ+, f (negConjH z) n := by
    calc
      conj (∑' n : ℕ+, f z n) = ∑' n : ℕ+, conj (f z n) := by
        simpa using! (Complex.conj_tsum (fun n : ℕ+ => f z n))
      _ = ∑' n : ℕ+, f (negConjH z) n := by
        exact tsum_congr hterm
  -- Rewrite `E₂` at `z` and `negConjH z`, then use `htsum`.
  rw [E₂_eq z, E₂_eq (negConjH z)]
  -- Match the sum with `f`.
  have hf :
      (∑' (n : ℕ+), (n : ℂ) * cexp (2 * π * Complex.I * n * z) /
          (1 - cexp (2 * π * Complex.I * n * z))) = ∑' n : ℕ+, f z n := by
    rfl
  have hf' :
      (∑' (n : ℕ+), (n : ℂ) * cexp (2 * π * Complex.I * n * (negConjH z)) /
          (1 - cexp (2 * π * Complex.I * n * (negConjH z)))) = ∑' n : ℕ+, f (negConjH z) n := by
    rfl
  -- Finish.
  have h24 : conj (24 : ℂ) = (24 : ℂ) := by
    simpa using! (Complex.conj_natCast 24)
  -- Rewrite both sums to the bundled version `f`, then compute conjugation explicitly.
  rw [hf, hf']
  calc
    conj (1 - 24 * (∑' n : ℕ+, f z n)) =
        1 - conj (24 : ℂ) * conj (∑' n : ℕ+, f z n) := by
          simp [map_sub, map_mul]
    _ = 1 - (24 : ℂ) * (∑' n : ℕ+, f (negConjH z) n) := by
          simp [h24, htsum]
    _ = 1 - 24 * (∑' n : ℕ+, f (negConjH z) n) := by
          ring

lemma conj_E₄ (z : ℍ) : conj (E₄ z) = E₄ (negConjH z) := by
  -- Use the q-expansion for `E 4` and compare termwise under conjugation.
  rw [E4_apply z, E4_apply (negConjH z)]
  have hz := E_k_q_expansion 4 (by decide) (by decide) z
  have hz' := E_k_q_expansion 4 (by decide) (by decide) (negConjH z)
  have hz0 := (by simpa using! hz)
  have hz0' := (by simpa using! hz')
  rw [hz0, hz0']
  -- Conjugation fixes the (real) coefficient and acts termwise on the `tsum`.
  have hzeta_im : (riemannZeta (4 : ℕ)).im = 0 := by
    simpa [show (2 * 2 : ℕ) = 4 by decide] using! (riemannZeta_even_im_eq_zero 2 (by decide))
  have hzeta_conj : conj (riemannZeta (4 : ℕ)) = riemannZeta (4 : ℕ) :=
    conj_eq_of_im_eq_zero hzeta_im
  have hzeta_inv_conj : conj ((riemannZeta (4 : ℕ))⁻¹) = (riemannZeta (4 : ℕ))⁻¹ := by
    simpa [map_inv₀, hzeta_conj]
  let base : ℂ := -(2 * (π : ℂ) * Complex.I)
  have hbase : conj base = -base := by
    simp [base, conj_two, mul_left_comm, mul_comm]
  have hpow : conj (base ^ 4) = base ^ 4 := by
    grind only [= map_mul, = map_pow, = map_neg]
  have hcoef :
      conj ((riemannZeta (4 : ℕ))⁻¹ * (base ^ 4 / (Nat.factorial 3 : ℂ))) =
        (riemannZeta (4 : ℕ))⁻¹ * (base ^ 4 / (Nat.factorial 3 : ℂ)) := by
    have hdiv : conj (base ^ 4 / (Nat.factorial 3 : ℂ)) = base ^ 4 / (Nat.factorial 3 : ℂ) := by
      simp [div_eq_mul_inv, map_mul, map_inv₀, hpow]
    calc
      conj ((riemannZeta (4 : ℕ))⁻¹ * (base ^ 4 / (Nat.factorial 3 : ℂ))) =
          conj ((riemannZeta (4 : ℕ))⁻¹) * conj (base ^ 4 / (Nat.factorial 3 : ℂ)) := by
            simp [map_mul]
      _ = (riemannZeta (4 : ℕ))⁻¹ * (base ^ 4 / (Nat.factorial 3 : ℂ)) := by
            rw [hzeta_inv_conj, hdiv]
  let term : ℍ → ℕ+ → ℂ :=
    fun w n =>
      (↑((ArithmeticFunction.sigma 3) (n : ℕ)) : ℂ) *
        cexp (2 * (π : ℂ) * Complex.I * (w : ℂ) * (n : ℂ))
  have hterm : ∀ n : ℕ+, conj (term z n) = term (negConjH z) n := by
    intro n
    have hArg :
        conj (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ)) =
          2 * (π : ℂ) * Complex.I * (negConjH z : ℂ) * (n : ℂ) := by
      simp [negConjH_coe, conj_two, mul_assoc, mul_left_comm, mul_comm]
    have hexp :
        conj (cexp (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ))) =
          cexp (2 * (π : ℂ) * Complex.I * (negConjH z : ℂ) * (n : ℂ)) := by
      calc
        conj (cexp (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ))) =
            cexp (conj (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ))) := by
              simp [conj_cexp]
        _ = cexp (2 * (π : ℂ) * Complex.I * (negConjH z : ℂ) * (n : ℂ)) := by
              simp [hArg]
    dsimp [term]
    calc
      conj ((↑((ArithmeticFunction.sigma 3) (n : ℕ)) : ℂ) *
            cexp (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ))) =
          conj (↑((ArithmeticFunction.sigma 3) (n : ℕ)) : ℂ) *
            conj (cexp (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ))) := by
            simp [map_mul]
      _ =
          (↑((ArithmeticFunction.sigma 3) (n : ℕ)) : ℂ) *
            cexp (2 * (π : ℂ) * Complex.I * (negConjH z : ℂ) * (n : ℂ)) := by
            simp [hexp]
  have htsum :
      conj (∑' n : ℕ+, term z n) = ∑' n : ℕ+, term (negConjH z) n := by
    calc
      conj (∑' n : ℕ+, term z n) = ∑' n : ℕ+, conj (term z n) := by
        simpa using! (Complex.conj_tsum (fun n : ℕ+ => term z n))
      _ = ∑' n : ℕ+, term (negConjH z) n :=
        tsum_congr hterm
  -- Assemble.
  calc
    conj
        (1 +
          (riemannZeta (4 : ℕ))⁻¹ * (base ^ 4 / (Nat.factorial 3 : ℂ)) *
            (∑' n : ℕ+, term z n)) =
        1 +
          conj ((riemannZeta (4 : ℕ))⁻¹ * (base ^ 4 / (Nat.factorial 3 : ℂ))) *
            conj (∑' n : ℕ+, term z n) := by
          simp [map_add, map_mul, mul_assoc]
    _ =
        1 +
          (riemannZeta (4 : ℕ))⁻¹ * (base ^ 4 / (Nat.factorial 3 : ℂ)) *
            (∑' n : ℕ+, term (negConjH z) n) := by
          rw [hcoef, htsum]

lemma conj_E₆ (z : ℍ) : conj (E₆ z) = E₆ (negConjH z) := by
  -- Use the q-expansion for `E 6` and compare termwise under conjugation.
  rw [E6_apply z, E6_apply (negConjH z)]
  have hz := E_k_q_expansion 6 (by decide) (by decide) z
  have hz' := E_k_q_expansion 6 (by decide) (by decide) (negConjH z)
  have hz0 := (by simpa using! hz)
  have hz0' := (by simpa using! hz')
  rw [hz0, hz0']
  have hzeta_im : (riemannZeta (6 : ℕ)).im = 0 := by
    simpa [show (2 * 3 : ℕ) = 6 by decide] using! (riemannZeta_even_im_eq_zero 3 (by decide))
  have hzeta_conj : conj (riemannZeta (6 : ℕ)) = riemannZeta (6 : ℕ) :=
    conj_eq_of_im_eq_zero hzeta_im
  have hzeta_inv_conj : conj ((riemannZeta (6 : ℕ))⁻¹) = (riemannZeta (6 : ℕ))⁻¹ := by
    simpa [map_inv₀, hzeta_conj]
  let base : ℂ := -(2 * (π : ℂ) * Complex.I)
  have hbase : conj base = -base := by
    simp [base, conj_two, mul_left_comm, mul_comm]
  have hpow : conj (base ^ 6) = base ^ 6 := by
    grind only [= map_mul, = map_pow, = map_neg]
  have hcoef :
      conj ((riemannZeta (6 : ℕ))⁻¹ * (base ^ 6 / (Nat.factorial 5 : ℂ))) =
        (riemannZeta (6 : ℕ))⁻¹ * (base ^ 6 / (Nat.factorial 5 : ℂ)) := by
    have hdiv : conj (base ^ 6 / (Nat.factorial 5 : ℂ)) = base ^ 6 / (Nat.factorial 5 : ℂ) := by
      simp [div_eq_mul_inv, map_mul, map_inv₀, hpow]
    calc
      conj ((riemannZeta (6 : ℕ))⁻¹ * (base ^ 6 / (Nat.factorial 5 : ℂ))) =
          conj ((riemannZeta (6 : ℕ))⁻¹) * conj (base ^ 6 / (Nat.factorial 5 : ℂ)) := by
            simp [map_mul]
      _ = (riemannZeta (6 : ℕ))⁻¹ * (base ^ 6 / (Nat.factorial 5 : ℂ)) := by
            rw [hzeta_inv_conj, hdiv]
  let term : ℍ → ℕ+ → ℂ :=
    fun w n =>
      (↑((ArithmeticFunction.sigma 5) (n : ℕ)) : ℂ) *
        cexp (2 * (π : ℂ) * Complex.I * (w : ℂ) * (n : ℂ))
  have hterm : ∀ n : ℕ+, conj (term z n) = term (negConjH z) n := by
    intro n
    have hArg :
        conj (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ)) =
          2 * (π : ℂ) * Complex.I * (negConjH z : ℂ) * (n : ℂ) := by
      simp [negConjH_coe, conj_two, mul_assoc, mul_left_comm, mul_comm]
    have hexp :
        conj (cexp (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ))) =
          cexp (2 * (π : ℂ) * Complex.I * (negConjH z : ℂ) * (n : ℂ)) := by
      calc
        conj (cexp (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ))) =
            cexp (conj (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ))) := by
              simp [conj_cexp]
        _ = cexp (2 * (π : ℂ) * Complex.I * (negConjH z : ℂ) * (n : ℂ)) := by
              simp [hArg]
    dsimp [term]
    calc
      conj ((↑((ArithmeticFunction.sigma 5) (n : ℕ)) : ℂ) *
            cexp (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ))) =
          conj (↑((ArithmeticFunction.sigma 5) (n : ℕ)) : ℂ) *
            conj (cexp (2 * (π : ℂ) * Complex.I * (z : ℂ) * (n : ℂ))) := by
            simp [map_mul]
      _ =
          (↑((ArithmeticFunction.sigma 5) (n : ℕ)) : ℂ) *
            cexp (2 * (π : ℂ) * Complex.I * (negConjH z : ℂ) * (n : ℂ)) := by
            simp [hexp]
  have htsum :
      conj (∑' n : ℕ+, term z n) = ∑' n : ℕ+, term (negConjH z) n := by
    calc
      conj (∑' n : ℕ+, term z n) = ∑' n : ℕ+, conj (term z n) := by
        simpa using! (Complex.conj_tsum (fun n : ℕ+ => term z n))
      _ = ∑' n : ℕ+, term (negConjH z) n :=
        tsum_congr hterm
  calc
    conj
        (1 +
          (riemannZeta (6 : ℕ))⁻¹ * (base ^ 6 / (Nat.factorial 5 : ℂ)) *
            (∑' n : ℕ+, term z n)) =
        1 +
          conj ((riemannZeta (6 : ℕ))⁻¹ * (base ^ 6 / (Nat.factorial 5 : ℂ))) *
            conj (∑' n : ℕ+, term z n) := by
          simp [map_add, map_mul, mul_assoc]
    _ =
        1 +
          (riemannZeta (6 : ℕ))⁻¹ * (base ^ 6 / (Nat.factorial 5 : ℂ)) *
            (∑' n : ℕ+, term (negConjH z) n) := by
          rw [hcoef, htsum]

lemma conj_varphi (z : ℍ) : conj (varphi z) = varphi (negConjH z) := by
  -- Work with the numerator/denominator separately: this keeps `simp` fast.
  let N : ℍ → ℂ :=
    fun w =>
      (25 * (E₄ w) ^ 4 - 49 * (E₆ w) ^ 2 * (E₄ w))
        + 48 * (E₆ w) * (E₄ w) ^ 2 * (E₂ w)
        + ((-49) * (E₄ w) ^ 3 + 25 * (E₆ w) ^ 2) * (E₂ w) ^ 2
  let D : ℍ → ℂ := fun w => (Δ w) ^ (2 : ℕ)
  have hN : conj (N z) = N (negConjH z) := by
    simp [-E4_apply, -E6_apply, N, conj_E₂, conj_E₄, conj_E₆, sub_eq_add_neg]
    simp [starRingEnd_apply]
  have hD : conj (D z) = D (negConjH z) := by
    simp [D, conj_Δ]
  calc
    conj (varphi z) = conj (N z / D z) := by rfl
    _ = conj (N z) / conj (D z) := by simp [div_eq_mul_inv, map_mul, map_inv₀]
    _ = N (negConjH z) / D (negConjH z) := by simp [hN, hD]
    _ = varphi (negConjH z) := by rfl

lemma conj_varphi' (z : ℂ) : conj (varphi' z) = varphi' (-conj z) := by
  by_cases hz : 0 < z.im
  · have hz' : 0 < (-conj z).im := by
      simpa [Complex.conj_im] using! hz
    -- Reduce to the `ℍ`-statement `conj_varphi`.
    have h := conj_varphi (z := (⟨z, hz⟩ : ℍ))
    -- `negConjH ⟨z, hz⟩` has underlying complex number `-conj z`.
    simpa [varphi', hz, hz', negConjH, negConjH_coe] using! h
  · have hz' : ¬ 0 < (-conj z).im := by
      simpa [Complex.conj_im] using! hz
    simp [varphi', hz]

lemma ResToImagAxis.Real.const (c : ℂ) (hc : c.im = 0) :
    ResToImagAxis.Real (fun _ : ℍ ↦ c) := by
  intro t ht
  simp [ResToImagAxis, ht, hc]

lemma ResToImagAxis.Real.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) :
    ∀ n : ℕ, ResToImagAxis.Real (fun z : ℍ ↦ (F z) ^ n)
  | 0 => by
      intro t ht
      simp [ResToImagAxis, ht]
  | n + 1 => by
      have hn : ResToImagAxis.Real (fun z : ℍ ↦ (F z) ^ n) := ResToImagAxis.Real.pow hF n
      have hmul := ResToImagAxis.Real.mul hn hF
      simpa [pow_succ] using! hmul

lemma Complex.im_inv_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : (z⁻¹).im = 0 := by
  -- Use the explicit formula for the imaginary part of the inverse.
  simp_all

lemma ResToImagAxis.Real.inv {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (fun z : ℍ ↦ (F z)⁻¹) := by
  intro t ht
  have hFreal := hF t ht
  -- Only unfold `ResToImagAxis`/`resToImagAxis`; do not simplify inverses.
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte]
  exact Complex.im_inv_of_im_eq_zero hFreal

lemma varphi_imag_axis_real : ResToImagAxis.Real varphi := by
  -- Build this from real-valuedness of `E₂,E₄,E₆,Δ` on the imaginary axis.
  have hE2 : ResToImagAxis.Real E₂ := E₂_imag_axis_real
  have hE4 : ResToImagAxis.Real (fun z : ℍ ↦ E₄ z) := by
    simpa using! (E₄_imag_axis_real : ResToImagAxis.Real E₄.toFun)
  have hE6 : ResToImagAxis.Real (fun z : ℍ ↦ E₆ z) := by
    simpa using! (E₆_imag_axis_real : ResToImagAxis.Real E₆.toFun)
  have hΔ : ResToImagAxis.Real Δ := Delta_imag_axis_real
  have hE4_2 : ResToImagAxis.Real (fun z : ℍ ↦ (E₄ z) ^ 2) := ResToImagAxis.Real.pow hE4 2
  have hE4_3 : ResToImagAxis.Real (fun z : ℍ ↦ (E₄ z) ^ 3) := ResToImagAxis.Real.pow hE4 3
  have hE4_4 : ResToImagAxis.Real (fun z : ℍ ↦ (E₄ z) ^ 4) := ResToImagAxis.Real.pow hE4 4
  have hE6_2 : ResToImagAxis.Real (fun z : ℍ ↦ (E₆ z) ^ 2) := ResToImagAxis.Real.pow hE6 2
  have hE2_2 : ResToImagAxis.Real (fun z : ℍ ↦ (E₂ z) ^ 2) := ResToImagAxis.Real.pow hE2 2
  have hΔ_2 : ResToImagAxis.Real (fun z : ℍ ↦ (Δ z) ^ 2) := ResToImagAxis.Real.pow hΔ 2
  have hnum1 :
      ResToImagAxis.Real (fun z : ℍ ↦ (25 : ℂ) * (E₄ z) ^ 4) :=
    ResToImagAxis.Real.mul (ResToImagAxis.Real.const (25 : ℂ) (by simp)) hE4_4
  have hnum2 :
      ResToImagAxis.Real (fun z : ℍ ↦ (49 : ℂ) * (E₆ z) ^ 2 * E₄ z) :=
    ResToImagAxis.Real.mul
      (ResToImagAxis.Real.mul (ResToImagAxis.Real.const (49 : ℂ) (by simp)) hE6_2) hE4
  have hnum12 :
      ResToImagAxis.Real (fun z : ℍ ↦ (25 : ℂ) * (E₄ z) ^ 4 - (49 : ℂ) * (E₆ z) ^ 2 * E₄ z) := by
    simpa [sub_eq_add_neg, mul_assoc] using!
      ResToImagAxis.Real.add hnum1 (ResToImagAxis.Real.neg hnum2)
  have hnum3 :
      ResToImagAxis.Real (fun z : ℍ ↦ (48 : ℂ) * E₆ z * (E₄ z) ^ 2 * E₂ z) :=
    ResToImagAxis.Real.mul
      (ResToImagAxis.Real.mul
        (ResToImagAxis.Real.mul (ResToImagAxis.Real.const (48 : ℂ) (by simp)) hE6) hE4_2) hE2
  have hnum4a :
      ResToImagAxis.Real (fun z : ℍ ↦ (-49 : ℂ) * (E₄ z) ^ 3) :=
    ResToImagAxis.Real.mul (ResToImagAxis.Real.const (-49 : ℂ) (by simp)) hE4_3
  have hnum4b :
      ResToImagAxis.Real (fun z : ℍ ↦ (25 : ℂ) * (E₆ z) ^ 2) :=
    ResToImagAxis.Real.mul (ResToImagAxis.Real.const (25 : ℂ) (by simp)) hE6_2
  have hnum4c :
      ResToImagAxis.Real (fun z : ℍ ↦ ((-49 : ℂ) * (E₄ z) ^ 3 + (25 : ℂ) * (E₆ z) ^ 2)) :=
    ResToImagAxis.Real.add hnum4a hnum4b
  have hnum4 :
      ResToImagAxis.Real
        (fun z : ℍ ↦ ((-49 : ℂ) * (E₄ z) ^ 3 + (25 : ℂ) * (E₆ z) ^ 2) * (E₂ z) ^ 2) :=
    ResToImagAxis.Real.mul hnum4c hE2_2
  -- Package the numerator as a sum of three functions to avoid brittle parenthesization issues.
  let num12F : ℍ → ℂ :=
    fun z ↦ (25 : ℂ) * (E₄ z) ^ 4 - (49 : ℂ) * (E₆ z) ^ 2 * E₄ z
  let num3F : ℍ → ℂ := fun z ↦ (48 : ℂ) * E₆ z * (E₄ z) ^ 2 * E₂ z
  let num4F : ℍ → ℂ := fun z ↦ ((-49 : ℂ) * (E₄ z) ^ 3 + (25 : ℂ) * (E₆ z) ^ 2) * (E₂ z) ^ 2
  let num : ℍ → ℂ := num12F + num3F + num4F
  have hnum : ResToImagAxis.Real num := by
    have hnum12' : ResToImagAxis.Real num12F := by
      simpa [num12F] using! hnum12
    have hnum3' : ResToImagAxis.Real num3F := by
      simpa [num3F] using! hnum3
    have hnum4' : ResToImagAxis.Real num4F := by
      simpa [num4F] using! hnum4
    have htmp : ResToImagAxis.Real (num12F + num3F) := ResToImagAxis.Real.add hnum12' hnum3'
    have hsum : ResToImagAxis.Real ((num12F + num3F) + num4F) := ResToImagAxis.Real.add htmp hnum4'
    simpa [num, add_assoc] using! hsum
  -- `varphi = num / (Δ^2)` as `num * (Δ^2)⁻¹`.
  have hden_inv : ResToImagAxis.Real (fun z : ℍ ↦ ((Δ z) ^ 2)⁻¹) := ResToImagAxis.Real.inv hΔ_2
  have hmul : ResToImagAxis.Real (fun z : ℍ ↦ num z * ((Δ z) ^ 2)⁻¹) := by
    simpa [num, mul_assoc] using! ResToImagAxis.Real.mul hnum hden_inv
  -- Avoid brittle associativity/commutativity matching: rewrite by pointwise equality.
  have hEq : (fun z : ℍ ↦ num z * ((Δ z) ^ 2)⁻¹) = varphi := by
    funext z
    simp [Dim24.varphi, num, num12F, num3F, num4F, div_eq_mul_inv, add_assoc, mul_assoc]
  simpa [hEq] using! hmul

lemma conj_varphi'_mul_I (t : ℝ) :
    conj (varphi' ((Complex.I : ℂ) * (t : ℂ))) = varphi' ((Complex.I : ℂ) * (t : ℂ)) := by
  by_cases ht : 0 < t
  · -- On the imaginary axis with `t>0`, `varphi' (I*t)` is real-valued.
    have hres : (varphi.resToImagAxis t).im = 0 := varphi_imag_axis_real t ht
    have hval :
        (varphi
              (⟨(Complex.I : ℂ) * (t : ℂ), by
                simpa [Complex.mul_im, Complex.I_re, Complex.I_im] using! ht⟩ : ℍ)).im = 0 := by
      -- `resToImagAxis` uses the same point `⟨I*t, _⟩`, possibly with a different proof term.
      simpa [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] using! hres
    have hconj :
        conj
              (varphi
                (⟨(Complex.I : ℂ) * (t : ℂ), by
                  simpa [Complex.mul_im, Complex.I_re, Complex.I_im] using! ht⟩ : ℍ)) =
          varphi
            (⟨(Complex.I : ℂ) * (t : ℂ), by
              simpa [Complex.mul_im, Complex.I_re, Complex.I_im] using! ht⟩ : ℍ) :=
      (Complex.conj_eq_iff_im).2 hval
    simp [varphi', ht, hconj]
  · -- Here `t ≤ 0`, so `varphi' (I*t) = 0`.
    simp [varphi', ht, Complex.mul_im, Complex.I_re, Complex.I_im]

lemma conj_I₁' (u : ℝ) : conj (RealIntegrals.I₁' u) = -RealIntegrals.I₃' u := by
  -- Pair the `z₁'` and `z₃'` contour pieces via `z₃' = -conj(z₁')`.
  rw [RealIntegrals.I₁', RealIntegrals.I₃', conj_intervalIntegral]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simp_all
  have hz : conj (z₁' t) = -z₃' t := by
    -- Use the explicit endpoint formulas to avoid projections from `IccExtend`.
    have hz1 : z₁' t = (-1 : ℂ) + (Complex.I : ℂ) * t := by
      simpa using! (z₁'_eq_of_mem (t := t) htIcc)
    have hz3 : z₃' t = (1 : ℂ) + (Complex.I : ℂ) * t := by
      simpa using! (z₃'_eq_of_mem (t := t) htIcc)
    simp [hz1, hz3, Complex.conj_ofReal, Complex.conj_I, map_add, map_mul, add_comm]
  have harg1 : -1 / (z₁' t + 1) = (Complex.I : ℂ) * ((t⁻¹ : ℝ) : ℂ) := by
    have hz1 : z₁' t = (-1 : ℂ) + (Complex.I : ℂ) * t := by
      simpa using! (z₁'_eq_of_mem (t := t) htIcc)
    -- `z₁' t + 1 = I * t`.
    have hz1' : z₁' t + 1 = (Complex.I : ℂ) * (t : ℂ) := by
      simp [hz1, add_left_comm, add_comm]
    -- `-1/(I*t) = I * (t⁻¹)`.
    simp [hz1', div_eq_mul_inv, mul_comm]
  have harg3 : -1 / (z₃' t - 1) = (Complex.I : ℂ) * ((t⁻¹ : ℝ) : ℂ) := by
    have hz3 : z₃' t = (1 : ℂ) + (Complex.I : ℂ) * t := by
      simpa using! (z₃'_eq_of_mem (t := t) htIcc)
    have hz3' : z₃' t - 1 = (Complex.I : ℂ) * (t : ℂ) := by
      simp [hz3, sub_eq_add_neg, add_assoc, add_comm]
    simp [hz3', div_eq_mul_inv, mul_comm]
  have hvar : conj (varphi' (-1 / (z₁' t + 1))) = varphi' (-1 / (z₁' t + 1)) := by
    -- Along this contour piece, `-1/(z₁' t + 1)` lies on the imaginary axis.
    simpa [harg1] using! (conj_varphi'_mul_I (t := (t⁻¹ : ℝ)))
  have hpow : (1 + -z₃' t) ^ (10 : ℕ) = (z₃' t - 1) ^ (10 : ℕ) := by
    ring
  have hvar2 :
      conj (varphi' (-1 / (1 + z₁' t))) = varphi' ((Complex.I : ℂ) * ((t⁻¹ : ℝ) : ℂ)) := by
    grind only
  -- Now unfold the integrands and simplify.
  simp [RealIntegrals.RealIntegrands.Φ₁, RealIntegrals.RealIntegrands.Φ₃,
    RealIntegrals.ComplexIntegrands.Φ₁', RealIntegrals.ComplexIntegrands.Φ₃',
    conj_cexp, hz, harg3, hpow, hvar2, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I,
    mul_assoc, mul_left_comm, mul_comm, add_comm]

lemma conj_I₂' (u : ℝ) : conj (RealIntegrals.I₂' u) = -RealIntegrals.I₄' u := by
  rw [RealIntegrals.I₂', RealIntegrals.I₄', conj_intervalIntegral]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have hz : -(conj (z₂' t)) = z₄' t := by
    simpa using! (z₄'_eq_neg_conj_z₂' (t := t)).symm
  have hz' : conj (z₂' t) = -z₄' t := by
    have h := congrArg (fun w : ℂ => -w) hz
    simpa [neg_neg] using! h
  have hpow : (1 + -z₄' t) ^ (10 : ℕ) = (z₄' t - 1) ^ (10 : ℕ) := by
    ring
  have hvar2 : conj (varphi' (-1 / (1 + z₂' t))) = varphi' (-1 / (z₄' t - 1)) := by
    have harg : -(-1 / (1 + conj (z₂' t))) = (-1 : ℂ) / (z₄' t - 1) := by
      have hden : (1 + -z₄' t : ℂ) = -(z₄' t - 1) := by ring
      calc
        -(-1 / (1 + conj (z₂' t))) = (1 : ℂ) / (1 + conj (z₂' t)) := by
          simp [neg_div]
        _ = (1 : ℂ) / (1 + -z₄' t) := by
          simp [hz']
        _ = (-1 : ℂ) / (z₄' t - 1) := by
          -- Avoid recursion in `simp` by expanding the divisions explicitly.
          rw [div_eq_mul_inv, div_eq_mul_inv]
          rw [one_mul, neg_one_mul]
          rw [hden]
          exact (inv_neg (a := (z₄' t - 1 : ℂ)))
    have h := conj_varphi' (z := (-1 / (1 + z₂' t)))
    have h' :
        conj (varphi' (-1 / (1 + z₂' t))) = varphi' (-(-1 / (1 + conj (z₂' t)))) := by
      simpa [map_div, map_add, map_one, map_neg] using! h
    simpa [harg] using! h'
  simp [RealIntegrals.RealIntegrands.Φ₂, RealIntegrals.RealIntegrands.Φ₄,
    RealIntegrals.ComplexIntegrands.Φ₂', RealIntegrals.ComplexIntegrands.Φ₄',
    RealIntegrals.ComplexIntegrands.Φ₁', RealIntegrals.ComplexIntegrands.Φ₃',
    conj_cexp, hz', hpow, hvar2, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I,
    mul_assoc, mul_left_comm, mul_comm, add_comm]

lemma conj_I₅' (u : ℝ) : conj (RealIntegrals.I₅' u) = -RealIntegrals.I₅' u := by
  -- Isolate the contour integral.
  set I :
      ℂ :=
        ∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ u t with hIdef
  have hI : conj I = -I := by
    rw [hIdef, conj_intervalIntegral]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have hz : -(conj (z₅' t)) = z₅' t := by
      simpa using! (z₅'_eq_neg_conj (t := t)).symm
    have hz' : conj (z₅' t) = -z₅' t := by
      have h := congrArg (fun w : ℂ => -w) hz
      simpa [neg_neg] using! h
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simp_all
    have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
      simpa using! (z₅'_eq_of_mem (t := t) htIcc)
    have harg : -1 / z₅' t = (Complex.I : ℂ) * ((t⁻¹ : ℝ) : ℂ) := by
      simp [hz5, div_eq_mul_inv, mul_comm]
    have hvar : conj (varphi' (-1 / z₅' t)) = varphi' (-1 / z₅' t) := by
      simpa [harg] using! (conj_varphi'_mul_I (t := (t⁻¹ : ℝ)))
    have hpow : (-z₅' t) ^ (10 : ℕ) = (z₅' t) ^ (10 : ℕ) := by
      have h10 : Even (10 : ℕ) := by decide
      simpa using! (Even.neg_pow h10 (z₅' t))
    simp [RealIntegrals.RealIntegrands.Φ₅, RealIntegrals.ComplexIntegrands.Φ₅',
      conj_cexp, hz', hvar, hpow, map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_assoc, mul_left_comm, mul_comm]
  -- Assemble `I₅' = (-2) * I`.
  rw [RealIntegrals.I₅']
  have hIint : conj (∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ u t) =
      -∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ u t := by
    simpa [hIdef] using! hI
  calc
    conj ((-2 : ℂ) * ∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ u t)
        = conj (-2 : ℂ) * conj (∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ u t) := by
          simp [map_mul]
    _ = (-2 : ℂ) * (-(∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ u t)) := by
          have h2 : conj (-2 : ℂ) = (-2 : ℂ) := by
            simp [map_neg, conj_two]
          rw [hIint, h2]
    _ = -((-2 : ℂ) * ∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ u t) := by
          ring

lemma conj_I₆' (u : ℝ) : conj (RealIntegrals.I₆' u) = -RealIntegrals.I₆' u := by
  -- Isolate the tail integral.
  set I : ℂ := ∫ t in Set.Ici (1 : ℝ), RealIntegrals.RealIntegrands.Φ₆ u t with hIdef
  have hI : conj I = -I := by
    have hconj :
        conj I =
          ∫ t in Set.Ici (1 : ℝ), conj (RealIntegrals.RealIntegrands.Φ₆ u t) := by
      simpa [hIdef] using!
        (integral_conj
            (μ := (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))))
            (f := fun t : ℝ => RealIntegrals.RealIntegrands.Φ₆ u t)).symm
    rw [hconj]
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have hz6 : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by
      simpa using! (z₆'_eq_of_mem (t := t) ht)
    have hz' : conj (z₆' t) = -z₆' t := by
      simp [hz6, map_mul, Complex.conj_I]
    have hvarI : conj (varphi' ((Complex.I : ℂ) * (t : ℂ))) = varphi' ((Complex.I : ℂ) * (t : ℂ)) :=
      conj_varphi'_mul_I (t := t)
    simp [RealIntegrals.RealIntegrands.Φ₆, RealIntegrals.ComplexIntegrands.Φ₆',
      conj_cexp, hz6, hvarI, map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_left_comm, mul_comm]
  -- Assemble `I₆' = 2 * I`.
  rw [RealIntegrals.I₆']
  have hIint : conj (∫ t in Set.Ici (1 : ℝ), RealIntegrals.RealIntegrands.Φ₆ u t) =
      -∫ t in Set.Ici (1 : ℝ), RealIntegrals.RealIntegrands.Φ₆ u t := by
    simpa [hIdef] using! hI
  calc
    conj ((2 : ℂ) * ∫ t in Set.Ici (1 : ℝ), RealIntegrals.RealIntegrands.Φ₆ u t)
        = conj (2 : ℂ) * conj (∫ t in Set.Ici (1 : ℝ), RealIntegrals.RealIntegrands.Φ₆ u t) := by
          simp [map_mul]
    _ = (2 : ℂ) * (-(∫ t in Set.Ici (1 : ℝ), RealIntegrals.RealIntegrands.Φ₆ u t)) := by
          -- Rewrite the second factor using `hIint` and simplify `conj (2 : ℂ)` explicitly.
          have h2 : conj (2 : ℂ) = (2 : ℂ) := by
            simpa using! (Complex.conj_natCast 2)
          rw [hIint, h2]
    _ = -((2 : ℂ) * ∫ t in Set.Ici (1 : ℝ), RealIntegrals.RealIntegrands.Φ₆ u t) := by
          ring

lemma conj_aProfile (u : ℝ) : conj (aProfile u) = -aProfile u := by
  -- `aProfile` is the sum of the six contour pieces; pair them under conjugation.
  have hI3 : conj (RealIntegrals.I₃' u) = -RealIntegrals.I₁' u := by
    have h := congrArg conj (conj_I₁' (u := u))
    have h' : RealIntegrals.I₁' u = -conj (RealIntegrals.I₃' u) := by
      simpa [map_neg] using! h
    have h'' := congrArg (fun z : ℂ => -z) h'
    simpa [neg_neg] using! h''.symm
  have hI4 : conj (RealIntegrals.I₄' u) = -RealIntegrals.I₂' u := by
    have h := congrArg conj (conj_I₂' (u := u))
    have h' : RealIntegrals.I₂' u = -conj (RealIntegrals.I₄' u) := by
      simpa [map_neg] using! h
    have h'' := congrArg (fun z : ℂ => -z) h'
    simpa [neg_neg] using! h''.symm
  unfold aProfile RealIntegrals.a'
  simp [map_add, conj_I₁' (u := u), conj_I₂' (u := u), hI3, hI4,
    conj_I₅' (u := u), conj_I₆' (u := u), add_assoc, add_left_comm, add_comm]

/-- The magic function `a` takes values in `iℝ`: `Re (a x) = 0` for all `x : ℝ²⁴`. -/
public theorem a_mapsTo_pureImag : ∀ x : ℝ²⁴, (a x).re = 0 := by
  /- Proof sketch:
  From the analytic continuation formula in the paper, `a(r)` is `i` times a real expression
  (a real Laplace integral times `sin(π r^2/2)^2`), hence purely imaginary. -/
  intro x
  have ha : a x = aProfile (‖x‖ ^ 2) := by
    simp [a, SpherePacking.Dim24.aAux]
  have hconj : conj (aProfile (‖x‖ ^ 2)) = -aProfile (‖x‖ ^ 2) :=
    conj_aProfile (u := ‖x‖ ^ 2)
  have hre : (aProfile (‖x‖ ^ 2)).re = 0 := by
    have h' : (aProfile (‖x‖ ^ 2)).re = -(aProfile (‖x‖ ^ 2)).re := by
      have : (conj (aProfile (‖x‖ ^ 2))).re = (-aProfile (‖x‖ ^ 2)).re := by
        simp [hconj]
      simpa only [Complex.conj_re] using! this
    linarith
  simp [ha, hre]

end

end SpherePacking.Dim24
