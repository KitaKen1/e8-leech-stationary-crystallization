-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.QHalfTheta4
import Mathlib.Analysis.Normed.Group.Tannery


/-!
# Truncation bounds for `Θ₂`

This file develops the first `q`-terms for `Θ₂` at the cusp `i∞` and proves a basic `o(qFull)`
estimate for the tail of `jacobiTheta₂ (z/2) z`.

The key tail term after dividing by `qFull` has exponent coefficient `n^2 + n - 2`.

## Main definitions
* `qQuarter`, `qFull`

## Main statements
* `qFull_eq_qHalf_sq`
* `tendsto_Θ₂_sub_trunc_div_qQuarter_mul_q`
* `qQuarter_pow_four`
-/

open scoped Real
open scoped Topology
open scoped UpperHalfPlane
open scoped Complex

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter UpperHalfPlane

namespace Deriv

/-- The quarter-parameter `qQuarter z = exp(π i z / 4)`. -/
@[expose] public def qQuarter (z : ℍ) : ℂ :=
  cexp (Real.pi * Complex.I * (z : ℂ) / 4)

/-- `qQuarter z` is nonzero for all `z` in the upper half-plane. -/
public lemma qQuarter_ne_zero (z : ℍ) : qQuarter z ≠ 0 := by
  simp [qQuarter]

/-- The full parameter `qFull z = exp(2π i z)`. -/
@[expose] public def qFull (z : ℍ) : ℂ :=
  cexp (2 * Real.pi * Complex.I * (z : ℂ))

lemma qFull_ne_zero (z : ℍ) : qFull z ≠ 0 := by
  simp [qFull]

lemma Θ₂_as_qQuarter_mul_jacobiTheta₂ (z : ℍ) :
    Θ₂ z = qQuarter z * jacobiTheta₂ (z / 2) z := by
  simpa [qQuarter, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! (Θ₂_as_jacobiTheta₂ z)


def coeff (n : ℤ) : ℤ := n ^ 2 + n - 2

lemma jacobiTheta₂_term_div_qFull (n : ℤ) (z : ℍ) :
    jacobiTheta₂_term n ((z : ℂ) / 2) (z : ℂ) / qFull z =
      cexp (Real.pi * Complex.I * (coeff n : ℂ) * (z : ℂ)) := by
  have h1 := jacobiTheta₂_term_half_apply (n := n) (z := (z : ℂ))
  -- Combine the quotient into a single exponential using `exp_sub`.
  have hsub :
      ((Real.pi : ℂ) * Complex.I * (n ^ 2 + n : ℂ) * (z : ℂ) -
          (2 * Real.pi * Complex.I * (z : ℂ))) =
        (Real.pi : ℂ) * Complex.I * (coeff n : ℂ) * (z : ℂ) := by
    simp [coeff]
    ring_nf
  -- Rewrite numerator/denominator via `jacobiTheta₂_term_half_apply` and `qFull`.
  rw [h1, qFull]
  -- `exp A / exp B = exp (A - B)`.
  have hA :
      cexp ((Real.pi : ℂ) * Complex.I * (n ^ 2 + n : ℂ) * (z : ℂ)) /
          cexp (2 * Real.pi * Complex.I * (z : ℂ)) =
        cexp
          (((Real.pi : ℂ) * Complex.I * (n ^ 2 + n : ℂ) * (z : ℂ)) -
            (2 * Real.pi * Complex.I * (z : ℂ))) := by
    simpa using!
      (Complex.exp_sub
        ((Real.pi : ℂ) * Complex.I * (n ^ 2 + n : ℂ) * (z : ℂ))
        (2 * Real.pi * Complex.I * (z : ℂ))).symm
  simpa [hsub] using! hA

lemma norm_cexp_pi_I_mul (m : ℤ) (z : ℍ) :
    ‖cexp (Real.pi * Complex.I * (m : ℂ) * (z : ℂ))‖ =
      Real.exp (-Real.pi * (m : ℝ) * z.im) := by
  -- Put the exponent in the form `w * I`, then use `‖exp (w * I)‖ = exp (-Im w)`.
  have hmul :
      (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ) =
        ((Real.pi : ℂ) * (m : ℂ) * (z : ℂ)) * Complex.I := by
    ac_rfl
  have him : (((Real.pi : ℂ) * (m : ℂ) * (z : ℂ)).im) = Real.pi * (m : ℝ) * z.im := by
    -- The prefactor is real.
    simp [Complex.mul_im, mul_assoc, mul_left_comm]
  calc
    ‖cexp (Real.pi * Complex.I * (m : ℂ) * (z : ℂ))‖ =
        ‖cexp (((Real.pi : ℂ) * (m : ℂ) * (z : ℂ)) * Complex.I)‖ := by
          simp [hmul]
    _ = Real.exp (-(((Real.pi : ℂ) * (m : ℂ) * (z : ℂ)).im)) := by
          simpa using! (Complex.norm_exp_mul_I ((Real.pi : ℂ) * (m : ℂ) * (z : ℂ)))
    _ = Real.exp (-Real.pi * (m : ℝ) * z.im) := by
          rw [him]
          simp [mul_assoc]

/-!
Elementary arithmetic facts for the tail indices.
-/

def S : Finset ℤ := {0, -1, 1, -2}

lemma not_mem_S_cases {n : ℤ} (hn : n ∉ S) : (2 : ℤ) ≤ n ∨ n ≤ (-3 : ℤ) := by
  have hn' : n ≠ (0 : ℤ) ∧ n ≠ (-1 : ℤ) ∧ n ≠ (1 : ℤ) ∧ n ≠ (-2 : ℤ) := by
    simpa [S] using! hn
  grind

lemma coeff_pos_of_not_mem {n : ℤ} (hn : n ∉ S) : (0 : ℤ) < coeff n := by
  rcases not_mem_S_cases (hn := hn) with hge | hle
  · -- `n ≥ 2`
    have : (0 : ℤ) < n ^ 2 + n - 2 := by nlinarith [hge]
    simpa [coeff] using! this
  · -- `n ≤ -3`
    have : (0 : ℤ) < n ^ 2 + n - 2 := by nlinarith [hle]
    simpa [coeff] using! this

lemma abs_le_coeff_of_not_mem {n : ℤ} (hn : n ∉ S) : |n| ≤ coeff n := by
  rcases not_mem_S_cases (hn := hn) with hge | hle
  · have hn0 : 0 ≤ n := le_trans (by omega : (0 : ℤ) ≤ 2) hge
    have habs : |n| = n := by simp [abs_of_nonneg hn0]
    have : n ≤ n ^ 2 + n - 2 := by nlinarith [hge]
    simpa [coeff, habs] using! this
  · have hn0 : n ≤ 0 := le_trans hle (by omega : (-3 : ℤ) ≤ 0)
    have habs : |n| = -n := by simp [abs_of_nonpos hn0]
    have : -n ≤ n ^ 2 + n - 2 := by nlinarith [hle]
    simpa [coeff, habs] using! this

/-!
Asymptotics: `jacobiTheta₂ (z/2) z = 2 + 2*qFull z + o(qFull z)` as `Im z → ∞`.
-/

lemma jacobiTheta₂_trunc_two_terms (z : ℍ) :
    (∑ n ∈ S, jacobiTheta₂_term n ((z : ℂ) / 2) (z : ℂ)) =
      (2 : ℂ) + (2 : ℂ) * qFull z := by
  -- Evaluate the four terms using `jacobiTheta₂_term_half_apply`.
  have h0 : jacobiTheta₂_term (0 : ℤ) ((z : ℂ) / 2) (z : ℂ) = (1 : ℂ) := by
    simpa using! (jacobiTheta₂_term_half_apply (n := (0 : ℤ)) (z := (z : ℂ)))
  have hneg1 : jacobiTheta₂_term (-1 : ℤ) ((z : ℂ) / 2) (z : ℂ) = (1 : ℂ) := by
    simpa using! (jacobiTheta₂_term_half_apply (n := (-1 : ℤ)) (z := (z : ℂ)))
  have h1 : jacobiTheta₂_term (1 : ℤ) ((z : ℂ) / 2) (z : ℂ) = qFull z := by
    have hbase :
        jacobiTheta₂_term (1 : ℤ) ((z : ℂ) / 2) (z : ℂ) =
          cexp (↑π * Complex.I * (1 + 1) * (z : ℂ)) := by
      simpa using! (jacobiTheta₂_term_half_apply (n := (1 : ℤ)) (z := (z : ℂ)))
    have htwo : (1 + 1 : ℂ) = (2 : ℂ) := by norm_num
    calc
      jacobiTheta₂_term (1 : ℤ) ((z : ℂ) / 2) (z : ℂ) =
          cexp (↑π * Complex.I * (1 + 1) * (z : ℂ)) := hbase
      _ = cexp (↑π * Complex.I * (2 : ℂ) * (z : ℂ)) := by simp [htwo]
      _ = qFull z := by
            simp [qFull, mul_assoc, mul_comm]
  have hneg2 : jacobiTheta₂_term (-2 : ℤ) ((z : ℂ) / 2) (z : ℂ) = qFull z := by
    have hbase :
        jacobiTheta₂_term (-2 : ℤ) ((z : ℂ) / 2) (z : ℂ) =
          cexp (↑π * Complex.I * ((2 : ℂ) ^ 2 + (-2 : ℂ)) * (z : ℂ)) := by
      simpa using! (jacobiTheta₂_term_half_apply (n := (-2 : ℤ)) (z := (z : ℂ)))
    have htwo : ((2 : ℂ) ^ 2 + (-2 : ℂ)) = (2 : ℂ) := by norm_num
    calc
      jacobiTheta₂_term (-2 : ℤ) ((z : ℂ) / 2) (z : ℂ) =
          cexp (↑π * Complex.I * ((2 : ℂ) ^ 2 + (-2 : ℂ)) * (z : ℂ)) := hbase
      _ = cexp (↑π * Complex.I * (2 : ℂ) * (z : ℂ)) := by simp [htwo]
      _ = qFull z := by
            simp [qFull, mul_assoc, mul_comm]
  simp [S, h0, hneg1, h1, hneg2, qFull]
  ring_nf

lemma tendsto_jacobiTheta₂_sub_trunc_div_qFull :
    Tendsto
        (fun z : ℍ =>
          (jacobiTheta₂ (z / 2) z - ((2 : ℂ) + (2 : ℂ) * qFull z)) / qFull z)
        atImInfty (𝓝 (0 : ℂ)) := by
  -- Expand `jacobiTheta₂` as a series and split off the four terms.
  have hs (z : ℍ) :
      Summable (fun n : ℤ => jacobiTheta₂_term n ((z : ℂ) / 2) (z : ℂ)) :=
    (summable_jacobiTheta₂_term_iff (z := (z : ℂ) / 2) (τ := (z : ℂ))).2 (by simpa using! z.im_pos)
  have hsplit (z : ℍ) :
      jacobiTheta₂ (z / 2) z =
        (∑ n ∈ S, jacobiTheta₂_term n ((z : ℂ) / 2) (z : ℂ)) +
          ∑' n : (Sᶜ : Set ℤ), jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) := by
    simpa [jacobiTheta₂] using! ((hs z).sum_add_tsum_compl (s := S)).symm
  have hrem (z : ℍ) :
      jacobiTheta₂ (z / 2) z - ((2 : ℂ) + (2 : ℂ) * qFull z) =
        ∑' n : (Sᶜ : Set ℤ), jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) := by
    have hfin :
        (∑ n ∈ S, jacobiTheta₂_term n ((z : ℂ) / 2) (z : ℂ)) =
          (2 : ℂ) + (2 : ℂ) * qFull z := jacobiTheta₂_trunc_two_terms (z := z)
    -- `((finite) + tail) - finite = tail`.
    simp [hsplit z, hfin, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Tail tends to 0 after dividing by `qFull`, by dominated convergence.
  have htail :
      Tendsto
          (fun z : ℍ =>
            (∑' n : (Sᶜ : Set ℤ),
                jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) / qFull z))
          atImInfty (𝓝 (0 : ℂ)) := by
    let r : ℝ := Real.exp (-Real.pi)
    have hr0 : 0 ≤ r := by positivity [r]
    have hr1 : r < 1 := by
      have : (-Real.pi : ℝ) < 0 := by nlinarith [Real.pi_pos]
      simpa [r] using! Real.exp_lt_one_iff.2 this
    have hsum_r : Summable (fun n : ℤ => r ^ Int.natAbs n) :=
      summable_pow_natAbs hr0 hr1
    have hpt :
        ∀ n : (Sᶜ : Set ℤ),
          Tendsto
              (fun z : ℍ => jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) / qFull z)
              atImInfty (𝓝 (0 : ℂ)) := by
      intro n
      have hnS : (n : ℤ) ∉ S := by simpa [S] using! n.property
      have hkpos : (0 : ℤ) < coeff (n : ℤ) := coeff_pos_of_not_mem (hn := hnS)
      -- Use the explicit norm formula to show decay.
      have him : Tendsto (fun z : ℍ => z.im) atImInfty atTop := tendsto_im_atImInfty
      have hbot :
          Tendsto (fun z : ℍ => (-Real.pi * ((coeff (n : ℤ) : ℤ) : ℝ)) * z.im) atImInfty atBot := by
        have hneg : (-Real.pi * ((coeff (n : ℤ) : ℤ) : ℝ)) < 0 := by
          have : (0 : ℝ) < ((coeff (n : ℤ) : ℤ) : ℝ) := by exact_mod_cast hkpos
          nlinarith [Real.pi_pos, this]
        exact him.const_mul_atTop_of_neg hneg
      have hExp :
          Tendsto
              (fun z : ℍ =>
                Real.exp ((-Real.pi * ((coeff (n : ℤ) : ℤ) : ℝ)) * z.im))
              atImInfty (𝓝 (0 : ℝ)) :=
        Real.tendsto_exp_atBot.comp hbot
      -- Convert to a complex limit via norms.
      apply tendsto_zero_iff_norm_tendsto_zero.2
      have hnormPoint (z : ℍ) :
          ‖cexp (Real.pi * Complex.I * (coeff (n : ℤ) : ℂ) * (z : ℂ))‖ =
            Real.exp ((-Real.pi * ((coeff (n : ℤ) : ℤ) : ℝ)) * z.im) := by
        -- `‖exp(π i m z)‖ = exp(-π m Im z)`.
        simpa [mul_assoc] using! (norm_cexp_pi_I_mul (m := coeff (n : ℤ)) z)
      have hEqNormPoint (z : ℍ) :
          ‖jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) / qFull z‖ =
            ‖cexp (Real.pi * Complex.I * (coeff (n : ℤ) : ℂ) * (z : ℂ))‖ := by
        simpa using! congrArg norm (jacobiTheta₂_term_div_qFull (n := (n : ℤ)) (z := z))
      have hExpNorm :
          Tendsto
              (fun z : ℍ => ‖cexp (Real.pi * Complex.I * (coeff (n : ℤ) : ℂ) * (z : ℂ))‖)
              atImInfty (𝓝 (0 : ℝ)) :=
        hExp.congr fun z => (hnormPoint z).symm
      exact hExpNorm.congr fun z => (hEqNormPoint z).symm
    have hdom :
        ∀ᶠ z : ℍ in atImInfty,
          ∀ n : (Sᶜ : Set ℤ),
            ‖jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) / qFull z‖ ≤
              r ^ Int.natAbs (n : ℤ) := by
      refine (Filter.eventually_atImInfty).2 ⟨1, ?_⟩
      intro z hz n
      have hnS : (n : ℤ) ∉ S := by simpa [S] using! n.property
      have hpos : (0 : ℤ) < coeff (n : ℤ) := coeff_pos_of_not_mem (hn := hnS)
      have habs : |(n : ℤ)| ≤ coeff (n : ℤ) := abs_le_coeff_of_not_mem (hn := hnS)
      -- Rewrite the norm using the exponential formula.
      have hnorm :
          ‖jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) / qFull z‖ =
            Real.exp (-Real.pi * (coeff (n : ℤ) : ℝ) * z.im) := by
        -- First rewrite the quotient to a single exponential.
        have hrew : jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) / qFull z =
            cexp (Real.pi * Complex.I * (coeff (n : ℤ) : ℂ) * (z : ℂ)) :=
          jacobiTheta₂_term_div_qFull (n := (n : ℤ)) (z := z)
        -- Take norms and use the explicit norm formula.
        calc
          ‖jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) / qFull z‖ =
              ‖cexp (Real.pi * Complex.I * (coeff (n : ℤ) : ℂ) * (z : ℂ))‖ := by
                simp [hrew]
          _ = Real.exp (-Real.pi * (coeff (n : ℤ) : ℝ) * z.im) := by
                simpa using! (norm_cexp_pi_I_mul (m := coeff (n : ℤ)) z)
      -- Compare exponents using `Im z ≥ 1` and `|n| ≤ coeff n`.
      have hz' : (1 : ℝ) ≤ z.im := hz
      have hcoeff0 : (0 : ℝ) ≤ (coeff (n : ℤ) : ℝ) := by exact_mod_cast (le_of_lt hpos)
      have habs' : ((Int.natAbs (n : ℤ) : ℤ) : ℝ) ≤ ((coeff (n : ℤ) : ℤ) : ℝ) := by
        -- `|(n:ℤ)| = (natAbs n : ℤ)` and then use `|n| ≤ coeff n`.
        have hnat : (Int.natAbs (n : ℤ) : ℤ) = |(n : ℤ)| := by
          simp
        -- Cast to `ℝ`.
        have habs'' : ((|(n : ℤ)| : ℤ) : ℝ) ≤ ((coeff (n : ℤ) : ℤ) : ℝ) := by exact_mod_cast habs
        simpa [hnat] using! habs''
      have hmul : ((Int.natAbs (n : ℤ) : ℤ) : ℝ) ≤ (coeff (n : ℤ) : ℝ) * z.im := by
        nlinarith
      have hexp_le :
          Real.exp (-Real.pi * (coeff (n : ℤ) : ℝ) * z.im) ≤
            Real.exp (-Real.pi * ((Int.natAbs (n : ℤ) : ℤ) : ℝ)) := by
        -- `-π < 0`, so inequalities reverse when multiplying.
        have hle :
            (-Real.pi) * ((coeff (n : ℤ) : ℝ) * z.im) ≤
              (-Real.pi) * ((Int.natAbs (n : ℤ) : ℤ) : ℝ) := by
          have hpi : (-Real.pi : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
          exact mul_le_mul_of_nonpos_left hmul hpi
        simpa [mul_assoc] using! (Real.exp_le_exp.2 hle)
      -- Convert `exp(-π * natAbs)` to `r ^ natAbs`.
      have hrpow :
          Real.exp (-Real.pi * ((Int.natAbs (n : ℤ) : ℤ) : ℝ)) = r ^ Int.natAbs (n : ℤ) := by
        -- `r = exp(-π)` and `exp (m * x) = (exp x)^m`.
        have := (Real.exp_nat_mul (-Real.pi) (Int.natAbs (n : ℤ)))
        -- Rewrite `m * (-π)` as `-π * m`.
        simpa [r, mul_comm, mul_assoc] using! this
      -- Assemble.
      have : Real.exp (-Real.pi * (coeff (n : ℤ) : ℝ) * z.im) ≤ r ^ Int.natAbs (n : ℤ) :=
        le_of_le_of_eq hexp_le hrpow
      -- Finish.
      -- Rewrite the goal using the explicit norm formula.
      rw [hnorm]
      exact this
    -- Dominated convergence for the tail series.
    simpa using!
      (tendsto_tsum_of_dominated_convergence
        (f := fun (z : ℍ) (n : (Sᶜ : Set ℤ)) =>
          jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) / qFull z)
        (g := fun _ => (0 : ℂ)) (bound := fun n : (Sᶜ : Set ℤ) => r ^ Int.natAbs (n : ℤ))
        (by simpa using! (hsum_r.subtype (Sᶜ : Set ℤ))) hpt hdom)
  -- Assemble.
  have hrew (z : ℍ) :
      (jacobiTheta₂ (z / 2) z - ((2 : ℂ) + (2 : ℂ) * qFull z)) / qFull z =
        ∑' n : (Sᶜ : Set ℤ), jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) / qFull z := by
    have hsum' :
        Summable (fun n : (Sᶜ : Set ℤ) =>
          jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ)) :=
      (hs z).subtype _
    calc
      (jacobiTheta₂ (z / 2) z - ((2 : ℂ) + (2 : ℂ) * qFull z)) / qFull z =
          (∑' n : (Sᶜ : Set ℤ), jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ)) / qFull z := by
            simp [hrem z]
      _ = ∑' n : (Sᶜ : Set ℤ), jacobiTheta₂_term (n : ℤ) ((z : ℂ) / 2) (z : ℂ) / qFull z := by
            simp [div_eq_mul_inv, tsum_mul_right]
  simpa [hrew] using! htail

lemma tendsto_Θ₂_sub_trunc_div_qQuarter_mul_qFull :
    Tendsto
        (fun z : ℍ =>
          (Θ₂ z - ((2 : ℂ) * qQuarter z + (2 : ℂ) * qQuarter z * qFull z)) / (qQuarter z * qFull z))
        atImInfty (𝓝 (0 : ℂ)) := by
  have hJ :
      Tendsto
        (fun z : ℍ => (jacobiTheta₂ (z / 2) z - ((2 : ℂ) + (2 : ℂ) * qFull z)) / qFull z)
        atImInfty (𝓝 (0 : ℂ)) :=
    tendsto_jacobiTheta₂_sub_trunc_div_qFull
  -- Factor `qQuarter` and cancel.
  have hEq :
      (fun z : ℍ =>
          (Θ₂ z - ((2 : ℂ) * qQuarter z + (2 : ℂ) * qQuarter z * qFull z)) /
            (qQuarter z * qFull z)) =
        fun z : ℍ => (jacobiTheta₂ (z / 2) z - ((2 : ℂ) + (2 : ℂ) * qFull z)) / qFull z := by
    funext z
    have hq : qQuarter z ≠ 0 := qQuarter_ne_zero z
    have hnum :
        Θ₂ z - ((2 : ℂ) * qQuarter z + (2 : ℂ) * qQuarter z * qFull z) =
          qQuarter z * (jacobiTheta₂ (z / 2) z - ((2 : ℂ) + (2 : ℂ) * qFull z)) := by
      simp
        [Θ₂_as_qQuarter_mul_jacobiTheta₂ (z := z),
          sub_eq_add_neg,
          add_mul,
          mul_assoc,
          mul_left_comm,
          mul_comm]
    -- Cancel `qQuarter z`.
    grind only
  simpa [hEq] using! hJ

/-- Relation between `qFull` and `qHalf`: `qFull z = qHalf(z)^2`. -/
public lemma qFull_eq_qHalf_sq (z : ℍ) : qFull z = (qHalf z) ^ (2 : ℕ) := by
  have h := Complex.exp_nat_mul (((Real.pi : ℂ) * (z : ℂ)) * Complex.I) 2
  have hmul :
      (2 : ℂ) * (((Real.pi : ℂ) * (z : ℂ)) * Complex.I) = 2 * Real.pi * Complex.I * (z : ℂ) := by
    ac_rfl
  simpa [qFull, qHalf, hmul, mul_assoc, mul_left_comm, mul_comm] using! h

/-- As `Im z → ∞`, the truncation error of `Θ₂` satisfies
`(Θ₂ z - (2*qQuarter z + 2*qQuarter z*qHalf(z)^2)) / (qQuarter z*qHalf(z)^2) → 0`. -/
public lemma tendsto_Θ₂_sub_trunc_div_qQuarter_mul_q :
    Tendsto
        (fun z : ℍ =>
          (Θ₂ z - ((2 : ℂ) * qQuarter z + (2 : ℂ) * qQuarter z * (qHalf z) ^ (2 : ℕ))) /
            (qQuarter z * (qHalf z) ^ (2 : ℕ)))
        atImInfty (𝓝 (0 : ℂ)) := by
  have h0 := tendsto_Θ₂_sub_trunc_div_qQuarter_mul_qFull
  have hEq :
      (fun z : ℍ =>
          (Θ₂ z - ((2 : ℂ) * qQuarter z + (2 : ℂ) * qQuarter z * qFull z)) /
            (qQuarter z * qFull z)) =
        (fun z : ℍ =>
          (Θ₂ z - ((2 : ℂ) * qQuarter z + (2 : ℂ) * qQuarter z * (qHalf z) ^ (2 : ℕ))) /
            (qQuarter z * (qHalf z) ^ (2 : ℕ))) := by
    funext z
    simp [qFull_eq_qHalf_sq (z := z), mul_left_comm, mul_comm]
  simpa [hEq] using! h0

/-- Relation between `qQuarter` and `qHalf`: `(qQuarter z)^4 = qHalf z`. -/
public lemma qQuarter_pow_four (z : ℍ) : (qQuarter z) ^ (4 : ℕ) = qHalf z := by
  -- Work with the exponent `x = I * (π * z) / 4`.
  let x : ℂ := Complex.I * ((Real.pi : ℂ) * (z : ℂ)) / 4
  have hx : qQuarter z = cexp x := by
    simp [qQuarter, x, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hpow : (qQuarter z) ^ (4 : ℕ) = cexp (4 * x) := by
    -- `exp (4*x) = exp x ^ 4`.
    have := (Complex.exp_nat_mul x 4).symm
    simpa [hx] using! this
  have hmul : (4 : ℂ) * x = ((Real.pi : ℂ) * (z : ℂ)) * Complex.I := by
    -- Cancel the factor `4` and reorder.
    simp [x, div_eq_mul_inv, mul_left_comm, mul_comm]
  -- Match `qHalf`.
  simp [qHalf, hpow, hmul]

lemma tendsto_qFull_atImInfty : Tendsto qFull atImInfty (𝓝 (0 : ℂ)) := by
  have : Tendsto (fun z : ℍ => (qHalf z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using! (tendsto_qHalf_atImInfty.pow 2)
  have hEq : qFull = fun z : ℍ => (qHalf z) ^ (2 : ℕ) := by
    funext z
    simp [qFull_eq_qHalf_sq (z := z)]
  simpa [hEq] using! this

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
