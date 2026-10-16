-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.ForMathlib.AtImInfty
public import SpherePacking.ModularForms.JacobiTheta
import Mathlib.Analysis.Normed.Group.Tannery


/-!
# The parameter `qHalf` and a truncation bound for `Θ₄`

We define the half-parameter `qHalf z = exp(π i z)` at the cusp `i∞` and record basic analytic
facts (nonvanishing, decay, and summability tools). We also prove the truncation estimate
`(Θ₄ z - (1 - 2*qHalf z)) / qHalf(z)^2 → 0`.

## Main definitions
* `qHalf`

## Main statements
* `tendsto_qHalf_atImInfty`
* `tendsto_Θ₄_sub_trunc_div_qHalf_sq`
-/

open scoped Real
open scoped Topology
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter UpperHalfPlane

namespace Deriv

/-- The half-parameter `qHalf z = exp(π i z)`. -/
@[expose] public def qHalf (z : ℍ) : ℂ :=
  Complex.exp (((Real.pi : ℂ) * (z : ℂ)) * Complex.I)

/-- `qHalf z` is nonzero for all `z` in the upper half-plane. -/
public lemma qHalf_ne_zero (z : ℍ) : qHalf z ≠ 0 := by
  simp [qHalf]

lemma norm_qHalf (z : ℍ) : ‖qHalf z‖ = Real.exp (-Real.pi * z.im) := by
  -- `‖exp(w * i)‖ = exp(-Im w)` with `w = π * z`.
  have him : (((Real.pi : ℂ) * (z : ℂ)).im) = Real.pi * z.im := by
    simp
  calc
    ‖qHalf z‖ = ‖Complex.exp (((Real.pi : ℂ) * (z : ℂ)) * Complex.I)‖ := by rfl
    _ = Real.exp (-(((Real.pi : ℂ) * (z : ℂ)).im)) := by
          simpa using! (Complex.norm_exp_mul_I ((Real.pi : ℂ) * (z : ℂ)))
    _ = Real.exp (-Real.pi * z.im) := by
          simp [him]

/-- As `Im z → ∞`, the parameter `qHalf z` tends to `0`. -/
public lemma tendsto_qHalf_atImInfty : Tendsto qHalf atImInfty (𝓝 (0 : ℂ)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hexp : Tendsto (fun z : ℍ => Real.exp (-Real.pi * z.im)) atImInfty (𝓝 (0 : ℝ)) := by
    have him : Tendsto (fun z : ℍ => z.im) atImInfty atTop :=
      tendsto_im_atImInfty
    have hbot : Tendsto (fun z : ℍ => (-Real.pi) * z.im) atImInfty atBot :=
      him.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos])
    exact Real.tendsto_exp_comp_nhds_zero.mpr hbot
  simpa [norm_qHalf] using! hexp

/-- Summability of the symmetric geometric series `∑_{n ∈ ℤ} r^{natAbs n}` for `0 ≤ r < 1`. -/
public lemma summable_pow_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => r ^ Int.natAbs n) := by
  -- Split the sum over `ℤ` into nonnegative and negative parts.
  refine (summable_int_iff_summable_nat_and_neg).2 ?_
  constructor
  · -- nonnegative integers: `natAbs (n : ℤ) = n`
    simpa using! (summable_geometric_of_lt_one hr0 hr1)
  · -- negative integers: `natAbs (-n) = natAbs n`
    simpa using! (summable_geometric_of_lt_one hr0 hr1)

lemma summable_Θ₄_term (z : ℍ) : Summable fun n : ℤ => Θ₄_term n z := by
  -- Reduce to the standard summability lemma for `jacobiTheta₂_term`.
  have hs :
      Summable (fun n : ℤ => jacobiTheta₂_term n (1 / 2 : ℂ) (z : ℂ)) :=
    (summable_jacobiTheta₂_term_iff (z := (1 / 2 : ℂ)) (τ := (z : ℂ))).2 (by simpa using! z.im_pos)
  have hEq :
      (fun n : ℤ => Θ₄_term n z) = fun n : ℤ => jacobiTheta₂_term n (1 / 2 : ℂ) (z : ℂ) := by
    funext n
    simpa using! (Θ₄_term_as_jacobiTheta₂_term (τ := z) n)
  simpa [hEq] using! hs

/-- As `Im z → ∞`, the truncation error of `Θ₄` satisfies
`(Θ₄ z - (1 - 2*qHalf z)) / qHalf(z)^2 → 0`. -/
public lemma tendsto_Θ₄_sub_trunc_div_qHalf_sq :
    Tendsto (fun z : ℍ => (Θ₄ z - ((1 : ℂ) - (2 : ℂ) * qHalf z)) / (qHalf z) ^ (2 : ℕ))
      atImInfty (𝓝 (0 : ℂ)) := by
  -- Split off the three terms `n = 0, ±1`.
  let S : Finset ℤ := {0, 1, -1}
  have hsplit (z : ℍ) :
      Θ₄ z =
        (∑ n ∈ S, Θ₄_term n z) + ∑' n : (Sᶜ : Set ℤ), Θ₄_term (n : ℤ) z := by
    simpa [Θ₄] using! ((summable_Θ₄_term z).sum_add_tsum_compl (s := S)).symm
  have hfin (z : ℍ) : (∑ n ∈ S, Θ₄_term n z) = (1 : ℂ) - (2 : ℂ) * qHalf z := by
    -- Evaluate the three terms explicitly.
    simp [S, Θ₄_term, qHalf, mul_assoc, mul_comm]
    ring_nf
  have hrem (z : ℍ) :
      Θ₄ z - ((1 : ℂ) - (2 : ℂ) * qHalf z) = ∑' n : (Sᶜ : Set ℤ), Θ₄_term (n : ℤ) z := by
    -- Use the decomposition and simplify.
    simp [hsplit z, hfin z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- The remainder is `o(q^2)` because every tail term has exponent `n^2 ≥ 4`.
  have htail :
      Tendsto
        (fun z : ℍ => ∑' n : (Sᶜ : Set ℤ), Θ₄_term (n : ℤ) z / (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (0 : ℂ)) := by
    -- New proof: dominated convergence with the geometric majorant `r ^ natAbs`.
    let r : ℝ := Real.exp (-Real.pi)
    have hr0 : 0 ≤ r := by positivity [r]
    have hr1 : r < 1 := by
      have : (-Real.pi) < 0 := by nlinarith [Real.pi_pos]
      simpa [r] using! (Real.exp_lt_one_iff.2 this)
    have hsum_r : Summable (fun n : (Sᶜ : Set ℤ) => r ^ Int.natAbs (n : ℤ)) :=
      (summable_pow_natAbs hr0 hr1).subtype _
    have hnAbs : ∀ n : (Sᶜ : Set ℤ), (2 : ℕ) ≤ Int.natAbs (n : ℤ) := by
      grind only [= Set.mem_compl_iff, = Finset.mem_coe, = Finset.mem_insert,
        = Finset.mem_singleton]
    -- A convenient closed form for the norm of each tail term after dividing by `qHalf^2`.
    have hnormTerm (n : ℤ) (z : ℍ) :
        ‖Θ₄_term n z / (qHalf z) ^ (2 : ℕ)‖ =
          Real.exp (-(Real.pi * ((n : ℝ) ^ 2 - 2) * z.im)) := by
      -- Compute numerator and denominator norms separately.
      have hq : ‖(qHalf z) ^ (2 : ℕ)‖ = Real.exp (-2 * Real.pi * z.im) := by
        calc
          ‖(qHalf z) ^ (2 : ℕ)‖ = ‖qHalf z‖ ^ (2 : ℕ) := by simp [norm_pow]
          _ = (Real.exp (-Real.pi * z.im)) ^ (2 : ℕ) := by simp [norm_qHalf]
          _ = Real.exp (-Real.pi * z.im) * Real.exp (-Real.pi * z.im) := by simp [pow_two]
          _ = Real.exp ((-Real.pi * z.im) + (-Real.pi * z.im)) := by
                simpa using! (Real.exp_add (-Real.pi * z.im) (-Real.pi * z.im)).symm
          _ = Real.exp (-2 * Real.pi * z.im) := by ring_nf
      have hΘ : ‖Θ₄_term n z‖ = Real.exp (-(Real.pi * ((n : ℝ) ^ 2) * z.im)) := by
        -- `‖(-1)^n‖ = 1` and `‖exp(π i n^2 z)‖ = exp(-π n^2 Im z)`.
        simp [Θ₄_term, Complex.norm_exp, mul_assoc, mul_left_comm, mul_comm, pow_two]
      -- Combine and simplify the exponent.
      have : ‖Θ₄_term n z / (qHalf z) ^ (2 : ℕ)‖ =
          Real.exp (-(Real.pi * ((n : ℝ) ^ 2) * z.im) + 2 * Real.pi * z.im) := by
        -- `exp(x) / exp(y) = exp(x - y)` and then unfold subtraction.
        simp [hΘ, hq, (Real.exp_sub _ _).symm, sub_eq_add_neg]
      have hexp :
          (-(Real.pi * ((n : ℝ) ^ 2) * z.im) + 2 * Real.pi * z.im) =
            -(Real.pi * ((n : ℝ) ^ 2 - 2) * z.im) := by
        ring_nf
      simpa [hexp] using! this
    -- Pointwise convergence: each tail term tends to `0`.
    have hpt :
        ∀ n : (Sᶜ : Set ℤ),
          Tendsto (fun z : ℍ => Θ₄_term (n : ℤ) z / (qHalf z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
      intro n
      have hn2 : (2 : ℕ) ≤ Int.natAbs (n : ℤ) := hnAbs n
      have hpos : 0 < ((Int.natAbs (n : ℤ) : ℝ) ^ 2 - 2) := by
        have : (2 : ℝ) ≤ (Int.natAbs (n : ℤ) : ℝ) := by exact_mod_cast hn2
        nlinarith
      apply tendsto_zero_iff_norm_tendsto_zero.2
      have hbot :
          Tendsto
            (fun z : ℍ =>
              (-Real.pi * ((Int.natAbs (n : ℤ) : ℝ) ^ 2 - 2)) * z.im)
            atImInfty atBot :=
        (tendsto_im_atImInfty.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos, hpos]))
      have hexp :
          Tendsto
            (Real.exp ∘ fun z : ℍ =>
              (-Real.pi * (((n : ℤ) : ℝ) ^ 2 - 2)) * z.im)
            atImInfty (𝓝 (0 : ℝ)) :=
        Real.tendsto_exp_atBot.comp (by
          -- same `atBot` statement, rewritten using `((n : ℤ) : ℝ)^2 = (natAbs n : ℝ)^2`
          have habs : (Int.natAbs (n : ℤ) : ℝ) = |((n : ℤ) : ℝ)| := by
            simp
          have hsq : (((n : ℤ) : ℝ) ^ 2 - 2) = ((Int.natAbs (n : ℤ) : ℝ) ^ 2 - 2) := by
            norm_num
          -- rewrite the previously established `hbot`
          simpa [hsq, Function.comp, mul_assoc, mul_left_comm, mul_comm] using! hbot)
      have hnorm :
          (fun z : ℍ => ‖Θ₄_term (n : ℤ) z‖ / ‖qHalf z‖ ^ (2 : ℕ)) =
            fun z : ℍ => Real.exp (-(Real.pi * (((n : ℤ) : ℝ) ^ 2 - 2) * z.im)) := by
        funext z
        -- Rewrite `‖a / b‖` as `‖a‖ / ‖b‖` and use `hnormTerm`.
        simpa [norm_div, norm_pow] using! (hnormTerm (n := (n : ℤ)) z)
      -- Use `hnorm` to transfer the known exponential limit to the quotient-of-norms expression.
      have hexp0 :
          Tendsto (fun z : ℍ => Real.exp ((-Real.pi * (((n : ℤ) : ℝ) ^ 2 - 2)) * z.im))
            atImInfty (𝓝 (0 : ℝ)) := by
        -- Avoid `simp` rewriting `Tendsto (exp ∘ ...) _ (𝓝 0)` into an `atTop` statement.
        assumption
      have hexp' :
          Tendsto (fun z : ℍ => Real.exp (-(Real.pi * (((n : ℤ) : ℝ) ^ 2 - 2) * z.im)))
            atImInfty (𝓝 (0 : ℝ)) :=
        (hexp0.congr (by
          norm_num))
      exact (tendsto_congr (hnormTerm ↑n)).mpr hexp'
    -- Eventual domination: once `Im z ≥ 1`, the norms are bounded by `r ^ natAbs`.
    have hdom :
        ∀ᶠ z : ℍ in atImInfty,
          ∀ n : (Sᶜ : Set ℤ),
            ‖Θ₄_term (n : ℤ) z / (qHalf z) ^ (2 : ℕ)‖ ≤ r ^ Int.natAbs (n : ℤ) := by
      have hIm : ∀ᶠ z : ℍ in atImInfty, (1 : ℝ) ≤ z.im := by
        exact (Filter.eventually_atImInfty).2 ⟨(1 : ℝ), fun _ hz => hz⟩
      filter_upwards [hIm] with z hz n
      have hn2 : (2 : ℕ) ≤ Int.natAbs (n : ℤ) := hnAbs n
      have hm : (Int.natAbs (n : ℤ) : ℝ) ≤ (Int.natAbs (n : ℤ) : ℝ) ^ 2 - 2 := by
        have : (2 : ℝ) ≤ (Int.natAbs (n : ℤ) : ℝ) := by exact_mod_cast hn2
        nlinarith
      -- Work with the explicit exponential decay coming from `hnormTerm` (involving `n^2 - 2`).
      have h0 :
          ‖Θ₄_term (n : ℤ) z / (qHalf z) ^ (2 : ℕ)‖ =
            Real.exp (-(Real.pi * (((n : ℤ) : ℝ) ^ 2 - 2) * z.im)) := by
        simpa using! (hnormTerm (n := (n : ℤ)) z)
      -- Convert `hm` into an inequality involving `((n : ℝ)^2 - 2)`.
      have habs : (Int.natAbs (n : ℤ) : ℝ) = |((n : ℤ) : ℝ)| := by
        simp
      have hsq : (Int.natAbs (n : ℤ) : ℝ) ^ 2 = (((n : ℤ) : ℝ) ^ 2) := by
        norm_num
      have hm' : (Int.natAbs (n : ℤ) : ℝ) ≤ (((n : ℤ) : ℝ) ^ 2 - 2) := by
        -- `natAbs ≤ natAbs^2 - 2 = n^2 - 2` on the tail.
        simpa [hsq] using! hm
      -- Step 1: bound the exponential term by replacing `n^2 - 2` with `natAbs n`.
      have hle :
          Real.exp (-(Real.pi * (((n : ℤ) : ℝ) ^ 2 - 2) * z.im)) ≤
            Real.exp (-(Real.pi * (Int.natAbs (n : ℤ) : ℝ) * z.im)) := by
        have hzpos : 0 < z.im := lt_of_lt_of_le (by norm_num) hz
        have hneg : (-Real.pi * z.im) < 0 := by nlinarith [Real.pi_pos, hzpos]
        have hmul :
            (-Real.pi * z.im) * (((n : ℤ) : ℝ) ^ 2 - 2) ≤
              (-Real.pi * z.im) * (Int.natAbs (n : ℤ) : ℝ) :=
          mul_le_mul_of_nonpos_left hm' hneg.le
        -- Rewrite to the form expected by `Real.exp_le_exp`.
        simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using! (Real.exp_le_exp.2 hmul)
      -- Step 2: `exp(-π * natAbs n * Im z) = exp(-π * Im z)^(natAbs n) ≤ r^(natAbs n)`.
      have hqle : Real.exp (-Real.pi * z.im) ≤ r := by
        have hnegPi : (-Real.pi) < 0 := by nlinarith [Real.pi_pos]
        have : (-Real.pi) * z.im ≤ (-Real.pi) * (1 : ℝ) := by
          exact mul_le_mul_of_nonpos_left hz hnegPi.le
        simpa [r, mul_assoc] using! (Real.exp_le_exp.2 this)
      have hpow :
          Real.exp (-(Real.pi * (Int.natAbs (n : ℤ) : ℝ) * z.im)) ≤ r ^ Int.natAbs (n : ℤ) := by
        -- Rewrite as a power using `Real.exp_nat_mul`, then compare bases.
        have h1 :
            Real.exp (-(Real.pi * (Int.natAbs (n : ℤ) : ℝ) * z.im)) =
              Real.exp (-Real.pi * z.im) ^ Int.natAbs (n : ℤ) := by
          -- `-(π * m * t) = m * (-(π * t))`.
          simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using!
            (Real.exp_nat_mul (-Real.pi * z.im) (Int.natAbs (n : ℤ)))
        have h2 :
            Real.exp (-Real.pi * z.im) ^ Int.natAbs (n : ℤ) ≤ r ^ Int.natAbs (n : ℤ) :=
          pow_le_pow_left₀ (by positivity) hqle _
        exact le_of_eq_of_le h1 h2
      -- Assemble.
      calc
        ‖Θ₄_term (n : ℤ) z / (qHalf z) ^ (2 : ℕ)‖
            = Real.exp (-(Real.pi * (((n : ℤ) : ℝ) ^ 2 - 2) * z.im)) := h0
        _ ≤ Real.exp (-(Real.pi * (Int.natAbs (n : ℤ) : ℝ) * z.im)) := hle
        _ ≤ r ^ Int.natAbs (n : ℤ) := hpow
    -- Conclude by dominated convergence.
    simpa using!
      (tendsto_tsum_of_dominated_convergence
        (f := fun z (n : (Sᶜ : Set ℤ)) => Θ₄_term (n : ℤ) z / (qHalf z) ^ (2 : ℕ))
        (g := fun _ : (Sᶜ : Set ℤ) => (0 : ℂ))
        (bound := fun n : (Sᶜ : Set ℤ) => r ^ Int.natAbs (n : ℤ))
        hsum_r hpt hdom)
  -- Rewrite the goal using the tail.
  have hq : ∀ z : ℍ, (qHalf z) ^ (2 : ℕ) ≠ 0 := by
    intro z
    exact pow_ne_zero 2 (qHalf_ne_zero z)
  -- Put everything together.
  have hrew (z : ℍ) :
      (Θ₄ z - ((1 : ℂ) - (2 : ℂ) * qHalf z)) / (qHalf z) ^ (2 : ℕ) =
        ∑' n : (Sᶜ : Set ℤ), Θ₄_term (n : ℤ) z / (qHalf z) ^ (2 : ℕ) := by
    -- Replace the numerator by the tail sum and move division inside the series.
    have hsum' : Summable (fun n : (Sᶜ : Set ℤ) => Θ₄_term (n : ℤ) z) :=
      (summable_Θ₄_term z).subtype _
    calc
      (Θ₄ z - ((1 : ℂ) - (2 : ℂ) * qHalf z)) / (qHalf z) ^ (2 : ℕ) =
          (∑' n : (Sᶜ : Set ℤ), Θ₄_term (n : ℤ) z) / (qHalf z) ^ (2 : ℕ) := by
            simp [hrem z]
      _ = ∑' n : (Sᶜ : Set ℤ), Θ₄_term (n : ℤ) z / (qHalf z) ^ (2 : ℕ) := by
            -- Distribute division over the series.
            simp [div_eq_mul_inv, tsum_mul_right]
  -- Conclude.
  simpa [hrew] using! htail

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
