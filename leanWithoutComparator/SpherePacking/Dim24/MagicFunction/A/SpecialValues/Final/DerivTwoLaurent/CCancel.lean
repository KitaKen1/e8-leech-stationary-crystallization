-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Defs
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Ptilde
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.CancelD

/-!
# Cancellation of the double pole at `u = 2`

This file proves the explicit cancellation of the `(u - 2)^{-2}` term coming from `pTildeProfile`
against the second-order zero of `coeffExp` in `eq:avalues`.

Paper reference: `dim_24.tex`, equation `eq:avalues` and the values listed right after it.

After rewriting `a(r)` in terms of `u = r^2`, we have

`aProfile u = -(i : ℂ) * coeffExp u * (pTildeProfile u + analyticRemainder u)`,

so the renormalized profile involves the combination

`-pTildeProfile u - constA2/(i*coeffExp u)`.

The main analytic content here is that this combination has only a simple pole at `u = 2`,
with residue `B`.

## Main definitions
* `coeffConstTerm`

## Main statements
* `exists_laurent_neg_pTilde_sub_coeffConstTerm_two`
-/

namespace SpherePacking.Dim24
noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex

/-- The constant-correction term coming from subtracting `aProfile(2)` before dividing by
`I * coeffExp`. -/
@[expose] public def coeffConstTerm (u : ℝ) : ℂ :=
  constA2_av / ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u)

/-- Laurent expansion of `coeffConstTerm` at `u=2`, isolating the double pole. -/
theorem exists_laurent_coeffConstTerm_two :
    ∃ g : ℝ → ℂ,
      ContinuousAt g (2 : ℝ) ∧
        (fun u : ℝ => coeffConstTerm u) =ᶠ[𝓝[>] (2 : ℝ)]
          fun u : ℝ =>
            (-(725760 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) /
                (((u - 2) ^ (2 : ℕ) : ℝ) : ℂ) +
              g u := by
  -- The correction term is proportional to `1/coeffExp`, and `coeffExp` has a second-order zero
  -- at `u=2`.
  let K : ℂ := (-(725760 : ℂ) / ((π : ℂ) ^ (3 : ℕ)))
  refine ⟨fun u : ℝ => K * sincCorr u, ?_, ?_⟩
  · simpa only [K] using! (continuousAt_const.mul continuousAt_sincCorr_two)
  · -- The identity only needs to hold on a right-neighborhood of `2`, where `u ≠ 2` and hence
    -- `sincCorr u` simplifies to its core quotient.
    refine
      Filter.eventually_of_mem (self_mem_nhdsWithin : Set.Ioi (2 : ℝ) ∈ 𝓝[>] (2 : ℝ)) ?_
    intro u hu
    have hu' : u ≠ (2 : ℝ) := ne_of_gt hu
    -- Rewrite `coeffExp` using the `sinc` normal form and split off the principal part.
    have hcoeff :
        SpecialValuesDeriv.coeffExp u =
          (-((Real.pi : ℂ) ^ (2 : ℕ))) * ((u - 2) ^ (2 : ℕ) : ℂ) * sincSqC u := by
      -- This is definitional once we unfold `sincSqC` and apply
      -- `coeffExp_eq_neg_pi_sq_mul_sq_mul_sinc_sq_two`.
      simpa only [sincSqC, sincSq, sincArg, mul_assoc] using!
        (coeffExp_eq_neg_pi_sq_mul_sq_mul_sinc_sq_two (u := u))
    -- Cancel the `I` in `constA2_av / (I * coeffExp u)` and use `hcoeff`.
    calc
      coeffConstTerm u =
          K * ((sincSqC u)⁻¹ / (((u - 2) ^ (2 : ℕ) : ℝ) : ℂ)) := by
            -- Pure algebra.
            have hII (z : ℂ) : (Complex.I : ℂ) * (Complex.I * z) = -z := by
              calc
                (Complex.I : ℂ) * (Complex.I * z) = ((Complex.I : ℂ) * Complex.I) * z :=
                  (mul_assoc (Complex.I : ℂ) Complex.I z).symm
                _ = (-1 : ℂ) * z := by rw [Complex.I_mul_I]
                _ = -z := (neg_one_mul z)
            -- Reduce to a goal of the form `I*(I*Z) = -W`.
            simp only [coeffConstTerm, constA2_av, mul_comm, div_eq_mul_inv, mul_left_comm, hcoeff,
              mul_neg, neg_mul, mul_assoc, inv_neg, mul_inv_rev, inv_I, neg_neg, ofReal_pow,
              ofReal_sub, ofReal_ofNat, K]
            -- Name the two big expressions and finish.
            set Z : ℂ :=
                ((π : ℂ)⁻¹ *
                  (725760 *
                    (((π : ℂ) ^ (2 : ℕ))⁻¹ *
                      (((((u : ℂ) - 2) ^ (2 : ℕ)))⁻¹ * (sincSqC u)⁻¹)))) with hZ
            set W : ℂ :=
                (725760 *
                  (((((u : ℂ) - 2) ^ (2 : ℕ)))⁻¹ *
                    (((π : ℂ) ^ (3 : ℕ))⁻¹ * (sincSqC u)⁻¹))) with hW
            have hpi :
                (π : ℂ)⁻¹ * ((π : ℂ) ^ (2 : ℕ))⁻¹ =
                  ((π : ℂ) ^ (3 : ℕ))⁻¹ := by
              -- `(π^3)⁻¹ = (π^2 * π)⁻¹ = π⁻¹ * (π^2)⁻¹`.
              ring
            have hZW : Z = W := by
              -- Commute factors and use the `π` inverse regrouping.
              ring
            -- Use `I*(I*Z) = -Z` and transport along `hZW`.
            calc
              (Complex.I : ℂ) * (Complex.I * Z) = -Z := hII Z
              _ = -W := congrArg (fun x : ℂ => -x) hZW
      _ = K / (((u - 2) ^ (2 : ℕ) : ℝ) : ℂ) + K * sincCorr u := by
            -- Expand `sincCorr` and regroup.
            -- On `u ≠ 2`, `sincCorr` agrees with its core quotient.
            have hsinc : sincCorr u = sincCorrCore u := sincCorr_of_ne_two (u := u) hu'
            -- Now this is a short algebraic manipulation.
            simp only [hsinc, sincCorrCore, div_eq_mul_inv, sub_eq_add_neg, mul_add, add_comm,
              mul_left_comm, mul_comm]
            ring_nf

/-- The explicit cancellation leaves only the simple pole `B/(u-2)`. -/
public theorem exists_laurent_neg_pTilde_sub_coeffConstTerm_two :
    ∃ g : ℝ → ℂ,
      ContinuousAt g (2 : ℝ) ∧
        (fun u : ℝ => -pTildeProfile u - coeffConstTerm u) =ᶠ[𝓝[>] (2 : ℝ)]
          fun u : ℝ => B / ((u - 2 : ℝ) : ℂ) + g u := by
  rcases pTildeProfile_eq_principalPart_two with ⟨g₁, hg₁Cont, hg₁Eq⟩
  rcases exists_laurent_coeffConstTerm_two with ⟨g₂, hg₂Cont, hg₂Eq⟩
  refine ⟨fun u : ℝ => -(g₁ u) - g₂ u, (hg₁Cont.neg.sub hg₂Cont), ?_⟩
  -- Combine the two `EventuallyEq` decompositions and cancel the double pole.
  have hEv :
      (fun u : ℝ => -pTildeProfile u - coeffConstTerm u) =ᶠ[𝓝[>] (2 : ℝ)]
        fun u : ℝ =>
          B / ((u - 2 : ℝ) : ℂ) + (-(g₁ u) - g₂ u) := by
    filter_upwards [hg₁Eq, hg₂Eq] with u hu₁ hu₂
    rw [hu₁, hu₂]
    simp only [B, sub_eq_add_neg, ofReal_pow, ofReal_add, ofReal_neg, ofReal_ofNat, add_comm,
      neg_add_rev, add_left_comm, add_assoc, add_right_inj]
    ring
  exact hEv

end SpecialValuesDerivTwoLaurent

end

end SpherePacking.Dim24
