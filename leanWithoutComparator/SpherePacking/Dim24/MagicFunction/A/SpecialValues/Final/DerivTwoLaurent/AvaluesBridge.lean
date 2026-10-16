-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Basic
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Defs
public import
  SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.CCancel
public import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegralDefs
import
  SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesEqAvaluesImpl
import
  SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegral
import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegralDCT

/-!
# Bridge to the Laurent expansion at `u = 2`

This file derives the right-neighborhood Laurent expansion at `u = 2` from the analytic
continuation identity `eq:avalues`, and packages it in the form used in the derivative arguments.

## Main statements
* `fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_nhdsGT_two`
* `exists_laurent_aProfile_two_bridge`
-/

open scoped Topology
open Filter

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex

/-
Interfaces for the paper's equation `eq:avalues` (`dim_24.tex`) in the profile variable `u = r^2`.

The core difficulty is analytic continuation from the convergent Laplace range `u > 4` down to a
right-neighborhood of `u = 2`. These are the interface lemmas used in the continuation and
derivative computations.
-/

/-- Convergent-range version of `eq:avalues` (`u > 4`), rewritten for the renormalized profile
`fProfile`. -/
public theorem fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_of_lt {u : ℝ}
    (hu4 : 4 < u) (hu6 : u < 6) :
    fProfile u = -pTildeProfile u - coeffConstTerm u - avaluesRemainderIntegral u := by
  simpa using!
    fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_of_mem_Ioo_four_six
      (u := u) ⟨hu4, hu6⟩

/-- Analytic continuation step: extend the convergent-range identity to a right-neighborhood of
`u = 2`. -/
public theorem fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_nhdsGT_two :
    (fun u : ℝ => fProfile u) =ᶠ[𝓝[>] (2 : ℝ)]
      fun u : ℝ => -pTildeProfile u - coeffConstTerm u - avaluesRemainderIntegral u := by
  simpa using! fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_nhdsGT_two_impl

/-- The paper's `eq:avalues` yields a Laurent expansion for `fProfile` at `u = 2` (on the right). -/
theorem exists_laurent_fProfile_two :
    ∃ h : ℝ → ℂ,
      ContinuousAt h (2 : ℝ) ∧
        (fun u : ℝ => fProfile u) =ᶠ[𝓝[>] (2 : ℝ)]
          fun u : ℝ => B / ((u - 2 : ℝ) : ℂ) + h u := by
  rcases exists_laurent_neg_pTilde_sub_coeffConstTerm_two with ⟨g, hgCont, hgEq⟩
  refine
    ⟨fun u : ℝ => g u - avaluesRemainderIntegral u,
      hgCont.sub continuousAt_avaluesRemainderIntegral_two_dct, ?_⟩
  have hEqAvalues := fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_nhdsGT_two
  have hStep :
      (fun u : ℝ =>
          -pTildeProfile u - coeffConstTerm u - avaluesRemainderIntegral u) =ᶠ[𝓝[>] (2 : ℝ)]
        fun u : ℝ => B / ((u - 2 : ℝ) : ℂ) + (g u - avaluesRemainderIntegral u) := by
    filter_upwards [hgEq] with u hu
    have hu' := congrArg (fun z : ℂ => z - avaluesRemainderIntegral u) hu
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hu'
  exact hEqAvalues.trans hStep

/-- Consequence: the remainder `remTwo` has a right-limit at `u = 2`. -/
theorem exists_tendsto_remTwo_nhdsGT_two :
    ∃ L : ℂ, Tendsto remTwo (𝓝[>] (2 : ℝ)) (𝓝 L) := by
  rcases exists_laurent_fProfile_two with ⟨h, hhCont, hhEq⟩
  refine ⟨h (2 : ℝ), ?_⟩
  have hEv :
      remTwo =ᶠ[𝓝[>] (2 : ℝ)] h := by
    filter_upwards [hhEq] with u hu
    dsimp [remTwo]
    rw [hu]
    simp
  have hlim : Tendsto h (𝓝[>] (2 : ℝ)) (𝓝 (h (2 : ℝ))) :=
    (hhCont.tendsto).mono_left nhdsWithin_le_nhds
  exact hlim.congr' hEv.symm

/--
Restated Laurent expansion for `aProfile`, matching the statement used in the derivative proof.
-/
public theorem exists_laurent_aProfile_two_bridge :
    ∃ h : ℝ → ℂ,
      ContinuousAt h (2 : ℝ) ∧
        (fun u : ℝ => aProfile u) =ᶠ[𝓝[>] (2 : ℝ)]
          fun u : ℝ =>
            (Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u) *
              (B / ((u - 2 : ℝ) : ℂ) + h u) +
              constA2_av := by
  rcases exists_laurent_fProfile_two with ⟨h, hhCont, hhEq⟩
  refine ⟨h, hhCont, ?_⟩
  -- On a small right-neighborhood `(2,3)`, the coefficient is nonzero, so we can clear the
  -- denominator in `fProfile`.
  have hIoo : Set.Ioo (2 : ℝ) 3 ∈ 𝓝[>] (2 : ℝ) :=
    inter_mem_nhdsWithin (Set.Ioi (2 : ℝ)) (Iio_mem_nhds (by norm_num : (2 : ℝ) < 3))
  filter_upwards [hhEq, hIoo] with u hu huIoo
  have hcoeff0 : SpecialValuesDeriv.coeffExp u ≠ 0 := by
    -- Reuse the argument from `ExistsLaurent.lean` (kept non-there).
    have hform := coeffExp_eq_neg_pi_sq_mul_sq_mul_sinc_sq_two (u := u)
    have hu' : 0 < u - 2 := sub_pos.2 huIoo.1
    set x : ℝ := Real.pi * (u - 2) / 2
    have hx0 : x ≠ 0 := by
      positivity
    have hxpos : 0 < x := by
      have hpi : 0 < Real.pi := Real.pi_pos
      have : 0 < Real.pi * (u - 2) := mul_pos hpi hu'
      have : 0 < Real.pi * (u - 2) / 2 := by nlinarith
      simpa [x] using! this
    have hxlt : x < Real.pi := by
      have hu2 : u - 2 < 1 := by linarith [huIoo.2]
      have hpi : 0 < Real.pi := Real.pi_pos
      have : Real.pi * (u - 2) / 2 < Real.pi := by nlinarith [hu2, hpi]
      simpa [x] using! this
    have hsin0 : Real.sin x ≠ 0 := by
      have hsinpos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hxpos hxlt
      exact ne_of_gt hsinpos
    have hsinc0 : Real.sinc x ≠ 0 := by
      have hs : Real.sinc x = Real.sin x / x := Real.sinc_of_ne_zero hx0
      simp [hs, hsin0, hx0]
    have hsub0 : (u - 2) ≠ 0 := sub_ne_zero.2 (ne_of_gt huIoo.1)
    have hsubSq0 : ((u - 2) ^ (2 : ℕ) : ℝ) ≠ 0 := pow_ne_zero 2 hsub0
    have hpi0 : ((Real.pi : ℂ) ^ (2 : ℕ)) ≠ 0 := by
      refine pow_ne_zero 2 ?_
      exact_mod_cast Real.pi_ne_zero
    have : (-((Real.pi : ℂ) ^ (2 : ℕ))) * ((u - 2) ^ (2 : ℕ) : ℂ) *
          (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) ≠ 0 := by
      have h1 : (-((Real.pi : ℂ) ^ (2 : ℕ))) ≠ 0 := by
        exact neg_ne_zero.2 hpi0
      have h2 : ((u - 2) ^ (2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hsubSq0
      have h3 : (((Real.sinc (Real.pi * (u - 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) ≠ 0 := by
        have : Real.sinc (Real.pi * (u - 2) / 2) ≠ 0 := by simpa [x] using! hsinc0
        exact_mod_cast pow_ne_zero 2 this
      exact mul_ne_zero (mul_ne_zero h1 h2) h3
    simpa [hform] using! this
  have hden0 : (Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u ≠ 0 := by
    exact mul_ne_zero (by simp) hcoeff0
  have hmul :
      fProfile u * ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u) =
        (B / ((u - 2 : ℝ) : ℂ) + h u) * ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u) := by
    exact congrArg (fun z : ℂ => z * ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u)) hu
  have hsub :
      aProfile u - constA2_av =
        (B / ((u - 2 : ℝ) : ℂ) + h u) * ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u) := by
    -- Clear the division in `fProfile` (using `mul_div_cancel₀` with the nonzero denominator).
    have hmul' :
        ((aProfile u - constA2_av) / ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u)) *
            ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u) =
          (B / ((u - 2 : ℝ) : ℂ) + h u) * ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u) := by
      simpa [fProfile] using! hmul
    simp_all
  have hadd := congrArg (fun z : ℂ => z + constA2_av) hsub
  -- Final rearrangement, matching the target form.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc,
    mul_left_comm, mul_comm] using! hadd

end SpecialValuesDerivTwoLaurent

end

end SpherePacking.Dim24
