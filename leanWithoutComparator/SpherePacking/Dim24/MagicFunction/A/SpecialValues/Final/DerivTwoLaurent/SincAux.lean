-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.CoeffExp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Continuity of the `sinc` factors near `u = 2`

This file defines the `sinc` factors appearing in the normal form for `coeffExp` near `u = 2`,
and records the continuity lemmas used in the cancellation of the double pole.

## Main definitions
* `sincArg`
* `sincSq`
* `sincSqC`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex

/-- The `sinc` argument `π (u - 2) / 2` used in the normal form for `coeffExp`. -/
@[expose] public def sincArg (u : ℝ) : ℝ := Real.pi * (u - 2) / 2

/-- The squared `sinc` factor appearing in the normal form for `coeffExp`. -/
@[expose] public def sincSq (u : ℝ) : ℝ := (Real.sinc (sincArg u)) ^ (2 : ℕ)

/-- Continuity of `sincArg` at the expansion point `u = 2`. -/
lemma continuousAt_sincArg_two : ContinuousAt sincArg (2 : ℝ) := by
  simpa [sincArg] using!
    (by
      fun_prop : ContinuousAt (fun u : ℝ => Real.pi * (u - 2) / 2) (2 : ℝ))

/-- Continuity of `sincSq` at `u = 2`. -/
lemma continuousAt_sincSq_two : ContinuousAt sincSq (2 : ℝ) := by
  unfold sincSq
  have hsinc : ContinuousAt (fun u : ℝ => Real.sinc (sincArg u)) (2 : ℝ) := by
    unfold sincArg
    fun_prop
  simpa using! hsinc.pow 2

/-- Continuity of the inverse of `sincSq` at `u = 2`. -/
lemma continuousAt_inv_sincSq_two : ContinuousAt (fun u : ℝ => (sincSq u)⁻¹) (2 : ℝ) := by
  have h0 : sincSq (2 : ℝ) ≠ 0 := by
    simp [sincSq, sincArg]
  exact (continuousAt_sincSq_two.inv₀ h0)

/-- Complex cast of `sincSq`. -/
@[expose] public def sincSqC (u : ℝ) : ℂ := ((sincSq u : ℝ) : ℂ)

/-- Continuity of `sincSqC` at `u = 2`. -/
lemma continuousAt_sincSqC_two : ContinuousAt sincSqC (2 : ℝ) := by
  unfold sincSqC sincSq sincArg
  fun_prop

/-- Continuity of the inverse of `sincSqC` at `u = 2`. -/
lemma continuousAt_inv_sincSqC_two : ContinuousAt (fun u : ℝ => (sincSqC u)⁻¹) (2 : ℝ) := by
  have h0 : sincSqC (2 : ℝ) ≠ 0 := by
    simp [sincSqC, sincSq, sincArg]
  exact (continuousAt_sincSqC_two.inv₀ h0)

end SpecialValuesDerivTwoLaurent

end

end SpherePacking.Dim24
