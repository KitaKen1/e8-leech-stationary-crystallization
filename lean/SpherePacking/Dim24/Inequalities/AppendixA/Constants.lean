-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.RBounds


/-!
Shared constants and basic functions used throughout the Appendix A truncation arguments.

We keep these definitions public (not `private`) so that other Appendix A files can reuse them
without carrying around hidden `_private` names in theorem statements.
-/


open scoped Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- The error tolerance `10^(-50)` used in `appendix.txt`. -/
@[expose]
public def eps : ℝ := (10 : ℝ) ^ (-50 : ℤ)

/-- The `q`-parameter on the imaginary axis: `q(t) = exp(-2πt)`. -/
@[expose]
public def q (t : ℝ) : ℝ := Real.exp (-2 * Real.pi * t)

/-- Positivity of the `q`-parameter: `0 < q t`. -/
public lemma q_pos (t : ℝ) : 0 < q t := by
  simpa [q] using! Real.exp_pos (-2 * Real.pi * t)

/-- Nonnegativity of the `q`-parameter: `0 ≤ q t`. -/
public lemma q_nonneg (t : ℝ) : 0 ≤ q t := (q_pos t).le

/-- Relation between `q(t) = exp(-2πt)` and `r(t) = exp(-πt)`: `q t = (r t)^2`. -/
public lemma q_eq_r_sq (t : ℝ) : q t = (r t) ^ (2 : ℕ) := by
  dsimp [q, r]
  have h : (-(2 * Real.pi * t)) = (-Real.pi * t) + (-Real.pi * t) := by ring
  simp [h, Real.exp_add, pow_two]

end

end SpherePacking.Dim24.AppendixA
