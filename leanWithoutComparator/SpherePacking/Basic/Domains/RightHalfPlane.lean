-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.Complex.Basic

/-!
# The open right half-plane

This file defines `rightHalfPlane : Set ℂ`, the open right half-plane `{u : ℂ | 0 < u.re}`,
and records basic topological facts.
-/

namespace SpherePacking

/-! ## Definitions -/

/-- The open right half-plane `{u : ℂ | 0 < u.re}`. -/
@[expose] public def rightHalfPlane : Set ℂ := {u : ℂ | 0 < u.re}

/-- The right half-plane is an open subset of `ℂ`. -/
public lemma rightHalfPlane_isOpen : IsOpen rightHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_re

end SpherePacking
