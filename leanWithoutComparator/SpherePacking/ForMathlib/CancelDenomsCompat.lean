-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
/-
Added for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Field.Basic

/-!
# `CancelDenoms` helper lemmas

Upstream proofs cite three helper lemmas of the `cancel_denoms` tactic by name. In the pinned
Mathlib these live in `Mathlib.Tactic.CancelDenoms` inside a `meta` section, so ordinary proofs can
no longer refer to them. This file restates them, with the same names and statements, in the
`CancelDenoms` namespace used upstream.
-/

@[expose] public section

namespace CancelDenoms

theorem mul_subst {α} [CommRing α] {n1 n2 k e1 e2 t1 t2 : α}
    (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2) (h3 : n1 * n2 = k) : k * (e1 * e2) = t1 * t2 := by
  rw [← h3, mul_comm n1, mul_assoc n2, ← mul_assoc n1, h1,
      ← mul_assoc n2, mul_comm n2, mul_assoc, h2]

theorem cancel_factors_eq_div {α} [Field α] {n e e' : α}
    (h : n * e = e') (h2 : n ≠ 0) : e = e' / n :=
  eq_div_of_mul_eq h2 <| by rwa [mul_comm] at h

theorem derive_trans {α} [Mul α] {a b c d : α} (h : a = b) (h' : c * b = d) : c * a = d := h ▸ h'

end CancelDenoms
