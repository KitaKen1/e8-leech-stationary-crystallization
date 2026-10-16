-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Orthogonality
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Dot/support bridge without Golay imports

The existing file `CodingTheory/DotSupport.lean` imports the global `Golay` aggregator, which pulls
in the full Golay-uniqueness pipeline. In the classical Witt-design route we need the
dot/support bridge *without* creating import cycles.

This file provides exactly the same bridge lemma as `DotSupport.lean`, but only depends on
`GolayDefs` + `Orthogonality` and basic `ZMod 2` facts.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open scoped BigOperators

namespace DotSupportLite

lemma mul_eq_ite_one_zero (a b : ZMod 2) :
    a * b = (if a = 1 ∧ b = 1 then (1 : ZMod 2) else 0) := by
  rcases GolayBounds.zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
    rcases GolayBounds.zmod2_eq_zero_or_eq_one b with rfl | rfl <;> simp

attribute [grind =] mul_eq_ite_one_zero

lemma support_inter_eq_filter {n : ℕ} (w₁ w₂ : BinWord n) :
    support w₁ ∩ support w₂ =
      Finset.univ.filter (fun i : Fin n => w₁ i = 1 ∧ w₂ i = 1) := by
  ext i
  simp [support, Finset.mem_inter]

attribute [grind =] support_inter_eq_filter

/-- The dot product equals the parity of the size of the intersection of supports. -/
public theorem dot_eq_card_support_inter {n : ℕ} (w₁ w₂ : BinWord n) :
    dot w₁ w₂ = ((support w₁ ∩ support w₂).card : ZMod 2) := by
  -- Expand `dot`, rewrite products into indicator functions, and turn the sum into a card.
  simp [dot, mul_eq_ite_one_zero, support_inter_eq_filter]

/-- The dot product vanishes iff the intersection of supports has even cardinality. -/
public theorem dot_eq_zero_iff_even_card_support_inter {n : ℕ} (w₁ w₂ : BinWord n) :
    dot w₁ w₂ = 0 ↔ Even (support w₁ ∩ support w₂).card := by
  simpa [dot_eq_card_support_inter (w₁ := w₁) (w₂ := w₂)] using!
    (ZMod.natCast_eq_zero_iff_even (n := (support w₁ ∩ support w₂).card))

end DotSupportLite

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
