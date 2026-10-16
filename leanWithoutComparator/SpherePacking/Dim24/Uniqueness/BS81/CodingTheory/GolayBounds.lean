-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import Mathlib.Data.ZMod.Basic

/-!
# Basic lemmas about `ZMod 2`

This file collects small facts about `ZMod 2` that are reused throughout the BS81 coding-theory
layer.
-/
namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayBounds

/-- Every element of `ZMod 2` is either `0` or `1`. -/
public lemma zmod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (Nat.lt_succ_iff.1 (ZMod.val_lt a)) with h | h
  · left; simpa [h] using! (ZMod.natCast_zmod_val a).symm
  · right; simpa [h] using! (ZMod.natCast_zmod_val a).symm

/-- A nonzero element of `ZMod 2` must be `1`. -/
public lemma zmod2_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a = 1 :=
  (zmod2_eq_zero_or_eq_one a).resolve_left ha

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayBounds
