-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Base
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Step

/-!
# BS81 Lemma 20: `Dₙ ⊆ L` for `3 ≤ n ≤ 24`

This file combines:
* the base case `ContainsDn C 3`, and
* the induction step `containsDn_succ_of_containsDn`,
to construct embedded copies of `Dₙ` inside `L := span_ℤ (2 • C)` for all `n = 3,...,24`.

## Main definition
* `containsDn_all`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Construct `ContainsDn C n` for every `n` with `3 ≤ n ≤ 24`. -/
public def containsDn_all
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    ∀ n : ℕ, 3 ≤ n → n ≤ 24 → ContainsDn C n := by
  intro n hn3 hn24
  -- Reindex by `m := n - 3` and build `ContainsDn C (m+3)` by recursion on `m ≤ 21`.
  have hm_le : n - 3 ≤ 21 := by
    -- `n ≤ 24` ⇒ `n - 3 ≤ 21`.
    simpa using! (Nat.sub_le_sub_right hn24 3)
  have aux : ∀ m : ℕ, m ≤ 21 → ContainsDn C (m + 3) := by
    intro m hm21
    induction m with
    | zero =>
        -- Base case: `m=0` gives `D₃`.
        simpa using! containsD3_of_eqCase (C := C) h
    | succ m ih =>
        -- Step: from `D_{m+3}` build `D_{m+4}`.
        have hm20 : m ≤ 20 := Nat.le_of_succ_le_succ (by simpa using! hm21)
        have hDn : ContainsDn C (m + 3) := ih (le_trans hm20 (Nat.le_succ 20))
        have hn3' : 3 ≤ m + 3 := Nat.le_add_left 3 m
        have hn23' : m + 3 ≤ 23 := by
          have : m + 3 ≤ 20 + 3 := Nat.add_le_add_right hm20 3
          simpa using! this
        -- Apply the induction-step constructor.
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using!
          containsDn_succ_of_containsDn (C := C) h (n := m + 3) hn3' hn23' hDn
  -- `3 ≤ n` ⇒ `n - 3 + 3 = n`.
  simpa [Nat.sub_add_cancel hn3] using! aux (n - 3) hm_le

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20
