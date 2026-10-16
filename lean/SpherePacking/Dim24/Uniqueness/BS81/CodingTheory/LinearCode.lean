-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayBounds
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Linear codes as submodules

This file turns a project-local `IsLinearCode` hypothesis (closure under `0` and `+`) into a
Mathlib `Submodule` over `ZMod 2`, so that we can use standard submodule language.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.LinearCode

noncomputable section

/-- The submodule associated to a project-local `IsLinearCode` hypothesis. -/
@[expose] public def submodule {n : ℕ} (C : Code n) (hC : IsLinearCode C) :
    Submodule (ZMod 2) (BinWord n) where
  carrier := C
  zero_mem' := hC.1
  add_mem' := by
    intro x y hx hy
    exact hC.2 x y hx hy
  smul_mem' := by
    intro a x hx
    rcases GolayBounds.zmod2_eq_zero_or_eq_one a with rfl | rfl
    · simpa using! (show (0 : BinWord n) ∈ C from hC.1)
    · simpa using! hx

/-- Membership in `submodule C hC` is definitionally the same as membership in `C`. -/
@[simp] public lemma mem_submodule {n : ℕ} {C : Code n} {hC : IsLinearCode C} {x : BinWord n} :
    x ∈ submodule (n := n) C hC ↔ x ∈ C := Iff.rfl

attribute [grind =] mem_submodule

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.LinearCode
