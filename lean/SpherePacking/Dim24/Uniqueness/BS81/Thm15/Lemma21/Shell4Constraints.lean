-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Patterns
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.InnerProducts

/-!
# Shell-4 constraints for pattern classification

This file packages the coordinate extraction and constraint verification step in BS81 Lemma 21:
given a `D₂₄` frame inside `latticeL C`, every shell-4 vector `u ∈ latticeShell4 C` has integer
coordinates satisfying the parity, norm, and inner-product constraints used to classify patterns.

## Main statement
* `Uniqueness.BS81.Thm15.Lemma21.shell4_patterns`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace Pointwise

open Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

local notation "innerSet" =>
  ({0, (1 : ℝ), (-1 : ℝ), (2 : ℝ), (-2 : ℝ), (4 : ℝ), (-4 : ℝ)} : Set ℝ)

lemma innerConstraint_of_shell4
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    {u : ℝ²⁴} (hu : u ∈ latticeShell4 C)
    (z : Fin 24 → ℤ) (hz : ∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ)) :
    innerConstraint z := by
  intro i j hij
  have hvPlusShell : (Real.sqrt 2 • (hDn.e i + hDn.e j)) ∈ latticeShell4 C :=
    (hDn.minVec_mem i j hij).1
  have hvMinusShell : (Real.sqrt 2 • (hDn.e i - hDn.e j)) ∈ latticeShell4 C :=
    (hDn.minVec_mem i j hij).2
  have hinnerPlus : (⟪Real.sqrt 2 • (hDn.e i + hDn.e j), u⟫ : ℝ) ∈ innerSet :=
    Lemma17.inner_mem_set_of_shell4 C hEq hvPlusShell hu
  have hinnerMinus : (⟪Real.sqrt 2 • (hDn.e i - hDn.e j), u⟫ : ℝ) ∈ innerSet :=
    Lemma17.inner_mem_set_of_shell4 C hEq hvMinusShell hu
  set Iplus : ℝ := (⟪Real.sqrt 2 • (hDn.e i + hDn.e j), u⟫ : ℝ) with hIplus
  set Iminus : ℝ := (⟪Real.sqrt 2 • (hDn.e i - hDn.e j), u⟫ : ℝ) with hIminus
  have hinnerPlus' : Iplus ∈ innerSet := by simpa [hIplus] using! hinnerPlus
  have hinnerMinus' : Iminus ∈ innerSet := by simpa [hIminus] using! hinnerMinus
  have hsum : Iplus + Iminus = scaledCoord hDn.e i u := by
    simpa [hIplus, hIminus, scaledCoord, coord] using!
      inner_sqrt2_add_sub_eq_sqrt8 (e := hDn.e) (i := i) (j := j) (x := u)
  have hji : hDn.e j - hDn.e i = -(hDn.e i - hDn.e j) := by
    simp [sub_eq_add_neg]
  have hdiff : Iplus - Iminus = scaledCoord hDn.e j u := by
    have h :=
      inner_sqrt2_add_sub_eq_sqrt8 (e := hDn.e) (i := j) (j := i) (x := u)
    have hplus : (⟪Real.sqrt 2 • (hDn.e j + hDn.e i), u⟫ : ℝ) = Iplus := by
      simp [hIplus, add_comm]
    have hminus : (⟪Real.sqrt 2 • (hDn.e j - hDn.e i), u⟫ : ℝ) = -Iminus := by
      have hrewrite :
          (⟪Real.sqrt 2 • (hDn.e j - hDn.e i), u⟫ : ℝ) =
            (⟪Real.sqrt 2 • (-(hDn.e i - hDn.e j)), u⟫ : ℝ) :=
        congrArg (fun v => (⟪Real.sqrt 2 • v, u⟫ : ℝ)) hji
      have hsmul :
          (Real.sqrt 2 : ℝ) • (-(hDn.e i - hDn.e j)) =
            -((Real.sqrt 2 : ℝ) • (hDn.e i - hDn.e j)) := by
        simpa using! (smul_neg (Real.sqrt 2 : ℝ) (hDn.e i - hDn.e j))
      have hneg :
          (⟪Real.sqrt 2 • (-(hDn.e i - hDn.e j)), u⟫ : ℝ) =
            -(⟪Real.sqrt 2 • (hDn.e i - hDn.e j), u⟫ : ℝ) := by
        calc
          (⟪Real.sqrt 2 • (-(hDn.e i - hDn.e j)), u⟫ : ℝ) =
              (⟪-((Real.sqrt 2 : ℝ) • (hDn.e i - hDn.e j)), u⟫ : ℝ) :=
                congrArg (fun v => (⟪v, u⟫ : ℝ)) hsmul
          _ = -(⟪Real.sqrt 2 • (hDn.e i - hDn.e j), u⟫ : ℝ) := by simp
      calc
        (⟪Real.sqrt 2 • (hDn.e j - hDn.e i), u⟫ : ℝ) =
            (⟪Real.sqrt 2 • (-(hDn.e i - hDn.e j)), u⟫ : ℝ) := hrewrite
        _ = -(⟪Real.sqrt 2 • (hDn.e i - hDn.e j), u⟫ : ℝ) := hneg
        _ = -Iminus := by simp [hIminus]
    -- Rewrite the swapped add/sub identity as a difference for `Iplus`/`Iminus`.
    have h' := h
    rw [hplus, hminus] at h'
    assumption
  grind only

/--
Every vector in `latticeShell4 C` has integer coordinates (in the `D₂₄` frame) satisfying the
constraints needed for `pattern_classification_of_constraints`, hence one of the three patterns.
-/
public theorem shell4_patterns
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    {u : ℝ²⁴} (hu : u ∈ latticeShell4 C) :
    ∃ z : Fin 24 → ℤ,
      (∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ)) ∧
        (∀ i j : Fin 24, Even (z i + z j)) ∧
          (∑ i : Fin 24, (z i : ℝ) ^ 2) = (32 : ℝ) ∧
            (isPattern1 z ∨ isPattern2 z ∨ isPattern3 z) := by
  -- Extract integer coordinates and parity.
  rcases exists_integer_coords_of_shell4 (C := C) hEq (e := hDn.e) (he := hDn.ortho)
      (hmin := hDn.minVec_mem) (u := u) hu with ⟨z, hz, hpar⟩
  have hsumsq : (∑ i : Fin 24, (z i : ℝ) ^ 2) = (32 : ℝ) :=
    sum_sq_integer_coords_eq_32 (e := hDn.e) (he := hDn.ortho) (u := u) (z := z) hu.2 hz
  have hinner : innerConstraint z :=
    innerConstraint_of_shell4 (C := C) (hEq := hEq) (hDn := hDn) (u := u) hu z hz
  have hpat : isPattern1 z ∨ isPattern2 z ∨ isPattern3 z :=
    pattern_classification_of_constraints (z := z) hpar hsumsq hinner
  refine ⟨z, hz, hpar, hsumsq, hpat⟩

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
