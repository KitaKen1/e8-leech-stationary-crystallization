-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Minimal vectors for an extended orthonormal frame

This file provides auxiliary lemmas for the induction step in BS81 Lemma 20. Given a copy of `Dₙ`
inside `L := span_ℤ (2 • C)`, we append a new orthonormal direction `eNew` and show that all
minimal vectors involving the new index lie in the shell `latticeShell4 C`.

## Main statement
* `minVec_mem_snoc_of_hw_eq`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Transfer the `minVec_mem` condition to the extended frame `Fin.snoc hDn.e eNew`, assuming that
`√2 (e0 + eNew)` is a shell vector and `eNew` is orthogonal to the old frame. -/
public theorem minVec_mem_snoc_of_hw_eq
    (C : Set ℝ²⁴) (n : ℕ) (hDn : ContainsDn C n)
    (i0 i1 : Fin n) (hi01 : i0 ≠ i1)
    (w eNew : ℝ²⁴)
    (hwShell : w ∈ latticeShell4 C)
    (norm_smul_sqrt2_sq : ∀ x : ℝ²⁴, ‖(Real.sqrt 2 : ℝ) • x‖ ^ 2 = (2 : ℝ) * ‖x‖ ^ 2)
    (hw_eq : (Real.sqrt 2 : ℝ) • (hDn.e i0 + eNew) = w)
    (heNew_eNew : (⟪eNew, eNew⟫ : ℝ) = (1 : ℝ))
    (heNew_orth_left : ∀ i : Fin n, (⟪hDn.e i, eNew⟫ : ℝ) = (0 : ℝ)) :
    ∀ (i j : Fin (n + 1)), i ≠ j →
      (Real.sqrt 2 •
          ((Fin.snoc hDn.e eNew : Fin (n + 1) → ℝ²⁴) i +
            (Fin.snoc hDn.e eNew : Fin (n + 1) → ℝ²⁴) j)) ∈ latticeShell4 C ∧
        (Real.sqrt 2 •
            ((Fin.snoc hDn.e eNew : Fin (n + 1) → ℝ²⁴) i -
              (Fin.snoc hDn.e eNew : Fin (n + 1) → ℝ²⁴) j)) ∈ latticeShell4 C := by
  -- The extended frame.
  let e' : Fin (n + 1) → ℝ²⁴ := Fin.snoc hDn.e eNew
  -- The two old minimal vectors involving `i0,i1`.
  let g1 : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 + hDn.e i1)
  let g2 : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 - hDn.e i1)
  have hg1Shell : g1 ∈ latticeShell4 C := by
    simpa [g1] using! (hDn.minVec_mem i0 i1 hi01).1
  have hg2Shell : g2 ∈ latticeShell4 C := by
    simpa [g2] using! (hDn.minVec_mem i0 i1 hi01).2
  have hnorm_eNew_sq : ‖eNew‖ ^ 2 = (1 : ℝ) := by
    calc
      ‖eNew‖ ^ 2 = (⟪eNew, eNew⟫ : ℝ) := by
        simp
      _ = (1 : ℝ) := heNew_eNew
  have hnorm_e_sq (i : Fin n) : ‖hDn.e i‖ ^ 2 = (1 : ℝ) := by
    simp [hDn.ortho.1 i]
  have hnorm_smul_sqrt2_add_sub (i : Fin n) :
      ‖Real.sqrt 2 • (hDn.e i + eNew)‖ ^ 2 = (4 : ℝ) ∧
        ‖Real.sqrt 2 • (hDn.e i - eNew)‖ ^ 2 = (4 : ℝ) := by
    have hi : (⟪hDn.e i, eNew⟫ : ℝ) = 0 := heNew_orth_left i
    have hadd : ‖hDn.e i + eNew‖ ^ 2 = (2 : ℝ) := by
      nlinarith [norm_add_sq_real (hDn.e i) eNew, hi, hnorm_e_sq i, hnorm_eNew_sq]
    have hsub : ‖hDn.e i - eNew‖ ^ 2 = (2 : ℝ) := by
      nlinarith [norm_sub_sq_real (hDn.e i) eNew, hi, hnorm_e_sq i, hnorm_eNew_sq]
    exact ⟨by rw [norm_smul_sqrt2_sq, hadd]; norm_num, by rw [norm_smul_sqrt2_sq, hsub]; norm_num⟩
  -- Minimal vectors involving the new index.
  have hpair_cast_last :
      ∀ i : Fin n,
        (Real.sqrt 2 • (hDn.e i + eNew)) ∈ latticeShell4 C ∧
          (Real.sqrt 2 • (hDn.e i - eNew)) ∈ latticeShell4 C := by
    intro i
    by_cases hi0 : i = i0
    · subst i
      -- `√2(e₀ + eNew) = w`.
      have hplus : (Real.sqrt 2 • (hDn.e i0 + eNew)) ∈ latticeShell4 C := by
        simpa [hw_eq] using! hwShell
      -- `√2(e₀ - eNew) = g₁ + g₂ - w`.
      have hminus_eq : g1 + g2 - w = Real.sqrt 2 • (hDn.e i0 - eNew) := by
        simp [g1, g2, hw_eq.symm, sub_eq_add_neg, smul_add]
        abel
      have hminus : (Real.sqrt 2 • (hDn.e i0 - eNew)) ∈ latticeShell4 C := by
        refine ⟨?_, (hnorm_smul_sqrt2_add_sub i0).2⟩
        have hL :
            (g1 + g2 - w) ∈ (latticeL C : Set ℝ²⁴) :=
          (latticeL C).sub_mem ((latticeL C).add_mem hg1Shell.1 hg2Shell.1) hwShell.1
        simpa [hminus_eq] using! hL
      exact ⟨hplus, hminus⟩
    · -- `i ≠ i0`: use `u± = √2(e₀ ± e_i)` and the equations
      -- `√2(e_i + eNew) = w - u-` and `√2(e_i - eNew) = u+ - w`.
      let uplus : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 + hDn.e i)
      let uminus : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 - hDn.e i)
      have hu := hDn.minVec_mem i0 i (Ne.symm hi0)
      have huplus : uplus ∈ latticeShell4 C := by simpa [uplus] using! hu.1
      have huminus : uminus ∈ latticeShell4 C := by simpa [uminus] using! hu.2
      have hplus_eq : w - uminus = Real.sqrt 2 • (hDn.e i + eNew) := by
        rw [← hw_eq]
        simp [uminus, sub_eq_add_neg, smul_add]
        abel
      have hminus_eq : uplus - w = Real.sqrt 2 • (hDn.e i - eNew) := by
        rw [← hw_eq]
        simp [uplus, sub_eq_add_neg, smul_add]
        abel
      have hplus : (Real.sqrt 2 • (hDn.e i + eNew)) ∈ latticeShell4 C := by
        refine ⟨?_, (hnorm_smul_sqrt2_add_sub i).1⟩
        simpa [hplus_eq] using! (latticeL C).sub_mem hwShell.1 huminus.1
      have hminus : (Real.sqrt 2 • (hDn.e i - eNew)) ∈ latticeShell4 C := by
        refine ⟨?_, (hnorm_smul_sqrt2_add_sub i).2⟩
        simpa [hminus_eq] using! (latticeL C).sub_mem huplus.1 hwShell.1
      exact ⟨hplus, hminus⟩
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last =>
          cases hij rfl
      | cast j0 =>
          have hp := hpair_cast_last j0
          refine ⟨?_, ?_⟩
          · -- plus: commute
            simpa [e', add_comm, Fin.snoc_castSucc, Fin.snoc_last] using! hp.1
          · -- minus: negate the already-known shell vector
            have hneg :
                -(Real.sqrt 2 • (hDn.e j0 - eNew)) ∈ latticeShell4 C :=
              latticeShell4_neg_mem (C := C) (v := Real.sqrt 2 • (hDn.e j0 - eNew)) hp.2
            simpa [e', sub_eq_add_neg, smul_add, smul_sub, Fin.snoc_castSucc, Fin.snoc_last]
              using! hneg
  | cast i0' =>
      cases j using Fin.lastCases with
      | last =>
          simpa [e', Fin.snoc_castSucc, Fin.snoc_last] using! (hpair_cast_last i0')
      | cast j0 =>
          have hij' : i0' ≠ j0 := by
            intro hEq
            exact hij (congrArg Fin.castSucc hEq)
          have hmem := hDn.minVec_mem i0' j0 hij'
          refine ⟨?_, ?_⟩
          · simpa [e', Fin.snoc_castSucc] using! hmem.1
          · simpa [e', Fin.snoc_castSucc] using! hmem.2

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20
