-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeLShell4
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.Bound
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import Mathlib.Data.Set.Card

/-!
# BS81 Lemma 17: the shell `L₄` equals `2 • C`

In the equality case, `L := span_ℤ (2 • C)` is an integral lattice and `L₄` denotes its norm-`4`
shell. BS81 Lemma 17 identifies this shell with the scaled code:
`latticeShell4 C = twoCodeVectors C = {2 • u | u ∈ C}`.

The proof is a subset + cardinality argument: `twoCodeVectors C ⊆ latticeShell4 C`, and both sets
have cardinality `196560`.

## Main statement
* `shell4_eq_twoCodeVectors`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17

noncomputable section

open scoped RealInnerProductSpace Pointwise

open Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- BS81 Lemma 17: in the equality case, the norm-`4` shell is exactly `twoCodeVectors C`. -/
public theorem shell4_eq_twoCodeVectors
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    latticeShell4 C = twoCodeVectors C := by
  have hsubset : twoCodeVectors C ⊆ latticeShell4 C :=
    Uniqueness.BS81.twoCodeVectors_subset_latticeShell4_of_code C h.code
  have hncard_shell : Set.ncard (latticeShell4 C) ≤ 196560 :=
    ncard_latticeShell4_le_196560 (C := C) h
  have hncard_two : Set.ncard (twoCodeVectors C) = 196560 := by
    calc
      Set.ncard (twoCodeVectors C) = Set.ncard C :=
        Uniqueness.BS81.ncard_twoCodeVectors_eq C
      _ = 196560 := h.card_eq
  have hncard_shell_le_two : Set.ncard (latticeShell4 C) ≤ Set.ncard (twoCodeVectors C) := by
    simpa [hncard_two] using! hncard_shell
  have htfin : (latticeShell4 C).Finite := by
    refine Set.Finite.of_finite_image (s := latticeShell4 C) (f := fun x : ℝ²⁴ => (1 / 2 : ℝ) • x)
      (by
        simpa [normalizeShell4] using! (normalizeShell4_isSphericalCode (C := C) h).finite)
      (by
        intro x _ y _ hxy
        have hu : IsUnit (1 / 2 : ℝ) := by
          have hne : (1 / 2 : ℝ) ≠ 0 := by simp
          exact isUnit_iff_ne_zero.2 hne
        exact (IsUnit.smul_left_cancel (a := (1 / 2 : ℝ)) hu).1 hxy)
  have : twoCodeVectors C = latticeShell4 C :=
    Set.eq_of_subset_of_ncard_le hsubset hncard_shell_le_two htfin
  exact this.symm

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17
