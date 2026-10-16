-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.Defs

import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.LeechKissingSpan
import SpherePacking.Dim24.Uniqueness.BS81.LatticeLShell4

/-!
# From shell isometries to lattice isometries

This file contains the algebraic closure step in BS81 Lemma 21: if a linear isometry sends the
norm-`4` shell `latticeShell4 C` onto the Leech kissing vectors (`leechKissingVectors`), then it
sends the whole lattice `latticeL C` onto `LeechLattice`.

## Main statements
* `spanZ_latticeShell4_eq_latticeL`
* `latticeL_image_eq_leechLattice_of_shell4_image_eq_leechKissingVectors`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/--
For an equality-case code `C`, the lattice `latticeL C` is the `ℤ`-span of its norm-`4` shell.
-/
public theorem spanZ_latticeShell4_eq_latticeL
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    Submodule.span ℤ (Uniqueness.BS81.latticeShell4 C) =
      Uniqueness.BS81.latticeL C := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · intro v hv
    exact hv.1
  · dsimp [Uniqueness.BS81.latticeL]
    exact Submodule.span_mono (Uniqueness.BS81.twoCodeVectors_subset_latticeShell4_of_code C h.code)

/--
If a linear isometry sends `latticeShell4 C` onto the Leech kissing vectors, then it sends the
whole lattice `latticeL C` onto `LeechLattice`.
-/
public theorem latticeL_image_eq_leechLattice_of_shell4_image_eq_leechKissingVectors
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴)
    (heShell : (e : ℝ²⁴ → ℝ²⁴) '' (Uniqueness.BS81.latticeShell4 C) =
        Uniqueness.RigidityClassify.CE.leechKissingVectors) :
    (e : ℝ²⁴ → ℝ²⁴) '' (Uniqueness.BS81.latticeL C : Set ℝ²⁴) =
      (LeechLattice : Set ℝ²⁴) := by
  -- Work with the ℤ-linear map underlying `e`.
  let f : ℝ²⁴ →ₗ[ℤ] ℝ²⁴ := e.toLinearEquiv.toLinearMap.restrictScalars ℤ
  have heShell' :
      (f : ℝ²⁴ → ℝ²⁴) '' (Uniqueness.BS81.latticeShell4 C) =
        Uniqueness.RigidityClassify.CE.leechKissingVectors := by
    simpa [f] using! heShell
  have hmap :
      Submodule.map f (Uniqueness.BS81.latticeL C) = LeechLattice := by
    calc
      Submodule.map f (Uniqueness.BS81.latticeL C)
          = Submodule.map f (Submodule.span ℤ (Uniqueness.BS81.latticeShell4 C)) := by
              simp [spanZ_latticeShell4_eq_latticeL (C := C) h]
      _ = Submodule.span ℤ ((f : ℝ²⁴ → ℝ²⁴) '' (Uniqueness.BS81.latticeShell4 C)) := by
              exact Submodule.map_span f (Uniqueness.BS81.latticeShell4 C)
      _ = Submodule.span ℤ (Uniqueness.RigidityClassify.CE.leechKissingVectors) := by
              simp [heShell']
      _ = LeechLattice := by
              simpa using! spanZ_leechKissingVectors_eq_leechLattice
  -- Convert the submodule equality `hmap` into a set-image equality.
  ext y
  constructor
  · rintro ⟨x, hxL, rfl⟩
    have : f x ∈ Submodule.map f (Uniqueness.BS81.latticeL C) := ⟨x, hxL, rfl⟩
    simpa [hmap, f] using! this
  · intro hy
    have : y ∈ (Submodule.map f (Uniqueness.BS81.latticeL C) : Set ℝ²⁴) := by
      simpa [hmap] using! hy
    rcases this with ⟨x, hxL, rfl⟩
    exact ⟨x, hxL, by simp [f]⟩

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
