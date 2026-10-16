-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.ContainsDn
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
public import SpherePacking.Dim24.LeechLattice.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayConcrete
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.Basic
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.ShellToLeechLattice

import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Patterns
import SpherePacking.Dim24.LeechLattice.Instances
import SpherePacking.Dim24.LeechLattice.Norm

/-!
# Identifying `latticeL C` with the Leech lattice

This file packages the final output of BS81 Lemma 21: in the 24-dimensional equality case, the
lattice `latticeL C` is linearly isometric to the Leech lattice.

The key input is an isometry between the norm-`4` shells `latticeShell4 C` and the Leech minimal
vectors, and a spanning lemma upgrading shell-level information to the full lattices.

## Main definitions
* `CodeFromLattice`

## Main statements
* `IsometrySteps.latticeL_isometric_leech_steps`
* `latticeL_isometric_leech`
* `latticeShell4_eq_leech_min_vectors`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace Pointwise

open Set
open Uniqueness.BS81.CodingTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
### Extracting a binary code from a lattice (interface)

The actual extraction from a lattice is handled elsewhere; here we only use existence of such a
package, witnessed by the concrete extended binary Golay code.
-/

/-- A package of coding-theoretic data (a length-`24` binary code with Golay parameters) extracted
from a lattice `L`. This is used as an interface in the shell-isometry argument. -/
public structure CodeFromLattice (L : Submodule ℤ ℝ²⁴) : Type where
  code : Code 24
  linear : IsLinearCode code
  minDist_ge : 8 ≤ minDist code
  card_le : Set.ncard code ≤ 2 ^ 12
  isGolay : IsExtendedBinaryGolayCode code

/-- A trivial nonempty instance of `CodeFromLattice L`, using the concrete extended binary Golay
code. This does not relate the lattice `L` to the code; it is only an interface convenience. -/
public theorem exists_codeFromLattice (L : Submodule ℤ ℝ²⁴) : Nonempty (CodeFromLattice L) := by
  refine ⟨{ code := extendedBinaryGolayConcrete
            linear := (isExtendedBinaryGolayCode_extendedBinaryGolayConcrete).linear
            minDist_ge := by
              simp [(isExtendedBinaryGolayCode_extendedBinaryGolayConcrete).minDist_eq]
            card_le := by
              simp [(isExtendedBinaryGolayCode_extendedBinaryGolayConcrete).card_eq]
            isGolay := isExtendedBinaryGolayCode_extendedBinaryGolayConcrete }⟩

namespace IsometrySteps

open scoped RealInnerProductSpace

open Uniqueness.BS81

/-- If a linear isometry sends the shell `latticeShell4 C` to the Leech norm-`4` shell, then it
sends the whole lattice `latticeL C` to `LeechLattice`. -/
public theorem exists_linearIsometry_lattice_to_leech_of_shell4
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴)
    (heShell :
      e '' (latticeShell4 C) = {x : ℝ²⁴ | x ∈ (LeechLattice : Set ℝ²⁴) ∧ ‖x‖ ^ 2 = (4 : ℝ)}) :
    e '' (latticeL C : Set ℝ²⁴) = (LeechLattice : Set ℝ²⁴) := by
  have hLeechShell :
      {x : ℝ²⁴ | x ∈ (LeechLattice : Set ℝ²⁴) ∧ ‖x‖ ^ 2 = (4 : ℝ)} =
        Uniqueness.RigidityClassify.CE.leechKissingVectors := by
    ext x
    constructor
    · rintro ⟨hxL, hxSq⟩
      refine ⟨hxL, (sq_eq_sq₀ (norm_nonneg x) (by norm_num1 : (0 : ℝ) ≤ (2 : ℝ))).1 ?_⟩
      simpa [show (2 : ℝ) ^ 2 = (4 : ℝ) by norm_num1] using! hxSq
    · rintro ⟨hxL, hxNorm⟩
      refine ⟨hxL, by simpa [hxNorm] using! (show (2 : ℝ) ^ 2 = (4 : ℝ) by norm_num1)⟩
  have heShell' :
      e '' (latticeShell4 C) = Uniqueness.RigidityClassify.CE.leechKissingVectors :=
    heShell.trans hLeechShell
  exact latticeL_image_eq_leechLattice_of_shell4_image_eq_leechKissingVectors
    (C := C) hEq e heShell'

/-- In the equality case, `latticeL C` is linearly isometric to `LeechLattice`. -/
public theorem latticeL_isometric_leech_steps
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    ∃ e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴, e '' (latticeL C : Set ℝ²⁴) = (LeechLattice : Set ℝ²⁴) := by
  rcases exists_linearIsometry_shell4_to_leech (C := C) hEq (hDn := hDn) with ⟨e, heShell⟩
  exact ⟨e, exists_linearIsometry_lattice_to_leech_of_shell4 (C := C) hEq e heShell⟩

end IsometrySteps

/-- In the equality case, `latticeL C` is linearly isometric to `LeechLattice`. -/
public theorem latticeL_isometric_leech
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    ∃ e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴, e '' (latticeL C : Set ℝ²⁴) = (LeechLattice : Set ℝ²⁴) :=
  IsometrySteps.latticeL_isometric_leech_steps C h hDn

/-- In the equality case, the shell `latticeShell4 C` is carried by a linear isometry onto the Leech
norm-`4` shell. -/
public theorem latticeShell4_eq_leech_min_vectors
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    ∃ e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴,
      e '' (latticeShell4 C) = {x : ℝ²⁴ | x ∈ (LeechLattice : Set ℝ²⁴) ∧ ‖x‖ ^ 2 = (4 : ℝ)} :=
  IsometrySteps.exists_linearIsometry_shell4_to_leech C h hDn

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
