-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.Defs
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.MinShell
import SpherePacking.Dim24.Uniqueness.LatticeInvariants
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.LeechMinShellSpan

/-!
# The Leech norm-`4` shell spans the lattice

This file packages the basic facts needed to upgrade an isometry of minimal shells to an isometry
of full lattices:

* `leechKissingVectors` agrees with the Niemeier `minShell` of `LeechLattice`,
* `Set.ncard leechKissingVectors = 196560`,
* `Submodule.span ℤ leechKissingVectors = LeechLattice`.

## Main statements
* `leechKissingVectors_eq_minShell`
* `ncard_leechKissingVectors`
* `spanZ_leechKissingVectors_eq_leechLattice`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace

open Uniqueness.RigidityClassify

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The set `leechKissingVectors` agrees with the Niemeier `minShell` for `LeechLattice`. -/
public lemma leechKissingVectors_eq_minShell :
    Uniqueness.RigidityClassify.CE.leechKissingVectors =
      (Uniqueness.RigidityClassify.NiemeierRootless.minShell LeechLattice : Set ℝ²⁴) := by
  ext v
  constructor
  · rintro ⟨hvL, hvNorm⟩
    refine ⟨hvL, ?_⟩
    -- `thetaShell` expects `‖v‖^2 = 2 * 2`.
    calc
      ‖v‖ ^ 2 = (4 : ℝ) := by simpa [hvNorm] using! (show (2 : ℝ) ^ 2 = (4 : ℝ) by norm_num)
      _ = (2 : ℝ) * (2 : ℕ) := by norm_num
  · intro hv
    refine ⟨hv.1, ?_⟩
    simpa using!
      (NiemeierRootless.norm_eq_two_of_mem_minShell (L := LeechLattice) hv)

/-- The Leech minimal shell has cardinality `196560`. -/
public lemma ncard_leechKissingVectors :
    Set.ncard Uniqueness.RigidityClassify.CE.leechKissingVectors = 196560 := by
  -- Use `minShell_ncard_eq_196560` for the Leech lattice.
  have hmin :
      Set.ncard (NiemeierRootless.minShell LeechLattice : Set ℝ²⁴) =
        196560 :=
    NiemeierRootless.minShell_ncard_eq_196560_of_even_unimodular_rootless
      (L := LeechLattice) leech_evenNormSq leech_unimodular leech_rootless
  simpa [leechKissingVectors_eq_minShell] using! hmin

/-- The `ℤ`-span of the Leech minimal shell is the full lattice. -/
public lemma spanZ_leechKissingVectors_eq_leechLattice :
    Submodule.span ℤ Uniqueness.RigidityClassify.CE.leechKissingVectors =
      (LeechLattice : Submodule ℤ ℝ²⁴) := by
  -- Reduce to the `minShell` span lemma.
  simpa [leechKissingVectors_eq_minShell] using!
    (Uniqueness.RigidityClassify.NiemeierRootless.spanZ_minShell_eq_leechLattice :
      Submodule.span ℤ
          (Uniqueness.RigidityClassify.NiemeierRootless.minShell LeechLattice : Set ℝ²⁴) =
        (LeechLattice : Submodule ℤ ℝ²⁴))

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
