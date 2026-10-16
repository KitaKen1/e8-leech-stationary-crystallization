-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.LeechLattice.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Defs
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.Auxiliary
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.GaugeFix

/-!
# A shell isometry from Golay parameters

Once the extracted code is identified with the extended binary Golay code, the coordinate patterns
in `Shell4Constraints.lean` match the standard description of the Leech lattice minimal vectors.
This yields a linear isometry sending `latticeShell4 C` onto the Leech norm-`4` shell.

## Main statement
* `exists_linearIsometry_shell4_to_leech`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps

noncomputable section

open scoped RealInnerProductSpace

open Uniqueness.BS81
open Uniqueness.BS81.CodingTheory
open Uniqueness.BS81.Thm15.Lemma21

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

section Shell4Isometry

/-- In the equality case, there is a linear isometry carrying `latticeShell4 C` onto the Leech
norm-`4` shell. -/
public theorem exists_linearIsometry_shell4_to_leech
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    ∃ e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴,
      e '' (latticeShell4 C) = {x : ℝ²⁴ | x ∈ (LeechLattice : Set ℝ²⁴) ∧ ‖x‖ ^ 2 = (4 : ℝ)} := by
  -- Step 1: the extracted code is an extended binary Golay code.
  have hGolay :
      Uniqueness.BS81.CodingTheory.IsExtendedBinaryGolayCode
        (CodeFromLattice.codeFromLattice (C := C) hDn) :=
    isExtendedBinaryGolayCode_codeFromLattice (C := C) hEq hDn
  -- Step 2: choose the code equivalence `σ` together with a sign-gauge of the `D₂₄` frame and a
  -- compatible odd basepoint (BS81 choice-of-basis step).
  rcases
      Shell4IsometryGaugeFix.exists_perm24_equiv_leechParityCode_and_basepoint
        (Cset := C) (hEq := hEq) (hDn := hDn) with
    ⟨σ, s, h⟩
  let hDn' :
      Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24 :=
    Uniqueness.BS81.Thm15.Lemma21.IsometrySteps.Shell4IsometryDnFrameGauge.signFlip hDn s
  rcases (by simpa [hDn'] using! h) with ⟨hσ, base⟩
  -- Step 3: translate the code equivalence into an ambient linear isometry on shell-4 vectors.
  rcases Shell4IsometryAux.exists_linearIsometry_shell4_to_leech_of_code_equiv
      (Cset := C) (hEq := hEq) (hDn := hDn') (σ := σ) (hσ := hσ) (base := base) with ⟨e, he⟩
  refine ⟨e, ?_⟩
  simpa [Shell4IsometryAux.leechShell4] using! he

end Shell4Isometry

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
