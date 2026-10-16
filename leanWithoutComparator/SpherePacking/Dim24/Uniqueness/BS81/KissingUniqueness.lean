-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.Defs
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Uniqueness
import SpherePacking.Dim24.Uniqueness.BS81.FromKissing
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.DistanceDistribution.FromSharpness

/-!
# Kissing uniqueness in dimension 24 (BS81)

This file assembles BS81's spherical-code uniqueness theorem (Theorem 22) into the repo's
statement `kissing_configuration_unique_24` about radius-2 kissing configurations in `ℝ²⁴`.

## Main statements
* `kissing_configuration_unique_24_bs81`

## References
* BS81, §4
-/

namespace SpherePacking.Dim24.Uniqueness.BS81

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- BS81 Theorem 22, reformulated: uniqueness of the 196560-point kissing configuration in `ℝ²⁴`. -/
public theorem kissing_configuration_unique_24_bs81
    (X : Set ℝ²⁴) :
    Uniqueness.RigidityClassify.CE.IsKissingConfiguration X →
      Set.ncard X = 196560 →
        ∃ e : ℝ²⁴ ≃ᵢ ℝ²⁴, e '' X = Uniqueness.RigidityClassify.CE.leechKissingVectors := by
  intro hX hcardX
  -- Normalize to a unit-sphere code.
  let C : Set ℝ²⁴ := Uniqueness.RigidityClassify.CE.normalizeKissing X
  have hCode : IsSphericalCode 24 C (1 / 2 : ℝ) :=
    normalizeKissing_isSphericalCode24 (X := X) hX
  have hcardC : Set.ncard C = 196560 := by
    simpa [C] using! (ncard_normalizeKissing_eq (X := X)).trans hcardX
  -- Equality case package (Theorem 14) and uniqueness (Theorem 15).
  have hPkg : Uniqueness.BS81.Thm14.EqCase24Pkg C :=
    Uniqueness.BS81.Thm14.thm14_eqCase24Pkg_of_optimal (C := C) hCode hcardC
  have hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24 :=
    Uniqueness.BS81.Thm15.Lemma20.containsDn_all (C := C) hPkg 24 (by decide) (by decide)
  rcases thm15_isometry_to_leechUnitCode (C := C) hPkg (hDn := hDn) with ⟨e, he⟩
  -- Transfer back from `C = (1/2)•X` to `X`.
  let s : ℝ²⁴ → ℝ²⁴ := fun x => (1 / 2 : ℝ) • x
  have hCdef : C = s '' X := rfl
  have hLeechDef : leechUnitCode = s '' Uniqueness.RigidityClassify.CE.leechKissingVectors := rfl
  -- Use linearity to rewrite images of scaled sets.
  have heScaled :
      e '' (s '' X) = s '' (e '' X) := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hxX, rfl⟩, rfl⟩
      refine ⟨e x, ⟨x, hxX, rfl⟩, ?_⟩
      simp [s, map_smul]
    · rintro ⟨y, ⟨x, hxX, rfl⟩, rfl⟩
      refine ⟨(1 / 2 : ℝ) • x, ?_, by simp [s]⟩
      refine ⟨x, hxX, rfl⟩
  have hScaledEq :
      s '' (e '' X) = s '' Uniqueness.RigidityClassify.CE.leechKissingVectors := by
    -- `he : e '' C = leechUnitCode`
    -- unfold `C` and `leechUnitCode`
    simpa [C, hCdef, hLeechDef, heScaled] using! he
  have hinj : Function.Injective (fun x : ℝ²⁴ => (1 / 2 : ℝ) • x) := by
    intro x y hxy
    have hu : IsUnit (1 / 2 : ℝ) := by
      have hne : (1 / 2 : ℝ) ≠ 0 := by simp
      exact isUnit_iff_ne_zero.2 hne
    exact (IsUnit.smul_left_cancel (a := (1 / 2 : ℝ)) hu).1 hxy
  have hFinal : e '' X = Uniqueness.RigidityClassify.CE.leechKissingVectors := by
    -- Cancel the common nonzero scaling from both sides.
    exact (Set.image_eq_image (f := fun x : ℝ²⁴ => (1 / 2 : ℝ) • x) hinj).1 hScaledEq
  refine ⟨e.toIsometryEquiv, ?_⟩
  simpa using! hFinal
end

end SpherePacking.Dim24.Uniqueness.BS81
