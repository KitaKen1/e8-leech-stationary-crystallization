-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Isometry.CodeIsGolayCountFinal
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.BasepointInjection

/-!
# Tightness for the Type III injection

Assuming the equality-case shell count `|latticeShell4 C| = 196560`, the Type III cardinality bound
is sharp. This upgrades the injection constructed in `BasepointInjection.lean` to a surjection
onto `Fin 24 × codeFromLattice`.

## Main statement
* `injMap_surjOn_of_sharp_count`

## References
`paper/Notes/CodingTheory/bs81_lemma21_golay_inputs.tex`, Theorem `thm:count_forces_parameters`,
item (3).
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps.Shell4IsometryBasepoint

noncomputable section

open scoped RealInnerProductSpace

open Set

open Uniqueness.BS81
open Uniqueness.BS81.CodingTheory
open Uniqueness.BS81.Thm15.Lemma21
open CodeIsGolayCountFinal

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

local notation "shell4" => Uniqueness.BS81.latticeShell4
local notation "code" => CodeFromLattice.codeFromLattice

/--
Under the equality-case hypotheses (shell count `196560`), the Type-III injection built from a
fixed basepoint `u₀ ∈ TypeIII` is *surjective* onto `Fin 24 × codeFromLattice`.

This is the formal statement that tightness upgrades the injection to a bijection.
-/
public theorem injMap_surjOn_of_sharp_count
    (C : Set ℝ²⁴)
    (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    (u0 : ℝ²⁴) (hu0 : u0 ∈ TypeIII (C := C) hDn)
    (z0 : Fin 24 → ℤ)
    (hz0 : ∀ i, scaledCoord hDn.e i u0 = (z0 i : ℝ))
    (hz0Pat : isPattern3 z0) :
    ∀ p ∈ (Set.univ : Set (Fin 24)) ×ˢ (code (C := C) hDn),
      ∃ u ∈ TypeIII (C := C) hDn, injMap (C := C) hDn z0 u = p := by
  -- Abbreviations.
  let I : Set ℝ²⁴ := CodeIsGolayCountFinal.TypeI (C := C) hDn
  let II : Set ℝ²⁴ := CodeIsGolayCountFinal.TypeII (C := C) hDn
  let III : Set ℝ²⁴ := CodeIsGolayCountFinal.TypeIII (C := C) hDn
  let T : Set (Fin 24 × BinWord 24) := (Set.univ : Set (Fin 24)) ×ˢ (code (C := C) hDn)
  let f : ℝ²⁴ → Fin 24 × BinWord 24 := injMap (C := C) hDn z0
  -- Forced code parameters.
  rcases CodeIsGolayCountFinal.forcing_parameters_codeFromLattice (C := C) hEq hDn with
    ⟨hcodeCard, hW8Card, _hminDist⟩
  -- Shell-4 size.
  have hshellCard : Set.ncard (shell4 C) = 196560 :=
    CodeIsGolayCountFinal.ncard_shell4_eq_196560 (C := C) hEq
  -- Shell-4 patterns cover.
  have hcover : shell4 C ⊆ I ∪ II ∪ III :=
    shell4_subset_TypeI_union_TypeII_union_TypeIII (C := C) (hEq := hEq) (hDn := hDn)
  -- The union is finite (as a subset of the finite shell-4 set).
  have hshell_finite : (shell4 C).Finite := by
    refine Set.finite_of_ncard_ne_zero ?_
    rw [hshellCard]
    decide
  have hunion_sub : (I ∪ II ∪ III) ⊆ shell4 C := by
    intro u hu
    rcases hu with hu12 | hu3
    · rcases hu12 with hu1 | hu2
      · exact hu1.1
      · exact hu2.1
    · exact hu3.1
  have hunion_finite : (I ∪ II ∪ III).Finite :=
    hshell_finite.subset hunion_sub
  -- Bound `|shell4|` by the sum of the type-cardinalities.
  have hshell_le_union : Set.ncard (shell4 C) ≤ Set.ncard (I ∪ II ∪ III) :=
    Set.ncard_le_ncard hcover hunion_finite
  have hunion_le_sum :
      Set.ncard (I ∪ II ∪ III) ≤ Set.ncard I + Set.ncard II + Set.ncard III := by
    have h12 : Set.ncard (I ∪ II) ≤ Set.ncard I + Set.ncard II :=
      Set.ncard_union_le I II
    have h123 : Set.ncard ((I ∪ II) ∪ III) ≤ Set.ncard (I ∪ II) + Set.ncard III :=
      Set.ncard_union_le (I ∪ II) III
    exact le_add_of_le_add_right h123 h12
  have hshell_le_sum : 196560 ≤ Set.ncard I + Set.ncard II + Set.ncard III := by
    have : Set.ncard (shell4 C) ≤ Set.ncard I + Set.ncard II + Set.ncard III :=
      le_trans hshell_le_union hunion_le_sum
    simpa [hshellCard] using! this
  -- Upper bounds on Types I/II/III.
  have hI_le : Set.ncard I ≤ 1104 :=
    CodeIsGolayCountFinal.ncard_TypeI_le_1104 (C := C) (hDn := hDn)
  have hII_le :
      Set.ncard II ≤ (2 ^ 7) * Set.ncard (weight8Words (code (C := C) hDn)) :=
    CodeIsGolayCountFinal.ncard_TypeII_le (C := C) (hEq := hEq) (hDn := hDn)
  have hII_le' : Set.ncard II ≤ (2 ^ 7) * 759 := by
    simpa [hW8Card, II] using! hII_le
  have hIII_le :
      Set.ncard III ≤ 24 * Set.ncard (code (C := C) hDn) :=
    CodeIsGolayCountFinal.ncard_TypeIII_le (C := C) (hDn := hDn)
  have hIII_le' : Set.ncard III ≤ 24 * (2 ^ 12) := by
    simpa [hcodeCard, III] using! hIII_le
  -- Sharpness forces `|TypeIII| = 24 * 2^12`.
  have hmax : 1104 + (2 ^ 7) * 759 + 24 * (2 ^ 12) = 196560 := by decide
  have hIII_ge' : 24 * (2 ^ 12) ≤ Set.ncard III := by
    nlinarith [hshell_le_sum, hI_le, hII_le', hmax]
  have hIII_card : Set.ncard III = 24 * (2 ^ 12) :=
    le_antisymm hIII_le' hIII_ge'
  -- Compute `|T| = 24 * 2^12`.
  have hT_card : Set.ncard T = 24 * (2 ^ 12) := by
    -- `ncard univ = 24` and `ncard code = 2^12`
    simp [T, hcodeCard, Set.ncard_prod]
  -- Conclude `|III| = |T|`.
  have hIII_eq_T : Set.ncard III = Set.ncard T := by
    simpa [hT_card] using! hIII_card
  -- `injMap` is an injection `III → T`, hence a bijection by cardinality.
  have hf_maps : Set.MapsTo f III T := by
    intro u hu
    exact injMap_mapsTo C hDn u0 hu0 z0 hz0 hz0Pat u hu
  have hf_inj : Set.InjOn f III := by
    simpa [f] using! injMap_injOn (C := C) hDn z0 hz0Pat
  have hT_le_image : T.ncard ≤ (f '' III).ncard := by
    simpa [hf_inj.ncard_image.symm] using! (le_of_eq hIII_eq_T.symm)
  have hT_finite : T.Finite :=
    toFinite T
  have himage_eq : f '' III = T :=
    Set.eq_of_subset_of_ncard_le hf_maps.image_subset hT_le_image hT_finite
  intro p hp
  have hp' : p ∈ f '' III := by
    -- `simp` reduces membership in `univ ×ˢ code` to the second-component condition, so unfold `T`.
    simpa [himage_eq, T] using! hp
  rcases hp' with ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩
end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps.Shell4IsometryBasepoint
