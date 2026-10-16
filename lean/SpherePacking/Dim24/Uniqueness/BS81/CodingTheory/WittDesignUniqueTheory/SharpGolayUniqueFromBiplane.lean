-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneIso
public import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.ReconstructedCanonBiplane
import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneUniqueness.ChooseB0
import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneUniqueness.Relabel
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.Step4.Step4Iso
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpGolayAux.Generators
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpGolayAux.Span
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerS3622.Classify.PermuteInvariants

/-!
# Sharp Golay code uniqueness from biplane uniqueness

This file is the bridge from the purely combinatorial biplane uniqueness theorem
`BiplaneUniqueness.biplane_unique'` to the coding-theory statement `sharpGolay_unique_of_biplane`.

Roadmap source (in-repo): `paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`,
final subsection "Conclude Golay uniqueness".
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory

noncomputable section

open GolayUniquenessSteps.CodeFromOctads

namespace BiplaneUniqueness

open Biplane

/-- Any biplane structure is isomorphic to the fixed canonical biplane on `Fin 11`. -/
public theorem biplane_unique (D : Biplane.Structure) :
    Biplane.IsIso D ReconstructedCanonicalBiplane.canonicalStructure := by
  -- Step 0: choose `B0`.
  let B0 : Biplane.Block := Aux.chooseBlock D
  have hB0 : B0 ∈ D.blocks := Aux.chooseBlock_mem D
  -- Step 3: transport the induced triple system to `Fin 6`.
  rcases Step3.tripleSystem6_is23632 (D := D) (B0 := B0) hB0 with ⟨e, hT⟩
  rcases Step3.exists_relabel_to_canonicalBlocks (D := D) (B0 := B0) (e := e) hT with ⟨σ, hσ⟩
  -- Step 4: vertex-family reconstruction.
  refine
    Step4.Aux4IsoProof.reconstruct_iso_to_canonical_of_tripleSystem6_eq_canonicalBlocks (D := D)
      (B0 := B0) hB0 (Step4.Aux4.e₁ (B0 := B0) e σ) ?_
  exact Step4.Aux4Iso.tripleSystem6_e1_eq_canonical (D := D) (B0 := B0) (e := e) (σ := σ) hσ

/-- A primed variant of `biplane_unique`: any two biplane structures are isomorphic. -/
public theorem biplane_unique' (D₁ D₂ : Biplane.Structure) : Biplane.IsIso D₁ D₂ := by
  -- Derive from `biplane_unique` by transitivity.
  refine Biplane.IsIso.trans (biplane_unique (D := D₁)) ?_
  exact Biplane.IsIso.symm (biplane_unique (D := D₂))

end BiplaneUniqueness

/-- Sharp Golay code uniqueness, proved via the biplane reduction and transport of generators. -/
public theorem sharpGolay_unique_of_biplane
    (C₁ C₂ : Code 24)
    (h₁ : IsSharpBS81GolayInput C₁)
    (h₂ : IsSharpBS81GolayInput C₂) :
    ∃ σ : Equiv (Fin 24) (Fin 24), permuteCode (n := 24) σ C₁ = C₂ := by
  -- deterministic extraction data
  let E₁ := SharpGolayUniqueFromBiplaneAux.extract C₁ h₁
  let E₂ := SharpGolayUniqueFromBiplaneAux.extract C₂ h₂
  -- biplane uniqueness gives a point permutation `τ`
  rcases BiplaneUniqueness.biplane_unique' E₁.D E₂.D with ⟨τ, hτD⟩
  have hτ : Biplane.mapBlocks τ E₁.blocks = E₂.blocks := by
    simpa [E₁.hD, E₂.hD] using! hτD
  let π : Equiv (Fin 11) (Fin 11) :=
    SharpGolayUniqueFromBiplaneAux.Transported.π (E₁ := E₁) (E₂ := E₂)
      (τ := τ) (hτ := hτ)
  -- coordinate permutation transporting the extracted generator data
  let σ : Equiv (Fin 24) (Fin 24) :=
    SharpGolayUniqueFromBiplaneAux.Transported.σ (E₁ := E₁) (E₂ := E₂)
      (τ := τ) (hτ := hτ)
  refine ⟨σ, ?_⟩
  -- inclusion `permuteCode σ C₁ ⊆ C₂` from spanning and generator transport
  have hsubset : permuteCode (n := 24) σ C₁ ⊆ C₂ := by
    intro w hw
    rcases hw with ⟨w0, hw0, rfl⟩
    -- span description of `w0`
    have hw0span :
        w0 ∈ Submodule.span (ZMod 2)
          (Set.insert E₁.u (Set.range E₁.v)) :=
      SharpGolayUniqueFromBiplaneAux.Extraction.mem_span_u_v_of_mem (E := E₁) hw0
    -- push the span through the linear equivalence induced by `σ`
    let L := GolayUniquenessSteps.CodeFromOctads.permuteLinearEquiv σ
    have hmem_map :
        permuteWord (n := 24) σ w0 ∈
          Submodule.map L.toLinearMap
            (Submodule.span (ZMod 2) (Set.insert E₁.u (Set.range E₁.v))) := by
      refine Submodule.mem_map.2 ?_
      exact ⟨w0, hw0span, rfl⟩
    have hmap_le :
        Submodule.map L.toLinearMap
            (Submodule.span (ZMod 2) (Set.insert E₁.u (Set.range E₁.v))) ≤
          LinearCode.submodule (n := 24) C₂ h₂.linear := by
      -- it suffices to check the images of the generators
      refine (Submodule.map_span_le (f := L.toLinearMap)
        (s := Set.insert E₁.u (Set.range E₁.v))
        (N := LinearCode.submodule (n := 24) C₂ h₂.linear)).2 ?_
      intro m hm
      rcases Set.mem_insert_iff.1 hm with hm | hm
      · subst hm
        have hu :
            permuteWord (n := 24) σ E₁.u = E₂.u :=
          SharpGolayUniqueFromBiplaneAux.Transported.permuteWord_u E₁ E₂ τ hτ
        have hLu : L.toLinearMap E₁.u = E₂.u := by
          -- `permuteLinearEquiv` has `toFun = permuteWord`.
          simpa [L, GolayUniquenessSteps.CodeFromOctads.permuteLinearEquiv] using! hu
        -- `E₂.u ∈ C₂`
        have : E₂.u ∈ LinearCode.submodule (n := 24) C₂ h₂.linear := by
          simpa using! E₂.huC
        simpa [hLu] using! this
      · rcases hm with ⟨i, rfl⟩
        have hv :
            permuteWord (n := 24) σ (E₁.v i) =
              E₂.v (π i) :=
          SharpGolayUniqueFromBiplaneAux.Transported.permuteWord_v E₁ E₂ τ hτ i
        have hLv :
            L.toLinearMap (E₁.v i) =
              E₂.v (π i) := by
          simpa [L, GolayUniquenessSteps.CodeFromOctads.permuteLinearEquiv] using! hv
        have :
            E₂.v (π i) ∈ LinearCode.submodule (n := 24) C₂ h₂.linear := by
          simpa [π] using! E₂.hvC _
        simpa [hLv] using! this
    have : permuteWord (n := 24) σ w0 ∈ LinearCode.submodule (n := 24) C₂ h₂.linear :=
      hmap_le hmem_map
    simpa using! this
  -- conclude equality by cardinality
  have hncard :
      Set.ncard C₂ ≤ Set.ncard (permuteCode (n := 24) σ C₁) := by
    have hperm :
        Set.ncard (permuteCode (n := 24) σ C₁) = Set.ncard C₁ := by
      simpa using!
        (SteinerS3622Classify.PermuteCode.ncard_permuteCode (σ := σ) C₁)
    -- both sides are `2^12`
    simp [hperm, h₁.card_eq, h₂.card_eq]
  exact Set.eq_of_subset_of_ncard_le hsubset hncard

end

end GolayUniquenessSteps.WittDesignUniqueTheory

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
