-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpGolayAux.Extraction
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneIso

/-!
# Transport layer for sharp Golay uniqueness

Given two extracted biplanes `E₁.D` and `E₂.D`, biplane uniqueness provides an isomorphism
`τ : Equiv (Fin 11) (Fin 11)` between their point sets. This file:

1. Turns `τ` into a permutation `π` of the `11` indexed blocks (hence of the lifted words `v i`),
2. Extends `(τ, π)` to a coordinate permutation `coordPerm : Equiv (Fin 24) (Fin 24)` sending the
   canonical decomposition `Fin 24 = T ⊔ U ⊔ {p}` for `E₁` to the corresponding decomposition
   for `E₂`.

No coding-theory arguments appear here: we only manipulate finsets and permutations.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.SharpGolayUniqueFromBiplaneAux

noncomputable section

open scoped BigOperators
open GolayUniquenessSteps.CodeFromOctadsAux
open Biplane

/-!
## Block indexing permutation induced by an isomorphism of block families
-/

namespace BlockTransport

open Extraction

variable {C₁ C₂ : Code 24}
variable {h₁ : IsSharpBS81GolayInput C₁} {h₂ : IsSharpBS81GolayInput C₂}

/-- Blocks in the extracted biplanes, viewed as finsets of points in `Fin 11`. -/
public abbrev Block := Finset (Fin 11)

/-- Mapping blocks by `τ` and then by `τ.symm` returns the original block finset. -/
public lemma mapBlocks_symm_comp (τ : Equiv (Fin 11) (Fin 11)) (T : Finset Block) :
    Biplane.mapBlocks τ.symm (Biplane.mapBlocks τ T) = T := by
  calc
    Biplane.mapBlocks τ.symm (Biplane.mapBlocks τ T)
        = Biplane.mapBlocks (τ.trans τ.symm) T := by
            simpa using! (Biplane.mapBlocks_trans (σ₁ := τ) (σ₂ := τ.symm) (T := T)).symm
    _ = Biplane.mapBlocks (Equiv.refl Point) T := by simp
    _ = T := Biplane.mapBlocks_refl (T := T)

/-- Mapping blocks by `τ.symm` and then by `τ` returns the original block finset. -/
public lemma mapBlocks_comp_symm (τ : Equiv (Fin 11) (Fin 11)) (T : Finset Block) :
    Biplane.mapBlocks τ (Biplane.mapBlocks τ.symm T) = T := by
  simpa using! mapBlocks_symm_comp (τ := τ.symm) (T := T)

/-- Each indexed block `E.block i` is a member of the extracted block family `E.blocks`. -/
public lemma block_mem_blocks {C : Code 24} {hC : IsSharpBS81GolayInput C}
    (E : Extraction C hC) (i : Fin 11) : E.block i ∈ E.blocks := by
  rw [E.hblocks]
  exact Finset.mem_image.2 ⟨i, by simp, rfl⟩

/-- For each block index `i` in `E₁`, find the corresponding block index in `E₂` under `τ`. -/
public lemma exists_block_index
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11))
    (hτ : Biplane.mapBlocks τ E₁.blocks = E₂.blocks) (i : Fin 11) :
    ∃ j : Fin 11, E₂.block j = (E₁.block i).map τ.toEmbedding := by
  have hmem_map : (E₁.block i).map τ.toEmbedding ∈ Biplane.mapBlocks τ E₁.blocks := by
    refine (Biplane.mem_mapBlocks (σ := τ) (T := E₁.blocks)
      (B := (E₁.block i).map τ.toEmbedding)).2 ?_
    exact ⟨E₁.block i, block_mem_blocks (E := E₁) i, rfl⟩
  simp_all

/-- The inverse-direction version of `exists_block_index`, using `τ.symm`. -/
public lemma exists_block_index_symm
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11))
    (hτ : Biplane.mapBlocks τ E₁.blocks = E₂.blocks) (j : Fin 11) :
    ∃ i : Fin 11, E₁.block i = (E₂.block j).map τ.symm.toEmbedding := by
  have hτsymm : Biplane.mapBlocks τ.symm E₂.blocks = E₁.blocks := by
    have h := congrArg (Biplane.mapBlocks τ.symm) hτ
    rw [mapBlocks_symm_comp (τ := τ) (T := E₁.blocks)] at h
    exact h.symm
  exact exists_block_index E₂ E₁ τ.symm hτsymm j

/-- The block index function induced by `τ` (defined using `Classical.choose`). -/
public noncomputable def blockIndexFun
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11))
    (hτ : Biplane.mapBlocks τ E₁.blocks = E₂.blocks) (i : Fin 11) : Fin 11 :=
  Classical.choose (exists_block_index (E₁ := E₁) (E₂ := E₂) τ hτ i)

/-- Specification lemma for `blockIndexFun`. -/
public lemma blockIndexFun_spec
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11))
    (hτ : Biplane.mapBlocks τ E₁.blocks = E₂.blocks) (i : Fin 11) :
    E₂.block (blockIndexFun (E₁ := E₁) (E₂ := E₂) τ hτ i) =
      (E₁.block i).map τ.toEmbedding :=
  Classical.choose_spec (exists_block_index (E₁ := E₁) (E₂ := E₂) τ hτ i)

/-- The inverse block index function induced by `τ` (defined using `Classical.choose`). -/
public noncomputable def blockIndexInvFun
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11))
    (hτ : Biplane.mapBlocks τ E₁.blocks = E₂.blocks) (j : Fin 11) : Fin 11 :=
  Classical.choose (exists_block_index_symm (E₁ := E₁) (E₂ := E₂) τ hτ j)

/-- Specification lemma for `blockIndexInvFun`. -/
public lemma blockIndexInvFun_spec
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11))
    (hτ : Biplane.mapBlocks τ E₁.blocks = E₂.blocks) (j : Fin 11) :
    E₁.block (blockIndexInvFun (E₁ := E₁) (E₂ := E₂) τ hτ j) =
      (E₂.block j).map τ.symm.toEmbedding :=
  Classical.choose_spec (exists_block_index_symm (E₁ := E₁) (E₂ := E₂) τ hτ j)

/-- The block index equivalence induced by `τ`. -/
public noncomputable def blockIndexEquiv
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11))
    (hτ : Biplane.mapBlocks τ E₁.blocks = E₂.blocks) : Equiv (Fin 11) (Fin 11) where
  toFun := blockIndexFun (E₁ := E₁) (E₂ := E₂) τ hτ
  invFun := blockIndexInvFun (E₁ := E₁) (E₂ := E₂) τ hτ
  left_inv := by
    intro i
    apply E₁.block_inj
    have :
        E₁.block (blockIndexInvFun (E₁ := E₁) (E₂ := E₂) τ hτ
          (blockIndexFun (E₁ := E₁) (E₂ := E₂) τ hτ i)) =
          ((E₁.block i).map τ.toEmbedding).map τ.symm.toEmbedding := by
      simpa [blockIndexFun_spec (E₁ := E₁) (E₂ := E₂) τ hτ i] using!
        (blockIndexInvFun_spec (E₁ := E₁) (E₂ := E₂) τ hτ
          (blockIndexFun (E₁ := E₁) (E₂ := E₂) τ hτ i))
    simpa [map_map_equiv_symm (σ := τ) (B := E₁.block i)] using! this
  right_inv := by
    intro j
    apply E₂.block_inj
    have :
        E₂.block (blockIndexFun (E₁ := E₁) (E₂ := E₂) τ hτ
          (blockIndexInvFun (E₁ := E₁) (E₂ := E₂) τ hτ j)) =
          ((E₂.block j).map τ.symm.toEmbedding).map τ.toEmbedding := by
      simpa [blockIndexInvFun_spec (E₁ := E₁) (E₂ := E₂) τ hτ j] using!
        (blockIndexFun_spec (E₁ := E₁) (E₂ := E₂) τ hτ
          (blockIndexInvFun (E₁ := E₁) (E₂ := E₂) τ hτ j))
    have hcancel :
        ((E₂.block j).map τ.symm.toEmbedding).map τ.toEmbedding = E₂.block j := by
      simpa using! (map_map_equiv_symm' (σ := τ) (B := E₂.block j))
    exact this.trans hcancel

/-- Specification lemma for `blockIndexEquiv`. -/
public lemma blockIndexEquiv_spec
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11))
    (hτ : Biplane.mapBlocks τ E₁.blocks = E₂.blocks) (i : Fin 11) :
    E₂.block (blockIndexEquiv (E₁ := E₁) (E₂ := E₂) τ hτ i) =
      (E₁.block i).map τ.toEmbedding := by
  simpa [blockIndexEquiv] using! blockIndexFun_spec (E₁ := E₁) (E₂ := E₂) τ hτ i

end BlockTransport

/-!
## Coordinate permutation induced by `(τ, π)`
-/

namespace CoordTransport

open Extraction

variable {C₁ C₂ : Code 24}
variable {h₁ : IsSharpBS81GolayInput C₁} {h₂ : IsSharpBS81GolayInput C₂}

/-- The permutation of `Fin 12` fixing `0` and permuting successors by `π`. -/
public def permFin12 (π : Equiv (Fin 11) (Fin 11)) : Equiv (Fin 12) (Fin 12) where
  toFun := fun k => Fin.cases 0 (fun i => Fin.succ (π i)) k
  invFun := fun k => Fin.cases 0 (fun i => Fin.succ (π.symm i)) k
  left_inv := by
    intro k
    cases k using Fin.cases <;> simp
  right_inv := by
    intro k
    cases k using Fin.cases <;> simp

/-- `permFin12` fixes the element `0 : Fin 12`. -/
@[simp] public lemma permFin12_zero (π : Equiv (Fin 11) (Fin 11)) :
    permFin12 π ⟨0, Nat.succ_pos 11⟩ = ⟨0, Nat.succ_pos 11⟩ := by
  simp [permFin12]

/-- `permFin12` sends `Fin.succ i` to `Fin.succ (π i)`. -/
@[simp] public lemma permFin12_succ (π : Equiv (Fin 11) (Fin 11)) (i : Fin 11) :
    permFin12 π (Fin.succ i) = Fin.succ (π i) := by
  simp [permFin12]

/-- A simplification lemma for `(permFin12 π).symm` on successors. -/
@[simp] public lemma permFin12_symm_succ (π : Equiv (Fin 11) (Fin 11)) (i : Fin 11) :
    (permFin12 π).symm (Fin.succ i) = Fin.succ (π.symm i) := by
  simp [permFin12]

/-- `(permFin12 π).symm` fixes the element `0 : Fin 12`. -/
@[simp] public lemma permFin12_symm_zero (π : Equiv (Fin 11) (Fin 11)) :
    (permFin12 π).symm ⟨0, Nat.succ_pos 11⟩ = ⟨0, Nat.succ_pos 11⟩ := by
  simp [permFin12]

/-- The coordinate permutation sending the `T/U/p` decomposition for `E₁` to that for `E₂`. -/
public def coordPerm
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11)) (π : Equiv (Fin 11) (Fin 11)) :
    Equiv (Fin 24) (Fin 24) where
  toFun := fun x =>
    if hxS : x ∈ support E₁.u then
      if hxP : x = E₁.p then
        E₂.p
      else
        -- `x ∈ U₁`
        E₂.eU (τ (E₁.idxU x ((E₁.mem_U_iff x).2 ⟨hxS, hxP⟩)))
    else
      -- `x ∈ T₁`
      E₂.fT (permFin12 π (E₁.idxT x ((E₁.mem_T_iff_not_mem_support x).2 hxS)))
  invFun := fun x =>
    if hxS : x ∈ support E₂.u then
      if hxP : x = E₂.p then
        E₁.p
      else
        -- `x ∈ U₂`
        E₁.eU (τ.symm (E₂.idxU x ((E₂.mem_U_iff x).2 ⟨hxS, hxP⟩)))
    else
      -- `x ∈ T₂`
      E₁.fT ((permFin12 π).symm (E₂.idxT x ((E₂.mem_T_iff_not_mem_support x).2 hxS)))
  left_inv := by
    intro x
    by_cases hxS : x ∈ support E₁.u
    · by_cases hxP : x = E₁.p
      · subst hxP
        simp [hxS, E₂.p_mem_support]
      · -- `x ∈ U₁`
        have hxU : x ∈ E₁.U := (E₁.mem_U_iff x).2 ⟨hxS, hxP⟩
        have hyU : E₂.eU (τ (E₁.idxU x hxU)) ∈ E₂.U := Extraction.eU_mem_U (E := E₂) _
        have hy := (E₂.mem_U_iff _).1 hyU
        simp only [dif_pos hxS, dif_neg hxP, dif_pos hy.1, dif_neg hy.2]
        grind only [! Extraction.idxU_eU_of_mem, Extraction.eU_idxU, Equiv.symm_apply_apply]
    · -- `x ∈ T₁`
      have hxT : x ∈ E₁.T := (E₁.mem_T_iff_not_mem_support x).2 (by simpa using! hxS)
      have hyS : E₂.fT (permFin12 π (E₁.idxT x hxT)) ∉ support E₂.u :=
        (E₂.mem_T_iff_not_mem_support _).1 (Extraction.fT_mem_T (E := E₂) _)
      simp only [dif_neg hxS, dif_neg hyS]
      grind only [! Extraction.idxT_fT_of_mem, Extraction.fT_idxT, Equiv.symm_apply_apply]
  right_inv := by
    intro x
    by_cases hxS : x ∈ support E₂.u
    · by_cases hxP : x = E₂.p
      · subst hxP
        simp [hxS, E₁.p_mem_support]
      · have hxU : x ∈ E₂.U := (E₂.mem_U_iff x).2 ⟨hxS, hxP⟩
        have hyU : E₁.eU (τ.symm (E₂.idxU x hxU)) ∈ E₁.U :=
          Extraction.eU_mem_U (E := E₁) _
        have hy := (E₁.mem_U_iff _).1 hyU
        simp only [dif_pos hxS, dif_neg hxP, dif_pos hy.1, dif_neg hy.2]
        grind only [! Extraction.idxU_eU_of_mem, Extraction.eU_idxU, Equiv.apply_symm_apply]
    · have hxT : x ∈ E₂.T := (E₂.mem_T_iff_not_mem_support x).2 (by simpa using! hxS)
      have hyS : E₁.fT ((permFin12 π).symm (E₂.idxT x hxT)) ∉ support E₁.u :=
        (E₁.mem_T_iff_not_mem_support _).1 (Extraction.fT_mem_T (E := E₁) _)
      simp only [dif_neg hxS, dif_neg hyS]
      grind only [! Extraction.idxT_fT_of_mem, Extraction.fT_idxT, Equiv.apply_symm_apply]

/-- `coordPerm` sends `E₁.fT k` to `E₂.fT (permFin12 π k)`. -/
@[simp] public lemma coordPerm_fT
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11)) (π : Equiv (Fin 11) (Fin 11)) (k : Fin 12) :
    coordPerm (E₁ := E₁) (E₂ := E₂) τ π (E₁.fT k) = E₂.fT (permFin12 π k) := by
  have hxS : E₁.fT k ∉ support E₁.u :=
    (E₁.mem_T_iff_not_mem_support _).1 (Extraction.fT_mem_T (E := E₁) k)
  dsimp [coordPerm]
  simp only [dif_neg hxS]
  have hxT : E₁.fT k ∈ E₁.T := (E₁.mem_T_iff_not_mem_support _).2 hxS
  simpa using! congrArg (fun i => E₂.fT (permFin12 π i))
    (Extraction.idxT_fT_of_mem (E := E₁) k hxT)

/-- `coordPerm` sends the pinned coordinate `E₁.p` to `E₂.p`. -/
@[simp] public lemma coordPerm_p
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11)) (π : Equiv (Fin 11) (Fin 11)) :
    coordPerm (E₁ := E₁) (E₂ := E₂) τ π E₁.p = E₂.p := by
  have hxS : E₁.p ∈ support E₁.u := E₁.p_mem_support
  dsimp [coordPerm]
  simp [hxS]

/-- `coordPerm` sends `E₁.eU j` to `E₂.eU (τ j)`. -/
@[simp] public lemma coordPerm_eU
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11)) (π : Equiv (Fin 11) (Fin 11)) (j : Fin 11) :
    coordPerm (E₁ := E₁) (E₂ := E₂) τ π (E₁.eU j) = E₂.eU (τ j) := by
  have hxS : E₁.eU j ∈ support E₁.u :=
    (E₁.mem_U_iff _).1 (Extraction.eU_mem_U (E := E₁) j) |>.1
  have hxP : E₁.eU j ≠ E₁.p := Extraction.eU_ne_p (E := E₁) j
  dsimp [coordPerm]
  simp only [dif_pos hxS, dif_neg hxP]
  have hjU : E₁.eU j ∈ E₁.U := (E₁.mem_U_iff _).2 ⟨hxS, hxP⟩
  simpa using! congrArg (fun i => E₂.eU (τ i))
    (Extraction.idxU_eU_of_mem (E := E₁) j hjU)

/-- A simplification lemma for `(coordPerm ...).symm` on `T`-coordinates. -/
@[simp] public lemma coordPerm_symm_fT
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11)) (π : Equiv (Fin 11) (Fin 11)) (k : Fin 12) :
    (coordPerm (E₁ := E₁) (E₂ := E₂) τ π).symm (E₂.fT k) =
      E₁.fT ((permFin12 π).symm k) := by
  have hxS : E₂.fT k ∉ support E₂.u :=
    (E₂.mem_T_iff_not_mem_support _).1 (Extraction.fT_mem_T (E := E₂) k)
  dsimp [coordPerm]
  simp only [dif_neg hxS]
  have hxT : E₂.fT k ∈ E₂.T := (E₂.mem_T_iff_not_mem_support _).2 hxS
  simpa using! congrArg (fun i => E₁.fT ((permFin12 π).symm i))
    (Extraction.idxT_fT_of_mem (E := E₂) k hxT)

/-- A simplification lemma for `(coordPerm ...).symm` at the pinned coordinate. -/
@[simp] public lemma coordPerm_symm_p
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11)) (π : Equiv (Fin 11) (Fin 11)) :
    (coordPerm (E₁ := E₁) (E₂ := E₂) τ π).symm E₂.p = E₁.p := by
  apply (coordPerm (E₁ := E₁) (E₂ := E₂) τ π).injective
  simp [coordPerm_p]

/-- A simplification lemma for `(coordPerm ...).symm` on `U`-coordinates. -/
@[simp] public lemma coordPerm_symm_eU
    (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
    (τ : Equiv (Fin 11) (Fin 11)) (π : Equiv (Fin 11) (Fin 11)) (j : Fin 11) :
    (coordPerm (E₁ := E₁) (E₂ := E₂) τ π).symm (E₂.eU j) = E₁.eU (τ.symm j) := by
  have hxS : E₂.eU j ∈ support E₂.u :=
    (E₂.mem_U_iff _).1 (Extraction.eU_mem_U (E := E₂) j) |>.1
  have hxP : E₂.eU j ≠ E₂.p := Extraction.eU_ne_p (E := E₂) j
  dsimp [coordPerm]
  simp only [dif_pos hxS, dif_neg hxP]
  have hjU : E₂.eU j ∈ E₂.U := (E₂.mem_U_iff _).2 ⟨hxS, hxP⟩
  simpa using! congrArg (fun i => E₁.eU (τ.symm i))
    (Extraction.idxU_eU_of_mem (E := E₂) j hjU)

end CoordTransport

end

end GolayUniquenessSteps.WittDesignUniqueTheory.SharpGolayUniqueFromBiplaneAux

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
