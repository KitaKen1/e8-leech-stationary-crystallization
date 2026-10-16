-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.BiplaneBasic

/-!
# Isomorphisms of `2-(11,5,2)` biplanes

We keep the notion lightweight: an isomorphism is just a permutation of points carrying the
family of blocks to the other family (as a `Finset` of `Finset`s).
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Biplane

/-- Map a family of blocks by applying a point permutation to each block. -/
public def mapBlocks (σ : Equiv Point Point) (T : Finset Block) : Finset Block :=
  T.map
    { toFun := fun B => B.map σ.toEmbedding
      inj' := by
        intro B B' h
        exact (Finset.map_inj (f := σ.toEmbedding)).1 h }

/-- Membership in `mapBlocks σ T` is membership in `T` after mapping by `σ`. -/
@[simp] public lemma mem_mapBlocks {σ : Equiv Point Point} {T : Finset Block} {B : Block} :
    B ∈ mapBlocks σ T ↔ ∃ B0 ∈ T, B = B0.map σ.toEmbedding := by
  -- `Finset.mem_map` gives `∃ B0 ∈ T, B0.map σ = B`; swap sides for readability.
  unfold mapBlocks
  rw [Finset.mem_map]
  constructor
  · rintro ⟨B0, hB0, rfl⟩
    exact ⟨B0, hB0, rfl⟩
  · rintro ⟨B0, hB0, rfl⟩
    exact ⟨B0, hB0, rfl⟩

attribute [grind =] mem_mapBlocks

/-- Mapping blocks by a permutation preserves cardinality. -/
@[simp] public lemma card_mapBlocks (σ : Equiv Point Point) (T : Finset Block) :
    (mapBlocks σ T).card = T.card := by
  simp [mapBlocks]

/-- An isomorphism of biplane structures is a point permutation transporting the block family. -/
@[expose] public def IsIso (D₁ D₂ : Structure) : Prop :=
  ∃ σ : Equiv Point Point, mapBlocks σ D₁.blocks = D₂.blocks

/-- `mapBlocks` respects composition of permutations. -/
public lemma mapBlocks_trans (σ₁ σ₂ : Equiv Point Point) (T : Finset Block) :
    mapBlocks (σ₁.trans σ₂) T = mapBlocks σ₂ (mapBlocks σ₁ T) := by
  ext B
  simp only [mem_mapBlocks]
  constructor
  · rintro ⟨B0, hB0, rfl⟩
    exact ⟨B0.map σ₁.toEmbedding, ⟨B0, hB0, rfl⟩, by rw [Finset.map_map, Equiv.trans_toEmbedding]⟩
  · rintro ⟨B1, ⟨B0, hB0, rfl⟩, rfl⟩
    exact ⟨B0, hB0, by rw [Finset.map_map, Equiv.trans_toEmbedding]⟩

/-- `mapBlocks` by the identity permutation is the identity on block families. -/
public lemma mapBlocks_refl (T : Finset Block) :
    mapBlocks (Equiv.refl Point) T = T := by
  ext B
  simp [mapBlocks]

/-- Reflexivity of biplane isomorphism. -/
public lemma IsIso.refl (D : Structure) : IsIso D D :=
  ⟨Equiv.refl _, by simp [mapBlocks_refl]⟩

/-- Symmetry of biplane isomorphism. -/
public lemma IsIso.symm {D₁ D₂ : Structure} : IsIso D₁ D₂ → IsIso D₂ D₁ := by
  rintro ⟨σ, hσ⟩
  refine ⟨σ.symm, ?_⟩
  have h := congrArg (mapBlocks σ.symm) hσ
  calc
    mapBlocks σ.symm D₂.blocks = mapBlocks σ.symm (mapBlocks σ D₁.blocks) := by
      simpa using! h.symm
    _ = mapBlocks (σ.trans σ.symm) D₁.blocks := by
      simpa using! (mapBlocks_trans (σ₁ := σ) (σ₂ := σ.symm) (T := D₁.blocks)).symm
    _ = mapBlocks (Equiv.refl Point) D₁.blocks := by simp
    _ = D₁.blocks := mapBlocks_refl (T := D₁.blocks)

/-- Transitivity of biplane isomorphism. -/
public lemma IsIso.trans {D₁ D₂ D₃ : Structure} : IsIso D₁ D₂ → IsIso D₂ D₃ → IsIso D₁ D₃ := by
  rintro ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩
  refine ⟨σ₁.trans σ₂, ?_⟩
  calc
    mapBlocks (σ₁.trans σ₂) D₁.blocks = mapBlocks σ₂ D₂.blocks := by
      simp [mapBlocks_trans, h₁]
    _ = D₃.blocks := by
      simp [h₂]

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Biplane
