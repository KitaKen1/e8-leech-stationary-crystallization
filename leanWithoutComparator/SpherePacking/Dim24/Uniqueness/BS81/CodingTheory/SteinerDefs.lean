module
public import Mathlib.Data.Finset.Card

/-!
# Steiner systems (basic definitions)

We implement a minimal definition of Steiner systems, plus a notion of isomorphism via a coordinate
permutation of `Fin v`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

/--
A Steiner system `S(t,k,v)` on `Fin v`, represented by its set of blocks as finsets.

We only record the block size and the unique-block covering property for `t`-subsets.
-/
public structure SteinerSystem (v k t : ℕ) where
  blocks : Set (Finset (Fin v))
  block_card : ∀ B : Finset (Fin v), B ∈ blocks → B.card = k
  cover_unique :
    ∀ S : Finset (Fin v), S.card = t →
      ∃! B : Finset (Fin v), B ∈ blocks ∧ S ⊆ B

/-- Two Steiner systems are isomorphic if their blocks are related by a permutation of `Fin v`. -/
@[expose] public def IsomorphicSteinerSystem (v k t : ℕ) (S₁ S₂ : SteinerSystem v k t) : Prop :=
  ∃ σ : Equiv (Fin v) (Fin v),
    {B : Finset (Fin v) | B ∈ S₁.blocks} =
      {B : Finset (Fin v) | (Finset.map σ.toEmbedding B) ∈ S₂.blocks}

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
