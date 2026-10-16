-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpGolayAux.Transport
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.Span

/-!
# Transporting the extracted generators

Given two extractions `E₁` and `E₂` and an isomorphism of their block families, this file builds:
* a block index permutation `π : Equiv (Fin 11) (Fin 11)`, and
* a coordinate permutation `σ : Equiv (Fin 24) (Fin 24)`.

The main lemmas show that `permuteWord σ` transports `E₁.u` to `E₂.u` and each pinned lift
`E₁.v i` to `E₂.v (π i)`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.SharpGolayUniqueFromBiplaneAux.Transported

noncomputable section

open GolayBounds
open GolayUniquenessSteps.CodeFromOctadsAux
open GolayUniquenessSteps.CodeFromOctads
open PunctureEven
open BiplaneFromSharp
open Biplane

variable {C₁ C₂ : Code 24}
variable {h₁ : IsSharpBS81GolayInput C₁} {h₂ : IsSharpBS81GolayInput C₂}

variable (E₁ : Extraction C₁ h₁) (E₂ : Extraction C₂ h₂)
variable (τ : Equiv (Fin 11) (Fin 11))
variable (hτ : Biplane.mapBlocks τ E₁.blocks = E₂.blocks)

/-- The induced permutation of the `11` block indices coming from the point relabelling `τ`. -/
public noncomputable def π : Equiv (Fin 11) (Fin 11) :=
  BlockTransport.blockIndexEquiv (E₁ := E₁) (E₂ := E₂) τ hτ

/--
The coordinate permutation transporting the extracted decomposition of `Fin 24` from `E₁` to
`E₂`.
-/
public noncomputable def ρ : Equiv (Fin 24) (Fin 24) :=
  CoordTransport.coordPerm (E₁ := E₁) (E₂ := E₂) τ
    (π (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ))

/-- The inverse coordinate permutation, used for transporting words via `permuteWord`. -/
public noncomputable def σ : Equiv (Fin 24) (Fin 24) :=
  (ρ (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ)).symm

local notation "π₀" => π (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ)
local notation "ρ₀" => ρ (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ)
local notation "σ₀" => σ (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ)

/-- Membership in transported blocks: `E₂.block (π i)` corresponds to `E₁.block i` via `τ.symm`. -/
public lemma mem_block_transport (i : Fin 11) (j : Fin 11) :
    j ∈ E₂.block (π₀ i) ↔ τ.symm j ∈ E₁.block i := by
  have hspec :
      E₂.block (π₀ i) = (E₁.block i).map τ.toEmbedding :=
    BlockTransport.blockIndexEquiv_spec (E₁ := E₁) (E₂ := E₂) τ hτ i
  simp [hspec, Finset.mem_map_equiv]

/-- Transport supports of pinned lifts along `τ` and the induced block permutation `π`. -/
public lemma eU_mem_support_v_transport (i : Fin 11) (j : Fin 11) :
    E₂.eU j ∈ support (E₂.v (π₀ i)) ↔
      E₁.eU (τ.symm j) ∈ support (E₁.v i) := by
  have h₂ :
      E₂.eU j ∈ support (E₂.v (π₀ i)) ↔ j ∉ E₂.block (π₀ i) :=
    Extraction.eU_mem_support_v_iff_not_mem_block (E := E₂) _ j
  have h₁ :
      E₁.eU (τ.symm j) ∈ support (E₁.v i) ↔ τ.symm j ∉ E₁.block i :=
    Extraction.eU_mem_support_v_iff_not_mem_block (E := E₁) i (τ.symm j)
  have hb :
      j ∈ E₂.block (π₀ i) ↔ τ.symm j ∈ E₁.block i :=
    mem_block_transport (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ) i j
  exact h₂.trans ((not_congr hb).trans h₁.symm)

attribute [grind =] eU_mem_support_v_transport

/-- The coordinate permutation `ρ` sends points of `U₁` into `U₂`. -/
public lemma map_U (x : Fin 24) :
    x ∈ E₁.U → ρ₀ x ∈ E₂.U := by
  intro hxU
  let j : Fin 11 := E₁.idxU x hxU
  have hx : E₁.eU j = x := Extraction.eU_idxU (E := E₁) x hxU
  have hρej : ρ₀ (E₁.eU j) = E₂.eU (τ j) := by
    simpa [ρ] using!
      (CoordTransport.coordPerm_eU (E₁ := E₁) (E₂ := E₂) τ
        π₀ j)
  have hρx : ρ₀ x = E₂.eU (τ j) := (congrArg ρ₀ hx).symm.trans hρej
  simp [hρx]

/-- The finset image of `U₁` under `ρ` is exactly `U₂`. -/
public lemma map_U_eq :
    (E₁.U).map (ρ₀).toEmbedding = E₂.U := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.1 hx with ⟨y, hy, rfl⟩
    exact map_U (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ) y hy
  · intro hxU2
    let j : Fin 11 := E₂.idxU x hxU2
    have hx : E₂.eU j = x := Extraction.eU_idxU (E := E₂) x hxU2
    refine Finset.mem_map.2 ?_
    refine ⟨E₁.eU (τ.symm j), Extraction.eU_mem_U (E := E₁) (τ.symm j), ?_⟩
    calc
      ρ₀ (E₁.eU (τ.symm j)) = E₂.eU j := by
        simpa [ρ] using!
          (CoordTransport.coordPerm_eU (E₁ := E₁) (E₂ := E₂) τ
            π₀ (τ.symm j))
      _ = x := hx

/-- The image of `support E₁.u` under `ρ` is `support E₂.u`. -/
public lemma map_support_u_eq :
    (support E₁.u).map (ρ₀).toEmbedding = support E₂.u := by
  -- `support u = insert p U`
  have hS₁ : insert E₁.p E₁.U = support E₁.u := Extraction.support_eq_insert_p_U (E := E₁)
  have hS₂ : insert E₂.p E₂.U = support E₂.u := Extraction.support_eq_insert_p_U (E := E₂)
  -- map both sides, using `ρ p = p` and `ρ(U₁) = U₂`.
  have hp : ρ₀ E₁.p = E₂.p := by
    dsimp [ρ]
    exact
      CoordTransport.coordPerm_p (E₁ := E₁) (E₂ := E₂) τ
        π₀
  -- start from `support u₁` and rewrite to `insert p₁ U₁`.
  rw [← hS₁]
  -- distribute `map` over `insert` and rewrite both images.
  calc
    (insert E₁.p E₁.U).map (ρ₀).toEmbedding
        = insert
            (ρ₀ E₁.p)
            (E₁.U.map (ρ₀).toEmbedding) := by
          simp
    _ = insert E₂.p E₂.U := by
          rw [hp, map_U_eq (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ)]
    _ = support E₂.u :=
          hS₂

/-- The dodecad word `u` is transported by `permuteWord σ`. -/
public lemma permuteWord_u :
    permuteWord (n := 24) σ₀ E₁.u = E₂.u := by
  let w :=
    permuteWord (n := 24) σ₀ E₁.u
  have hsupp : support w = support E₂.u := by
    simpa [w, σ, support_permuteWord] using!
      (map_support_u_eq (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ))
  funext x
  change w x = E₂.u x
  rw [word_apply_eq_ite_mem_support (w := w) (i := x),
    word_apply_eq_ite_mem_support (w := E₂.u) (i := x)]
  simp [w, hsupp]

/-- Transport the pinned lifts on `T`-coordinates. -/
public lemma permuteWord_v_fT (i : Fin 11) (k : Fin 12) :
    permuteWord (n := 24) σ₀ (E₁.v i) (E₂.fT k) = E₂.v (π₀ i) (E₂.fT k) := by
  have hxT2 : E₂.fT k ∈ E₂.T := Extraction.fT_mem_T (E := E₂) k
  have hxT1 :
      E₁.fT ((CoordTransport.permFin12 π₀).symm k) ∈ E₁.T :=
    Extraction.fT_mem_T (E := E₁) _
  -- rewrite both sides using the puncture-even normal form on `T`
  simp only [permuteWord_apply, σ, ρ, CoordTransport.coordPerm_symm_fT]
  rw [Extraction.v_apply_eq_evenBasisFamily_of_mem_T (E := E₁) (i := i) (hxT := hxT1),
    Extraction.v_apply_eq_evenBasisFamily_of_mem_T (E := E₂)
      (i := π₀ i) (hxT := hxT2)]
  rw [Extraction.evenBasisFamily_apply_fT (E := E₁) (i := i)
        (k := (CoordTransport.permFin12 π₀).symm k),
    Extraction.evenBasisFamily_apply_fT (E := E₂)
      (i := π₀ i) (k := k)]
  cases k using Fin.cases with
  | zero =>
      have h0 :
          (CoordTransport.permFin12 π₀).symm (0 : Fin 12) = (0 : Fin 12) := by
        simpa using! (CoordTransport.permFin12_symm_zero (π := π₀))
      simp [h0]
  | succ j =>
      simp [(π₀).symm_apply_eq]

/-- Transport the pinned lifts at the pinned coordinate `p`. -/
public lemma permuteWord_v_p (i : Fin 11) :
    permuteWord (n := 24) σ₀ (E₁.v i) E₂.p = E₂.v (π₀ i) E₂.p := by
  -- use the pinned coordinate.
  simp [Transported.σ, Transported.ρ, permuteWord_apply, CoordTransport.coordPerm_symm_p,
    E₁.hvp0, E₂.hvp0]

/-- Transport the pinned lifts on the `U`-coordinates. -/
public lemma permuteWord_v_eU (i : Fin 11) (j : Fin 11) :
    permuteWord (n := 24) σ₀ (E₁.v i) (E₂.eU j) = E₂.v (π₀ i) (E₂.eU j) := by
  grind (splits := 1) only
    [permuteWord_apply,
      Transported.σ, Transported.ρ,
      CoordTransport.coordPerm_symm_eU,
      word_apply_eq_ite_mem_support,
      eU_mem_support_v_transport (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ) i j]

/-- The full transport statement for pinned lifts: `permuteWord σ` sends `v₁ i` to `v₂ (π i)`. -/
public lemma permuteWord_v (i : Fin 11) :
    permuteWord (n := 24) σ₀ (E₁.v i) = E₂.v (π₀ i) := by
  funext x
  by_cases hxS : x ∈ support E₂.u
  · by_cases hxP : x = E₂.p
    · subst hxP
      simpa using! permuteWord_v_p (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ) i
    · -- `x ∈ U₂`, represent as `eU j`
      have hxU : x ∈ E₂.U := (E₂.mem_U_iff x).2 ⟨hxS, hxP⟩
      let j : Fin 11 := E₂.idxU x hxU
      have hx : E₂.eU j = x := Extraction.eU_idxU (E := E₂) x hxU
      -- rewrite the goal to the `eU`-indexed statement
      rw [← hx]
      exact permuteWord_v_eU (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ) i j
  · -- `x ∈ T₂`, represent as `fT k`
    have hxT : x ∈ E₂.T := (E₂.mem_T_iff_not_mem_support x).2 (by simpa using! hxS)
    let k : Fin 12 := E₂.idxT x hxT
    have hx : E₂.fT k = x := Extraction.fT_idxT (E := E₂) x hxT
    rw [← hx]
    exact permuteWord_v_fT (E₁ := E₁) (E₂ := E₂) (τ := τ) (hτ := hτ) i k

end

end GolayUniquenessSteps.WittDesignUniqueTheory.SharpGolayUniqueFromBiplaneAux.Transported

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
