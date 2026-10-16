-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.BiplaneFromSharp.Blocks
public import Mathlib.Data.Finset.Sort

/-!
# Extraction data for the biplane reduction

Starting from a sharp BS81 Golay input code `C`, the biplane reduction makes a sequence of
deterministic choices:
* choose a weight-`12` word `u`,
* choose a pinned coordinate `p ∈ support u`,
* enumerate the complement `T = univ \\ support u` as `t0` and `t : Fin 11 → Fin 24`,
* choose pinned lifts `v i`,
* build the biplane `D` on the `11` points `U = support u \\ {p}`.

This file packages all of this data in the structure `Extraction` and provides basic lemmas for
working with the resulting finsets and embeddings. Biplane uniqueness is later used to transport
the extracted generator data.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.SharpGolayUniqueFromBiplaneAux

noncomputable section

open scoped BigOperators
open GolayBounds
open GolayUniquenessSteps.CodeFromOctadsAux
open PunctureEven
open BiplaneFromSharp

local notation "Word" => BinWord 24

/-- The deterministic extraction data for the biplane reduction. -/
public structure Extraction (C : Code 24) (hC : IsSharpBS81GolayInput C) where
  u : Word
  huC : u ∈ C
  hwt : weight u = 12
  p : Fin 24
  hp : p ∈ support u

  /-- Complement of the dodecad support. -/
  T : Finset (Fin 24)
  hT : T = (Finset.univ : Finset (Fin 24)) \ support u
  hTcard : T.card = 12
  fT : Fin 12 ↪o Fin 24
  hfT : fT = T.orderEmbOfFin hTcard
  t0 : Fin 24
  ht0 : t0 = fT ⟨0, by decide⟩
  t : Fin 11 → Fin 24
  ht : t = fun i => fT (Fin.succ i)
  ht0_not : t0 ∉ support u
  ht_not : ∀ i, t i ∉ support u
  htinj : Function.Injective t
  hne : ∀ i, t0 ≠ t i

  /-- Pinned lifts of the even-basis family. -/
  v : Fin 11 → Word
  hvC : ∀ i, v i ∈ C
  hvp0 : ∀ i, v i p = 0
  hverase : ∀ i, eraseCoords (support u) (v i) = evenBasisFamily t0 t i

  /-- The `11`-set `U = supp u \\ {p}`. -/
  U : Finset (Fin 24)
  hU : U = (support u).erase p
  hUcard : U.card = 11
  eU : Fin 11 ↪o Fin 24
  heU : eU = U.orderEmbOfFin hUcard

  /-- Blocks as subsets of `Fin 11` (preimages under `eU`). -/
  block : Fin 11 → Finset (Fin 11)
  block_spec : ∀ i j, j ∈ block i ↔ eU j ∈ B u p (v i)
  blocks : Finset (Finset (Fin 11))
  hblocks : blocks = (Finset.univ : Finset (Fin 11)).image block
  block_inj : Function.Injective block

  /-- The extracted biplane structure. -/
  D : Biplane.Structure
  hD : D.blocks = blocks

namespace Extraction

attribute [simp] hT hU hfT ht ht0 heU hblocks hD

variable {C : Code 24} {hC : IsSharpBS81GolayInput C}

/-- Membership in the complement `T = univ \\ support u`. -/
public lemma mem_T_iff_not_mem_support (E : Extraction C hC) (x : Fin 24) :
    x ∈ E.T ↔ x ∉ support E.u := by
  simp

attribute [grind =] mem_T_iff_not_mem_support

lemma not_mem_T_iff_mem_support (E : Extraction C hC) (x : Fin 24) :
    x ∉ E.T ↔ x ∈ support E.u := by
  simp

/-- Membership in `U = (support u).erase p`. -/
public lemma mem_U_iff (E : Extraction C hC) (x : Fin 24) :
    x ∈ E.U ↔ x ∈ support E.u ∧ x ≠ E.p := by
  simp [Finset.mem_erase, and_comm]

attribute [grind =] mem_U_iff

/-- The pinned coordinate `p` lies in `support u`. -/
public lemma p_mem_support (E : Extraction C hC) : E.p ∈ support E.u := E.hp

lemma p_not_mem_T (E : Extraction C hC) : E.p ∉ E.T :=
  fun hpT => (mem_T_iff_not_mem_support (E := E) E.p).1 hpT E.hp

/-- The order embedding `eU : Fin 11 ↪o Fin 24` lands in `U`. -/
public lemma eU_mem_U (E : Extraction C hC) (j : Fin 11) : E.eU j ∈ E.U := by
  -- `eU = U.orderEmbOfFin ...`
  simp

/-- The order embedding `fT : Fin 12 ↪o Fin 24` lands in `T`. -/
public lemma fT_mem_T (E : Extraction C hC) (k : Fin 12) : E.fT k ∈ E.T := by
  simp

attribute [grind .] eU_mem_U fT_mem_T

/-- Points in the image of `eU` are never the pinned coordinate `p`. -/
public lemma eU_ne_p (E : Extraction C hC) (j : Fin 11) : E.eU j ≠ E.p :=
  (E.mem_U_iff (E.eU j)).1 (eU_mem_U (E := E) j) |>.2

section Indexing

variable {n : ℕ} (s : Finset (Fin 24)) (hs : s.card = n)

/-- The `Fin n` index of a point in a finset `s` (defined using `orderIsoOfFin`). -/
public def idx (x : Fin 24) (hx : x ∈ s) : Fin n :=
  (s.orderIsoOfFin hs).symm ⟨x, hx⟩

/-- `orderEmbOfFin` inverts `idx`. -/
public lemma orderEmbOfFin_idx (x : Fin 24) (hx : x ∈ s) :
    s.orderEmbOfFin hs (idx s hs x hx) = x := by
  have hIso : s.orderIsoOfFin hs (idx s hs x hx) = ⟨x, hx⟩ := by
    simp [idx]
  have hval := congrArg (fun y : {z // z ∈ s} => (y : Fin 24)) hIso
  simpa [Finset.coe_orderIsoOfFin_apply] using! hval

/-- `idx` inverts `orderEmbOfFin` on points that lie in the finset. -/
public lemma idx_orderEmbOfFin_of_mem (k : Fin n) (hx : s.orderEmbOfFin hs k ∈ s) :
    idx s hs (s.orderEmbOfFin hs k) hx = k :=
  (s.orderEmbOfFin hs).injective <| by
    simpa using! orderEmbOfFin_idx (s := s) (hs := hs) (x := s.orderEmbOfFin hs k) (hx := hx)

end Indexing

/-- The `Fin 12` index of a point in `T` (defined using `orderIsoOfFin`). -/
public def idxT (E : Extraction C hC) (x : Fin 24) (hx : x ∈ E.T) : Fin 12 :=
  idx (s := E.T) (hs := E.hTcard) x hx

/-- The index `idxT` does not depend on the choice of proof of membership. -/
public lemma idxT_congr (E : Extraction C hC) (x : Fin 24) (hx₁ hx₂ : x ∈ E.T) :
    idxT E x hx₁ = idxT E x hx₂ := by
  rfl

/-- Applying `fT` to `idxT` recovers the original point in `T`. -/
public lemma fT_idxT (E : Extraction C hC) (x : Fin 24) (hx : x ∈ E.T) :
    E.fT (idxT E x hx) = x := by
  simpa [E.hfT, idxT] using!
    orderEmbOfFin_idx (s := E.T) (hs := E.hTcard) (x := x) (hx := hx)

attribute [grind =] fT_idxT

/-- The index of a point of the form `fT k` is `k`. -/
public lemma idxT_fT (E : Extraction C hC) (k : Fin 12) :
    idxT E (E.fT k) (fT_mem_T (E := E) k) = k := by
  simpa [E.hfT, idxT] using!
    idx_orderEmbOfFin_of_mem (s := E.T) (hs := E.hTcard) (k := k)
      (hx := by simp)

attribute [grind =] idxT_fT

/-- A variant of `idxT_fT` using an arbitrary membership proof. -/
public lemma idxT_fT_of_mem (E : Extraction C hC) (k : Fin 12) (hx : E.fT k ∈ E.T) :
    idxT E (E.fT k) hx = k :=
  (idxT_congr (E := E) (x := E.fT k) (hx₁ := hx) (hx₂ := fT_mem_T (E := E) k)).trans
    (idxT_fT (E := E) k)

/-- The `Fin 11` index of a point in `U` (defined using `orderIsoOfFin`). -/
public def idxU (E : Extraction C hC) (x : Fin 24) (hx : x ∈ E.U) : Fin 11 :=
  idx (s := E.U) (hs := E.hUcard) x hx

/-- The index `idxU` does not depend on the choice of proof of membership. -/
public lemma idxU_congr (E : Extraction C hC) (x : Fin 24) (hx₁ hx₂ : x ∈ E.U) :
    idxU E x hx₁ = idxU E x hx₂ := by
  rfl

/-- Applying `eU` to `idxU` recovers the original point in `U`. -/
public lemma eU_idxU (E : Extraction C hC) (x : Fin 24) (hx : x ∈ E.U) :
    E.eU (idxU E x hx) = x := by
  simpa [E.heU, idxU] using!
    orderEmbOfFin_idx (s := E.U) (hs := E.hUcard) (x := x) (hx := hx)

attribute [grind =] eU_idxU

/-- The index of a point of the form `eU j` is `j`. -/
public lemma idxU_eU (E : Extraction C hC) (j : Fin 11) :
    idxU E (E.eU j) (eU_mem_U (E := E) j) = j := by
  simpa [E.heU, idxU] using!
    idx_orderEmbOfFin_of_mem (s := E.U) (hs := E.hUcard) (k := j)
      (hx := by simp)

attribute [grind =] idxU_eU

/-- A variant of `idxU_eU` using an arbitrary membership proof. -/
public lemma idxU_eU_of_mem (E : Extraction C hC) (j : Fin 11) (hx : E.eU j ∈ E.U) :
    idxU E (E.eU j) hx = j :=
  (idxU_congr (E := E) (x := E.eU j) (hx₁ := hx) (hx₂ := eU_mem_U (E := E) j)).trans
    (idxU_eU (E := E) j)

/-- Decompose `support u` into the pinned point `p` and the remaining set `U`. -/
public lemma support_eq_insert_p_U (E : Extraction C hC) :
    insert E.p E.U = support E.u := by
  -- `U = (support u).erase p` and `p ∈ support u`.
  simpa [E.hU] using! (Finset.insert_erase E.hp)

/--
Membership in the biplane block `B u p (v i)` is the complement of membership in
`support (v i)`.
-/
public lemma mem_B_iff_not_mem_support_v (E : Extraction C hC) (i : Fin 11) (j : Fin 11) :
    E.eU j ∈ B E.u E.p (E.v i) ↔ E.eU j ∉ support (E.v i) := by
  have hj : E.eU j ∈ support E.u ∧ E.eU j ≠ E.p :=
    (E.mem_U_iff (E.eU j)).1 (eU_mem_U (E := E) j)
  simp [BiplaneFromSharp.mem_B_iff, hj.1, hj.2, -Extraction.heU]

attribute [grind =] mem_B_iff_not_mem_support_v

/-- A point `eU j` lies in `support (v i)` if and only if `j` is not in the pulled-back block. -/
public lemma eU_mem_support_v_iff_not_mem_block (E : Extraction C hC) (i : Fin 11) (j : Fin 11) :
    E.eU j ∈ support (E.v i) ↔ j ∉ E.block i := by
  grind only [= Extraction.block_spec, = mem_B_iff_not_mem_support_v]

attribute [grind =] eU_mem_support_v_iff_not_mem_block

/-- On the complement set `T`, the pinned lift `v i` agrees with `evenBasisFamily`. -/
public lemma v_apply_eq_evenBasisFamily_of_mem_T (E : Extraction C hC) (i : Fin 11) {x : Fin 24}
    (hxT : x ∈ E.T) :
    E.v i x = evenBasisFamily E.t0 E.t i x := by
  have hxS : x ∉ support E.u := (E.mem_T_iff_not_mem_support x).1 hxT
  -- outside `support u`, `eraseCoords` is the identity
  simpa [eraseCoords, hxS] using! congrArg (fun w : BinWord 24 => w x) (E.hverase i)

/-- Evaluate `evenBasisFamily` on the `T`-embedding `fT : Fin 12 ↪o Fin 24`. -/
public lemma evenBasisFamily_apply_fT (E : Extraction C hC) (i : Fin 11) (k : Fin 12) :
    evenBasisFamily E.t0 E.t i (E.fT k) =
      (if k = ⟨0, Nat.succ_pos 11⟩ ∨ k = Fin.succ i then (1 : ZMod 2) else 0) := by
  -- reduce by cases on `k : Fin 12`
  cases k using Fin.cases with
  | zero =>
      -- `k = 0`
      simp [BiplaneFromSharp.evenBasisFamily, BiplaneFromSharp.evenBasisWord, wordOfFinset]
  | succ j =>
      -- `k = succ j`
      by_cases hj : j = i <;>
        simp [BiplaneFromSharp.evenBasisFamily, BiplaneFromSharp.evenBasisWord, wordOfFinset, hj]

attribute [grind =] evenBasisFamily_apply_fT

end Extraction

/-- Build the full extraction data (no choice left implicit). -/
public noncomputable def extract (C : Code 24) (hC : IsSharpBS81GolayInput C) :
    Extraction C hC := by
  -- choose a dodecad `u`
  let u : Word := Classical.choose (exists_weight12_word_of_sharp (C := C) hC)
  have hu_spec :
      u ∈ C ∧ weight u = 12 := Classical.choose_spec (exists_weight12_word_of_sharp (C := C) hC)
  have huC : u ∈ C := hu_spec.1
  have hwt : weight u = 12 := hu_spec.2
  have hScard : (support u).card = 12 := by
    simpa [GolayBounds.weight_eq_card_support] using! hwt
  have hSnonempty : (support u).Nonempty :=
    Finset.card_pos.1 (by simp [hScard] : 0 < (support u).card)
  let p : Fin 24 := (support u).min' hSnonempty
  have hp : p ∈ support u := Finset.min'_mem (support u) hSnonempty
  -- enumerate the complement `T = univ \\ support u` as `t0` and `t : Fin 11 → Fin 24`
  let T : Finset (Fin 24) := (Finset.univ : Finset (Fin 24)) \ support u
  have hTcard : T.card = 12 := by
    have huniv : (Finset.univ : Finset (Fin 24)).card = 24 := by simp
    have : T.card = (Finset.univ : Finset (Fin 24)).card - (support u).card := by
      simp [T, Finset.card_sdiff, Finset.inter_comm]
    calc
      T.card = 24 - 12 := by simpa [huniv, hScard] using! this
      _ = 12 := by decide
  let fT : Fin 12 ↪o Fin 24 := T.orderEmbOfFin hTcard
  let t0 : Fin 24 := fT ⟨0, by decide⟩
  let t : Fin 11 → Fin 24 := fun i => fT (Fin.succ i)
  have ht0 : t0 ∉ support u := by
    have ht0' : t0 ∈ T := by simp [t0, fT]
    have : t0 ∈ (Finset.univ : Finset (Fin 24)) \ support u := by
      simpa [T] using! ht0'
    exact (Finset.mem_sdiff.1 this).2
  have ht : ∀ i : Fin 11, t i ∉ support u := by
    intro i
    have ht' : t i ∈ T := by simp [t, fT]
    have : t i ∈ (Finset.univ : Finset (Fin 24)) \ support u := by
      simpa [T] using! ht'
    exact (Finset.mem_sdiff.1 this).2
  have htinj : Function.Injective t := by
    intro i j hij
    have : (Fin.succ i : Fin 12) = Fin.succ j := fT.injective hij
    exact (Fin.succ_injective 11) this
  have hne : ∀ i : Fin 11, t0 ≠ t i := by
    intro i h
    have : (⟨0, by decide⟩ : Fin 12) = Fin.succ i :=
      fT.injective (by simpa [t0, t] using! h)
    exact (Fin.succ_ne_zero i) this.symm
  -- choose pinned lifts
  have hv_ex :
      ∃ v : Fin 11 → Word,
        (∀ i, v i ∈ C) ∧ (∀ i, v i p = 0) ∧
          (∀ i, eraseCoords (support u) (v i) = evenBasisFamily t0 t i) :=
    BiplaneFromSharp.exists_pinned_lifts_of_sharp (C := C) hC (huC := huC) (hwt := hwt)
      (hp := hp) (t0 := t0) (t := t) ht0 ht hne
  let v : Fin 11 → Word := Classical.choose hv_ex
  have hv_spec :
      (∀ i, v i ∈ C) ∧ (∀ i, v i p = 0) ∧
        (∀ i, eraseCoords (support u) (v i) = evenBasisFamily t0 t i) :=
    Classical.choose_spec hv_ex
  have hvC : ∀ i, v i ∈ C := hv_spec.1
  have hvp0 : ∀ i, v i p = 0 := hv_spec.2.1
  have hverase : ∀ i, eraseCoords (support u) (v i) = evenBasisFamily t0 t i := hv_spec.2.2
  -- build blocks on `Fin 11` by pulling back `B u p (v i) ⊆ (support u).erase p`.
  let U : Finset (Fin 24) := (support u).erase p
  have hUcard : U.card = 11 := by simpa [U, hScard] using! (Finset.card_erase_of_mem hp)
  let eU : Fin 11 ↪o Fin 24 := U.orderEmbOfFin hUcard
  let pre (S : Finset (Fin 24)) : Finset (Fin 11) :=
    (Finset.univ : Finset (Fin 11)).filter fun i => eU i ∈ S
  have card_pre {S : Finset (Fin 24)} (hS : S ⊆ U) : (pre S).card = S.card := by
    have himage_univ : Finset.image eU (Finset.univ : Finset (Fin 11)) = U := by
      simp [eU]
    have himage : Finset.image eU (pre S) = S := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.1 hx with ⟨i, hi, rfl⟩
        exact (Finset.mem_filter.1 hi).2
      · intro hx
        have hxU : x ∈ U := hS hx
        have hxImg : x ∈ Finset.image eU (Finset.univ : Finset (Fin 11)) := by
          simpa [himage_univ] using! hxU
        rcases Finset.mem_image.1 hxImg with ⟨i, hiU, rfl⟩
        refine Finset.mem_image.2 ?_
        refine ⟨i, ?_, rfl⟩
        exact Finset.mem_filter.2 ⟨hiU, hx⟩
    have hinj : Function.Injective eU := eU.injective
    have hcard : (Finset.image eU (pre S)).card = (pre S).card := by
      simpa using! Finset.card_image_of_injective (s := pre S) hinj
    simpa [himage] using! hcard.symm
  have pre_inter (S S' : Finset (Fin 24)) : pre S ∩ pre S' = pre (S ∩ S') := by
    ext x
    simp [pre]
  -- We expand `B u p (v i)` to `U \\ K u p (v i)` to keep later rewriting lightweight.
  let blockU (i : Fin 11) : Finset (Fin 24) := U \ K u p (v i)
  have hblockU_subset : ∀ i, blockU i ⊆ U := by
    intro i
    simp [blockU]
  let block (i : Fin 11) : Finset (Fin 11) := pre (blockU i)
  let blocks : Finset (Finset (Fin 11)) := (Finset.univ : Finset (Fin 11)).image block
  have hblockU_card : ∀ i, (blockU i).card = 5 := by
    intro i
    have hK : (K u p (v i)).card = 6 :=
      BiplaneFromSharp.K_card_eq_six_of_sharp (C := C) hC huC hwt hp ht0 hne hvC hvp0 hverase i
    have hsub : K u p (v i) ⊆ U := by
      intro x hx
      exact (Finset.mem_inter.1 hx).2
    have : (blockU i).card = U.card - (K u p (v i)).card := by
      -- `|U \\ K| = |U| - |K|` since `K ⊆ U`.
      exact Finset.card_sdiff_of_subset hsub
    omega
  have hinterU_card : ∀ i j, i ≠ j → (blockU i ∩ blockU j).card = 2 := by
    intro i j hij
    have hKi : (K u p (v i)).card = 6 :=
      K_card_eq_six_of_sharp (C := C) hC huC hwt hp ht0 hne hvC hvp0 hverase i
    have hKj : (K u p (v j)).card = 6 :=
      K_card_eq_six_of_sharp (C := C) hC huC hwt hp ht0 hne hvC hvp0 hverase j
    have hKij : (K u p (v i) ∩ K u p (v j)).card = 3 :=
      K_inter_card_eq_three_of_sharp (C := C) hC huC hwt hp ht0 ht htinj hne hvC hvp0
        hverase i j hij
    have hunion : (K u p (v i) ∪ K u p (v j)).card = 9 := by
      have := Finset.card_union_add_card_inter (K u p (v i)) (K u p (v j))
      omega
    have hEq' :
        (U \ K u p (v i)) ∩ (U \ K u p (v j)) = U \ (K u p (v i) ∪ K u p (v j)) :=
      (Finset.sdiff_union_distrib (s := U) (t₁ := K u p (v i)) (t₂ := K u p (v j))).symm
    have hEq : blockU i ∩ blockU j = U \ (K u p (v i) ∪ K u p (v j)) := by
      simpa [blockU] using! hEq'
    have hsub : (K u p (v i) ∪ K u p (v j)) ⊆ U := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact (Finset.mem_inter.1 hx).2
      · exact (Finset.mem_inter.1 hx).2
    have hcard_sdiff :
        (U \ (K u p (v i) ∪ K u p (v j))).card =
          U.card - (K u p (v i) ∪ K u p (v j)).card := by
      exact Finset.card_sdiff_of_subset hsub
    have : (blockU i ∩ blockU j).card = U.card - (K u p (v i) ∪ K u p (v j)).card := by
      simp [hEq, hcard_sdiff]
    omega
  have hblock_card : ∀ B ∈ blocks, B.card = 5 := by
    intro B hB
    rcases Finset.mem_image.1 hB with ⟨i, _, rfl⟩
    have : (block i).card = (blockU i).card := by
      simpa [block, pre] using! card_pre (S := blockU i) (hS := hblockU_subset i)
    simp [this, hblockU_card i]
  have hcard_inter_block : ∀ i j, (block i ∩ block j).card = (blockU i ∩ blockU j).card := by
    intro i j
    have hsub : blockU i ∩ blockU j ⊆ U := by
      intro x hx
      exact hblockU_subset i (Finset.mem_inter.1 hx).1
    have hpre_inter : block i ∩ block j = pre (blockU i ∩ blockU j) := by
      simpa [block] using! pre_inter (blockU i) (blockU j)
    simpa [hpre_inter] using! (card_pre (S := blockU i ∩ blockU j) hsub)
  have hinter_card :
      ∀ ⦃B B'⦄, B ∈ blocks → B' ∈ blocks → B ≠ B' → (B ∩ B').card = 2 := by
    intro B B' hB hB' hne'
    rcases Finset.mem_image.1 hB with ⟨i, _, rfl⟩
    rcases Finset.mem_image.1 hB' with ⟨j, _, rfl⟩
    have hij : i ≠ j := by
      exact ne_of_apply_ne block hne'
    simp [hcard_inter_block i j, hinterU_card i j hij]
  have hinj_block : Function.Injective block := by
    intro i j hij
    by_contra hne
    have hinterij : (block i ∩ block j).card = 2 := by
      simpa [hcard_inter_block i j] using! hinterU_card i j hne
    have hcardi : (block i).card = 5 := hblock_card (block i) (by simp [blocks])
    have hcardi2 : (block i).card = 2 := by simpa [hij] using! hinterij
    grind only
  have hblocks_card : blocks.card = 11 := by
    simp [blocks, Finset.card_image_of_injective, hinj_block]
  let D : Biplane.Structure :=
    { blocks := blocks
      blocks_card := hblocks_card
      block_card := hblock_card
      inter_card := by
        intro B B' hB hB' hne'
        exact hinter_card (B := B) (B' := B') hB hB' hne' }
  refine
    { u := u
      huC := huC
      hwt := hwt
      p := p
      hp := hp
      T := T
      hT := rfl
      hTcard := hTcard
      fT := fT
      hfT := rfl
      t0 := t0
      ht0 := rfl
      t := t
      ht := rfl
      ht0_not := ht0
      ht_not := ht
      htinj := htinj
      hne := hne
      v := v
      hvC := hvC
      hvp0 := hvp0
      hverase := hverase
      U := U
      hU := rfl
      hUcard := hUcard
      eU := eU
      heU := rfl
      block := block
      block_spec := by
        intro i j
        -- unfold `blockU` back to `B u p (v i)` for the API field
        simp [block, pre, blockU, B, U]
      blocks := blocks
      hblocks := rfl
      block_inj := hinj_block
      D := D
      hD := rfl }

end

end GolayUniquenessSteps.WittDesignUniqueTheory.SharpGolayUniqueFromBiplaneAux

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
