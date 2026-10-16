-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Orthogonality
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.DotSupportLite
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.ClassicalWitt.DesignCodeCard
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpInput
public import
 SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.ClassicalWitt.CodeFromDes
public import
 SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.ClassicalWitt.BlockInter
public import
 SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctads.WordFinset
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittParams

/-!
# From a Witt design to sharp Golay input data

Given `S : SteinerSystem 24 8 5`, we define the code `designCode S` spanned by block indicator
vectors and prove it satisfies `IsSharpBS81GolayInput`. The key bridge lemma is
`octadsFromCode_designCode_eq_blocks`, identifying the octads of `designCode S` with the blocks of
the original design.

References:
- `paper/Bro08Witt/brouwer_witt_designs_golay_mathieu.tex` (Golay/Witt design interface).
- `paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex` (in-repo, gap-free target).
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.ClassicalWitt

noncomputable section

open scoped symmDiff
open CodeFromOctadsAux GolayBounds

/-- The code spanned by indicator vectors of blocks of `S`. -/
@[expose] public def designCode (S : SteinerSystem 24 8 5) : Code 24 := codeFromSteinerSystem S

/-- The code `designCode S` is a linear code. -/
public lemma designCode_linear (S : SteinerSystem 24 8 5) : IsLinearCode (designCode S) :=
  isLinearCode_codeFromSteinerSystem (S := S)

/-!
### Basic facts: generators and block count

These are small supporting lemmas used repeatedly in the later proofs.
-/

/-- Every block of `S` is an octad in the code `designCode S`. -/
public lemma blocks_subset_octadsFromCode_designCode (S : SteinerSystem 24 8 5) :
    S.blocks ⊆ octadsFromCode (designCode S) := by
  intro B hB
  refine ⟨wordOfFinset (n := 24) B, ?_, ?_, ?_⟩
  · change wordOfFinset (n := 24) B ∈ (blockSubmodule S.blocks : Set (BinWord 24))
    exact wordOfFinset_mem_blockSubmodule_of_mem_blocks (S := S) hB
  · -- weight is card of support, which is card of `B`, hence `8`.
    have hcard : B.card = 8 := S.block_card B hB
    simp [GolayBounds.weight_eq_card_support, support_wordOfFinset, hcard]
  · simp [support_wordOfFinset]

/-- A Witt design has `759` blocks. -/
public lemma ncard_blocks_eq_759 (S : SteinerSystem 24 8 5) :
    Set.ncard S.blocks = 759 := by
  have hfin : S.blocksFinset.card = 759 := WittParams.card_blocks (S := S)
  -- convert `blocksFinset.card` to `Set.ncard blocks`
  simpa [SteinerSystem.card_blocksFinset_eq_ncard_blocks (S := S)] using! hfin

/-!
### Structural properties of `designCode S`

These are the fields of `IsSharpBS81GolayInput` and the key bridge lemma
`octadsFromCode (designCode S) = S.blocks`.
-/

/-- The code `designCode S` has cardinality `2 ^ 12`. -/
public lemma designCode_card_eq (S : SteinerSystem 24 8 5) :
    Set.ncard (designCode S) = 2 ^ 12 := by
  simpa [designCode] using! codeFromSteinerSystem_ncard_eq_two_pow_12 (S := S)

/-- The code `designCode S` is self-orthogonal with respect to the dot product. -/
public lemma designCode_selfOrth (S : SteinerSystem 24 8 5) :
    IsSelfOrthogonal (designCode S) := by
  intro x y hx hy
  have hx' : x ∈ blockSubmodule S.blocks := by
    simpa [designCode, codeFromSteinerSystem, codeFromBlocks] using! hx
  have hy' : y ∈ blockSubmodule S.blocks := by
    simpa [designCode, codeFromSteinerSystem, codeFromBlocks] using! hy
  exact dot_eq_zero_of_mem_blockSubmodule (S := S) hx' hy'

/-- The code `designCode S` is doubly even: every codeword has weight divisible by `4`. -/
public lemma designCode_doublyEven (S : SteinerSystem 24 8 5) :
    IsDoublyEven (designCode S) := by
  intro w hw
  -- Convert membership in the code (a `Set`) to membership in the spanning submodule.
  have hwSub : w ∈ blockSubmodule S.blocks := by
    simpa [designCode, codeFromSteinerSystem, codeFromBlocks] using! hw
  change w ∈ Submodule.span (ZMod 2) (blockWordSet S.blocks) at hwSub
  -- Induction over the span.
  refine
    Submodule.span_induction (p := fun w _ => 4 ∣ weight w)
      (x := w) ?_ (by simp [weight]) ?_ ?_ hwSub
  · intro w hw
    rcases hw with ⟨B, hB, rfl⟩
    have hcard : B.card = 8 := S.block_card B hB
    -- `weight(wordOfFinset B) = B.card = 8`.
    simp [GolayBounds.weight_eq_card_support, support_wordOfFinset, hcard]
  · intro x y hx hy hx4 hy4
    -- Use the symmDiff card identity and evenness of intersections coming from self-orthogonality.
    have hx' : x ∈ blockSubmodule S.blocks := by
      simpa [blockSubmodule] using! hx
    have hy' : y ∈ blockSubmodule S.blocks := by
      simpa [blockSubmodule] using! hy
    have hdot : dot (n := 24) x y = 0 := dot_eq_zero_of_mem_blockSubmodule (S := S) hx' hy'
    have hEven : Even (support x ∩ support y).card :=
      (DotSupportLite.dot_eq_zero_iff_even_card_support_inter (w₁ := x) (w₂ := y)).1 hdot
    have hx4' : 4 ∣ (support x).card := by simpa [GolayBounds.weight_eq_card_support] using! hx4
    have hy4' : 4 ∣ (support y).card := by simpa [GolayBounds.weight_eq_card_support] using! hy4
    have hsum4 : 4 ∣ (support x).card + (support y).card := Nat.dvd_add hx4' hy4'
    have hinter4 : 4 ∣ 2 * (support x ∩ support y).card := by
      rcases hEven with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      -- `2 * (m+m) = 4*m`.
      have : 2 * (m + m) = 4 * m := by omega
      simpa [hm, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using! this
    have hcardEq :
        (support x ∆ support y).card + 2 * (support x ∩ support y).card =
          (support x).card + (support y).card :=
      card_symmDiff_add_two_mul_card_inter (A := support x) (B := support y)
    have hsymm4 : 4 ∣ (support x ∆ support y).card := by
      have hsum4' : 4 ∣ (support x ∆ support y).card + 2 * (support x ∩ support y).card := by
        rcases hsum4 with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        calc
          (support x ∆ support y).card + 2 * (support x ∩ support y).card
              = (support x).card + (support y).card := hcardEq
          _ = 4 * k := hk
      exact (Nat.dvd_add_iff_left hinter4).mpr hsum4'
    -- Translate back to weights.
    have hsupp : support (x + y) = support x ∆ support y := by
      simpa using! (GolayBounds.support_add_eq_symmDiff (w₁ := x) (w₂ := y))
    have hwt : weight (x + y) = (support x ∆ support y).card := by
      simp [GolayBounds.weight_eq_card_support, hsupp]
    simpa [hwt] using! hsymm4
  · intro a x hx hx4
    rcases GolayBounds.zmod2_eq_zero_or_eq_one a with rfl | rfl
    · simp [weight]
    · simpa using! hx4

/-!
### Minimum distance

We show `minDist (designCode S) = 8`.

Outline:
- `minDist ≤ 8` by exhibiting any block word of weight `8`.
- `minDist ≥ 8` because the code is doubly even and self-orthogonal, hence has no weight-`4`
  codewords (a weight-`4` support would meet some block in `3` points).
  -/

/-- The code `designCode S` contains a nonzero codeword of weight `8`. -/
public lemma exists_nonzero_mem_designCode_weight_eq_8 (S : SteinerSystem 24 8 5) :
    ∃ w : BinWord 24, w ∈ designCode S ∧ w ≠ 0 ∧ weight w = 8 := by
  have hcard : S.blocksFinset.card = 759 := WittParams.card_blocks (S := S)
  have hpos : 0 < S.blocksFinset.card := by
    rw [hcard]
    decide
  rcases Finset.card_pos.1 hpos with ⟨B, hBfin⟩
  have hB : B ∈ S.blocks := (SteinerSystem.mem_blocksFinset _ _).1 hBfin
  have hBcode : wordOfFinset (n := 24) B ∈ designCode S := by
    change wordOfFinset (n := 24) B ∈ (blockSubmodule S.blocks : Set (BinWord 24))
    exact wordOfFinset_mem_blockSubmodule_of_mem_blocks (S := S) hB
  have hw8 : weight (wordOfFinset (n := 24) B) = 8 := by
    have hBcard : B.card = 8 := S.block_card B hB
    simp [GolayBounds.weight_eq_card_support, support_wordOfFinset, hBcard]
  refine ⟨wordOfFinset (n := 24) B, hBcode, ?_, hw8⟩
  intro hEq
  have hw0 : weight (wordOfFinset (n := 24) B) = 0 := by simpa [hEq] using! (by simp [weight])
  have : (8 : ℕ) = 0 := hw8.symm.trans hw0
  exact (by decide : (8 : ℕ) ≠ 0) this

/-- The code `designCode S` has no codeword of weight `4`. -/
public lemma no_weight4_mem_designCode
    (S : SteinerSystem 24 8 5) {w : BinWord 24} (hw : w ∈ designCode S)
    (hw4 : weight w = 4) :
    False := by
  -- Let `T = support w`.
  let T : Finset (Fin 24) := support w
  have hTcard : T.card = 4 := by simpa [T, GolayBounds.weight_eq_card_support] using! hw4
  -- Find a block meeting `T` in exactly `3` points.
  rcases exists_block_inter_card_eq_three (S := S) (T := T) hTcard with ⟨B, hB, hTB⟩
  have hBcode : wordOfFinset (n := 24) B ∈ designCode S :=
    by
      change wordOfFinset (n := 24) B ∈ (blockSubmodule S.blocks : Set (BinWord 24))
      exact wordOfFinset_mem_blockSubmodule_of_mem_blocks (S := S) hB
  have hdot0 : dot (n := 24) w (wordOfFinset (n := 24) B) = 0 :=
    designCode_selfOrth (S := S) hw hBcode
  -- But `dot w (wordOfFinset B) = card (T ∩ B)` mod 2, which is `1`.
  have hdot :
      dot (n := 24) w (wordOfFinset (n := 24) B) =
        ((T ∩ B).card : ZMod 2) := by
    simpa [T, support_wordOfFinset] using!
      (DotSupportLite.dot_eq_card_support_inter (w₁ := w) (w₂ := wordOfFinset (n := 24) B))
  have hodd : ((T ∩ B).card : ZMod 2) ≠ 0 := by
    -- `card = 3` implies cast is nonzero.
    simpa [hTB] using! (show ((3 : ℕ) : ZMod 2) ≠ 0 from by decide)
  exact hodd (by simpa [hdot] using! hdot0)

/-- Every nonzero codeword in `designCode S` has weight at least `8`. -/
public lemma weight_ge_8_of_mem_designCode_of_ne_zero
    (S : SteinerSystem 24 8 5) {w : BinWord 24} (hw : w ∈ designCode S) (h0 : w ≠ 0) :
    8 ≤ weight w := by
  have h4 : 4 ∣ weight w := designCode_doublyEven (S := S) hw
  have hne4 : weight w ≠ 4 := by
    intro hw4
    exact no_weight4_mem_designCode (S := S) hw hw4
  have hpos : 0 < weight w := by
    by_contra h0w
    have hw0 : weight w = 0 := Nat.eq_zero_of_not_pos h0w
    -- `weight w = 0` forces `support w = ∅`, hence `w = 0`.
    have hsupp0 : support w = ∅ := by
      have : (support w).card = 0 := by simpa [GolayBounds.weight_eq_card_support] using! hw0
      exact Finset.card_eq_zero.1 this
    have hwzero : w = 0 := by
      funext i
      have hi : i ∉ support w := by simp [hsupp0]
      simpa using! (GolayBounds.eq_zero_of_not_mem_support (w := w) (i := i) hi)
    exact h0 hwzero
  -- If `weight w < 8`, then since `4 ∣ weight w` and `weight w > 0` we would have `weight w = 4`.
  by_contra hlt8
  have hlt : weight w < 8 := Nat.lt_of_not_ge hlt8
  rcases h4 with ⟨k, hk⟩
  have hlt' : 4 * k < 8 := by simpa [hk] using! hlt
  have hk_lt2 : k < 2 := by omega
  have hk_pos : 0 < k := by
    have : 0 < 4 * k := by simpa [hk] using! hpos
    omega
  have hk_eq1 : k = 1 := by omega
  simp_all

/-- The minimum distance of `designCode S` is `8`. -/
public lemma designCode_minDist_eq (S : SteinerSystem 24 8 5) :
    minDist (designCode S) = 8 := by
  obtain ⟨w, hwC, hwne0, hw8⟩ := exists_nonzero_mem_designCode_weight_eq_8 (S := S)
  have h0mem : (0 : BinWord 24) ∈ designCode S := (designCode_linear (S := S)).1
  have hdist0 : hammingDist (0 : BinWord 24) w = 8 := by
    have : hammingDist (0 : BinWord 24) w = weight w := by
      simp [hammingDist]
    simpa [hw8] using! this
  -- First, `minDist ≤ 8` by exhibiting a block word.
  have hle : minDist (designCode S) ≤ 8 := by
    have hmem :
        8 ∈ {d : ℕ | ∃ x y : BinWord 24,
          x ∈ designCode S ∧ y ∈ designCode S ∧ x ≠ y ∧ hammingDist x y = d} := by
      have h0w : (0 : BinWord 24) ≠ w := by simpa [eq_comm] using! hwne0
      exact ⟨0, w, h0mem, hwC, h0w, hdist0⟩
    exact Nat.sInf_le hmem
  -- Second, `8 ≤ minDist`: if `minDist < 8`, `Nat.sInf_mem` produces a pair at that distance.
  have hge : 8 ≤ minDist (designCode S) := by
    by_contra hlt
    have hlt' : minDist (designCode S) < 8 := Nat.lt_of_not_ge hlt
    -- Let `D` be the set of realized distances; it is nonempty since `8` is realized.
    let D : Set ℕ :=
      {d : ℕ | ∃ x y : BinWord 24,
        x ∈ designCode S ∧ y ∈ designCode S ∧ x ≠ y ∧ hammingDist x y = d}
    have hminDist : minDist (designCode S) = sInf D := rfl
    have hDne : D.Nonempty := by
      refine ⟨8, ?_⟩
      have h0w : (0 : BinWord 24) ≠ w := by simpa [eq_comm] using! hwne0
      exact ⟨0, w, h0mem, hwC, h0w, hdist0⟩
    have hsInf_mem : minDist (designCode S) ∈ D := by
      simpa [hminDist] using! (Nat.sInf_mem (s := D) hDne)
    rcases hsInf_mem with ⟨x, y, hx, hy, hxy, hdist⟩
    -- But all nontrivial distances are at least `8`.
    have hlin : IsLinearCode (designCode S) := designCode_linear (S := S)
    have hxy' : (fun i => x i + y i) ≠ 0 := by
      intro h0
      have hxy0 : x + y = 0 := by simpa using! h0
      exact hxy ((GolayBounds.binWord_add_eq_zero_iff_eq (u := x) (v := y)).1 hxy0)
    have hsum_mem : (fun i => x i + y i) ∈ designCode S := hlin.2 x y hx hy
    have hdist_ge : 8 ≤ hammingDist x y := by
      have hwt_ge : 8 ≤ weight (fun i => x i + y i) :=
        weight_ge_8_of_mem_designCode_of_ne_zero (S := S) hsum_mem hxy'
      simpa [hammingDist] using! hwt_ge
    have hdist_eq : hammingDist x y = minDist (designCode S) := by
      simpa [D] using! hdist
    have hdist_lt : hammingDist x y < 8 := by
      simpa [hdist_eq] using! hlt'
    exact (not_lt_of_ge hdist_ge) hdist_lt
  exact le_antisymm hle hge

/-- The set `weight8Words (designCode S)` has cardinality `759`. -/
public lemma designCode_weight8_card (S : SteinerSystem 24 8 5) :
    Set.ncard (weight8Words (designCode S)) = 759 := by
  -- Lower bound: each block gives a distinct weight-8 codeword.
  have hinj : Function.Injective (wordOfFinset (n := 24)) := by
    intro B B' h
    have := congrArg support h
    simpa [support_wordOfFinset] using! this
  have hsubset :
      (wordOfFinset (n := 24)) '' S.blocks ⊆ weight8Words (designCode S) := by
    intro w hw
    rcases hw with ⟨B, hB, rfl⟩
    refine ⟨?_, ?_⟩
    · change wordOfFinset (n := 24) B ∈ (blockSubmodule S.blocks : Set (BinWord 24))
      exact wordOfFinset_mem_blockSubmodule_of_mem_blocks (S := S) hB
    have hcard : B.card = 8 := S.block_card B hB
    simp [GolayBounds.weight_eq_card_support, support_wordOfFinset, hcard]
  have hLower : 759 ≤ Set.ncard (weight8Words (designCode S)) := by
    have hblocks : Set.ncard S.blocks = 759 := ncard_blocks_eq_759 (S := S)
    have himg : Set.ncard ((wordOfFinset (n := 24)) '' S.blocks) = 759 := by
      simpa [hblocks] using!
        (Set.ncard_image_of_injective (s := S.blocks) (f := wordOfFinset (n := 24)) hinj)
    have hle :
        Set.ncard ((wordOfFinset (n := 24)) '' S.blocks) ≤
          Set.ncard (weight8Words (designCode S)) :=
      Set.ncard_le_ncard hsubset
    simpa [himg] using! hle
  -- Upper bound: the general 5-subset counting bound using `minDist ≥ 8`.
  have hUpper : Set.ncard (weight8Words (designCode S)) ≤ 759 := by
    have hmin : 8 ≤ minDist (designCode S) :=
      le_of_eq (designCode_minDist_eq (S := S)).symm
    simpa using! (weight8_codewords_le_759_of_minDist_ge (C := designCode S) hmin)
  exact le_antisymm hUpper hLower

/-- The octads of `designCode S` are exactly the blocks of the original design `S`. -/
public lemma octadsFromCode_designCode_eq_blocks (S : SteinerSystem 24 8 5) :
    octadsFromCode (designCode S) = S.blocks := by
  have hsub : S.blocks ⊆ octadsFromCode (designCode S) :=
    blocks_subset_octadsFromCode_designCode (S := S)
  -- Relate `octadsFromCode` to the image of `support` on `weight8Words`.
  have hoct :
      octadsFromCode (designCode S) = support '' weight8Words (designCode S) := by
    ext B
    constructor
    · rintro ⟨w, hwC, hw8, rfl⟩
      exact ⟨w, ⟨hwC, hw8⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw.1, hw.2, rfl⟩
  have hsup_inj : Function.Injective (support : BinWord 24 → Finset (Fin 24)) := by
    intro w w' h
    calc
      w = wordOfFinset (n := 24) (support w) := by
        simpa using! CodeFromOctadsAux.word_eq_wordOfFinset_support (w := w)
      _ = wordOfFinset (n := 24) (support w') := by simp [h]
      _ = w' := by
        simpa using! (CodeFromOctadsAux.word_eq_wordOfFinset_support (w := w')).symm
  have hOct_card : Set.ncard (octadsFromCode (designCode S)) = 759 := by
    calc
      Set.ncard (octadsFromCode (designCode S))
          = Set.ncard (support '' weight8Words (designCode S)) := by simp [hoct]
      _ = Set.ncard (weight8Words (designCode S)) :=
            Set.ncard_image_of_injective (weight8Words (designCode S)) hsup_inj
      _ = 759 := designCode_weight8_card (S := S)
  have hBlocks_card : Set.ncard S.blocks = 759 := ncard_blocks_eq_759 (S := S)
  have hle : Set.ncard (octadsFromCode (designCode S)) ≤ Set.ncard S.blocks := by
    simp [hOct_card, hBlocks_card]
  -- Use subset + equal cardinalities to conclude equality.
  have : S.blocks = octadsFromCode (designCode S) :=
    Set.eq_of_subset_of_ncard_le hsub hle
  exact this.symm

/-- The code `designCode S` satisfies `IsSharpBS81GolayInput`. -/
public theorem isSharpBS81GolayInput_designCode (S : SteinerSystem 24 8 5) :
    IsSharpBS81GolayInput (designCode S) := by
  refine
    { linear := designCode_linear (S := S)
      card_eq := designCode_card_eq (S := S)
      minDist_eq := designCode_minDist_eq (S := S)
      selfOrth := designCode_selfOrth (S := S)
      doublyEven := designCode_doublyEven (S := S)
      weight8_card := designCode_weight8_card (S := S) }

end

end GolayUniquenessSteps.WittDesignUniqueTheory.ClassicalWitt

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
