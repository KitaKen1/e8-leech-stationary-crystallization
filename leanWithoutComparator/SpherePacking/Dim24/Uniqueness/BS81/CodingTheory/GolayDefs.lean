-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayBounds
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerDefs
public import Mathlib.Data.Set.Card
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.DerivedS3622

/-!
# Extended binary Golay codes (BS81 layer)

This file defines the predicate `IsExtendedBinaryGolayCode` and basic objects built from a code:
weight-8 words, their supports (octads), and the associated derived blocks on 22 points.
It also contains the combinatorial bound on weight-8 codewords and the coordinate permutation API
used in uniqueness arguments.

## Main definitions
* `IsExtendedBinaryGolayCode`
* `weight8Words`
* `octadsFromCode`
* `blocksFromGolay`
* `permuteWord`, `permuteCode`

## Main statements
* `weight8_codewords_le_759_of_minDist_ge`
* `WittDesign.steiner_S_5_8_24_of_weight8_count`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open Set
open scoped BigOperators

/-!
## Golay code characterization
-/

/--
Predicate characterizing an extended binary Golay code: linear, of size `2^12`, and with minimum
distance `8`.
-/
public structure IsExtendedBinaryGolayCode (C : Code 24) : Prop where
  linear : IsLinearCode C
  card_eq : Set.ncard C = 2 ^ 12
  minDist_eq : minDist C = 8

attribute [grind cases] IsExtendedBinaryGolayCode

/-- An `IsExtendedBinaryGolayCode` has minimum distance at least `8`. -/
public lemma IsExtendedBinaryGolayCode.minDist_ge (C : Code 24) (hC : IsExtendedBinaryGolayCode C) :
    8 ≤ minDist C := by
  simp [hC.minDist_eq]

attribute [grind →] IsExtendedBinaryGolayCode.minDist_ge

/-!
## Weight-8 bounds and Steiner system
-/

/-- Predicate that a length-24 binary word begins with `11` in the first two positions. -/
@[expose] public def startsWith11 (w : BinWord 24) : Prop :=
  w 0 = 1 ∧ w 1 = 1

attribute [grind =] startsWith11

/-- Drop the first two coordinates of a length-24 word. -/
@[expose] public def puncture22 (w : BinWord 24) : BinWord 22 :=
  fun i : Fin 22 => w (Fin.addNat i 2)

/-- The support of a binary word: indices where the value is `1`. -/
@[expose] public def support {n : ℕ} (w : BinWord n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => w i = 1)

/-!
## Shared `56` / `759*56` bookkeeping

These small combinatorial numerics appear repeatedly in the weight-8 / Witt-design arguments.
-/

/-- A weight-8 word has exactly `56` different `5`-subsets of its support. -/
public lemma card_powersetCard5_support_eq_56 {w : BinWord 24} (hw8 : weight w = 8) :
    ((support w).powersetCard 5).card = 56 := by
  have hchoose8 : Nat.choose 8 5 = 56 := by decide
  have hwt : weight w = (support w).card := by
    simp [weight, support]
  simp_all only [Finset.card_powersetCard]

/-- The number of `5`-subsets of `Fin 24` is `759 * 56` (i.e. `Nat.choose 24 5`). -/
public lemma card_powersetCard5_univ_fin24_eq_759_mul_56 :
    ((Finset.univ : Finset (Fin 24)).powersetCard 5).card = 759 * 56 := by
  have : ((Finset.univ : Finset (Fin 24)).powersetCard 5).card = Nat.choose 24 5 := by
    simp
  simpa [this] using! (by decide : Nat.choose 24 5 = 759 * 56)

/-- Summing the `5`-subset counts over a family of weight-8 words gives `|S| * 56`. -/
public lemma sum_card_powersetCard5_support_eq_mul_56 (S : Finset (BinWord 24))
    (hwt : ∀ w ∈ S, weight w = 8) :
    (∑ w ∈ S, ((support w).powersetCard 5).card) = S.card * 56 := by
  have hterm : ∀ w ∈ S, ((support w).powersetCard 5).card = 56 := by
    intro w hw
    exact card_powersetCard5_support_eq_56 (w := w) (hwt w hw)
  exact Finset.sum_const_nat hterm

/-- The set of weight-`8` codewords in `C`. -/
@[expose] public def weight8Words (C : Code 24) : Set (BinWord 24) :=
  {w : BinWord 24 | w ∈ C ∧ weight w = 8}

/-- The octads (supports of weight-`8` words) coming from `C`. -/
@[expose] public def octadsFromCode (C : Code 24) : Set (Finset (Fin 24)) :=
  {B | ∃ w : BinWord 24, w ∈ C ∧ weight w = 8 ∧ B = support w}

/--
The `6`-subset of `{0, 1, ..., 21}` obtained from a weight-8 word starting with `11` by dropping
the first two `1`s.
-/
@[expose] public def blockFromWord (w : BinWord 24) : Finset (Fin 22) :=
  support (puncture22 w)

/-- The derived blocks on `Fin 22` coming from weight-8 words in `C` that start with `11`. -/
@[expose] public def blocksFromGolay (C : Code 24) : Set (Finset (Fin 22)) :=
  {B | ∃ w : BinWord 24, w ∈ C ∧ weight w = 8 ∧ startsWith11 w ∧ B = blockFromWord w}

namespace GolayBounds

open scoped symmDiff

lemma zmod2_add_eq_one_iff_ne (a b : ZMod 2) : a + b = 1 ↔ a ≠ b := by
  rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one b with rfl | rfl <;> decide

attribute [grind =] zmod2_add_eq_one_iff_ne

lemma zmod2_add_eq_zero_iff_eq (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one b with rfl | rfl <;> decide

attribute [grind =] zmod2_add_eq_zero_iff_eq

/-- Over `ZMod 2`, `u + v = 0` iff `u = v` for binary words. -/
public lemma binWord_add_eq_zero_iff_eq {n : ℕ} (u v : BinWord n) : u + v = 0 ↔ u = v := by
  constructor
  · intro huv
    ext i
    have : u i + v i = 0 := by
      simpa [Pi.add_apply] using! congrArg (fun w : BinWord n => w i) huv
    exact (zmod2_add_eq_zero_iff_eq (u i) (v i)).1 this
  · rintro rfl
    ext i
    exact (zmod2_add_eq_zero_iff_eq (u i) (u i)).2 rfl

attribute [grind =] binWord_add_eq_zero_iff_eq

/-- In `ZMod 2`, adding an element to itself gives `0`. -/
@[simp] public lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  simpa using! (zmod2_add_eq_zero_iff_eq a a).2 rfl

attribute [grind =] zmod2_add_self

/-- In `ZMod 2`, negation is the identity. -/
@[simp] public lemma zmod2_neg (a : ZMod 2) : -a = a :=
  ((add_eq_zero_iff_eq_neg).1 (zmod2_add_self a)).symm

attribute [grind =] zmod2_neg

/-- Binary words are self-negating: `-w = w`. -/
@[simp] public lemma neg_word {n : ℕ} (w : BinWord n) : -w = w := by
  ext i
  simp

attribute [grind =] neg_word

/-- Membership in `support w` is equivalent to the coordinate being `1`. -/
public lemma mem_support {n : ℕ} (w : BinWord n) (i : Fin n) : i ∈ support w ↔ w i = 1 := by
  simp [support]

attribute [grind =] mem_support

/-- If `i` is not in `support w`, then `w i = 0`. -/
public lemma eq_zero_of_not_mem_support {n : ℕ} (w : BinWord n) (i : Fin n) :
    i ∉ support w → w i = 0 := by
  intro hi
  rcases zmod2_eq_zero_or_eq_one (w i) with h0 | h1
  · exact h0
  · exact (False.elim (hi ((mem_support (w := w) (i := i)).2 h1)))

attribute [grind →] eq_zero_of_not_mem_support

/-- `i ∉ support w` iff `w i = 0`. -/
public lemma not_mem_support {n : ℕ} (w : BinWord n) (i : Fin n) :
    i ∉ support w ↔ w i = 0 := by
  grind only [= mem_support, → eq_zero_of_not_mem_support]

attribute [grind =] not_mem_support

/-- Rewrite a coordinate as an indicator for membership in the support. -/
public lemma word_apply_eq_ite_mem_support {n : ℕ} (w : BinWord n) (i : Fin n) :
    w i = (if i ∈ support w then (1 : ZMod 2) else 0) := by
  by_cases hi : i ∈ support w
  · simpa [hi] using! (mem_support (w := w) i).1 hi
  · simpa [hi] using! (not_mem_support (w := w) (i := i)).1 hi

/-- The weight of a binary word equals the cardinality of its support. -/
public lemma weight_eq_card_support {n : ℕ} (w : BinWord n) : weight w = (support w).card := by
  simp [weight, support]

attribute [grind =] weight_eq_card_support

/-- The support of `w₁ + w₂` is the symmetric difference of supports. -/
public lemma support_add_eq_symmDiff {n : ℕ} (w₁ w₂ : BinWord n) :
    support (w₁ + w₂) = support w₁ ∆ support w₂ := by
  ext i
  -- expand membership in supports, then dispatch by `grind` (ZMod2 has only `0/1`).
  grind (splits := 2) only
    [Finset.mem_symmDiff, mem_support, not_mem_support, zmod2_add_eq_one_iff_ne, Pi.add_apply]

attribute [grind =_] support_add_eq_symmDiff

/-- Subadditivity of weight: `weight (w₁ + w₂) ≤ weight w₁ + weight w₂`. -/
public lemma weight_add_le {n : ℕ} (x y : BinWord n) :
    weight (fun i => x i + y i) ≤ weight x + weight y := by
  have hsupp : support (fun i => x i + y i) = support x ∆ support y := by
    simpa [Pi.add_apply] using! (support_add_eq_symmDiff (w₁ := x) (w₂ := y))
  have hsubset : support (fun i => x i + y i) ⊆ support x ∪ support y := by
    simpa [hsupp] using! (Finset.symmDiff_subset_union (s := support x) (t := support y))
  have hcard :
      (support (fun i => x i + y i)).card ≤ (support x).card + (support y).card := by
    refine le_trans (Finset.card_le_card hsubset) ?_
    simpa using! Finset.card_union_le (support x) (support y)
  simpa [weight_eq_card_support] using! hcard

/-- Hamming distance equals the cardinality of the symmetric difference of supports. -/
public lemma hammingDist_eq_card_support_symmDiff {n : ℕ} (w₁ w₂ : BinWord n) :
    hammingDist w₁ w₂ = (support w₁ ∆ support w₂).card := by
  have hsupp : support (fun i => w₁ i + w₂ i) = support w₁ ∆ support w₂ := by
    simpa [Pi.add_apply] using! (support_add_eq_symmDiff (w₁ := w₁) (w₂ := w₂))
  simp [hammingDist, weight_eq_card_support, hsupp]

attribute [grind =] hammingDist_eq_card_support_symmDiff

lemma card_support_inter_ge_of_common_subset
    {n : ℕ} {w₁ w₂ : BinWord n} {S : Finset (Fin n)} {m : ℕ}
    (hS₁ : S ⊆ support w₁) (hS₂ : S ⊆ support w₂) (hcard : S.card = m) :
    m ≤ (support w₁ ∩ support w₂).card := by
  have hsubset : S ⊆ support w₁ ∩ support w₂ := by
    intro i hi
    exact Finset.mem_inter.2 ⟨hS₁ hi, hS₂ hi⟩
  simpa [hcard] using! (Finset.card_le_card hsubset)

lemma hammingDist_le_six_of_common_5subset
    (w₁ w₂ : BinWord 24)
    (hw₁ : weight w₁ = 8) (hw₂ : weight w₂ = 8)
    {S : Finset (Fin 24)}
    (hS₁ : S ∈ (support w₁).powersetCard 5)
    (hS₂ : S ∈ (support w₂).powersetCard 5) :
    hammingDist w₁ w₂ ≤ 6 := by
  obtain ⟨hsub₁, hcard₁⟩ := Finset.mem_powersetCard.mp hS₁
  obtain ⟨hsub₂, hcard₂⟩ := Finset.mem_powersetCard.mp hS₂
  have hinter_ge : 5 ≤ (support w₁ ∩ support w₂).card :=
    card_support_inter_ge_of_common_subset hsub₁ hsub₂ hcard₁
  have hwt₁ : (support w₁).card = 8 := by simpa [weight_eq_card_support] using! hw₁
  have hwt₂ : (support w₂).card = 8 := by simpa [weight_eq_card_support] using! hw₂
  have hsymm :
      (support w₁ ∆ support w₂).card =
        16 - 2 * (support w₁ ∩ support w₂).card := by
    have hdisj : Disjoint (support w₁ \ support w₂) (support w₂ \ support w₁) :=
      disjoint_sdiff_sdiff
    calc
      (support w₁ ∆ support w₂).card
          = ((support w₁ \ support w₂) ∪ (support w₂ \ support w₁)).card := by
              rfl
      _ = (support w₁ \ support w₂).card + (support w₂ \ support w₁).card := by
              simpa using! (Finset.card_union_of_disjoint hdisj)
      _ = ((support w₁).card - (support w₁ ∩ support w₂).card) +
            ((support w₂).card - (support w₁ ∩ support w₂).card) := by
              simp [Finset.card_sdiff, Finset.inter_comm]
      _ = 16 - 2 * (support w₁ ∩ support w₂).card := by omega
  grind only [= hammingDist_eq_card_support_symmDiff]

/-- A lower bound on `minDist C` gives a lower bound on pairwise distances inside `C`. -/
public lemma hammingDist_ge_of_minDist_ge
    {n : ℕ} (C : Code n) {d : ℕ} (hd : d ≤ minDist C)
    {x y : BinWord n} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    d ≤ hammingDist x y :=
  hd.trans (Nat.sInf_le ⟨x, y, hx, hy, hxy, rfl⟩)

end GolayBounds

/--
If `minDist C ≥ 8`, then `C` has at most `759` codewords of weight `8`.
-/
public theorem weight8_codewords_le_759_of_minDist_ge
    (C : Code 24) (hmin : 8 ≤ minDist C) :
    Set.ncard (weight8Words C) ≤ 759 := by
  -- Work with the finite set of weight-8 codewords as a `Finset`.
  set S : Set (BinWord 24) := weight8Words C
  letI : DecidablePred (fun w : BinWord 24 => w ∈ S) := Classical.decPred _
  have hS_card : Set.ncard S = S.toFinset.card := by
    simpa using! (Set.ncard_eq_toFinset_card S)
  -- Each weight-8 word contributes 56 distinct 5-subsets of its support.
  let f : BinWord 24 → Finset (Finset (Fin 24)) := fun w => (support w).powersetCard 5
  have hf_disj : (S.toFinset : Set (BinWord 24)).PairwiseDisjoint f := by
    intro w hw w' hw' hne
    -- If a 5-subset is shared, we get distance ≤ 6, contradicting `minDist ≥ 8`.
    refine Finset.disjoint_left.2 ?_
    intro T hT hT'
    have hwS : w ∈ S := by
      have hw' : w ∈ S.toFinset := by simpa using! hw
      simpa using! (Set.mem_toFinset.mp hw')
    have hw'S : w' ∈ S := by
      have hw'' : w' ∈ S.toFinset := by simpa using! hw'
      simpa using! (Set.mem_toFinset.mp hw'')
    have hwC : w ∈ C := (hwS).1
    have hw'C : w' ∈ C := (hw'S).1
    have hw8 : weight w = 8 := (hwS).2
    have hw'8 : weight w' = 8 := (hw'S).2
    have hdist_ge : 8 ≤ hammingDist w w' :=
      GolayBounds.hammingDist_ge_of_minDist_ge (C := C) (d := 8) ( hmin) hwC hw'C hne
    have hdist_le : hammingDist w w' ≤ 6 :=
      GolayBounds.hammingDist_le_six_of_common_5subset w w' hw8 hw'8 hT hT'
    exact (not_lt_of_ge hdist_ge) (lt_of_le_of_lt hdist_le (by decide))
  -- Count 5-subsets covered by the disjoint family `{f w | w ∈ S}`.
  have hsum_le :
      (∑ w ∈ S.toFinset, (f w).card) ≤ ((Finset.univ : Finset (Fin 24)).powersetCard 5).card := by
    have hsubset :
        S.toFinset.biUnion f ⊆ (Finset.univ : Finset (Fin 24)).powersetCard 5 := by
      intro T hT
      rcases Finset.mem_biUnion.mp hT with ⟨w, hw, hTw⟩
      -- Any subset of a support is a subset of `univ`.
      have hTsub : T ⊆ (Finset.univ : Finset (Fin 24)) := by
        intro i _hi
        exact Finset.mem_univ i
      exact (Finset.mem_powersetCard.mpr ⟨hTsub, (Finset.mem_powersetCard.mp hTw).2⟩)
    have hcard_union :
        (S.toFinset.biUnion f).card = ∑ w ∈ S.toFinset, (f w).card := by
      simpa using! (Finset.card_biUnion hf_disj)
    -- Compare with the ambient 5-subset finset.
    have := Finset.card_le_card hsubset
    -- Rewrite the LHS using disjointness.
    simpa [hcard_union] using! this
  -- Compute the LHS sum as `|S| * 56`.
  have hconst :
      (∑ w ∈ S.toFinset, (f w).card) = S.toFinset.card * 56 := by
    have hwt : ∀ w ∈ S.toFinset, weight w = 8 := by
      intro w hw
      have hwS : w ∈ S := by
        simpa using! (Set.mem_toFinset.mp (by simpa using! hw : w ∈ S.toFinset))
      exact hwS.2
    simpa [f] using! (sum_card_powersetCard5_support_eq_mul_56 (S := S.toFinset) hwt)
  -- Finish the numeric bound.
  have hchoose : ((Finset.univ : Finset (Fin 24)).powersetCard 5).card = 759 * 56 :=
    card_powersetCard5_univ_fin24_eq_759_mul_56
  -- Combine and cancel the factor 56.
  grind only

/-- A Golay code has at most `759` weight-8 codewords. -/
public theorem weight8_codewords_le_759
    (C : Code 24) (hC : IsExtendedBinaryGolayCode C) :
    Set.ncard (weight8Words C) ≤ 759 := by
  simpa using! (weight8_codewords_le_759_of_minDist_ge (C := C) hC.minDist_ge)

/-!
## Witt design `S(5,8,24)` from `759` weight-8 words
-/

namespace WittDesign

/--
If a code has minimum distance at least `8` and exactly `759` weight-8 codewords, then the octads
`octadsFromCode C` form the blocks of a Steiner system `S(5,8,24)`.
-/
public theorem steiner_S_5_8_24_of_weight8_count
    (C : Code 24)
    (hmin : 8 ≤ minDist C)
    (hN : Set.ncard (weight8Words C) = 759) :
    ∃ S : SteinerSystem 24 8 5, S.blocks = octadsFromCode C := by
  set W : Set (BinWord 24) := weight8Words C
  letI : DecidablePred (fun w : BinWord 24 => w ∈ W) := Classical.decPred _
  have hW_card : W.toFinset.card = 759 := by
    have hn' : Set.ncard W = 759 := by simpa [W] using! hN
    calc
      W.toFinset.card = Set.ncard W := by
        simpa using! (Eq.symm (Set.ncard_eq_toFinset_card' W))
      _ = 759 := hn'
  let f : BinWord 24 → Finset (Finset (Fin 24)) := fun w => (support w).powersetCard 5
  have hf_disj : (W.toFinset : Set (BinWord 24)).PairwiseDisjoint f := by
    intro w hw w' hw' hne
    refine Finset.disjoint_left.2 ?_
    intro T hT hT'
    have hwW : w ∈ W := by
      simpa [W] using! (Set.mem_toFinset.mp (by simpa using! hw : w ∈ W.toFinset))
    have hw'W : w' ∈ W := by
      simpa [W] using! (Set.mem_toFinset.mp (by simpa using! hw' : w' ∈ W.toFinset))
    have hwC : w ∈ C := hwW.1
    have hw'C : w' ∈ C := hw'W.1
    have hw8 : weight w = 8 := hwW.2
    have hw'8 : weight w' = 8 := hw'W.2
    have hdist_ge : 8 ≤ hammingDist w w' :=
      GolayBounds.hammingDist_ge_of_minDist_ge (C := C) (d := 8) hmin hwC hw'C hne
    have hdist_le : hammingDist w w' ≤ 6 :=
      GolayBounds.hammingDist_le_six_of_common_5subset w w' hw8 hw'8 hT hT'
    exact (not_lt_of_ge hdist_ge) (lt_of_le_of_lt hdist_le (by decide))
  have hsubset :
      W.toFinset.biUnion f ⊆ (Finset.univ : Finset (Fin 24)).powersetCard 5 := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨w, hw, hTw⟩
    have hTsub : T ⊆ (Finset.univ : Finset (Fin 24)) := by
      intro i _
      exact Finset.mem_univ i
    exact Finset.mem_powersetCard.mpr ⟨hTsub, (Finset.mem_powersetCard.mp hTw).2⟩
  have hcard_union :
      (W.toFinset.biUnion f).card = ∑ w ∈ W.toFinset, (f w).card := by
    simpa using! (Finset.card_biUnion hf_disj)
  have hconst :
      (∑ w ∈ W.toFinset, (f w).card) = W.toFinset.card * 56 := by
    have hwt : ∀ w ∈ W.toFinset, weight w = 8 := by
      intro w hw
      have hwW : w ∈ W := by
        simpa [W] using! (Set.mem_toFinset.mp (by simpa using! hw : w ∈ W.toFinset))
      exact hwW.2
    simpa [f] using! (sum_card_powersetCard5_support_eq_mul_56 (S := W.toFinset) hwt)
  have hchoose24 : ((Finset.univ : Finset (Fin 24)).powersetCard 5).card = 759 * 56 :=
    card_powersetCard5_univ_fin24_eq_759_mul_56
  have hUnion_eq :
      W.toFinset.biUnion f = (Finset.univ : Finset (Fin 24)).powersetCard 5 := by
    have hcard :
        (W.toFinset.biUnion f).card = ((Finset.univ : Finset (Fin 24)).powersetCard 5).card := by
      calc
        (W.toFinset.biUnion f).card = ∑ w ∈ W.toFinset, (f w).card := by simp [hcard_union]
        _ = W.toFinset.card * 56 := hconst
        _ = 759 * 56 := by simp [hW_card]
        _ = ((Finset.univ : Finset (Fin 24)).powersetCard 5).card := by simp [hchoose24]
    have hcard_le : ((Finset.univ : Finset (Fin 24)).powersetCard 5).card ≤
        (W.toFinset.biUnion f).card := by
      rw [← hcard]
    exact Finset.eq_of_subset_of_card_le hsubset hcard_le
  refine ⟨
    { blocks := octadsFromCode C
      block_card := ?_
      cover_unique := ?_ }, rfl⟩
  · intro B hB
    rcases hB with ⟨w, hwC, hw8, rfl⟩
    simpa [GolayBounds.weight_eq_card_support] using! hw8
  · intro T hTcard
    have hTmem : T ∈ (Finset.univ : Finset (Fin 24)).powersetCard 5 := by
      exact Finset.mem_powersetCard_univ.mpr hTcard
    have hTmem' : T ∈ W.toFinset.biUnion f := by simpa [hUnion_eq] using! hTmem
    rcases Finset.mem_biUnion.mp hTmem' with ⟨w, hwW, hTw⟩
    have hwW' : w ∈ W := by
      simpa [W] using! (Set.mem_toFinset.mp (by simpa using! hwW : w ∈ W.toFinset))
    have hwC : w ∈ C := hwW'.1
    have hw8 : weight w = 8 := hwW'.2
    have hsub : T ⊆ support w := (Finset.mem_powersetCard.mp hTw).1
    refine ⟨support w, ⟨⟨w, hwC, hw8, rfl⟩, hsub⟩, ?_⟩
    intro B' hB'
    rcases hB' with ⟨hB'mem, hsub'⟩
    rcases hB'mem with ⟨w', hw'C, hw'8, rfl⟩
    by_cases hww' : w = w'
    · subst hww'
      rfl
    · have hwW_fin : w ∈ W.toFinset := by
        refine Set.mem_toFinset.mpr ?_
        exact ⟨hwC, hw8⟩
      have hw'W_fin : w' ∈ W.toFinset := by
        refine Set.mem_toFinset.mpr ?_
        exact ⟨hw'C, hw'8⟩
      have hdisj : Disjoint (f w) (f w') :=
        hf_disj (x := w) hwW_fin (y := w') hw'W_fin hww'
      have hT_in : T ∈ f w := Finset.mem_powersetCard.mpr ⟨hsub, hTcard⟩
      have hT_in' : T ∈ f w' := Finset.mem_powersetCard.mpr ⟨hsub', hTcard⟩
      exact False.elim (Finset.disjoint_left.mp hdisj hT_in hT_in')

end WittDesign

lemma startsWith11_iff_mem_support (w : BinWord 24) :
    startsWith11 w ↔ (0 : Fin 24) ∈ support w ∧ (1 : Fin 24) ∈ support w := by
  simp [startsWith11, support]

lemma blockFromWord_eq_drop2_support (w : BinWord 24) :
    blockFromWord w = drop2 (support w) := by
  ext i
  rw [mem_drop2]
  unfold blockFromWord support
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact Iff.rfl

theorem steiner_S_3_6_22_from_golay
    (C : Code 24) (hC : IsExtendedBinaryGolayCode C)
    (hN : Set.ncard (weight8Words C) = 759) :
    ∃ S : SteinerSystem 22 6 3,
      S.blocks = blocksFromGolay C := by
  rcases WittDesign.steiner_S_5_8_24_of_weight8_count (C := C) (hC.minDist_ge) hN with ⟨S24, hS24⟩
  refine ⟨DerivedS3622.derivedSteinerSystem S24, ?_⟩
  -- blocks: derived octads containing `0,1` correspond to `startsWith11` codewords
  ext B22
  constructor
  · intro hB
    have hB' : B22 ∈ DerivedS3622.derivedBlocks S24 := by
      simpa [DerivedS3622.derivedSteinerSystem] using! hB
    rcases hB' with ⟨B24, hB24, h0, h1, rfl⟩
    have hB24' : B24 ∈ octadsFromCode C := by simpa [hS24] using! hB24
    rcases hB24' with ⟨w, hwC, hw8, rfl⟩
    refine ⟨w, hwC, hw8, ?_, ?_⟩
    · exact (startsWith11_iff_mem_support w).2 ⟨h0, h1⟩
    · simp [blockFromWord_eq_drop2_support]
  · intro hB
    rcases hB with ⟨w, hwC, hw8, h11, rfl⟩
    have h01 : (0 : Fin 24) ∈ support w ∧ (1 : Fin 24) ∈ support w :=
      (startsWith11_iff_mem_support w).1 h11
    have hmem : support w ∈ S24.blocks := by
      have : support w ∈ octadsFromCode C := ⟨w, hwC, hw8, rfl⟩
      simpa [hS24] using! this
    have : drop2 (support w) ∈ DerivedS3622.derivedBlocks S24 :=
      ⟨support w, hmem, h01.1, h01.2, rfl⟩
    -- rewrite `blockFromWord` as `drop2 (support w)` and fold back into the derived design
    have : blockFromWord w ∈ (DerivedS3622.derivedSteinerSystem S24).blocks := by
      simpa [DerivedS3622.derivedSteinerSystem, blockFromWord_eq_drop2_support] using! this
    simpa using! this

/-!
## Uniqueness up to equivalence
-/

/-- Permute the coordinates of a binary word by an equivalence `σ`. -/
@[expose] public def permuteWord {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (w : BinWord n) : BinWord n :=
  fun i => w (σ i)

/-- Unfolding lemma for `permuteWord`. -/
@[simp] public lemma permuteWord_apply {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (w : BinWord n)
    (i : Fin n) : permuteWord (n := n) σ w i = w (σ i) := rfl

attribute [grind =] permuteWord_apply

/-- Permute the coordinates of a code by applying `permuteWord` to all codewords. -/
@[expose] public def permuteCode {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (C : Code n) : Code n :=
  (permuteWord (n := n) σ) '' C

/-- The support of `permuteWord σ w` is the image of `support w` under `σ`. -/
public lemma support_permuteWord {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (w : BinWord n) :
    support (permuteWord (n := n) σ w) = (support w).map σ.symm.toEmbedding := by
  ext i
  have hsymm : σ.symm.symm i = σ i := by simp
  grind (splits := 1) only [= GolayBounds.mem_support, permuteWord, Finset.mem_map_equiv]

attribute [grind =] support_permuteWord

/-- The weight of a word is invariant under coordinate permutations. -/
public lemma weight_permuteWord {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (w : BinWord n) :
    weight (permuteWord (n := n) σ w) = weight w := by
  simp [GolayBounds.weight_eq_card_support, support_permuteWord]

attribute [grind =] weight_permuteWord

/-- Hamming distance is invariant under coordinate permutations. -/
public lemma hammingDist_permuteWord {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (w₁ w₂ : BinWord n) :
    hammingDist (permuteWord (n := n) σ w₁) (permuteWord (n := n) σ w₂) = hammingDist w₁ w₂ := by
  simpa [hammingDist, permuteWord, Pi.add_apply] using!
    (weight_permuteWord (σ := σ) (w := fun i => w₁ i + w₂ i))

attribute [grind =] hammingDist_permuteWord

/-- Coordinate permutation preserves linearity of codes. -/
public lemma isLinearCode_permuteCode {n : ℕ} (σ : Equiv (Fin n) (Fin n)) {C : Code n} :
    IsLinearCode C → IsLinearCode (permuteCode (n := n) σ C) := by
  intro hC
  refine ⟨?_, ?_⟩
  · exact ⟨0, hC.1, rfl⟩
  · intro x y hx hy
    rcases hx with ⟨x0, hx0, rfl⟩
    rcases hy with ⟨y0, hy0, rfl⟩
    exact ⟨x0 + y0, hC.2 x0 y0 hx0 hy0, rfl⟩

/-- The map `permuteWord σ` is injective. -/
public lemma permuteWord_injective {n : ℕ} (σ : Equiv (Fin n) (Fin n)) :
    Function.Injective (permuteWord (n := n) σ) := by
  intro w₁ w₂ h
  funext i
  have := congrArg (fun w : BinWord n => w (σ.symm i)) h
  simpa [permuteWord] using! this

attribute [grind inj] permuteWord_injective

lemma permuteWord_trans {n : ℕ} (σ₁ σ₂ : Equiv (Fin n) (Fin n)) (w : BinWord n) :
    permuteWord (n := n) (σ₁.trans σ₂) w = permuteWord (n := n) σ₁ (permuteWord (n := n) σ₂ w) := by
  rfl

attribute [grind =] permuteWord_trans

/-- Unfold membership in `permuteCode σ C` as an explicit preimage in `C`. -/
public lemma mem_permuteCode_iff {n : ℕ} (σ : Equiv (Fin n) (Fin n)) (C : Code n) (w : BinWord n) :
    w ∈ permuteCode (n := n) σ C ↔ ∃ w0, w0 ∈ C ∧ permuteWord (n := n) σ w0 = w := by
  rfl

attribute [grind =] mem_permuteCode_iff

/-- Functoriality of `permuteCode` with respect to composition of permutations. -/
public lemma permuteCode_trans {n : ℕ} (σ₁ σ₂ : Equiv (Fin n) (Fin n)) (C : Code n) :
    permuteCode (n := n) (σ₁.trans σ₂) C = permuteCode (n := n) σ₁ (permuteCode (n := n) σ₂ C) := by
  ext w
  grind

/-!
Further uniqueness results for the Golay/Witt configuration are proved in
`CodingTheory/GolayUniqueness/Main.lean`.
-/

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
