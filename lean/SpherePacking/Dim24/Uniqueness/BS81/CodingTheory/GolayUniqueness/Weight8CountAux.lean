-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
import Mathlib.Data.Matrix.Mul
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctadsAux
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.ByContra

/-!
# Auxiliary lemmas for the weight-8 count

Starting from the `[24,12,8]` invariants packaged as `IsExtendedBinaryGolayCode`, we show that
every `5`-subset of coordinates is contained in some weight-`8` codeword. Combined with the
universal upper bound `≤ 759`, this forces the exact weight-`8` count `= 759`.

The key combinatorial input is that puncturing a `[24,12,8]` code at any coordinate yields a
perfect `[23,12,≥7]` code, via the Hamming bound with radius `3`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.Weight8CountAux

noncomputable section

open scoped BigOperators symmDiff

open GolayUniquenessSteps.CodeFromOctadsAux

/-!
## Words ↔ supports
-/

/-!
## Puncturing at one coordinate
-/

def puncture23 (p : Fin 24) (w : BinWord 24) : BinWord 23 :=
  p.removeNth w

def punctureCode23 (p : Fin 24) (C : Code 24) : Code 23 :=
  puncture23 (p := p) '' C

lemma puncture23_apply (p : Fin 24) (w : BinWord 24) (i : Fin 23) :
    puncture23 (p := p) w i = w (p.succAbove i) := by
  simp [puncture23, Fin.removeNth_apply]

attribute [grind =] puncture23_apply

@[simp] lemma puncture23_zero (p : Fin 24) : puncture23 (p := p) (0 : BinWord 24) = 0 := by
  ext i
  simp [puncture23, Fin.removeNth_apply]

lemma succAboveEmb_ne {n : ℕ} (p : Fin (n + 1)) (i : Fin n) : p.succAboveEmb i ≠ p := by
  simp

lemma zmod2_add_add_cancel_left (a b : ZMod 2) : a + (a + b) = b :=
  CharTwo.add_cancel_left a b

lemma support_puncture23_map {p : Fin 24} (w : BinWord 24) :
    Finset.map (Fin.succAboveEmb p) (support (puncture23 (p := p) w)) =
      (support w).erase p := by
  ext j
  by_cases hj : j = p
  · subst hj
    grind (splits := 1) only [Finset.mem_map, Finset.mem_erase, succAboveEmb_ne]
  · constructor
    · rintro hjm
      rcases Finset.mem_map.1 hjm with ⟨i, hi, rfl⟩
      simp at *
      grind (splits := 1) only
        [Finset.mem_erase, Fin.succAbove_ne, puncture23_apply, = GolayBounds.mem_support]
    · intro hjm
      have hjne : j ≠ p := (Finset.mem_erase.1 hjm).1
      rcases Fin.exists_succAbove_eq hjne with ⟨i, rfl⟩
      refine Finset.mem_map.2 ⟨i, ?_, rfl⟩
      grind only
        [= Finset.mem_erase, = GolayBounds.not_mem_support, = GolayBounds.mem_support,
          = puncture23_apply]

attribute [grind =] support_puncture23_map

lemma card_support_puncture23 (p : Fin 24) (w : BinWord 24) :
    (support (puncture23 (p := p) w)).card = ((support w).erase p).card := by
  simpa [Finset.card_map] using! congrArg Finset.card (support_puncture23_map (p := p) w)

lemma weight_puncture23_le (p : Fin 24) (w : BinWord 24) :
    weight (puncture23 (p := p) w) ≤ weight w := by
  have hcard := card_support_puncture23 (p := p) w
  have herase : ((support w).erase p).card ≤ (support w).card :=
    Finset.card_erase_le (s := support w) (a := p)
  simpa [GolayBounds.weight_eq_card_support, hcard] using! herase

lemma weight_le_weight_puncture23_add_one (p : Fin 24) (w : BinWord 24) :
    weight w ≤ weight (puncture23 (p := p) w) + 1 := by
  have hcard := card_support_puncture23 (p := p) w
  have hle : (support w).card ≤ ((support w).erase p).card + 1 := by
    by_cases hp : p ∈ support w
    · -- `erase` drops exactly one element
      exact le_of_eq (Finset.card_erase_add_one hp).symm
    · -- otherwise `erase` does nothing
      simp [Finset.erase_eq_of_notMem hp]
  simpa [GolayBounds.weight_eq_card_support, hcard] using! hle

lemma weight_puncture23_add_one_of_mem_support (p : Fin 24) (w : BinWord 24) (hp : p ∈ support w) :
    weight (puncture23 (p := p) w) + 1 = weight w := by
  have hcard := card_support_puncture23 (p := p) w
  have herase : ((support w).erase p).card + 1 = (support w).card :=
    Finset.card_erase_add_one hp
  simpa [GolayBounds.weight_eq_card_support, hcard] using! herase

/-!
## Error patterns of weight ≤ 3 in length 23
-/

def errorSupports23 : Finset (Finset (Fin 23)) :=
  (Finset.range 4).biUnion fun i => (Finset.univ : Finset (Fin 23)).powersetCard i

def errorWords23 : Set (BinWord 23) :=
  {e : BinWord 23 | weight e ≤ 3}

lemma errorSupports23_mem_iff_card_le_three (S : Finset (Fin 23)) :
    S ∈ errorSupports23 ↔ S.card ≤ 3 := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.1 h with ⟨i, hi, hSi⟩
    have hi4 : i < 4 := Finset.mem_range.1 hi
    have hcard : S.card = i := (Finset.mem_powersetCard.1 hSi).2
    -- `i < 4` iff `i ≤ 3`
    have : i ≤ 3 := Nat.lt_succ_iff.1 hi4
    simpa [hcard] using! this
  · intro hcard
    have hi4 : S.card < 4 := lt_of_le_of_lt hcard (Nat.lt_succ_self 3)
    refine Finset.mem_biUnion.2 ?_
    refine ⟨S.card, Finset.mem_range.2 hi4, ?_⟩
    exact Finset.mem_powersetCard.2 ⟨by simp, rfl⟩

attribute [grind =] errorSupports23_mem_iff_card_le_three

private lemma errorWords23_eq_image_wordOfFinset :
    errorWords23 = (wordOfFinset (n := 23)) '' (errorSupports23 : Set (Finset (Fin 23))) := by
  ext e
  constructor
  · intro he
    refine ⟨support e, ?_, ?_⟩
    · -- `support e` has cardinality `weight e`
      have : (support e).card ≤ 3 := by
        simpa [GolayBounds.weight_eq_card_support] using! he
      exact (errorSupports23_mem_iff_card_le_three (S := support e)).2 this
    · simpa using! (word_eq_wordOfFinset_support (w := e)).symm
  · rintro ⟨S, hS, rfl⟩
    have : S.card ≤ 3 := (errorSupports23_mem_iff_card_le_three (S := S)).1 hS
    simpa [errorWords23, GolayBounds.weight_eq_card_support, support_wordOfFinset] using! this

lemma errorSupports23_card :
    errorSupports23.card = 2048 := by
  let U : Finset (Fin 23) := Finset.univ
  have hpair :
      ((Finset.range 4 : Finset ℕ) : Set ℕ).PairwiseDisjoint (fun i => U.powersetCard i) := by
    intro i _hi j _hj hij
    exact U.pairwise_disjoint_powersetCard hij
  calc
    errorSupports23.card
        = ((Finset.range 4).biUnion (fun i => U.powersetCard i)).card := by
            simp [errorSupports23, U]
    _ = ∑ i ∈ Finset.range 4, (U.powersetCard i).card := by
          simpa using!
            (Finset.card_biUnion (s := Finset.range 4) (t := fun i => U.powersetCard i) hpair)
    _ = ∑ i ∈ Finset.range 4, Nat.choose 23 i := by
          simp [U, Finset.card_powersetCard]
    _ = 2048 := by decide

theorem errorWords23_ncard : Set.ncard (errorWords23) = 2048 := by
  -- transport to a finite set of supports using the injective `wordOfFinset`
  have hinj : Function.Injective (wordOfFinset (n := 23)) := by
    intro S T h
    have :
        support (wordOfFinset (n := 23) S) = support (wordOfFinset (n := 23) T) := by
      simp [h]
    simpa [support_wordOfFinset] using! this
  calc
    Set.ncard (errorWords23)
        = Set.ncard ((wordOfFinset (n := 23)) '' (errorSupports23 : Set (Finset (Fin 23)))) := by
            simp [errorWords23_eq_image_wordOfFinset]
    _ = Set.ncard (errorSupports23 : Set (Finset (Fin 23))) := by
          simpa using!
            (Set.ncard_image_of_injective (f := (wordOfFinset (n := 23)))
              (s := (errorSupports23 : Set (Finset (Fin 23)))) hinj)
    _ = errorSupports23.card := by simp
    _ = 2048 := errorSupports23_card

/-!
## Decoding in the punctured code
-/

lemma punctureCode23_injOn
    (C : Code 24) (hmin : 8 ≤ minDist C) (p : Fin 24) :
    Set.InjOn (puncture23 (p := p)) C := by
  intro x hx y hy hxy
  by_contra hne
  -- if punctures are equal, `x+y` has support contained in `{p}`, so distance ≤ 1
  have hdist_le : hammingDist x y ≤ 1 := by
    have hsubset : support x ∆ support y ⊆ ({p} : Finset (Fin 24)) := by
      intro j hj
      by_cases hjp : j = p
      · simp [hjp]
      · rcases Fin.exists_succAbove_eq hjp with ⟨i, hij⟩
        have hx' : puncture23 (p := p) x i = puncture23 (p := p) y i := by
          simp [hxy]
        have hxyj : x j = y j := by
          have : x (p.succAbove i) = y (p.succAbove i) := by
            simpa [puncture23_apply] using! hx'
          simpa [hij] using! this
        have hmem : (j ∈ support x) ↔ (j ∈ support y) := by
          simp [GolayBounds.mem_support, hxyj]
        have hnot : j ∉ support x ∆ support y := by
          simp [Finset.mem_symmDiff, hmem]
        exact False.elim (hnot hj)
    have hcard : (support x ∆ support y).card ≤ 1 := by
      have : (support x ∆ support y).card ≤ ({p} : Finset (Fin 24)).card :=
        Finset.card_le_card hsubset
      exact le_trans this (le_of_eq (by simp))
    simpa [GolayBounds.hammingDist_eq_card_support_symmDiff] using! hcard
  have hdist_ge : 8 ≤ hammingDist x y :=
    GolayBounds.hammingDist_ge_of_minDist_ge (C := C) (d := 8) hmin hx hy hne
  exact (not_lt_of_ge hdist_ge) (lt_of_le_of_lt hdist_le (by decide))

lemma punctureCode23_ncard
    (C : Code 24) (hC : IsExtendedBinaryGolayCode C) (p : Fin 24) :
    Set.ncard (punctureCode23 (p := p) C) = 2 ^ 12 := by
  have hmin : 8 ≤ minDist C := hC.minDist_ge
  have hinj : Set.InjOn (puncture23 (p := p)) C := punctureCode23_injOn (C := C) hmin p
  -- `punctureCode23` is the image
  calc
    Set.ncard (punctureCode23 (p := p) C)
        = Set.ncard C := by
            simpa [punctureCode23] using! hinj.ncard_image
    _ = 2 ^ 12 := hC.card_eq

lemma punctureCode23_dist_ge7
    (C : Code 24) (hC : IsExtendedBinaryGolayCode C) (p : Fin 24)
    {x y : BinWord 23} (hx : x ∈ punctureCode23 (p := p) C) (hy : y ∈ punctureCode23 (p := p) C)
    (hxy : x ≠ y) :
    7 ≤ hammingDist x y := by
  rcases hx with ⟨x24, hx24, rfl⟩
  rcases hy with ⟨y24, hy24, rfl⟩
  -- show `x24 ≠ y24` using injectivity on `C`
  have hmin : 8 ≤ minDist C := hC.minDist_ge
  have hinj : Set.InjOn (puncture23 (p := p)) C := punctureCode23_injOn (C := C) hmin p
  have hne24 : x24 ≠ y24 :=
    ne_of_apply_ne (puncture23 p) hxy
  have hdist_ge : 8 ≤ hammingDist x24 y24 :=
    GolayBounds.hammingDist_ge_of_minDist_ge (C := C) (d := 8) hmin hx24 hy24 hne24
  -- puncturing removes at most one differing coordinate
  have hle :
      hammingDist x24 y24 ≤
        hammingDist (puncture23 (p := p) x24) (puncture23 (p := p) y24) + 1 := by
    -- translate to weights
    simpa [hammingDist, puncture23, Fin.removeNth_apply] using!
      weight_le_weight_puncture23_add_one (p := p) (w := fun i => x24 i + y24 i)
  -- conclude
  lia

def decodeMap23 (x : BinWord 23 × BinWord 23) : BinWord 23 :=
  fun i => x.1 i + x.2 i

lemma decodeMap23_injOn
    (C : Code 24) (hC : IsExtendedBinaryGolayCode C) (p : Fin 24) :
    Set.InjOn (decodeMap23)
      (punctureCode23 (p := p) C ×ˢ errorWords23) := by
  intro a ha b hb hab
  rcases ha with ⟨haC, haE⟩
  rcases hb with ⟨hbC, hbE⟩
  -- rewrite as `a.1 + a.2 = b.1 + b.2`
  have hab' : (fun i => a.1 i + a.2 i) = fun i => b.1 i + b.2 i := by
    simpa [decodeMap23] using! hab
  -- rearrange to `a.1 + b.1 = a.2 + b.2`
  have hEq : (fun i => a.1 i + b.1 i) = fun i => a.2 i + b.2 i := by
    funext i
    have hi := congrArg (fun f => f i) hab'
    grind only
  have hdist_le6 : hammingDist a.1 b.1 ≤ 6 := by
    have hE1 : weight a.2 ≤ 3 := by simpa [errorWords23] using! haE
    have hE2 : weight b.2 ≤ 3 := by simpa [errorWords23] using! hbE
    have hwt : weight (fun i => a.2 i + b.2 i) ≤ 6 := by
      have hab := GolayBounds.weight_add_le (x := a.2) (y := b.2)
      have hsum : weight a.2 + weight b.2 ≤ 6 := by omega
      exact le_trans hab hsum
    -- `hammingDist a.1 b.1 = weight (a.1+b.1) = weight (a.2+b.2)`
    simpa [hammingDist, hEq] using! hwt
  by_cases hcb : a.1 = b.1
  · -- then `a.2 = b.2` by cancellation
    have hab2 : a.2 = b.2 := by
      funext i
      have hi := congrArg (fun f => f i) hab'
      -- replace `b.1 i` by `a.1 i` and cancel by adding `a.1 i`
      have hi' := congrArg (fun t => t + a.1 i) (by simpa [hcb] using! hi)
      -- normalize in the `ZMod 2` additive commutative group
      simpa [add_assoc, add_left_comm, add_comm, GolayBounds.zmod2_add_self] using! hi'
    exact Prod.ext hcb hab2
  · -- otherwise contradict distance lower bound in punctured code
    have hdist_ge7 : 7 ≤ hammingDist a.1 b.1 :=
      punctureCode23_dist_ge7 (C := C) (hC := hC) (p := p) haC hbC hcb
    exfalso
    exact (not_lt_of_ge hdist_ge7) (lt_of_le_of_lt hdist_le6 (by decide))

theorem decodeMap23_surj
    (C : Code 24) (hC : IsExtendedBinaryGolayCode C) (p : Fin 24) :
    decodeMap23 '' (punctureCode23 (p := p) C ×ˢ errorWords23) = (Set.univ : Set (BinWord 23)) := by
  -- `decodeMap23` is injective on the domain, and the domain has full cardinality `2^23`,
  -- hence the image must be all of `univ`.
  have hinj : Set.InjOn decodeMap23 (punctureCode23 (p := p) C ×ˢ errorWords23) :=
    decodeMap23_injOn (C := C) (hC := hC) (p := p)
  have hCp : Set.ncard (punctureCode23 (p := p) C) = 2 ^ 12 := punctureCode23_ncard (C := C) hC p
  have hE : Set.ncard errorWords23 = 2048 := errorWords23_ncard
  have hdom :
      Set.ncard (punctureCode23 (p := p) C ×ˢ errorWords23) =
        (Set.univ : Set (BinWord 23)).ncard := by
    have hU : (Set.univ : Set (BinWord 23)).ncard = 2 ^ 23 := by
      simp [Set.ncard_univ, BinWord, Nat.card_eq_fintype_card]
    calc
      Set.ncard (punctureCode23 (p := p) C ×ˢ errorWords23)
          = Set.ncard (punctureCode23 (p := p) C) * Set.ncard errorWords23 := by simp
      _ = (2 ^ 12) * 2048 := by simp [hCp, hE]
      _ = 2 ^ 23 := by decide
      _ = (Set.univ : Set (BinWord 23)).ncard := by simp [hU]
  have himage :
      Set.ncard (decodeMap23 '' (punctureCode23 (p := p) C ×ˢ errorWords23))
        = (Set.univ : Set (BinWord 23)).ncard := by
    have : Set.ncard (decodeMap23 '' (punctureCode23 (p := p) C ×ˢ errorWords23)) =
        Set.ncard (punctureCode23 (p := p) C ×ˢ errorWords23) := by
      simpa using! hinj.ncard_image
    simpa [hdom] using! this
  -- compare by cardinality inside a finite ambient type
  refine Set.eq_of_subset_of_ncard_le (by intro x hx; simp) ?_ (by simp)
  -- `univ.ncard ≤ image.ncard`
  simp [himage]

/-!
## A decoding lemma for weight-4 words in the punctured space
-/

lemma weight7_of_close_weight4
    {c v : BinWord 23}
    (hc7 : 7 ≤ weight c) (hv4 : weight v = 4)
    (hd : hammingDist c v ≤ 3) :
    weight c = 7 ∧ support v ⊆ support c := by
  -- set `A = supp(c)` and `B = supp(v)`
  set A : Finset (Fin 23) := support c
  set B : Finset (Fin 23) := support v
  have hBcard : B.card = 4 := by
    simpa [B, GolayBounds.weight_eq_card_support] using! hv4
  have hAcard_ge : 7 ≤ A.card := by
    simpa [A, GolayBounds.weight_eq_card_support] using! hc7
  have hsymm_le : (A ∆ B).card ≤ 3 := by
    -- `hammingDist c v = card (supp(c) Δ supp(v))`
    simpa [A, B, GolayBounds.hammingDist_eq_card_support_symmDiff] using! hd
  have hcardEq : (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card :=
    card_symmDiff_add_two_mul_card_inter A B
  have hinter_le : (A ∩ B).card ≤ B.card := Finset.card_le_card (Finset.inter_subset_right)
  have hinter_le4 : (A ∩ B).card ≤ 4 := by
    omega
  -- Bound `A.card` using `A.card + B.card = symm + 2*inter`.
  have hAcard_le : A.card ≤ 7 := by
    grind only
  have hAcard_eq : A.card = 7 := le_antisymm hAcard_le hAcard_ge
  -- solve for `(A ∩ B).card`: since `symm + 2*inter = 11` and `symm ≤ 3`, we get `inter = 4`.
  have hinter_eq4 : (A ∩ B).card = 4 := by
    grind only
  have hinter_eq : A ∩ B = B := by
    apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_right : A ∩ B ⊆ B)
    omega
  have hB_subset : B ⊆ A := by
    exact Finset.inter_eq_right.mp hinter_eq
  refine ⟨?_, ?_⟩
  · simp [A, GolayBounds.weight_eq_card_support, hAcard_eq]
  · simpa [A, B] using! hB_subset

/-!
## Every 5-set is contained in a weight-8 codeword
-/

/--
In an extended binary Golay code, every 5-subset of coordinates is contained in the support of some
weight-8 codeword.
-/
public theorem exists_weight8Word_of_mem_powersetCard5
    (C : Code 24) (hC : IsExtendedBinaryGolayCode C)
    (T : Finset (Fin 24)) (hT : T ∈ (Finset.univ : Finset (Fin 24)).powersetCard 5) :
    ∃ w : BinWord 24, w ∈ C ∧ weight w = 8 ∧ T ⊆ support w := by
  have hTcard : T.card = 5 := (Finset.mem_powersetCard.1 hT).2
  have hTnonempty : T.Nonempty := by
    have : 0 < T.card := by
      rw [hTcard]
      decide
    exact Finset.card_pos.mp this
  rcases hTnonempty with ⟨p, hpT⟩
  -- build the weight-5 indicator word and puncture at `p` to obtain a weight-4 word in length 23
  let v24 : BinWord 24 := wordOfFinset (n := 24) T
  let v23 : BinWord 23 := puncture23 (p := p) v24
  have hv24_support : support v24 = T := support_wordOfFinset (n := 24) T
  have hv24_weight : weight v24 = 5 := by
    simpa [v24, GolayBounds.weight_eq_card_support, support_wordOfFinset] using! hTcard
  have hp_support : p ∈ support v24 := by simpa [hv24_support] using! hpT
  have hv23_weight : weight v23 = 4 := by
    -- puncturing removes exactly one `1` since `p ∈ support v24`
    have hsucc : weight v23 + 1 = weight v24 := by
      simpa [v23] using! weight_puncture23_add_one_of_mem_support (p := p) (w := v24) hp_support
    simp_all
  -- Perfect decoding in the punctured code: represent `v23` as `c + e` with `c ∈ punctureCode` and
  -- `weight e ≤ 3`.
  have hsurj := decodeMap23_surj (C := C) (hC := hC) (p := p)
  have : v23 ∈ decodeMap23 '' (punctureCode23 (p := p) C ×ˢ errorWords23) := by
    simp [hsurj]
  rcases this with ⟨⟨c, e⟩, hce, hceEq⟩
  rcases hce with ⟨hcC, heE⟩
  have hv23_eq : v23 = fun i => c i + e i := by
    simpa [decodeMap23] using! hceEq.symm
  -- show `c ≠ 0` since `v23` has weight `4`
  have hc0 : c ≠ 0 := by
    intro hc0
    subst hc0
    -- then `v23 = e`, so `weight v23 ≤ 3`, contradict `=4`
    have hv23e : v23 = e := by
      funext i
      simp [hv23_eq]
    have hwle : weight v23 ≤ 3 := by
      have : weight e ≤ 3 := by simpa [errorWords23] using! heE
      simpa [hv23e] using! this
    omega
  -- `hammingDist c v23 ≤ 3` since `v23 = c + e`
  have hdist : hammingDist c v23 ≤ 3 := by
    have he : weight e ≤ 3 := by simpa [errorWords23] using! heE
    have hcv : (fun i => c i + v23 i) = e := by
      funext i
      have hi : v23 i = c i + e i := congrArg (fun f => f i) hv23_eq
      have hi' : c i + v23 i = c i + (c i + e i) := congrArg (fun t => c i + t) hi
      -- normalize in the `ZMod 2` additive commutative group
      simpa [add_assoc, add_left_comm, add_comm, GolayBounds.zmod2_add_self,
        zmod2_add_add_cancel_left] using! hi'
    simpa [hammingDist, hcv] using! he
  -- lower bound on `weight c`: `c` is a nonzero codeword, so it has weight ≥ 7
  have hmin7 : 7 ≤ weight c := by
    -- lift `c` to a codeword in `C` and use `minDist C = 8`
    rcases hcC with ⟨w24, hw24C, rfl⟩
    -- if the punctured codeword is nonzero, then the original is nonzero
    have hw24_ne : w24 ≠ 0 := by
      intro hw
      subst hw
      exact hc0 (by simp)
    have hmin : 8 ≤ minDist C := hC.minDist_ge
    have hwt8 : 8 ≤ weight w24 := by
      -- `minDist ≤ dist 0 w24 = weight w24`, then use `hmin`
      have hdist_ge : 8 ≤ hammingDist (0 : BinWord 24) w24 := by
        exact
          GolayBounds.hammingDist_ge_of_minDist_ge (C := C) (d := 8) hmin
            (by simpa using! hC.linear.1) hw24C (by simpa [eq_comm] using! hw24_ne)
      simpa [hammingDist] using! hdist_ge
    -- puncturing removes at most one `1`
    have : weight w24 ≤ weight (puncture23 (p := p) w24) + 1 :=
      weight_le_weight_puncture23_add_one (p := p) (w := w24)
    have : 7 ≤ weight (puncture23 (p := p) w24) := by omega
    simpa [puncture23] using! this
  have hcw7 : weight c = 7 ∧ support v23 ⊆ support c :=
    weight7_of_close_weight4 (c := c) (v := v23) hmin7 hv23_weight hdist
  have hc_weight : weight c = 7 := hcw7.1
  have hsup : support v23 ⊆ support c := hcw7.2
  -- lift `c` back to `w ∈ C` and conclude `weight w = 8` and `T ⊆ support w`
  rcases hcC with ⟨w, hwC, rfl⟩
  have hw_ne : w ≠ 0 := by
    intro hw
    subst hw
    exact hc0 (by simp)
  have hmin8 : 8 ≤ minDist C := hC.minDist_ge
  have hw_weight_ge8 : 8 ≤ weight w := by
    -- same as above: use distance from zero
    have hdist_ge : 8 ≤ hammingDist (0 : BinWord 24) w := by
      exact
        GolayBounds.hammingDist_ge_of_minDist_ge (C := C) (d := 8) hmin8
          (by simpa using! hC.linear.1) hwC (by simpa [eq_comm] using! hw_ne)
    simpa [hammingDist] using! hdist_ge
  -- show `w p = 1` (otherwise puncturing preserves weight and we get `weight w = 7`)
  have hwp1 : w p = (1 : ZMod 2) := by
    by_contra hwp
    have hp_not : p ∉ support w := by
      intro hp
      exact hwp ((GolayBounds.mem_support (w := w) p).1 hp)
    -- then `erase p` does nothing, so weights match
    have : weight (puncture23 (p := p) w) = weight w := by
      -- compare supports via `support_puncture23_map`
      have hmap := support_puncture23_map (p := p) w
      have herase : (support w).erase p = support w := Finset.erase_eq_of_notMem hp_not
      have hcard :
          (support (puncture23 (p := p) w)).card = (support w).card := by
        have : (support (puncture23 (p := p) w)).card = ((support w).erase p).card := by
          simpa [Finset.card_map] using! congrArg Finset.card hmap
        simpa [herase] using! this
      simp [GolayBounds.weight_eq_card_support, hcard]
    -- but `puncture23 w = c` has weight 7
    have hpun : weight (puncture23 (p := p) w) = 7 := by
      simpa [puncture23] using! hc_weight
    have : weight w = 7 := by
      calc
        weight w = weight (puncture23 (p := p) w) := this.symm
        _ = 7 := hpun
    omega
  have hw_weight : weight w = 8 := by
    -- `weight w ≤ weight puncture + 1` and `weight puncture = 7`
    have hle : weight w ≤ weight (puncture23 (p := p) w) + 1 :=
      weight_le_weight_puncture23_add_one (p := p) (w := w)
    have : weight (puncture23 (p := p) w) = 7 := by simpa [puncture23] using! hc_weight
    omega
  -- support inclusion `T ⊆ support w`
  have hp_in : p ∈ support w := by
    -- `p ∈ support w ↔ w p = 1`
    exact (GolayBounds.mem_support (w := w) p).2 hwp1
  have hrest :
      T.erase p ⊆ support w := by
    -- map `support v23 ⊆ support (puncture23 w)` through `succAbove`
    have hmap_w := support_puncture23_map (p := p) w
    have hmap_v := support_puncture23_map (p := p) v24
    have hsub_map :
        Finset.map (Fin.succAboveEmb p) (support v23) ⊆
          Finset.map (Fin.succAboveEmb p) (support (puncture23 (p := p) w)) := by
      exact Finset.map_subset_map.2 hsup
    -- rewrite both sides using the mapping lemmas
    have : T.erase p ⊆ (support w).erase p := by
      -- `support v24 = T`
      have hv24 : support v24 = T := hv24_support
      -- `map support v23 = erase p T`
      have hl : Finset.map (Fin.succAboveEmb p) (support v23) = T.erase p := by
        -- `v23 = puncture v24`
        simpa [v23, v24, puncture23, hv24] using! hmap_v
      have hr :
          Finset.map (Fin.succAboveEmb p) (support (puncture23 (p := p) w)) =
            (support w).erase p := by
        simpa [puncture23] using! hmap_w
      simpa [hl, hr] using! hsub_map
    have herase : (support w).erase p ⊆ support w := by
      intro x hx
      exact (Finset.mem_erase.1 hx).2
    exact this.trans herase
  have hTsub : T ⊆ support w := by
    exact (Finset.erase_subset_iff_of_mem hp_in).mp hrest
  exact ⟨w, hwC, hw_weight, hTsub⟩

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.Weight8CountAux
