-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
import Mathlib.Data.Finset.Powerset
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctadsAux

/-!
# Hamming bound for length-`24` codes

Assuming `8 ≤ minDist C`, puncturing one coordinate gives an injection into `𝔽₂^{23}` whose image
has pairwise distance at least `7`. Radius-`3` Hamming balls in `𝔽₂^{23}` are disjoint and have
cardinality `2^11`, yielding the bound `|C| ≤ 2^12`.

## Main statement
* `CodeCardBound.ncard_code_le_two_pow12_of_minDist_ge`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped BigOperators
open Set

open Uniqueness.BS81.CodingTheory
open Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctadsAux

namespace CodeCardBound

/-- Puncture a length-`24` word to a length-`23` word by deleting the `0`-th coordinate. -/
def puncture23 (w : BinWord 24) : BinWord 23 :=
  fun i : Fin 23 => w (Fin.succ i)

/-- The image of a length-`24` code under `puncture23`. -/
def punctureCode23 (C : Code 24) : Code 23 :=
  puncture23 '' C

lemma weight_le_puncture_add_one (d : BinWord 24) :
    weight d ≤ weight (puncture23 d) + 1 := by
  have hsubset :
      support d ⊆ insert (0 : Fin 24) ((support (puncture23 d)).image Fin.succ) := by
    intro i hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · rcases Fin.eq_succ_of_ne_zero hi0 with ⟨j, rfl⟩
      have : (puncture23 d) j = 1 := by
        have : d (Fin.succ j) = 1 := (CodingTheory.GolayBounds.mem_support d (Fin.succ j)).1 hi
        simpa [puncture23] using! this
      have hj : j ∈ support (puncture23 d) := (CodingTheory.GolayBounds.mem_support _ j).2 this
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_image.2 ⟨j, hj, rfl⟩))
  have hcard := Finset.card_le_card hsubset
  have h0not : (0 : Fin 24) ∉ (support (puncture23 d)).image Fin.succ := by
    intro h0
    rcases Finset.mem_image.1 h0 with ⟨j, _hj, hj0⟩
    exact (Fin.succ_ne_zero j) hj0
  have hR :
      (insert (0 : Fin 24) ((support (puncture23 d)).image Fin.succ)).card =
        ((support (puncture23 d)).image Fin.succ).card + 1 := by
    simp [Finset.card_insert_of_notMem, h0not]
  have hinj : Function.Injective (Fin.succ : Fin 23 → Fin 24) := by
    simpa using! (Fin.succ_injective 23)
  have himg : ((support (puncture23 d)).image Fin.succ).card = (support (puncture23 d)).card := by
    simpa using! (Finset.card_image_of_injective _ hinj)
  have : (support d).card ≤ (support (puncture23 d)).card + 1 := by
    -- combine the bounds
    have : (support d).card ≤ ((support (puncture23 d)).image Fin.succ).card + 1 := by
      simpa [hR] using! hcard
    simpa [himg] using! this
  simpa [CodingTheory.GolayBounds.weight_eq_card_support] using! this

lemma hammingDist_puncture_ge_of_ge
    {x y : BinWord 24} (hxy : 8 ≤ hammingDist x y) :
    7 ≤ hammingDist (puncture23 x) (puncture23 y) := by
  have hle :
      hammingDist x y ≤ hammingDist (puncture23 x) (puncture23 y) + 1 := by
    have := weight_le_puncture_add_one (d := fun i => x i + y i)
    simpa [hammingDist, puncture23, add_assoc, add_left_comm, add_comm] using! this
  omega

lemma puncture23_injOn_of_minDist_ge
    (C : Code 24) (hmin : 8 ≤ minDist C) :
    Set.InjOn puncture23 C := by
  intro x hx y hy hxy
  by_contra hne
  have hdist_ge : 8 ≤ hammingDist x y :=
    CodingTheory.GolayBounds.hammingDist_ge_of_minDist_ge (C := C) (d := 8) hmin hx hy hne
  -- If punctures are equal, then distance is ≤ 1.
  have hdist_le : hammingDist x y ≤ 1 := by
    have hEq : ∀ j : Fin 23, x (Fin.succ j) = y (Fin.succ j) := by
      intro j
      simpa [puncture23] using! congrArg (fun w => w j) hxy
    have hsupp : support (fun i => x i + y i) ⊆ ({0} : Finset (Fin 24)) := by
      intro i hi
      by_cases hi0 : i = 0
      · simp [hi0]
      · rcases Fin.eq_succ_of_ne_zero hi0 with ⟨j, rfl⟩
        have hsum0 : x (Fin.succ j) + y (Fin.succ j) = 0 := by simp [hEq j]
        have hsum1 : x (Fin.succ j) + y (Fin.succ j) = (1 : ZMod 2) :=
          (CodingTheory.GolayBounds.mem_support (w := fun i => x i + y i) (i := Fin.succ j)).1 hi
        have : (0 : ZMod 2) = 1 := hsum0.symm.trans hsum1
        exact (False.elim <| zero_ne_one this)
    have hcard := Finset.card_le_card hsupp
    simpa [hammingDist, CodingTheory.GolayBounds.weight_eq_card_support] using! hcard
  exact (not_lt_of_ge hdist_ge) (lt_of_le_of_lt hdist_le (by decide))

/-- The radius-`3` Hamming ball in `𝔽₂^{23}`, implemented as a `Finset`. -/
def ball3 (w : BinWord 23) : Finset (BinWord 23) :=
  Finset.univ.filter fun u => hammingDist u w ≤ 3

lemma card_ball3_zero : (ball3 (0 : BinWord 23)).card = 2 ^ 11 := by
  -- `ball3 0 = {u | weight u ≤ 3}`.
  have hdescr : ball3 (0 : BinWord 23) = Finset.univ.filter fun u : BinWord 23 => weight u ≤ 3 := by
    ext u
    unfold ball3
    rw [Finset.mem_filter, Finset.mem_filter]
    simp [hammingDist, CodingTheory.weight]
  -- Partition by supports of size `k = 0,1,2,3`.
  let U : Finset (Fin 23) := Finset.univ
  let W : ℕ → Finset (BinWord 23) := fun k =>
    (U.powersetCard k).image (fun S : Finset (Fin 23) => wordOfFinset (n := 23) S)
  have hsplit :
      (Finset.univ.filter fun u : BinWord 23 => weight u ≤ 3) =
        (Finset.range 4).biUnion W := by
    ext u
    constructor
    · intro hu
      have hle : weight u ≤ 3 := (Finset.mem_filter.1 hu).2
      refine Finset.mem_biUnion.2 ?_
      refine ⟨(support u).card, ?_, ?_⟩
      · have : (support u).card ≤ 3 := by
          simpa [CodingTheory.GolayBounds.weight_eq_card_support] using! hle
        exact Finset.mem_range.2 (Nat.lt_succ_of_le this)
      · refine Finset.mem_image.2 ⟨support u, ?_, ?_⟩
        · refine Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, ?_⟩
          simp
        · simpa using! (word_eq_wordOfFinset_support (w := u)).symm
    · intro hu
      rcases Finset.mem_biUnion.1 hu with ⟨k, hk, huk⟩
      rcases Finset.mem_image.1 huk with ⟨S, hS, rfl⟩
      have hk' : k ≤ 3 := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
      have hcard : S.card = k := (Finset.mem_powersetCard.1 hS).2
      refine Finset.mem_filter.2 ⟨by simp, ?_⟩
      have : weight (wordOfFinset (n := 23) S) = S.card := by
        simp [GolayBounds.weight_eq_card_support]
      simpa [this, hcard] using! hk'
  have hdisj : ((Finset.range 4 : Finset ℕ) : Set ℕ).PairwiseDisjoint W := by
    intro a ha b hb hab
    refine Finset.disjoint_left.2 ?_
    intro u hua hub
    rcases Finset.mem_image.1 hua with ⟨Sa, hSa, rfl⟩
    rcases Finset.mem_image.1 hub with ⟨Sb, hSb, hEq⟩
    have hcarda : Sa.card = a := (Finset.mem_powersetCard.1 hSa).2
    have hcardb : Sb.card = b := (Finset.mem_powersetCard.1 hSb).2
    have hSab : Sa = Sb := by
      have : support (wordOfFinset Sa) = support (wordOfFinset Sb) := by
        simpa using! (congrArg support hEq).symm
      simpa [support_wordOfFinset] using! this
    have : a = b := by
      calc
        a = Sa.card := by simp [hcarda]
        _ = Sb.card := by simp [hSab]
        _ = b := by simp [hcardb]
    exact hab this
  have hcardW : ∀ k, k ∈ Finset.range 4 → (W k).card = Nat.choose 23 k := by
    intro k hk
    have hinj : Function.Injective fun S : Finset (Fin 23) => wordOfFinset (n := 23) S :=
      fun S T h => by simpa [support_wordOfFinset] using! congrArg support h
    calc
      (W k).card = (U.powersetCard k).card := by
        simpa [W, U] using! (Finset.card_image_of_injective (s := U.powersetCard k) hinj)
      _ = Nat.choose 23 k := by
        simp [U, Finset.card_powersetCard]
  have hsum : (∑ k ∈ Finset.range 4, Nat.choose 23 k) = 2 ^ 11 := by decide
  calc
    (ball3 (0 : BinWord 23)).card
        = (Finset.univ.filter fun u : BinWord 23 => weight u ≤ 3).card := by simp [hdescr]
    _ = ((Finset.range 4).biUnion W).card := by simp [hsplit]
    _ = ∑ k ∈ Finset.range 4, (W k).card := by simpa using! (Finset.card_biUnion hdisj)
    _ = ∑ k ∈ Finset.range 4, Nat.choose 23 k :=
          Finset.sum_congr rfl hcardW
    _ = 2 ^ 11 := hsum

lemma card_ball3 (w : BinWord 23) : (ball3 w).card = 2 ^ 11 := by
  -- translate by `w`
  let τ : BinWord 23 → BinWord 23 := fun u i => u i + w i
  have hdist_translate (x y : BinWord 23) :
      hammingDist (τ x) (τ y) = hammingDist x y := by
    have hfun : (fun i => (x i + w i) + (y i + w i)) = fun i => x i + y i := by
      funext i
      grind (splits := 0)
    simp [τ, hammingDist, hfun]
  have hτ_invol : Function.Involutive τ := by
    intro u; funext i; simp [τ, add_assoc]
  have hτ_inj : Function.Injective τ := hτ_invol.injective
  have himage : ball3 w = (ball3 0).image τ := by
    ext u
    constructor
    · intro hu
      refine Finset.mem_image.2 ⟨τ u, ?_, hτ_invol u⟩
      have hu' : hammingDist (τ u) 0 ≤ 3 := by
        have hu'' : hammingDist (τ u) (τ w) ≤ 3 := by
          simpa [hdist_translate u w] using! (Finset.mem_filter.1 hu).2
        simpa [τ] using! hu''
      exact Finset.mem_filter.2 ⟨by simp, hu'⟩
    · rintro hu
      rcases Finset.mem_image.1 hu with ⟨u', hu', rfl⟩
      refine Finset.mem_filter.2 ⟨by simp, ?_⟩
      have hu'' : hammingDist (τ u') (τ 0) ≤ 3 := by
        simpa [hdist_translate u' 0] using! (Finset.mem_filter.1 hu').2
      simpa [τ] using! hu''
  have hcard : (ball3 w).card = (ball3 (0 : BinWord 23)).card := by
    simp [himage, Finset.card_image_of_injective, hτ_inj]
  simpa [hcard] using! card_ball3_zero

section HammingBound

/-- Hamming bound: a length-`24` binary code with `8 ≤ minDist` has at most `2^12` words. -/
public theorem ncard_code_le_two_pow12_of_minDist_ge
    (C : Code 24) (hmin : 8 ≤ minDist C) :
    Set.ncard C ≤ 2 ^ 12 := by
  classical
  have hinj : Set.InjOn puncture23 C := puncture23_injOn_of_minDist_ge C hmin
  have hcard_eq : Set.ncard (punctureCode23 C) = Set.ncard C := by
    simpa [punctureCode23] using!
      hinj.ncard_image
  -- Pairwise distance ≥ 7 in the punctured code.
  have hdist7 :
      ∀ {x y : BinWord 23},
        x ∈ punctureCode23 C → y ∈ punctureCode23 C → x ≠ y → 7 ≤ hammingDist x y := by
    intro x y hx hy hxy
    rcases hx with ⟨x0, hx0, rfl⟩
    rcases hy with ⟨y0, hy0, rfl⟩
    have hne : x0 ≠ y0 := by
      exact ne_of_apply_ne puncture23 hxy
    have hdist8 : 8 ≤ hammingDist x0 y0 :=
      CodingTheory.GolayBounds.hammingDist_ge_of_minDist_ge (C := C) (d := 8) hmin hx0 hy0 hne
    exact hammingDist_puncture_ge_of_ge hdist8
  let C' : Finset (BinWord 23) := (punctureCode23 C).toFinset
  have hdisj : (C' : Set (BinWord 23)).PairwiseDisjoint ball3 := by
    intro x hx y hy hne
    refine Finset.disjoint_left.2 ?_
    intro u hux huy
    have hx3 : hammingDist u x ≤ 3 := (Finset.mem_filter.1 hux).2
    have hy3 : hammingDist u y ≤ 3 := (Finset.mem_filter.1 huy).2
    have htri :
        hammingDist x y ≤ hammingDist x u + hammingDist u y := by
      -- triangle inequality specialized to `𝔽₂^n`: `x+y = (x+u) + (u+y)`.
      have hxy :
          (fun i => x i + y i) = fun i => (x i + u i) + (u i + y i) := by
        funext i
        -- in `ZMod 2`, `u+u=0`
        simp [add_left_comm, add_comm]
      have :=
        CodingTheory.GolayBounds.weight_add_le
          (x := fun i => x i + u i) (y := fun i => u i + y i)
      simpa [hammingDist, hxy, add_assoc, add_left_comm, add_comm] using! this
    have hx3' : hammingDist x u ≤ 3 := by
      -- symmetry of `hammingDist`
      simpa [hammingDist, add_comm] using! hx3
    have hsum : hammingDist x u + hammingDist u y ≤ 6 := by
      have := Nat.add_le_add hx3' hy3
      simpa using! this
    have hdist_le : hammingDist x y ≤ 6 := le_trans htri hsum
    have hdist_ge : 7 ≤ hammingDist x y := by
      have hxC : x ∈ punctureCode23 C := by simpa [C'] using! hx
      have hyC : y ∈ punctureCode23 C := by simpa [C'] using! hy
      exact hdist7 hxC hyC hne
    exact (not_lt_of_ge hdist_ge) (lt_of_le_of_lt hdist_le (by decide))
  have hsum_le :
      (∑ w ∈ C', (ball3 w).card) ≤ (Finset.univ : Finset (BinWord 23)).card := by
    have hsubset : C'.biUnion ball3 ⊆ (Finset.univ : Finset (BinWord 23)) := by
      intro u hu
      exact Finset.mem_univ u
    have hcard_union : (C'.biUnion ball3).card = ∑ w ∈ C', (ball3 w).card := by
      simpa using! (Finset.card_biUnion hdisj)
    have := Finset.card_le_card hsubset
    simpa [hcard_union] using! this
  have hconst : (∑ w ∈ C', (ball3 w).card) = C'.card * (2 ^ 11) := by
    simp [card_ball3]
  have hambient : (Finset.univ : Finset (BinWord 23)).card = 2 ^ 23 := by
    simp [BinWord]
  have hmul : C'.card * (2 ^ 11) ≤ 2 ^ 23 := by
    simpa [hconst, hambient] using! hsum_le
  have hcardC' : Set.ncard (punctureCode23 C) = C'.card := by
    simpa [C'] using! (Set.ncard_eq_toFinset_card' (punctureCode23 C))
  grind only

end HammingBound

end CodeCardBound

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
