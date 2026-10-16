-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# A concrete extended binary Golay code

We build the standard `[24,12,8]` code from a `2-(11,5,2)` biplane as in
`paper/Bro08Witt/brouwer_witt_designs_golay_mathieu.tex`.

The rows of the `12×24` systematic generator matrix `(I | X)` generate the code, where
`X = ( 0 1ᵀ ; 1 (J-B) )` and `B` is the biplane incidence matrix.

This file proves *existence* of a code satisfying `IsExtendedBinaryGolayCode` (linearity, card
`2^12`, and minimum distance `8`).

The minimum distance is certified by a computable `Finset` minimum over the `2^12-1` nonzero
messages.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open scoped BigOperators

/-- Messages for the systematic encoder: binary words of length `12`. -/
public abbrev Msg := BinWord 12

/-- Codewords produced by the encoder: binary words of length `24`. -/
public abbrev Word := BinWord 24

/-!
## The biplane incidence matrix `B`

Points are indexed by `Fin 11`, identified with `ℤ/11ℤ`. Blocks are the translates of the set of
nonzero squares `{1,3,4,5,9}`.
-/

/-- The set of nonzero squares `{1,3,4,5,9}` in `ZMod 11`. -/
@[expose] public def squareSet : Finset (ZMod 11) :=
  { (1 : ZMod 11), 3, 4, 5, 9 }

set_option backward.isDefEq.respectTransparency false in
/-- The biplane incidence matrix, encoded as a function `Fin 11 → Fin 11 → ZMod 2`. -/
@[expose] public def biplaneIncidence (i j : Fin 11) : ZMod 2 :=
  -- `j ∈ {1,3,4,5,9} + i` ↔ `j - i ∈ {1,3,4,5,9}`.
  if ((j : ZMod 11) - (i : ZMod 11)) ∈ squareSet then (1 : ZMod 2) else 0

/-!
## The `12×12` right half `X`

We treat `Fin 12` as `0` and `Fin 11` via `Fin.cases`.

`X = ( 0 1ᵀ ; 1 (J-B) )`, so:
- first row: `0` then eleven `1`s;
- other rows: leading `1`, then the complement of the corresponding biplane block.
-/

/-- The `12×12` matrix `X` defining the right half of the systematic generator `(I | X)`. -/
@[expose] public def X (i j : Fin 12) : ZMod 2 :=
  Fin.cases
    (Fin.cases (0 : ZMod 2) (fun _ => (1 : ZMod 2)) j)
    (fun i' : Fin 11 =>
      Fin.cases (1 : ZMod 2) (fun j' : Fin 11 => (1 : ZMod 2) + biplaneIncidence i' j') j)
    i

/-!
## Encoding map `encode : 𝔽₂¹² → 𝔽₂²⁴` for the systematic generator matrix `(I | X)`
-/

/-- Parity bits for a message `m`, given by multiplying `m` against the columns of `X`. -/
@[expose] public def parity (m : Msg) (j : Fin 12) : ZMod 2 :=
  ∑ i : Fin 12, m i * X i j

/-- The systematic encoder associated to the generator matrix `(I | X)`. -/
@[expose] public def encode (m : Msg) : Word :=
  fun k : Fin 24 =>
    if hk : (k.1 < 12) then
      m ⟨k.1, hk⟩
    else
      parity m ⟨k.1 - 12, by
        have hk' : 12 ≤ k.1 := Nat.le_of_not_gt hk
        omega⟩

lemma encode_left (m : Msg) (i : Fin 12) :
    encode m ⟨i.1, by omega⟩ = m i := by
  simp [encode]

lemma encode_right (m : Msg) (j : Fin 12) :
    encode m ⟨12 + j.1, by omega⟩ = parity m j := by
  have hj : ¬((12 + j.1) < 12) := by
    exact Nat.not_lt.mpr (Nat.le_add_right 12 j.1)
  simp [encode, hj, parity]

lemma encode_injective : Function.Injective encode := by
  intro m m' h
  funext i
  simpa [encode_left] using!
    congrArg (fun w : Word => w ⟨i.1, by omega⟩) h

lemma encode_zero : encode (0 : Msg) = 0 := by
  ext k
  by_cases hk : k.1 < 12 <;> simp [encode, hk, parity]

lemma parity_add (m₁ m₂ : Msg) (j : Fin 12) :
    parity (fun i => m₁ i + m₂ i) j = parity m₁ j + parity m₂ j := by
  simp [parity, add_mul, Finset.sum_add_distrib]

lemma encode_add (m₁ m₂ : Msg) :
    encode (fun i => m₁ i + m₂ i) = fun k => encode m₁ k + encode m₂ k := by
  funext k
  by_cases hk : k.1 < 12 <;> simp [encode, hk, parity_add]

/-!
## The concrete code and its basic invariants
-/

/-- The concrete extended binary Golay code, defined as the range of `encode`. -/
@[expose] public def extendedBinaryGolayConcrete : Code 24 :=
  Set.range encode

/-- Unfolding lemma for `extendedBinaryGolayConcrete`. -/
public lemma extendedBinaryGolayConcrete_eq_range_encode :
    extendedBinaryGolayConcrete = Set.range encode := by
  rfl

/-- The concrete code `extendedBinaryGolayConcrete` is a linear code. -/
public lemma extendedBinaryGolayConcrete_linear : IsLinearCode extendedBinaryGolayConcrete := by
  refine ⟨⟨0, by simp [encode_zero]⟩, ?_⟩
  rintro _ _ ⟨m₁, rfl⟩ ⟨m₂, rfl⟩
  refine ⟨fun i => m₁ i + m₂ i, ?_⟩
  simpa using! (encode_add (m₁ := m₁) (m₂ := m₂))

/-- The concrete code `extendedBinaryGolayConcrete` has `2^12` codewords. -/
public lemma extendedBinaryGolayConcrete_card :
    Set.ncard extendedBinaryGolayConcrete = 2 ^ 12 := by
  simpa [extendedBinaryGolayConcrete, Msg, Nat.card_eq_fintype_card] using!
    (Set.ncard_range_of_injective (f := encode) encode_injective)

/-!
## Minimum distance via a computable minimum over messages

For a linear code given as a range of a systematic encoder, the minimum distance equals the
minimum weight among nonzero codewords, which we compute as `minWeight`.
-/

abbrev Prefix := BinWord 4
abbrev Suffix := BinWord 8

def pref (m : Msg) : Prefix :=
  fun i : Fin 4 => m ⟨i.1, by omega⟩

def suff (m : Msg) : Suffix :=
  fun i : Fin 8 => m ⟨4 + i.1, by omega⟩

def merge (p : Prefix) (s : Suffix) : Msg :=
  fun i : Fin 12 =>
    if hi : i.1 < 4 then
      p ⟨i.1, hi⟩
    else
      s ⟨i.1 - 4, by
        have hi' : 4 ≤ i.1 := Nat.le_of_not_gt hi
        omega⟩

lemma merge_pref_suff (m : Msg) : merge (pref m) (suff m) = m := by
  funext i
  by_cases hi : i.1 < 4
  · simp [merge, pref, hi]
  · simp [merge, suff, hi, Nat.add_sub_of_le (Nat.le_of_not_gt hi)]

lemma merge_zero_zero : merge (0 : Prefix) (0 : Suffix) = (0 : Msg) := by
  funext i
  by_cases hi : i.1 < 4 <;> simp [merge, hi]

abbrev SuffixIdx := Fin 256

lemma zmod2_ite_decide_eq (a : ZMod 2) :
    (if decide (a = 1) then (1 : ZMod 2) else 0) = a := by
  rcases GolayBounds.zmod2_eq_zero_or_eq_one a with rfl | rfl <;> simp

lemma zmod2_ite_eq (a : ZMod 2) :
    (if a = 1 then (1 : ZMod 2) else 0) = a := by
  rcases GolayBounds.zmod2_eq_zero_or_eq_one a with rfl | rfl <;> simp

def suffixNat (s : Suffix) : ℕ :=
  Nat.bit (decide (s 0 = 1))
    (Nat.bit (decide (s 1 = 1))
      (Nat.bit (decide (s 2 = 1))
        (Nat.bit (decide (s 3 = 1))
          (Nat.bit (decide (s 4 = 1))
            (Nat.bit (decide (s 5 = 1))
              (Nat.bit (decide (s 6 = 1))
                (Nat.bit (decide (s 7 = 1)) 0)))))))

lemma suffixNat_lt (s : Suffix) : suffixNat s < 256 := by
  have h0 : (0 : ℕ) < 2 ^ 0 := by simp
  have h1 : Nat.bit (decide (s 7 = 1)) 0 < 2 ^ 1 := (Nat.bit_lt_two_pow_succ_iff).2 h0
  have h2 : Nat.bit (decide (s 6 = 1)) (Nat.bit (decide (s 7 = 1)) 0) < 2 ^ 2 :=
    (Nat.bit_lt_two_pow_succ_iff).2 (by simpa using! h1)
  have h3 :
      Nat.bit (decide (s 5 = 1)) (Nat.bit (decide (s 6 = 1)) (Nat.bit (decide (s 7 = 1)) 0)) <
        2 ^ 3 :=
    (Nat.bit_lt_two_pow_succ_iff).2 (by simpa using! h2)
  have h4 :
      Nat.bit (decide (s 4 = 1))
          (Nat.bit (decide (s 5 = 1))
            (Nat.bit (decide (s 6 = 1)) (Nat.bit (decide (s 7 = 1)) 0))) < 2 ^ 4 :=
    (Nat.bit_lt_two_pow_succ_iff).2 (by simpa using! h3)
  have h5 :
      Nat.bit (decide (s 3 = 1))
          (Nat.bit (decide (s 4 = 1))
            (Nat.bit (decide (s 5 = 1))
              (Nat.bit (decide (s 6 = 1)) (Nat.bit (decide (s 7 = 1)) 0)))) < 2 ^ 5 :=
    (Nat.bit_lt_two_pow_succ_iff).2 (by simpa using! h4)
  have h6 :
      Nat.bit (decide (s 2 = 1))
          (Nat.bit (decide (s 3 = 1))
            (Nat.bit (decide (s 4 = 1))
              (Nat.bit (decide (s 5 = 1))
                (Nat.bit (decide (s 6 = 1)) (Nat.bit (decide (s 7 = 1)) 0))))) < 2 ^ 6 :=
    (Nat.bit_lt_two_pow_succ_iff).2 (by simpa using! h5)
  have h7 :
      Nat.bit (decide (s 1 = 1))
          (Nat.bit (decide (s 2 = 1))
            (Nat.bit (decide (s 3 = 1))
              (Nat.bit (decide (s 4 = 1))
                (Nat.bit (decide (s 5 = 1))
                  (Nat.bit (decide (s 6 = 1)) (Nat.bit (decide (s 7 = 1)) 0)))))) < 2 ^ 7 :=
    (Nat.bit_lt_two_pow_succ_iff).2 (by simpa using! h6)
  have h8 :
      Nat.bit (decide (s 0 = 1))
          (Nat.bit (decide (s 1 = 1))
            (Nat.bit (decide (s 2 = 1))
              (Nat.bit (decide (s 3 = 1))
                (Nat.bit (decide (s 4 = 1))
                  (Nat.bit (decide (s 5 = 1))
                    (Nat.bit (decide (s 6 = 1)) (Nat.bit (decide (s 7 = 1)) 0))))))) < 2 ^ 8 :=
    (Nat.bit_lt_two_pow_succ_iff).2 (by simpa using! h7)
  simpa [suffixNat] using! h8

def suffixToIdx (s : Suffix) : SuffixIdx :=
  ⟨suffixNat s, by simpa using! suffixNat_lt s⟩

def idxToSuffix (k : SuffixIdx) : Suffix :=
  fun i : Fin 8 => if (k.1.testBit i.1) then (1 : ZMod 2) else 0

lemma idxToSuffix_zero : idxToSuffix (0 : SuffixIdx) = 0 := by
  ext i
  simp [idxToSuffix]

lemma idxToSuffix_suffixToIdx (s : Suffix) : idxToSuffix (suffixToIdx s) = s := by
  funext i
  fin_cases i <;>
    simp [idxToSuffix, suffixToIdx, suffixNat, Nat.testBit_bit_succ, zmod2_ite_eq]

def chunk (p : Prefix) : Finset Msg :=
  (Finset.univ : Finset Suffix).image (fun s => merge p s)

def chunkMsgs (p : Prefix) : Finset Msg :=
  (chunk p).erase 0

def suffixBit0 : Suffix :=
  fun i : Fin 8 => if i.1 = 0 then (1 : ZMod 2) else 0

def lift4 (i : Fin 4) : Fin 12 :=
  ⟨i.1, by omega⟩

lemma merge_lift4 (p : Prefix) (s : Suffix) (i : Fin 4) :
    merge p s (lift4 i) = p i := by
  simp [merge, lift4]

lemma chunkMsgs_nonempty (p : Prefix) : (chunkMsgs p).Nonempty := by
  refine ⟨merge p suffixBit0, Finset.mem_erase.2 ?_⟩
  refine ⟨?_, Finset.mem_image.2 ⟨suffixBit0, by simp, rfl⟩⟩
  intro h0
  have h10 : (1 : ZMod 2) = 0 := by
    simpa [merge, suffixBit0] using! congrArg (fun m : Msg => m (4 : Fin 12)) h0
  exact one_ne_zero h10

def suffixIdxFinset (p : Prefix) : Finset SuffixIdx :=
  if p = 0 then (Finset.univ : Finset SuffixIdx).erase 0 else Finset.univ

lemma suffixIdxFinset_nonempty (p : Prefix) : (suffixIdxFinset p).Nonempty := by
  by_cases hp : p = 0
  · subst hp
    exact ⟨1, by simp [suffixIdxFinset]⟩
  · exact ⟨0, by simp [suffixIdxFinset, hp]⟩

def chunkMinWeight (p : Prefix) : ℕ :=
  (suffixIdxFinset p).inf' (suffixIdxFinset_nonempty p)
    (fun k => weight (encode (merge p (idxToSuffix k))))

lemma univPrefix_nonempty : (Finset.univ : Finset Prefix).Nonempty :=
  ⟨0, by simp⟩

def minWeight : ℕ :=
  (Finset.univ : Finset Prefix).inf' univPrefix_nonempty chunkMinWeight

def codewordWeight (p : Prefix) (k : SuffixIdx) : ℕ :=
  weight (encode (merge p (idxToSuffix k)))

abbrev SuffixLo := Fin 16

def mk0 (r : SuffixLo) : SuffixIdx :=
  ⟨r.1, lt_trans r.2 (by decide : 16 < 256)⟩

def mk16 (r : SuffixLo) : SuffixIdx := ⟨16 + r.1, by omega⟩
def mk32 (r : SuffixLo) : SuffixIdx := ⟨32 + r.1, by omega⟩
def mk48 (r : SuffixLo) : SuffixIdx := ⟨48 + r.1, by omega⟩
def mk64 (r : SuffixLo) : SuffixIdx := ⟨64 + r.1, by omega⟩
def mk80 (r : SuffixLo) : SuffixIdx := ⟨80 + r.1, by omega⟩
def mk96 (r : SuffixLo) : SuffixIdx := ⟨96 + r.1, by omega⟩
def mk112 (r : SuffixLo) : SuffixIdx := ⟨112 + r.1, by omega⟩
def mk128 (r : SuffixLo) : SuffixIdx := ⟨128 + r.1, by omega⟩
def mk144 (r : SuffixLo) : SuffixIdx := ⟨144 + r.1, by omega⟩
def mk160 (r : SuffixLo) : SuffixIdx := ⟨160 + r.1, by omega⟩
def mk176 (r : SuffixLo) : SuffixIdx := ⟨176 + r.1, by omega⟩
def mk192 (r : SuffixLo) : SuffixIdx := ⟨192 + r.1, by omega⟩
def mk208 (r : SuffixLo) : SuffixIdx := ⟨208 + r.1, by omega⟩
def mk224 (r : SuffixLo) : SuffixIdx := ⟨224 + r.1, by omega⟩
def mk240 (r : SuffixLo) : SuffixIdx := ⟨240 + r.1, by omega⟩

lemma codewordWeight_ge_eight_chunk0 :
    ∀ p : Prefix, ∀ r : SuffixLo, (p ≠ 0 ∨ mk0 r ≠ 0) → 8 ≤ codewordWeight p (mk0 r) := by
  decide

lemma codewordWeight_ge_eight_chunk16 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk16 r) := by decide
lemma codewordWeight_ge_eight_chunk32 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk32 r) := by decide
lemma codewordWeight_ge_eight_chunk48 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk48 r) := by decide
lemma codewordWeight_ge_eight_chunk64 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk64 r) := by decide
lemma codewordWeight_ge_eight_chunk80 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk80 r) := by decide
lemma codewordWeight_ge_eight_chunk96 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk96 r) := by decide
lemma codewordWeight_ge_eight_chunk112 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk112 r) := by decide
lemma codewordWeight_ge_eight_chunk128 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk128 r) := by decide
lemma codewordWeight_ge_eight_chunk144 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk144 r) := by decide
lemma codewordWeight_ge_eight_chunk160 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk160 r) := by decide
lemma codewordWeight_ge_eight_chunk176 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk176 r) := by decide
lemma codewordWeight_ge_eight_chunk192 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk192 r) := by decide
lemma codewordWeight_ge_eight_chunk208 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk208 r) := by decide
lemma codewordWeight_ge_eight_chunk224 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk224 r) := by decide
lemma codewordWeight_ge_eight_chunk240 :
    ∀ p : Prefix, ∀ r : SuffixLo, 8 ≤ codewordWeight p (mk240 r) := by decide

lemma codewordWeight_ge_eight_of_not_both_zero :
    ∀ p : Prefix, ∀ k : SuffixIdx, (p ≠ 0 ∨ k ≠ 0) → 8 ≤ codewordWeight p k := by
  intro p k hk
  have hklt : k.1 < 16 * 16 := by
    exact k.2
  let qv : ℕ := k.1 / 16
  have hqv : qv < 16 := Nat.div_lt_of_lt_mul hklt
  let r : SuffixLo := ⟨k.1 % 16, Nat.mod_lt _ (by decide : 0 < 16)⟩
  have hdivAddMod : 16 * (k.1 / 16) + k.1 % 16 = k.1 := by
    simpa [Nat.mul_comm] using! (Nat.div_add_mod k.1 16)
  have hval : 16 * qv + r.1 = k.1 := by
    simpa [qv, r] using! hdivAddMod
  interval_cases qv
  · have hmk : mk0 r = k := by
      ext
      simpa [mk0] using! hval
    have hk' : p ≠ 0 ∨ mk0 r ≠ 0 := by simpa [hmk] using! hk
    simpa [hmk] using! codewordWeight_ge_eight_chunk0 p r hk'
  · have hmk : mk16 r = k := by
      ext
      simpa [mk16] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk16 p r
  · have hmk : mk32 r = k := by
      ext
      simpa [mk32] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk32 p r
  · have hmk : mk48 r = k := by
      ext
      simpa [mk48] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk48 p r
  · have hmk : mk64 r = k := by
      ext
      simpa [mk64] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk64 p r
  · have hmk : mk80 r = k := by
      ext
      simpa [mk80] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk80 p r
  · have hmk : mk96 r = k := by
      ext
      simpa [mk96] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk96 p r
  · have hmk : mk112 r = k := by
      ext
      simpa [mk112] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk112 p r
  · have hmk : mk128 r = k := by
      ext
      simpa [mk128] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk128 p r
  · have hmk : mk144 r = k := by
      ext
      simpa [mk144] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk144 p r
  · have hmk : mk160 r = k := by
      ext
      simpa [mk160] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk160 p r
  · have hmk : mk176 r = k := by
      ext
      simpa [mk176] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk176 p r
  · have hmk : mk192 r = k := by
      ext
      simpa [mk192] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk192 p r
  · have hmk : mk208 r = k := by
      ext
      simpa [mk208] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk208 p r
  · have hmk : mk224 r = k := by
      ext
      simpa [mk224] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk224 p r
  · have hmk : mk240 r = k := by
      ext
      simpa [mk240] using! hval
    simpa [hmk] using! codewordWeight_ge_eight_chunk240 p r

lemma minWeight_eq_eight : minWeight = 8 := by
  -- Lower bound: every nonzero message yields weight ≥ 8.
  have hchunk_ge : ∀ p : Prefix, 8 ≤ chunkMinWeight p := by
    intro p
    unfold chunkMinWeight
    refine
      (Finset.le_inf'_iff (s := suffixIdxFinset p) (H := suffixIdxFinset_nonempty p)
          (f := fun k => codewordWeight p k)).2 ?_
    intro k hk
    have hk' : p ≠ 0 ∨ k ≠ 0 := by
      by_cases hp0 : p = 0
      · right
        exact (by simpa [suffixIdxFinset, hp0] using! hk)
      · exact Or.inl hp0
    simpa [codewordWeight] using! codewordWeight_ge_eight_of_not_both_zero p k hk'
  have hmin_ge : 8 ≤ minWeight := by
    unfold minWeight
    exact (Finset.le_inf'_iff univPrefix_nonempty chunkMinWeight).mpr fun b a => hchunk_ge b
  -- Upper bound: exhibit a weight-8 codeword (a generator row).
  let p0 : Prefix := fun i : Fin 4 => if i = 1 then (1 : ZMod 2) else 0
  have hp0 : p0 ≠ 0 := by
    trivial
  have hmin_le : minWeight ≤ 8 := by
    have h₁ : minWeight ≤ chunkMinWeight p0 := by
      unfold minWeight
      refine
        (Finset.inf'_le_iff (s := (Finset.univ : Finset Prefix)) (H := univPrefix_nonempty)
            (f := chunkMinWeight) (a := chunkMinWeight p0)).2 ?_
      exact ⟨p0, by simp, le_rfl⟩
    have h₂ : chunkMinWeight p0 ≤ codewordWeight p0 0 := by
      unfold chunkMinWeight
      refine
        (Finset.inf'_le_iff (s := suffixIdxFinset p0) (H := suffixIdxFinset_nonempty p0)
            (f := fun k => codewordWeight p0 k) (a := codewordWeight p0 0)).2 ?_
      exact ⟨0, by simp [suffixIdxFinset, hp0], le_rfl⟩
    have hw : codewordWeight p0 0 = 8 := by
      decide
    have h : minWeight ≤ codewordWeight p0 0 := h₁.trans h₂
    simpa [hw] using! h
  exact le_antisymm hmin_le hmin_ge

lemma minWeight_le_weight_encode {m : Msg} (hm : m ≠ 0) :
    minWeight ≤ weight (encode m) := by
  let p : Prefix := pref m
  let k : SuffixIdx := suffixToIdx (suff m)
  have hmin_le : minWeight ≤ chunkMinWeight p := by
    unfold minWeight
    refine
      (Finset.inf'_le_iff (s := (Finset.univ : Finset Prefix)) (H := univPrefix_nonempty)
          (f := chunkMinWeight) (a := chunkMinWeight p)).2 ?_
    exact ⟨p, by simp, le_rfl⟩
  have hk_mem : k ∈ suffixIdxFinset p := by
    by_cases hp : p = 0
    · have hsuff_ne : suff m ≠ 0 := by
        intro hs0
        have : (0 : Msg) = m := by
          have : merge (0 : Prefix) (0 : Suffix) = m := by
            simpa [hp, hs0, p] using! merge_pref_suff m
          simpa [merge_zero_zero] using! this
        exact hm (by simpa using! this.symm)
      have hk_ne : k ≠ 0 := by
        intro hk0
        have hk_suff : idxToSuffix k = suff m := by
          simpa [k] using! (idxToSuffix_suffixToIdx (s := suff m))
        have : suff m = 0 := by
          have : idxToSuffix k = 0 := by simp [hk0, idxToSuffix_zero]
          simpa [hk_suff] using! this
        exact hsuff_ne this
      have hk' : k ∈ (Finset.univ : Finset SuffixIdx).erase 0 :=
        Finset.mem_erase.2 ⟨hk_ne, by simp⟩
      simpa [suffixIdxFinset, hp] using! hk'
    · simp [suffixIdxFinset, hp]
  have hchunk_le : chunkMinWeight p ≤ weight (encode m) := by
    unfold chunkMinWeight
    refine
      (Finset.inf'_le_iff (s := suffixIdxFinset p) (H := suffixIdxFinset_nonempty p)
          (f := fun k => weight (encode (merge p (idxToSuffix k)))) (a := weight (encode m))).2 ?_
    refine ⟨k, hk_mem, ?_⟩
    have hmerge : merge p (idxToSuffix k) = m := by
      simp [p, k, idxToSuffix_suffixToIdx, merge_pref_suff m]
    simp [hmerge]
  exact hmin_le.trans hchunk_le

lemma minDist_eq_minWeight :
    minDist extendedBinaryGolayConcrete = minWeight := by
  set Sdist : Set ℕ :=
    {d : ℕ | ∃ x y : Word, x ∈ extendedBinaryGolayConcrete ∧ y ∈ extendedBinaryGolayConcrete ∧
      x ≠ y ∧ hammingDist x y = d}
  have hminDist : minDist extendedBinaryGolayConcrete = sInf Sdist := by
    rfl
  have hle : minDist extendedBinaryGolayConcrete ≤ minWeight := by
    have hp : (Finset.univ : Finset Prefix).Nonempty := univPrefix_nonempty
    rcases Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset Prefix)) (H := hp)
        (f := chunkMinWeight) with
      ⟨p, hp_mem, hp_min⟩
    have hk : (suffixIdxFinset p).Nonempty := suffixIdxFinset_nonempty p
    rcases Finset.exists_mem_eq_inf' (s := suffixIdxFinset p) (H := hk)
        (f := fun k => weight (encode (merge p (idxToSuffix k)))) with
      ⟨k, hk_mem, hk_min⟩
    let m : Msg := merge p (idxToSuffix k)
    have hm0 : m ≠ 0 := by
      by_cases hp0 : p = 0
      · subst hp0
        have hk_ne : k ≠ 0 := by
          have : k ∈ (Finset.univ : Finset SuffixIdx).erase 0 := by
            simpa [suffixIdxFinset] using! hk_mem
          exact (Finset.mem_erase.1 this).1
        have hk_suff_ne : idxToSuffix k ≠ 0 := by
          intro hs0
          -- `idxToSuffix k = 0` forces `k = 0` since all bits are `false`.
          have hbits : ∀ i, k.1.testBit i = false := by
            intro i
            by_cases hi : i < 8
            · have hki : idxToSuffix k ⟨i, hi⟩ = 0 := by simp [hs0]
              by_cases hb : k.1.testBit i
              · have h1ne : (1 : ZMod 2) ≠ 0 := one_ne_zero
                have : (1 : ZMod 2) = 0 := by
                  have hi1 : idxToSuffix k ⟨i, hi⟩ = (1 : ZMod 2) := by
                    simp [idxToSuffix, hb]
                  exact hi1.symm.trans hki
                exact (h1ne this).elim
              · simp [hb]
            · have hklt : k.1 < 2 ^ 8 := k.2
              have hi' : 8 ≤ i := Nat.le_of_not_gt hi
              have hpow : 2 ^ 8 ≤ 2 ^ i :=
                Nat.pow_le_pow_right (by decide : 0 < 2) hi'
              have : k.1 < 2 ^ i := lt_of_lt_of_le hklt hpow
              simpa using! Nat.testBit_eq_false_of_lt (n := k.1) (i := i) this
          have hk0 : k.1 = 0 := Nat.zero_of_testBit_eq_false hbits
          have : k = 0 := by
            apply Fin.ext
            simp [hk0]
          exact hk_ne this
        intro hm0'
        have hs0 : idxToSuffix k = 0 := by
          funext i
          have hi4 : (4 + i.1) < 12 := by
            have : 4 + i.1 < 4 + 8 := Nat.add_lt_add_left i.2 4
            simpa using! this
          have := congrArg (fun m : Msg => m ⟨4 + i.1, hi4⟩) hm0'
          have hlt : ¬((⟨4 + i.1, hi4⟩ : Fin 12).1 < 4) := by
            exact Nat.not_lt.mpr (Nat.le_add_right 4 i.1)
          -- evaluate `merge` at a suffix coordinate
          simpa [m, merge, hlt, idxToSuffix, Pi.zero_apply] using! this
        exact hk_suff_ne hs0
      · intro hm0'
        have hp0' : p = 0 := by
          funext i
          have := congrArg (fun m : Msg => m (lift4 i)) hm0'
          simpa [m, merge_lift4, Pi.zero_apply] using! this
        exact hp0 (hp0')
    have hmC : encode m ∈ extendedBinaryGolayConcrete := ⟨m, rfl⟩
    have h0C : encode 0 ∈ extendedBinaryGolayConcrete := ⟨0, rfl⟩
    have hdist : hammingDist (encode 0) (encode m) = minWeight := by
      have hdist' : hammingDist (encode 0) (encode m) = weight (encode m) := by
        simp [hammingDist, encode_zero]
      have hw : weight (encode m) = chunkMinWeight p := by
        have : weight (encode (merge p (idxToSuffix k))) = chunkMinWeight p := by
          change
            weight (encode (merge p (idxToSuffix k))) =
              (suffixIdxFinset p).inf' (suffixIdxFinset_nonempty p)
                (fun k => weight (encode (merge p (idxToSuffix k))))
          exact hk_min.symm
        simpa [m] using! this
      have hmin : minWeight = chunkMinWeight p := by
        have h' : chunkMinWeight p = minWeight := by
          change chunkMinWeight p =
              (Finset.univ : Finset Prefix).inf' univPrefix_nonempty chunkMinWeight
          exact hp_min.symm
        simpa using! h'.symm
      simp [hdist', hw, hmin]
    have hmem : minWeight ∈ Sdist := by
      refine ⟨encode 0, encode m, h0C, hmC, ?_, ?_⟩
      · intro hEq
        have : (0 : Msg) = m := encode_injective hEq
        exact hm0 this.symm
      · simp [hdist]
    have := Nat.sInf_le hmem
    simpa [hminDist] using! this
  have hge : minWeight ≤ minDist extendedBinaryGolayConcrete := by
    have hLB : ∀ d ∈ Sdist, minWeight ≤ d := by
      intro d hd
      rcases hd with ⟨x, y, hx, hy, hxy, rfl⟩
      rcases hx with ⟨mx, rfl⟩
      rcases hy with ⟨my, rfl⟩
      have hsum_ne : mx + my ≠ 0 := by
        intro h0
        have hmxmy : mx = my :=
          (GolayBounds.binWord_add_eq_zero_iff_eq (u := mx) (v := my)).1 (by simpa using! h0)
        exact hxy (by simp [hmxmy])
      have hdist :
          hammingDist (encode mx) (encode my) = weight (encode (mx + my)) := by
        have hwt : weight (encode (mx + my)) = weight (fun i => encode mx i + encode my i) := by
          simpa using! congrArg weight (encode_add (m₁ := mx) (m₂ := my))
        simpa [hammingDist] using! hwt.symm
      have hmin : minWeight ≤ weight (encode (mx + my)) :=
        minWeight_le_weight_encode (m := mx + my) hsum_ne
      simpa [hdist] using! hmin
    have hSdist : Sdist.Nonempty := by
      -- explicit witness distance between `encode 0` and `encode (merge p0 0)`.
      let p0 : Prefix := fun i : Fin 4 => if i = 0 then (1 : ZMod 2) else 0
      let m0 : Msg := merge p0 0
      refine ⟨hammingDist (encode 0) (encode m0), ?_⟩
      refine ⟨encode 0, encode m0, ⟨0, rfl⟩, ⟨m0, rfl⟩, ?_, rfl⟩
      trivial
    have hmin : minWeight ≤ sInf Sdist :=
      hLB (sInf Sdist) (Nat.sInf_mem hSdist)
    simpa [hminDist] using! hmin
  exact le_antisymm hle hge

/-- The concrete code `extendedBinaryGolayConcrete` satisfies `IsExtendedBinaryGolayCode`. -/
public theorem isExtendedBinaryGolayCode_extendedBinaryGolayConcrete :
    IsExtendedBinaryGolayCode extendedBinaryGolayConcrete := by
  refine ⟨extendedBinaryGolayConcrete_linear, ?_, ?_⟩
  · simp [extendedBinaryGolayConcrete_card]
  · -- `minDist = minWeight = 8`
    simp [minDist_eq_minWeight, minWeight_eq_eight]

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
