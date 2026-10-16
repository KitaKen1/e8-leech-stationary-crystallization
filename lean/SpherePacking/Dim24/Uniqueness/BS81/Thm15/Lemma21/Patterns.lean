-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IntegerCoords
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Coordinate patterns in BS81 Lemma 21

BS81 classify integer coordinate vectors `z : Fin 24 → ℤ` (of uniform parity) that satisfy the
shell constraint `∑ i, (z i : ℝ)^2 = 32` together with inner-product restrictions coming from the
embedded `D₂₄` frame.

The outcome is a trichotomy into three patterns, encoded by `isPattern1`, `isPattern2`,
`isPattern3`.

## Main definitions
* `isPattern1`, `isPattern2`, `isPattern3`
* `innerConstraint`

## Main statement
* `pattern_classification_of_constraints`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped BigOperators
open Finset

/-- Pattern `((±2)^8 0^16)`: exactly `16` zero entries, and all entries lie in `{0,±2}`. -/
@[expose] public def isPattern1 (z : Fin 24 → ℤ) : Prop :=
  (#{i : Fin 24 | z i = 0} = 16) ∧ (∀ i, z i = 0 ∨ z i = 2 ∨ z i = -2)

/-- Pattern `((±4)^2 0^22)`: exactly `22` zero entries, and all entries lie in `{0,±4}`. -/
@[expose] public def isPattern2 (z : Fin 24 → ℤ) : Prop :=
  (#{i : Fin 24 | z i = 0} = 22) ∧ (∀ i, z i = 0 ∨ z i = 4 ∨ z i = -4)

/-- Pattern `((±1)^23 (±3)^1)`: exactly one entry in `{±3}`, and all entries lie in `{±1,±3}`. -/
@[expose] public def isPattern3 (z : Fin 24 → ℤ) : Prop :=
  (#{i : Fin 24 | z i = 3 ∨ z i = -3} = 1) ∧ (∀ i, z i = 1 ∨ z i = -1 ∨ z i = 3 ∨ z i = -3)

/-- In pattern 1, every coordinate is even. -/
public lemma even_of_isPattern1 {z : Fin 24 → ℤ} (hz : isPattern1 z) (i : Fin 24) :
    Even (z i) := by
  rcases hz.2 i with h0 | h2 | hN2
  · exact ⟨0, by simp [h0]⟩
  · exact ⟨1, by simp [h2]⟩
  · exact ⟨-1, by simp [hN2]⟩

/-- In pattern 3, there is a unique coordinate index with value `±3`. -/
public lemma exists_specialIdx_of_isPattern3 {z : Fin 24 → ℤ} (hz : isPattern3 z) :
    ∃ j : Fin 24, (z j = 3 ∨ z j = -3) ∧ ∀ i : Fin 24, (z i = 3 ∨ z i = -3) → i = j := by
  -- Let `S := {i | z i = ±3}` as a finset; `isPattern3` says `#S = 1`.
  let S : Finset (Fin 24) := {i | z i = 3 ∨ z i = -3}
  have hcard : S.card = 1 := by
    simpa [S] using! hz.1
  rcases (Finset.card_eq_one.1 hcard) with ⟨j, hSj⟩
  refine ⟨j, ?_, ?_⟩
  · have : j ∈ S := by simp [hSj]
    simpa [S] using! this
  · intro i hi
    have hiS : i ∈ S := by simpa [S] using! hi
    have : i ∈ ({j} : Finset (Fin 24)) := by simpa [hSj] using! hiS
    simpa using! (Finset.mem_singleton.1 this)

/-- In pattern 3, every coordinate is odd. -/
public lemma notEven_of_isPattern3 {z : Fin 24 → ℤ} (hz : isPattern3 z) (i : Fin 24) :
    ¬ Even (z i) := by
  rcases hz.2 i with h | h | h | h
  · simp [h]
  · simp [h]
  · simpa [h, show (3 : ℤ) = 2 * (1 : ℤ) + 1 by ring] using!
      (Int.not_even_two_mul_add_one (1 : ℤ))
  · simpa [h, show (3 : ℤ) = 2 * (1 : ℤ) + 1 by ring] using!
      (Int.not_even_two_mul_add_one (1 : ℤ))

/-- If `z` and `z0` are both in pattern 3, then `z - z0` is coordinatewise even. -/
public lemma even_sub_of_isPattern3 {z z0 : Fin 24 → ℤ} (hz : isPattern3 z) (hz0 : isPattern3 z0)
    (i : Fin 24) :
    Even (z i - z0 i) := by
  refine (Int.even_sub).2 ⟨?_, ?_⟩
  · intro hE; exact (notEven_of_isPattern3 hz i hE).elim
  · intro hE; exact (notEven_of_isPattern3 hz0 i hE).elim

/-- If `a,b ∈ {±1}` and `4 ∣ (b - a)`, then `a = b`. -/
public lemma eq_of_pm1_of_four_dvd_sub {a b : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (h4 : (4 : ℤ) ∣ (b - a)) :
    a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> try rfl
  all_goals
    exfalso
    simp at h4

/-- If `a,b ∈ {±3}` and `4 ∣ (b - a)`, then `a = b`. -/
public lemma eq_of_pm3_of_four_dvd_sub {a b : ℤ}
    (ha : a = 3 ∨ a = -3) (hb : b = 3 ∨ b = -3) (h4 : (4 : ℤ) ∣ (b - a)) :
    a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> try rfl
  all_goals
    exfalso
    simp at h4

/-- Inner-product constraints: for `i ≠ j`, the quantities `(z i ± z j)/2` lie in the allowed set
of values coming from shell-4 geometry. -/
@[expose] public def innerConstraint (z : Fin 24 → ℤ) : Prop :=
  ∀ i j : Fin 24, i ≠ j →
    ((z i : ℝ) + (z j : ℝ)) / 2 ∈
        ({0, (1 : ℝ), (-1 : ℝ), (2 : ℝ), (-2 : ℝ), (4 : ℝ), (-4 : ℝ)} : Set ℝ) ∧
      ((z i : ℝ) - (z j : ℝ)) / 2 ∈
        ({0, (1 : ℝ), (-1 : ℝ), (2 : ℝ), (-2 : ℝ), (4 : ℝ), (-4 : ℝ)} : Set ℝ)

/-- Under the parity, sum-of-squares, and `innerConstraint` hypotheses, the coordinates satisfy one
of the three BS81 patterns. -/
public theorem pattern_classification_of_constraints
    (z : Fin 24 → ℤ)
    (hpar : ∀ i j : Fin 24, Even (z i + z j))
    (hsumsq : (∑ i : Fin 24, (z i : ℝ) ^ 2) = (32 : ℝ))
    (hinner : innerConstraint z) :
    isPattern1 z ∨ isPattern2 z ∨ isPattern3 z := by
  -- Same parity for all coordinates.
  have hEvenEq : ∀ i j : Fin 24, Even (z i) ↔ Even (z j) := by
    intro i j
    exact (Int.even_add).1 (hpar i j)
  let i0 : Fin 24 := 0
  have hEvenAll : ∀ i : Fin 24, Even (z i) ↔ Even (z i0) := by
    intro i
    simpa using! hEvenEq i i0
  -- Rewrite the sum-of-squares as a `Finset.univ` sum.
  have hsumsq_univ :
      (∑ i ∈ (Finset.univ : Finset (Fin 24)), (z i : ℝ) ^ 2) = (32 : ℝ) := by
    simpa using! hsumsq
  -- Bound each coordinate using `term ≤ sum` and `6^2 = 36 > 32`.
  have hzAbs_lt6 : ∀ i : Fin 24, |(z i : ℝ)| < (6 : ℝ) := by
    intro i
    have hnonneg :
        ∀ j ∈ (Finset.univ : Finset (Fin 24)), (0 : ℝ) ≤ (z j : ℝ) ^ 2 := by
      intro j _hj
      exact sq_nonneg (z j : ℝ)
    have hleSum :
        (z i : ℝ) ^ 2 ≤ (∑ j ∈ (Finset.univ : Finset (Fin 24)), (z j : ℝ) ^ 2) := by
      simpa using!
        (Finset.single_le_sum (s := (Finset.univ : Finset (Fin 24)))
          (f := fun j : Fin 24 => (z j : ℝ) ^ 2) hnonneg (by simp))
    have : (z i : ℝ) ^ 2 < (6 : ℝ) ^ 2 := by nlinarith [hleSum, hsumsq_univ]
    have : |(z i : ℝ)| < |(6 : ℝ)| := (sq_lt_sq).1 this
    simpa using! this
  have hzNatAbs_lt6 : ∀ i : Fin 24, (z i).natAbs < 6 := by
    intro i
    have hR : ((|z i| : ℤ) : ℝ) < (6 : ℝ) := by
      simpa [Int.cast_abs] using! hzAbs_lt6 i
    have hZ : |z i| < (6 : ℤ) := by exact_mod_cast hR
    have hNatZ : ((z i).natAbs : ℤ) < 6 := by
      have habs : |z i| = ((z i).natAbs : ℤ) := Int.abs_eq_natAbs (z i)
      -- Avoid `simp` loops between `abs` and `natAbs`.
      rw [← habs]
      exact hZ
    exact_mod_cast hNatZ
  have hzVals_even :
      ∀ i : Fin 24,
        Even (z i) → z i = 0 ∨ z i = 2 ∨ z i = -2 ∨ z i = 4 ∨ z i = -4 := by
    grind only [= Int.even_iff]
  have hzVals_odd :
      ∀ i : Fin 24,
        ¬ Even (z i) →
          z i = -5 ∨ z i = -3 ∨ z i = -1 ∨ z i = 1 ∨ z i = 3 ∨ z i = 5 := by
    grind only [= Int.even_iff]
  -- A small disjointness fact used to forbid mixing `±4` and `±2`.
  let S : Set ℝ := ({0, (1 : ℝ), (-1 : ℝ), (2 : ℝ), (-2 : ℝ), (4 : ℝ), (-4 : ℝ)} : Set ℝ)
  have hnot_mem3 : (3 : ℝ) ∉ S := by
    simp [S]
    grind
  have hnot_mem_neg3 : (-3 : ℝ) ∉ S := by
    simp [S]
    grind
  by_cases hE0 : Even (z i0)
  · -- Even case: all coordinates are `0`, `±2`, `±4`.
    have hEven : ∀ i : Fin 24, Even (z i) := fun i => (hEvenAll i).2 hE0
    have hzVals : ∀ i : Fin 24, z i = 0 ∨ z i = 2 ∨ z i = -2 ∨ z i = 4 ∨ z i = -4 := by
      intro i
      exact hzVals_even i (hEven i)
    have hnoMix :
        ∀ i j : Fin 24, i ≠ j → (z i = 4 ∨ z i = -4) → (z j = 2 ∨ z j = -2) → False := by
      intro i j hij hi4 hj2
      have hsum := (hinner i j hij).1
      have hdiff := (hinner i j hij).2
      rcases hi4 with hi4 | hi4 <;> rcases hj2 with hj2 | hj2
      · have hEq : (((z i : ℝ) + (z j : ℝ)) / 2) = (3 : ℝ) := by
          simp [hi4, hj2]
          norm_num
        have : (3 : ℝ) ∈ S := by simpa [S, hEq] using! hsum
        exact hnot_mem3 this
      · have hEq : (((z i : ℝ) - (z j : ℝ)) / 2) = (3 : ℝ) := by
          simp [hi4, hj2]
          norm_num
        have : (3 : ℝ) ∈ S := by simpa [S, hEq] using! hdiff
        exact hnot_mem3 this
      · have hEq : (((z i : ℝ) - (z j : ℝ)) / 2) = (-3 : ℝ) := by
          simp [hi4, hj2]
          norm_num
        have : (-3 : ℝ) ∈ S := by simpa [S, hEq] using! hdiff
        exact hnot_mem_neg3 this
      · have hEq : (((z i : ℝ) + (z j : ℝ)) / 2) = (-3 : ℝ) := by
          simp [hi4, hj2]
          norm_num
        have : (-3 : ℝ) ∈ S := by simpa [S, hEq] using! hsum
        exact hnot_mem_neg3 this
    by_cases hEx4 : ∃ i : Fin 24, z i = 4 ∨ z i = -4
    · -- Pattern 2: all nonzero coordinates are `±4`.
      rcases hEx4 with ⟨i4, hi4⟩
      have hzVals4 : ∀ i : Fin 24, z i = 0 ∨ z i = 4 ∨ z i = -4 := by
        intro i
        rcases hzVals i with h0 | h2 | hN2 | h4 | hN4
        · exact Or.inl h0
        · exfalso
          have hij : i4 ≠ i := by
            intro hEq
            subst hEq
            rcases hi4 with hi4 | hi4 <;> simp [hi4] at h2
          exact hnoMix i4 i hij hi4 (Or.inl h2)
        · exfalso
          have hij : i4 ≠ i := by
            intro hEq
            subst hEq
            rcases hi4 with hi4 | hi4 <;> simp [hi4] at hN2
          exact hnoMix i4 i hij hi4 (Or.inr hN2)
        · exact Or.inr (Or.inl h4)
        · exact Or.inr (Or.inr hN4)
      let sNZ : Finset (Fin 24) := Finset.univ.filter fun i : Fin 24 => z i ≠ 0
      have hsNZ : (∑ i : Fin 24, (z i : ℝ) ^ 2) = (16 : ℝ) * (sNZ.card : ℝ) := by
        have hterm : ∀ i : Fin 24, (z i : ℝ) ^ 2 = if z i = 0 then (0 : ℝ) else 16 := by
          intro i
          rcases hzVals4 i with h0 | h4 | hN4
          · simp [h0]
          · simp [h4]; norm_num
          · simp [hN4]; norm_num
        have hite :
            (∑ i ∈ (Finset.univ : Finset (Fin 24)), if z i = 0 then (0 : ℝ) else 16) =
              ∑ i ∈ (Finset.univ : Finset (Fin 24)), if z i ≠ 0 then (16 : ℝ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases hzi : z i = 0 <;> simp [hzi]
        calc
          (∑ i : Fin 24, (z i : ℝ) ^ 2) =
              ∑ i ∈ (Finset.univ : Finset (Fin 24)), (if z i = 0 then (0 : ℝ) else 16) := by
                simp [hterm]
          _ = ∑ i ∈ (Finset.univ : Finset (Fin 24)), if z i ≠ 0 then (16 : ℝ) else 0 := hite
          _ = ∑ i ∈ (Finset.univ.filter fun i : Fin 24 => z i ≠ 0), (16 : ℝ) := by
                exact Eq.symm (sum_filter (fun a => z a ≠ 0) fun a => 16)
            _ = (16 : ℝ) * (sNZ.card : ℝ) := by
                  simp [sNZ, mul_comm]
      have hsNZcard : sNZ.card = 2 := by
        have : (16 : ℝ) * (sNZ.card : ℝ) = (32 : ℝ) := by simpa [hsNZ] using! hsumsq
        have hcardR : (sNZ.card : ℝ) = (2 : ℝ) := by nlinarith
        exact_mod_cast hcardR
      have hcard0 : (#{i : Fin 24 | z i = 0}) = 22 := by
        have hpart :
            (Finset.univ.filter (fun i : Fin 24 => z i = 0)).card + sNZ.card = 24 := by
          simpa [sNZ] using!
            (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 24)))
              (p := fun i : Fin 24 => z i = 0))
        have h0card' :
            (Finset.univ.filter (fun i : Fin 24 => z i = 0)).card = 24 - sNZ.card :=
          Nat.eq_sub_of_add_eq hpart
        have h0card : (Finset.univ.filter (fun i : Fin 24 => z i = 0)).card = 22 := by
          simpa [hsNZcard] using! h0card'
        simpa using! h0card
      refine Or.inr (Or.inl ?_)
      refine ⟨hcard0, ?_⟩
      assumption
    · -- Pattern 1: no `±4`, so all coordinates are `0` or `±2`.
      have hzVals2 : ∀ i : Fin 24, z i = 0 ∨ z i = 2 ∨ z i = -2 := by
        intro i
        rcases hzVals i with h0 | h2 | hN2 | h4 | hN4
        · exact Or.inl h0
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr hN2)
        · exfalso
          exact hEx4 ⟨i, Or.inl h4⟩
        · exfalso
          exact hEx4 ⟨i, Or.inr hN4⟩
      let sNZ : Finset (Fin 24) := Finset.univ.filter fun i : Fin 24 => z i ≠ 0
      have hsNZ : (∑ i : Fin 24, (z i : ℝ) ^ 2) = (4 : ℝ) * (sNZ.card : ℝ) := by
        have hterm : ∀ i : Fin 24, (z i : ℝ) ^ 2 = if z i = 0 then (0 : ℝ) else 4 := by
          intro i
          rcases hzVals2 i with h0 | h2 | hN2
          · simp [h0]
          · simp [h2]; norm_num
          · simp [hN2]; norm_num
        have hite :
            (∑ i ∈ (Finset.univ : Finset (Fin 24)), if z i = 0 then (0 : ℝ) else 4) =
              ∑ i ∈ (Finset.univ : Finset (Fin 24)), if z i ≠ 0 then (4 : ℝ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases hzi : z i = 0 <;> simp [hzi]
        calc
          (∑ i : Fin 24, (z i : ℝ) ^ 2) =
              ∑ i ∈ (Finset.univ : Finset (Fin 24)), (if z i = 0 then (0 : ℝ) else 4) := by
                simp [hterm]
          _ = ∑ i ∈ (Finset.univ : Finset (Fin 24)), if z i ≠ 0 then (4 : ℝ) else 0 := hite
          _ = ∑ i ∈ (Finset.univ.filter fun i : Fin 24 => z i ≠ 0), (4 : ℝ) := by
                exact Eq.symm (sum_filter (fun a => z a ≠ 0) fun a => 4)
            _ = (4 : ℝ) * (sNZ.card : ℝ) := by
                  simp [sNZ, mul_comm]
      have hsNZcard : sNZ.card = 8 := by
        have : (4 : ℝ) * (sNZ.card : ℝ) = (32 : ℝ) := by simpa [hsNZ] using! hsumsq
        have hcardR : (sNZ.card : ℝ) = (8 : ℝ) := by nlinarith
        exact_mod_cast hcardR
      have hcard0 : (#{i : Fin 24 | z i = 0}) = 16 := by
        have hpart :
            (Finset.univ.filter (fun i : Fin 24 => z i = 0)).card + sNZ.card = 24 := by
          simpa [sNZ] using!
            (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 24)))
              (p := fun i : Fin 24 => z i = 0))
        have h0card' :
            (Finset.univ.filter (fun i : Fin 24 => z i = 0)).card = 24 - sNZ.card :=
          Nat.eq_sub_of_add_eq hpart
        have h0card : (Finset.univ.filter (fun i : Fin 24 => z i = 0)).card = 16 := by
          simpa [hsNZcard] using! h0card'
        simpa using! h0card
      refine Or.inl ?_
      refine ⟨hcard0, ?_⟩
      assumption
  · -- Odd case: no `0`, and the sum-of-squares forces exactly one `±3` and the rest `±1`.
    have hOdd : ∀ i : Fin 24, ¬ Even (z i) := by
      intro i hiE
      exact hE0 ((hEvenAll i).1 hiE)
    have hzNonzero : ∀ i : Fin 24, z i ≠ 0 := by
      intro i h0
      have : Even (z i) := by
        rw [h0]
        refine ⟨0, by simp⟩
      exact hOdd i this
    have hone_sq : ∀ i : Fin 24, (1 : ℝ) ≤ (z i : ℝ) ^ 2 := by
      intro i
      have habsZ : (1 : ℤ) ≤ |z i| := Int.one_le_abs (hzNonzero i)
      have habsR : (1 : ℝ) ≤ |(z i : ℝ)| := by
        have : (1 : ℝ) ≤ (|z i| : ℝ) := by exact_mod_cast habsZ
        simpa [Int.cast_abs] using! this
      have : (1 : ℝ) ≤ |(z i : ℝ)| ^ 2 := by nlinarith
      simpa [sq_abs] using! this
    have hzNo5 : ∀ i : Fin 24, z i ≠ 5 ∧ z i ≠ -5 := by
      intro i
      refine ⟨?_, ?_⟩
      · intro h5
        have hsum_decomp :
            (∑ j ∈ (Finset.univ : Finset (Fin 24)), (z j : ℝ) ^ 2) =
              (z i : ℝ) ^ 2 + ∑ j ∈ (Finset.univ.erase i), (z j : ℝ) ^ 2 := by
          have h :=
              (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 24)))
                (f := fun j : Fin 24 => (z j : ℝ) ^ 2) (a := i) (by simp)).symm
          refine h.trans ?_
          simp [add_comm]
        have hrest : (23 : ℝ) ≤ ∑ j ∈ (Finset.univ.erase i), (z j : ℝ) ^ 2 := by
          have hle :
              (∑ j ∈ (Finset.univ.erase i), (1 : ℝ)) ≤
                ∑ j ∈ (Finset.univ.erase i), (z j : ℝ) ^ 2 :=
            sum_le_sum fun i_1 a => hone_sq i_1
          have hsum1 : (∑ j ∈ (Finset.univ.erase i), (1 : ℝ)) = (23 : ℝ) := by
            simp
          simpa [hsum1] using! hle
        have hsumEq :
            (z i : ℝ) ^ 2 + ∑ j ∈ (Finset.univ.erase i), (z j : ℝ) ^ 2 = (32 : ℝ) := by
          calc
            (z i : ℝ) ^ 2 + ∑ j ∈ (Finset.univ.erase i), (z j : ℝ) ^ 2 =
                (∑ j ∈ (Finset.univ : Finset (Fin 24)), (z j : ℝ) ^ 2) :=
                  hsum_decomp.symm
            _ = (32 : ℝ) := hsumsq_univ
        have hzi : (z i : ℝ) ^ 2 = (25 : ℝ) := by
          simp [h5]
          norm_num
        nlinarith [hsumEq, hrest, hzi]
      · intro h5
        have hsum_decomp :
            (∑ j ∈ (Finset.univ : Finset (Fin 24)), (z j : ℝ) ^ 2) =
              (z i : ℝ) ^ 2 + ∑ j ∈ (Finset.univ.erase i), (z j : ℝ) ^ 2 := by
          have h :=
              (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 24)))
                (f := fun j : Fin 24 => (z j : ℝ) ^ 2) (a := i) (by simp)).symm
          refine h.trans ?_
          simp [add_comm]
        have hrest : (23 : ℝ) ≤ ∑ j ∈ (Finset.univ.erase i), (z j : ℝ) ^ 2 := by
          have hle :
              (∑ j ∈ (Finset.univ.erase i), (1 : ℝ)) ≤
                ∑ j ∈ (Finset.univ.erase i), (z j : ℝ) ^ 2 :=
            sum_le_sum fun i_1 a => hone_sq i_1
          have hsum1 : (∑ j ∈ (Finset.univ.erase i), (1 : ℝ)) = (23 : ℝ) := by
            simp
          simpa [hsum1] using! hle
        have hsumEq :
            (z i : ℝ) ^ 2 + ∑ j ∈ (Finset.univ.erase i), (z j : ℝ) ^ 2 = (32 : ℝ) := by
          calc
            (z i : ℝ) ^ 2 + ∑ j ∈ (Finset.univ.erase i), (z j : ℝ) ^ 2 =
                (∑ j ∈ (Finset.univ : Finset (Fin 24)), (z j : ℝ) ^ 2) :=
                  hsum_decomp.symm
            _ = (32 : ℝ) := hsumsq_univ
        have hzi : (z i : ℝ) ^ 2 = (25 : ℝ) := by
          simp [h5]
          norm_num
        nlinarith [hsumEq, hrest, hzi]
    have hzValsOdd : ∀ i : Fin 24, z i = 1 ∨ z i = -1 ∨ z i = 3 ∨ z i = -3 := by
      intro i
      have hi := hzVals_odd i (hOdd i)
      rcases hi with hN5 | hN3 | hN1 | h1 | h3 | h5
      · exfalso
        exact (hzNo5 i).2 (by simpa using! hN5)
      · exact Or.inr (Or.inr (Or.inr (by simpa using! hN3)))
      · exact Or.inr (Or.inl (by simpa using! hN1))
      · exact Or.inl (by simpa using! h1)
      · exact Or.inr (Or.inr (Or.inl (by simpa using! h3)))
      · exfalso
        exact (hzNo5 i).1 (by simpa using! h5)
    let s3 : Finset (Fin 24) := Finset.univ.filter fun i : Fin 24 => z i = 3 ∨ z i = -3
    have hsumForm :
        (∑ i : Fin 24, (z i : ℝ) ^ 2) = (24 : ℝ) + (8 : ℝ) * (s3.card : ℝ) := by
      have hterm :
          ∀ i : Fin 24, (z i : ℝ) ^ 2 = (1 : ℝ) + if (z i = 3 ∨ z i = -3) then (8 : ℝ) else 0 := by
        intro i
        rcases hzValsOdd i with h1 | hN1 | h3 | hN3
        · simp [h1]
        · simp [hN1]
        · simp [h3]; norm_num
        · simp [hN3]; norm_num
      have hfilter :
          (∑ i ∈ (Finset.univ.filter fun i : Fin 24 => z i = 3 ∨ z i = -3), (8 : ℝ)) =
            ∑ i ∈ (Finset.univ : Finset (Fin 24)), if (z i = 3 ∨ z i = -3) then (8 : ℝ) else 0 :=
        sum_filter (fun a => z a = 3 ∨ z a = -3) fun a => 8
      calc
        (∑ i : Fin 24, (z i : ℝ) ^ 2) =
            ∑ i : Fin 24, ((1 : ℝ) + if (z i = 3 ∨ z i = -3) then (8 : ℝ) else 0) := by
              simp [hterm]
        _ =
            (∑ i : Fin 24, (1 : ℝ)) +
              ∑ i : Fin 24, if (z i = 3 ∨ z i = -3) then (8 : ℝ) else 0 := by
              simp [Finset.sum_add_distrib]
        _ = (24 : ℝ) + ∑ i ∈ (Finset.univ : Finset (Fin 24)),
              (if (z i = 3 ∨ z i = -3) then (8 : ℝ) else 0) := by
              simp
        _ =
            (24 : ℝ) +
              ∑ i ∈ (Finset.univ.filter fun i : Fin 24 => z i = 3 ∨ z i = -3), (8 : ℝ) := by
              simpa [Finset.sum_filter] using! congrArg (fun t => (24 : ℝ) + t) hfilter.symm
        _ = (24 : ℝ) + (8 : ℝ) * (s3.card : ℝ) := by
              simp [s3, mul_comm]
    have hs3card : s3.card = 1 := by
      have : (24 : ℝ) + (8 : ℝ) * (s3.card : ℝ) = (32 : ℝ) := by simpa [hsumForm] using! hsumsq
      have hcardR : (s3.card : ℝ) = (1 : ℝ) := by nlinarith
      exact_mod_cast hcardR
    refine Or.inr (Or.inr ?_)
    refine ⟨?_, ?_⟩
    · simp [s3, hs3card]
    · intro i
      exact Or.symm ((fun {a b} => Or.comm.mp) (hzValsOdd i))

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
