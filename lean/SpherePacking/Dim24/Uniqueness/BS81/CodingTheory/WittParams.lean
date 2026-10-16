-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerLambda

/-!
# Numerical parameters for the Witt design `S(5,8,24)`

This file records the concrete `λ_s` parameters for a Steiner system `S(5,8,24)`:
the numbers of blocks containing a given `s`-subset for `s = 1,2,3,4`, and the total number of
blocks.

Each statement is obtained from the general double-counting identity in `SteinerLambda.lean` by
plugging in `v = 24`, `k = 8`, `t = 5`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittParams

variable (S : SteinerSystem 24 8 5)

/-- A `4`-subset is contained in exactly `5` blocks of a Witt design. -/
public lemma card_blocksContaining_four (T : Finset (Fin 24)) (hT : T.card = 4) :
    (S.blocksContaining T).card = 5 := by
  have hmul :
      (S.blocksContaining T).card * Nat.choose (8 - 4) (5 - 4) =
        Nat.choose (24 - 4) (5 - 4) := by
    simpa [SteinerSystem.blocksContaining] using!
      (SteinerSystem.card_blocksContaining_mul_choose (S := S) (T := T) (s := 4) hT (by decide))
  have h' : (S.blocksContaining T).card * 4 = 20 := by simpa using! hmul
  exact Nat.mul_right_cancel (by decide : 0 < 4) (by simpa using! h'.trans (by decide : 20 = 5 * 4))

/-- A `3`-subset is contained in exactly `21` blocks of a Witt design. -/
public lemma card_blocksContaining_three (T : Finset (Fin 24)) (hT : T.card = 3) :
    (S.blocksContaining T).card = 21 := by
  have h' : (S.blocksContaining T).card * 10 = 210 := by
    simpa [SteinerSystem.blocksContaining] using!
      (SteinerSystem.card_blocksContaining_mul_choose (S := S) (T := T) (s := 3) hT (by decide))
  refine Nat.mul_right_cancel (by decide : 0 < 10) ?_
  simpa using! h'.trans (by decide : 210 = 21 * 10)

/-- A `2`-subset is contained in exactly `77` blocks of a Witt design. -/
public lemma card_blocksContaining_two (T : Finset (Fin 24)) (hT : T.card = 2) :
    (S.blocksContaining T).card = 77 := by
  have h' : (S.blocksContaining T).card * 20 = 1540 := by
    simpa [SteinerSystem.blocksContaining] using!
      (SteinerSystem.card_blocksContaining_mul_choose (S := S) (T := T) (s := 2) hT (by decide))
  refine Nat.mul_right_cancel (by decide : 0 < 20) ?_
  simpa using! h'.trans (by decide : 1540 = 77 * 20)

/-- A `1`-subset is contained in exactly `253` blocks of a Witt design. -/
public lemma card_blocksContaining_one (T : Finset (Fin 24)) (hT : T.card = 1) :
    (S.blocksContaining T).card = 253 := by
  have h' : (S.blocksContaining T).card * 35 = 8855 := by
    simpa [SteinerSystem.blocksContaining] using!
      (SteinerSystem.card_blocksContaining_mul_choose (S := S) (T := T) (s := 1) hT (by decide))
  refine Nat.mul_right_cancel (by decide : 0 < 35) ?_
  simpa using! h'.trans (by decide : 8855 = 253 * 35)

/-- A Witt design `S(5,8,24)` has exactly `759` blocks. -/
public lemma card_blocks (S : SteinerSystem 24 8 5) :
    S.blocksFinset.card = 759 := by
  -- Take `s=0`: `#blocks * choose 8 5 = choose 24 5`.
  have hmul :
      S.blocksFinset.card * Nat.choose (8 - 0) (5 - 0) =
        Nat.choose (24 - 0) (5 - 0) := by
    -- `blocksContaining ∅` is `blocksFinset`.
    have h0 :
        (S.blocksContaining (T := (∅ : Finset (Fin 24)))).card * Nat.choose (8 - 0) (5 - 0) =
          Nat.choose (24 - 0) (5 - 0) := by
      simpa [SteinerSystem.blocksContaining] using!
        (SteinerSystem.card_blocksContaining_mul_choose (S := S) (s := 0)
          (T := (∅ : Finset (Fin 24))) (by simp) (by decide))
    simpa [SteinerSystem.blocksContaining] using! h0
  have h' : S.blocksFinset.card * 56 = 42504 := by
    simpa using! hmul
  refine Nat.mul_right_cancel (by decide : 0 < 56) ?_
  simpa using! h'.trans (by decide : 42504 = 759 * 56)

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittParams
