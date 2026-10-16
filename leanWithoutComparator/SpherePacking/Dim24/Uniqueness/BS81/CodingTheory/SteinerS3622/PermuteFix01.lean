-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
import Mathlib.Data.Fin.Basic

/-!
# Permuting the last 22 coordinates while fixing `0,1`

Given `π : Equiv (Fin 22) (Fin 22)`, we extend it to an equivalence of `Fin 24`
by keeping the first two coordinates fixed. We record how this interacts with:
* `puncture22 : BinWord 24 → BinWord 22`,
* `blockFromWord : BinWord 24 → Finset (Fin 22)`, and
* `blocksFromGolay`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerS3622PermuteFix01

noncomputable section

private def fin2Sum22Equiv : Fin 2 ⊕ Fin 22 ≃ Fin 24 :=
  { toFun := Sum.elim (Fin.castAdd 22) (Fin.natAdd 2)
    invFun := fun i => @Fin.addCases 2 22 (fun _ => Fin 2 ⊕ Fin 22) Sum.inl Sum.inr i
    left_inv := by
      rintro (i | i) <;> simp
    right_inv := by
      intro i
      refine Fin.addCases (m := 2) (n := 22) (fun i => ?_) (fun i => ?_) i <;> simp }

/-- Extend a permutation of the last `22` coordinates to `Fin 24` by fixing `0` and `1`. -/
public def extendFix01 (π : Equiv (Fin 22) (Fin 22)) : Equiv (Fin 24) (Fin 24) :=
  (fin2Sum22Equiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin 2)) π)).trans fin2Sum22Equiv

private lemma fin2Sum22Equiv_symm_castAdd (i : Fin 2) :
    fin2Sum22Equiv.symm (Fin.castAdd 22 i) = Sum.inl i := by
  simp [fin2Sum22Equiv]

private lemma fin2Sum22Equiv_symm_natAdd (i : Fin 22) :
    fin2Sum22Equiv.symm (Fin.natAdd 2 i) = Sum.inr i := by
  simp [fin2Sum22Equiv]

private lemma addNat_eq_natAdd (i : Fin 22) : Fin.addNat i 2 = Fin.natAdd 2 i := by
  ext
  simp [Fin.val_addNat, Fin.val_natAdd, Nat.add_comm]

private lemma extendFix01_castAdd (π : Equiv (Fin 22) (Fin 22)) (i : Fin 2) :
    extendFix01 π (Fin.castAdd 22 i) = Fin.castAdd 22 i := by
  simp [extendFix01, fin2Sum22Equiv]

private lemma extendFix01_natAdd (π : Equiv (Fin 22) (Fin 22)) (i : Fin 22) :
    extendFix01 π (Fin.natAdd 2 i) = Fin.natAdd 2 (π i) := by
  simp [extendFix01, fin2Sum22Equiv]

/-- `extendFix01 π` fixes `0`. -/
@[simp] public lemma extendFix01_zero (π : Equiv (Fin 22) (Fin 22)) : extendFix01 π 0 = 0 := by
  simpa using! (extendFix01_castAdd (π := π) (i := 0))

/-- `extendFix01 π` fixes `1`. -/
@[simp] public lemma extendFix01_one (π : Equiv (Fin 22) (Fin 22)) : extendFix01 π 1 = 1 := by
  simpa using! (extendFix01_castAdd (π := π) (i := 1))

/-- On indices `Fin.addNat i 2`, `extendFix01 π` acts as `π` on `i : Fin 22`. -/
@[simp] public lemma extendFix01_addNat (π : Equiv (Fin 22) (Fin 22)) (i : Fin 22) :
    extendFix01 π (Fin.addNat i 2) = Fin.addNat (π i) 2 := by
  -- Reduce to the `Fin.natAdd` form used by `fin2Sum22Equiv`.
  simpa [addNat_eq_natAdd] using! (extendFix01_natAdd (π := π) i)

private lemma puncture22_permuteWord_extendFix01 (π : Equiv (Fin 22) (Fin 22)) (w : BinWord 24) :
    puncture22 (permuteWord (extendFix01 π) w) = permuteWord π (puncture22 w) := by
  funext i
  -- unfold `puncture22` and push `extendFix01` through `Fin.addNat`.
  simp [puncture22, permuteWord, extendFix01_addNat]

private lemma blockFromWord_permuteWord_extendFix01
    (π : Equiv (Fin 22) (Fin 22)) (w : BinWord 24) :
    blockFromWord (permuteWord (extendFix01 π) w) = (blockFromWord w).map π.symm.toEmbedding := by
  -- unfold `blockFromWord` and use puncture compatibility
  have hpun := puncture22_permuteWord_extendFix01 (π := π) (w := w)
  simp [blockFromWord, hpun, support_permuteWord]

/--
Description of `blocksFromGolay` for a permuted code, when the permutation fixes `0` and `1` and
permutes only the last `22` coordinates.
-/
public lemma blocksFromGolay_permuteCode_extendFix01 (π : Equiv (Fin 22) (Fin 22)) (C : Code 24) :
    blocksFromGolay (permuteCode (n := 24) (extendFix01 π) C) =
      {B : Finset (Fin 22) | (Finset.map π.toEmbedding B) ∈ blocksFromGolay C} := by
  ext B
  constructor
  · rintro ⟨w, hwC, hw8, hw11, hB⟩
    rcases hwC with ⟨w0, hw0C, rfl⟩
    refine ⟨w0, hw0C, ?_, ?_, ?_⟩
    · simpa [weight_permuteWord] using! hw8
    · rcases hw11 with ⟨h0, h1⟩
      constructor
      · simpa [startsWith11, permuteWord, extendFix01_zero] using! h0
      · simpa [startsWith11, permuteWord, extendFix01_one] using! h1
    · have hblock :
          blockFromWord (permuteWord (n := 24) (extendFix01 π) w0) =
            (blockFromWord w0).map π.symm.toEmbedding :=
        blockFromWord_permuteWord_extendFix01 (π := π) (w := w0)
      have := congrArg (Finset.map π.toEmbedding) hB
      simpa [hblock, Finset.map_map] using! this
  · rintro ⟨w, hwC, hw8, hw11, hB⟩
    refine ⟨permuteWord (n := 24) (extendFix01 π) w, ⟨w, hwC, rfl⟩, ?_, ?_, ?_⟩
    · simpa [weight_permuteWord] using! hw8
    · rcases hw11 with ⟨h0, h1⟩
      constructor
      · simpa [startsWith11, permuteWord, extendFix01_zero] using! h0
      · simpa [startsWith11, permuteWord, extendFix01_one] using! h1
    · have hblock :
          blockFromWord (permuteWord (n := 24) (extendFix01 π) w) =
            (blockFromWord w).map π.symm.toEmbedding :=
        blockFromWord_permuteWord_extendFix01 (π := π) (w := w)
      have hB' : B = (blockFromWord w).map π.symm.toEmbedding := by
        have := congrArg (Finset.map π.symm.toEmbedding) hB
        simpa [Finset.map_map] using! this
      simp [hB', hblock]

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerS3622PermuteFix01
