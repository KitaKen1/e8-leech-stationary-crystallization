-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.LeechLattice.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayConcrete
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
public import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

/-!
# The Leech parity code

This file defines the 12-generator binary code on `Fin 24` coming from the concrete Leech
generator matrix used in this repository. We call it `leechParityCode`.

We also fix an explicit coordinate permutation `leechGolayPerm : Equiv (Fin 24) (Fin 24)`
identifying `leechParityCode` with a permuted copy of the concrete extended binary Golay code
`extendedBinaryGolayConcrete`.

The permutation was computed externally by matching the octad designs (weight-8 supports) of the
two codes.

## Main definitions
* `Shell4IsometryLeechParityCode.leechGolayPerm`
* `Shell4IsometryLeechParityCode.leechParityVec`
* `Shell4IsometryLeechParityCode.leechParityCode`

## Main statement
* `Shell4IsometryLeechParityCode.leechParityCode_eq_leechGolayCode`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
noncomputable section

open scoped BigOperators

open Module

open Uniqueness.BS81.CodingTheory

namespace Shell4IsometryLeechParityCode

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-!
### A fixed coordinate permutation between concrete Golay and the Leech parity code

`leechGolayPerm` is an `Equiv (Fin 24) (Fin 24)` whose action is specified by the image of each
index `0, ..., 23`.
-/

def leechGolayPermFun : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 4, 14, 16, 20, 5, 18, 8, 12, 7, 21, 9, 10, 19, 11, 13, 15, 22, 6, 17, 23]

def leechGolayPermInvFun : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 4, 8, 21, 12, 10, 14, 15, 17, 11, 18, 5, 19, 6, 22, 9, 16, 7, 13, 20, 23]

/-- The coordinate permutation identifying `leechParityCode` with a permuted concrete Golay code. -/
public noncomputable def leechGolayPerm : Equiv (Fin 24) (Fin 24) where
  toFun := leechGolayPermFun
  invFun := leechGolayPermInvFun
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-!
### The Leech parity basis vectors and their span (as a `Code`)
-/

/--
The parity-code word attached to the `i`-th Leech generator row.

For `i = 23` the row is used directly modulo `2`; for the other rows we take the entrywise halves
(`z / 2`) modulo `2`.
-/
@[expose] public def leechParityVec (i : Fin 24) : BinWord 24 :=
  if i = (23 : Fin 24) then
    fun j : Fin 24 => (leechGeneratorMatrixInt i j : ZMod 2)
  else
    fun j : Fin 24 => ((leechGeneratorMatrixInt i j / 2 : ℤ) : ZMod 2)

/-- The ordered list of 12 indices in `Fin 24` used to define the parity-code generators. -/
@[expose] public def leechParityBasisIdx : Fin 12 → Fin 24
  | ⟨0, _⟩ => ⟨23, by decide⟩
  | ⟨1, _⟩ => ⟨22, by decide⟩
  | ⟨2, _⟩ => ⟨21, by decide⟩
  | ⟨3, _⟩ => ⟨20, by decide⟩
  | ⟨4, _⟩ => ⟨19, by decide⟩
  | ⟨5, _⟩ => ⟨18, by decide⟩
  | ⟨6, _⟩ => ⟨17, by decide⟩
  | ⟨7, _⟩ => ⟨15, by decide⟩
  | ⟨8, _⟩ => ⟨14, by decide⟩
  | ⟨9, _⟩ => ⟨13, by decide⟩
  | ⟨10, _⟩ => ⟨11, by decide⟩
  | ⟨11, _⟩ => ⟨7, by decide⟩

/-- The `t`-th parity-code generator word. -/
@[expose] public def leechParityBasisVec (t : Fin 12) : BinWord 24 :=
  leechParityVec (leechParityBasisIdx t)

/-- The `ZMod 2`-submodule spanned by the 12 parity-code generators. -/
@[expose] public noncomputable def leechParitySubmodule : Submodule (ZMod 2) (BinWord 24) :=
  Submodule.span (ZMod 2) (Set.range leechParityBasisVec)

/-- The Leech parity code as a set of words (the carrier of `leechParitySubmodule`). -/
@[expose] public def leechParityCode : Code 24 :=
  (leechParitySubmodule : Set (BinWord 24))

/-!
### Linearity and cardinalities (used to identify with a permuted concrete Golay code)
-/

lemma isLinearCode_leechGolayCode :
    IsLinearCode (permuteCode (n := 24) leechGolayPerm extendedBinaryGolayConcrete) := by
  have hlin : IsLinearCode extendedBinaryGolayConcrete :=
    Uniqueness.BS81.CodingTheory.extendedBinaryGolayConcrete_linear
  simpa using! isLinearCode_permuteCode (σ := leechGolayPerm) (C := extendedBinaryGolayConcrete) hlin

def msgOfMask (m : Nat) : BinWord 12 :=
  fun i : Fin 12 => if Nat.testBit m i.1 then (1 : ZMod 2) else 0

lemma leechParityBasisVec_mem_leechGolayCode (t : Fin 12) :
    leechParityBasisVec t ∈ permuteCode (n := 24) leechGolayPerm extendedBinaryGolayConcrete := by
  -- Witness message masks found by octad-design matching.
  let m : Nat :=
    match t.1 with
    | 0 => 4095
    | 1 => 928
    | 2 => 2272
    | 3 => 190
    | 4 => 51
    | 5 => 313
    | 6 => 2101
    | 7 => 1209
    | 8 => 949
    | 9 => 179
    | 10 => 303
    | 11 => 31
    | _ => 0
  have hm :
      permuteWord (n := 24) leechGolayPerm (encode (msgOfMask m)) = leechParityBasisVec t := by
    -- brute-force equality of words on `Fin 24`, split into 24 coordinate goals for each `t`
    fin_cases t <;> ext k <;> fin_cases k <;> decide
  refine ⟨encode (msgOfMask m), ?_, hm⟩
  -- `encode msg` lies in the concrete Golay code by definition.
  -- (This rewrites `extendedBinaryGolayConcrete = range encode`.)
  -- unfold `extendedBinaryGolayConcrete` to a range membership.
  simp [extendedBinaryGolayConcrete_eq_range_encode]

lemma leechParityCode_subset_leechGolayCode :
    leechParityCode ⊆ permuteCode (n := 24) leechGolayPerm extendedBinaryGolayConcrete := by
  intro w hw
  -- Use span induction in `leechParitySubmodule`, discharging the goal using only the linear-code
  -- closure properties.
  -- Work with the `ZMod 2`-submodule membership.
  change w ∈ leechParitySubmodule at hw
  -- set-level linear code structure for the target.
  have hlin := isLinearCode_leechGolayCode
  -- Induct over `span`.
  refine
    Submodule.span_induction
      (p := fun w _ => w ∈ permuteCode (n := 24) leechGolayPerm extendedBinaryGolayConcrete)
      (x := w) ?_ ?_ ?_ ?_ hw
  · intro x hx
    rcases hx with ⟨t, rfl⟩
    exact leechParityBasisVec_mem_leechGolayCode t
  · simpa using! hlin.1
  · intro x y _hx _hy hx' hy'
    exact hlin.2 x y hx' hy'
  · intro a x _hx hx'
    -- Scalars are `0` or `1` in `ZMod 2`.
    rcases (GolayBounds.zmod2_eq_zero_or_eq_one a) with rfl | rfl
    · simpa using! hlin.1
    · simpa using! hx'

lemma ncard_leechGolayCode :
    Set.ncard (permuteCode (n := 24) leechGolayPerm extendedBinaryGolayConcrete) = 2 ^ 12 := by
  classical
  have hinj : Function.Injective (permuteWord (n := 24) leechGolayPerm) :=
    permuteWord_injective (σ := leechGolayPerm)
  -- `ncard` is preserved under images of injective maps.
  simpa [permuteCode] using!
    (Set.ncard_image_of_injective (s := extendedBinaryGolayConcrete)
      (f := (permuteWord (n := 24) leechGolayPerm)) hinj).trans
        (Uniqueness.BS81.CodingTheory.extendedBinaryGolayConcrete_card)

lemma ncard_leechParityCode :
    Set.ncard leechParityCode = 2 ^ 12 := by
  classical
  -- Linear independence of the 12 generators by an explicit 12×12 inverse matrix on coordinate
  -- evaluation.
  let eval12 : (BinWord 24) →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
    { toFun := fun w t => w (leechParityBasisIdx t)
      map_add' := by
        tauto
      map_smul' := by
        tauto }
  let A : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
    fun i j => eval12 (leechParityBasisVec j) i
  -- A concrete normalization of `A` (computed externally once and checked below).
  let A0 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
    ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
      ![1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      ![1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1]]
  let Ainv0 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
    ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      ![1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0],
      ![0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1]]
  have hA : A = A0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hmulL : Ainv0 * A0 = 1 := by
    decide +kernel
  have hmulR : A0 * Ainv0 = 1 := by
    decide +kernel
  have hprojInd :
      LinearIndependent (ZMod 2) (fun j : Fin 12 => eval12 (leechParityBasisVec j)) := by
    -- the columns of `A0` are independent since `Ainv0` is a left inverse for `A0`
    have hmulVec_inj : Function.Injective A0.mulVec := by
      intro v w hvw
      have hvw' := congrArg (fun u => Ainv0.mulVec u) hvw
      simpa [Matrix.mulVec_mulVec, hmulL] using! hvw'
    have hcols0 : LinearIndependent (ZMod 2) A0.col :=
      (Matrix.mulVec_injective_iff (M := A0)).1 hmulVec_inj
    have hcols : LinearIndependent (ZMod 2) A.col := by
      simpa [hA] using! hcols0
    simpa [A, Matrix.col] using! hcols
  have hliWord : LinearIndependent (ZMod 2) leechParityBasisVec :=
    LinearIndependent.of_comp (f := eval12) hprojInd
  have hfinrank : Module.finrank (ZMod 2) leechParitySubmodule = 12 := by
    simpa [leechParitySubmodule] using!
      (finrank_span_eq_card (R := ZMod 2) (b := leechParityBasisVec) hliWord)
  have hcard : Fintype.card leechParitySubmodule = 2 ^ 12 := by
    simpa [hfinrank, ZMod.card] using!
      (Module.card_eq_pow_finrank (K := ZMod 2) (V := leechParitySubmodule))
  -- Turn the set-level `ncard` into the card of the carrier type.
  have hncard :
      Set.ncard (leechParitySubmodule : Set (BinWord 24)) = Fintype.card leechParitySubmodule := by
    simp [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  simpa [leechParityCode] using! (hncard.trans hcard)

/-- `leechParityCode` is a coordinate permutation of the concrete extended binary Golay code. -/
public theorem leechParityCode_eq_leechGolayCode :
    leechParityCode = permuteCode (n := 24) leechGolayPerm extendedBinaryGolayConcrete := by
  classical
  have hfin : (permuteCode (n := 24) leechGolayPerm extendedBinaryGolayConcrete).Finite :=
    (Set.finite_univ : (Set.univ : Set (BinWord 24)).Finite).subset (by intro _ _; trivial)
  apply Set.eq_of_subset_of_ncard_le (ht := hfin)
  · exact leechParityCode_subset_leechGolayCode
  · -- both sets have the same cardinality `2^12`
    simp [ncard_leechParityCode, ncard_leechGolayCode]

end Shell4IsometryLeechParityCode

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
