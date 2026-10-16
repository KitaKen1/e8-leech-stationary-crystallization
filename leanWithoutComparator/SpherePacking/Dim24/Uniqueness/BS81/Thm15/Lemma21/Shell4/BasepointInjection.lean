-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Isometry.Types
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Patterns
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeFromLattice
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionA
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.CodeFromLatticeDiff
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.ScaledCoord

/-!
# Type III injection used in the forcing count

This file constructs the injection used in the Type III bound in BS81 Lemma 21, mapping
`TypeIII (C := C) hDn` into `Fin 24 × codeFromLattice` by recording:

* the unique index where the integer coordinates take the value `±3`, and
* the mod-`2` word coming from the even coordinate difference to a fixed basepoint.

## Main definitions
* `specialIdx`
* `injMap`

## Main statement
* `injMap_injOn`

## References
`paper/Notes/CodingTheory/bs81_lemma21_golay_inputs.tex`, Lemma `typeIII_bound`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps.Shell4IsometryBasepoint

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Set

attribute [local instance] Classical.propDecidable

open Uniqueness.BS81
open Uniqueness.BS81.CodingTheory
open Uniqueness.BS81.Thm15.Lemma21
open CodeIsGolayCountFinal

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

local notation "shell4" => Uniqueness.BS81.latticeShell4
local notation "L" => Uniqueness.BS81.latticeL
local notation "code" => CodeFromLattice.codeFromLattice

/-- The unique index where an `isPattern3` vector has value `±3`. -/
@[expose] public def specialIdx (z : Fin 24 → ℤ) (hz : isPattern3 z) : Fin 24 :=
  Classical.choose (exists_specialIdx_of_isPattern3 (z := z) hz)

/-- Specification of `specialIdx`: it is the unique coordinate index where `z` takes the value
`±3`. -/
public lemma specialIdx_spec (z : Fin 24 → ℤ) (hz : isPattern3 z) :
    (z (specialIdx z hz) = 3 ∨ z (specialIdx z hz) = -3) ∧
      ∀ i : Fin 24, (z i = 3 ∨ z i = -3) → i = specialIdx z hz := by
  simpa [specialIdx] using!
    (Classical.choose_spec (exists_specialIdx_of_isPattern3 (z := z) hz))

/-- Two pattern-3 integer coordinate vectors are equal if they have the same special index and the
same half-word difference mod `2` relative to a fixed pattern-3 vector `z0`. -/
public lemma eq_of_isPattern3_of_specialIdx_eq_of_halfWord_sub_eq
    {zu zv z0 : Fin 24 → ℤ}
    (hpatU : isPattern3 zu) (hpatV : isPattern3 zv) (hz0Pat : isPattern3 z0)
    (hj : specialIdx zu hpatU = specialIdx zv hpatV)
    (hcode :
      (fun i : Fin 24 => (((zu i - z0 i) / 2 : ℤ) : ZMod 2)) =
        fun i : Fin 24 => (((zv i - z0 i) / 2 : ℤ) : ZMod 2)) :
    zu = zv := by
  funext i
  have hcast :
      (((zu i - z0 i) / 2 : ℤ) : ZMod 2) = (((zv i - z0 i) / 2 : ℤ) : ZMod 2) := by
    simpa using! congrArg (fun c => c i) hcode
  have heven_u : Even (zu i - z0 i) := even_sub_of_isPattern3 hpatU hz0Pat i
  have heven_v : Even (zv i - z0 i) := even_sub_of_isPattern3 hpatV hz0Pat i
  have h4 : (4 : ℤ) ∣ ((zv i - z0 i) - (zu i - z0 i)) :=
    Shell4IsometryLeechConstructionA.four_dvd_sub_of_halves_cast_eq heven_u heven_v hcast
  have h4dvd : (4 : ℤ) ∣ (zv i - zu i) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! h4
  set j : Fin 24 := specialIdx zu hpatU with hjdef
  by_cases hij : i = j
  · subst hij
    have ha : zu j = 3 ∨ zu j = -3 := (specialIdx_spec (z := zu) hpatU).1
    have hb : zv j = 3 ∨ zv j = -3 := by
      have : specialIdx zv hpatV = j := by simpa [hjdef] using! hj.symm
      simpa [this] using! (specialIdx_spec (z := zv) hpatV).1
    exact eq_of_pm3_of_four_dvd_sub ha hb (by simpa using! h4dvd)
  · have hnot3_u : ¬ (zu i = 3 ∨ zu i = -3) := by
      intro h3
      have : i = specialIdx zu hpatU := (specialIdx_spec (z := zu) hpatU).2 i h3
      exact hij (by simpa [hjdef] using! this)
    have hnot3_v : ¬ (zv i = 3 ∨ zv i = -3) := by
      intro h3
      have : i = specialIdx zv hpatV := (specialIdx_spec (z := zv) hpatV).2 i h3
      have : i = specialIdx zu hpatU := by simpa [hj.symm] using! this
      exact hij (by simpa [hjdef] using! this)
    have ha : zu i = 1 ∨ zu i = -1 := by
      rcases hpatU.2 i with h1 | hrest
      · exact Or.inl h1
      rcases hrest with hN1 | hrest
      · exact Or.inr hN1
      rcases hrest with h3 | hN3
      · exact False.elim (hnot3_u (Or.inl h3))
      · exact False.elim (hnot3_u (Or.inr hN3))
    have hb : zv i = 1 ∨ zv i = -1 := by
      rcases hpatV.2 i with h1 | hrest
      · exact Or.inl h1
      rcases hrest with hN1 | hrest
      · exact Or.inr hN1
      rcases hrest with h3 | hN3
      · exact False.elim (hnot3_v (Or.inl h3))
      · exact False.elim (hnot3_v (Or.inr hN3))
    exact eq_of_pm1_of_four_dvd_sub ha hb (by simpa using! h4dvd)

/--
The Type-III injection used in BS81 Lemma 21:
pick a basepoint `u₀ ∈ TypeIII`, then map `u ∈ TypeIII` to
`(specialIdx z(u), ρ( √8 (u-u₀))) ∈ Fin 24 × codeFromLattice`.
-/
@[expose] public def injMap
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    (z0 : Fin 24 → ℤ) :
    ℝ²⁴ → Fin 24 × BinWord 24 :=
  fun u =>
    if hu : u ∈ TypeIII (C := C) hDn then
      let z : Fin 24 → ℤ := Classical.choose hu.2
      let hpat : isPattern3 z := (Classical.choose_spec hu.2).2
      let j : Fin 24 := specialIdx z hpat
      let c : BinWord 24 := fun i : Fin 24 => (((z i - z0 i) / 2 : ℤ) : ZMod 2)
      (j, c)
    else (0, 0)

/-- `injMap` maps Type-III vectors into `Fin 24 × codeFromLattice`. -/
public lemma injMap_mapsTo
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    (u0 : ℝ²⁴) (hu0 : u0 ∈ TypeIII (C := C) hDn)
    (z0 : Fin 24 → ℤ) (hz0 : ∀ i : Fin 24, scaledCoord hDn.e i u0 = (z0 i : ℝ))
    (hz0Pat : isPattern3 z0) :
    ∀ u ∈ TypeIII (C := C) hDn,
      injMap (C := C) hDn z0 u ∈ (Set.univ : Set (Fin 24)) ×ˢ (code (C := C) hDn) := by
  intro u hu
  set z : Fin 24 → ℤ := Classical.choose hu.2 with hz_def
  have hz : ∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ) := by
    simpa [hz_def] using! (Classical.choose_spec hu.2).1
  have hpat : isPattern3 z := by
    simpa [hz_def] using! (Classical.choose_spec hu.2).2
  simp only [injMap, hu, dif_pos, mem_prod, mem_univ, true_and]
  exact
    Shell4IsometryCodeFromLatticeDiff.halfWord_sub_mem_codeFromLattice (C := C) hDn
      (hx := hu.1.1) (hy := hu0.1.1) (zx := z) (zy := z0) (hzx := hz) (hzy := hz0)
      (hEven := fun i => even_sub_of_isPattern3 hpat hz0Pat i)

/-- The Type-III injection used in BS81 Lemma 21 is injective on `TypeIII`. -/
public lemma injMap_injOn
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    (z0 : Fin 24 → ℤ) (hz0Pat : isPattern3 z0) :
    Set.InjOn (injMap (C := C) hDn z0) (TypeIII (C := C) hDn) := by
  intro u hu v hv huv
  -- unfold `injMap` at both points
  have huv' : injMap (C := C) hDn z0 u = injMap (C := C) hDn z0 v := huv
  have huv'' :
      (injMap (C := C) hDn z0 u).1 = (injMap (C := C) hDn z0 v).1 ∧
        (injMap (C := C) hDn z0 u).2 = (injMap (C := C) hDn z0 v).2 := by
    exact Prod.ext_iff.mp huv'
  -- pull out chosen integer coordinates
  set zu : Fin 24 → ℤ := Classical.choose hu.2 with hzu_def
  have hzu : ∀ i : Fin 24, scaledCoord hDn.e i u = (zu i : ℝ) := by
    simpa [hzu_def] using! (Classical.choose_spec hu.2).1
  have hpatU : isPattern3 zu := by
    simpa [hzu_def] using! (Classical.choose_spec hu.2).2
  set zv : Fin 24 → ℤ := Classical.choose hv.2 with hzv_def
  have hzv : ∀ i : Fin 24, scaledCoord hDn.e i v = (zv i : ℝ) := by
    simpa [hzv_def] using! (Classical.choose_spec hv.2).1
  have hpatV : isPattern3 zv := by
    simpa [hzv_def] using! (Classical.choose_spec hv.2).2
  -- the special indices extracted by `injMap`
  set ju : Fin 24 := specialIdx zu hpatU with hju
  set jv : Fin 24 := specialIdx zv hpatV with hjv
  have hj : ju = jv := by
    have := huv''.1
    simpa [injMap, hu, hv, zu, zv, ju, jv] using! this
  have hj' : specialIdx zu hpatU = specialIdx zv hpatV := by
    simpa [hju, hjv] using! hj
  have hcode :
      (fun i : Fin 24 => (((zu i - z0 i) / 2 : ℤ) : ZMod 2)) =
        fun i : Fin 24 => (((zv i - z0 i) / 2 : ℤ) : ZMod 2) := by
    have := huv''.2
    simpa [injMap, hu, hv, zu, zv, ju, jv] using! this
  have hz_eq : zu = zv :=
    eq_of_isPattern3_of_specialIdx_eq_of_halfWord_sub_eq
      (hpatU := hpatU) (hpatV := hpatV) (hz0Pat := hz0Pat) (hj := hj') hcode
  have hsc : ∀ i : Fin 24, scaledCoord hDn.e i u = scaledCoord hDn.e i v := by
    intro i
    -- rewrite via integer coordinate equalities
    have : zu i = zv i := congrArg (fun f : Fin 24 → ℤ => f i) hz_eq
    simp [hzu i, hzv i, this]
  exact eq_of_scaledCoord_eq (e := hDn.e) hDn.ortho hsc

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps.Shell4IsometryBasepoint
