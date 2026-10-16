-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.DnFrameGauge
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.Bridge
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.Auxiliary
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.BasepointTightness
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Isometry.CodeIsGolayCountFinal

/-!
# Gauge fixing for the shell-to-Leech bridge

This file packages the gauge-fixing step in the shell-to-Leech bridge (BS81 Lemma 21): we
simultaneously choose

* a coordinate permutation `σ` aligning `codeFromLattice` with the Leech parity code,
* a coordinatewise sign flip of the `D₂₄` frame, and
* a Type III basepoint whose (permuted) integer coordinates match `rowInt last`.

## Main statement
* `Shell4IsometryGaugeFix.exists_perm24_equiv_leechParityCode_and_basepoint`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps

noncomputable section

open scoped RealInnerProductSpace

open Uniqueness.BS81
open Uniqueness.BS81.CodingTheory
open Uniqueness.BS81.Thm15.Lemma21
open CodeIsGolayCountFinal

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace Shell4IsometryGaugeFix

open Shell4IsometryAux

open Uniqueness.BS81.Thm15.Lemma21.IsometrySteps.Shell4IsometryDnFrameGauge
open Uniqueness.BS81.Thm15.Lemma21.IsometrySteps.Shell4IsometryBasepoint
open Shell4IsometryLeechConstructionA

/--
Choose the code equivalence `σ` together with a sign-gauge of the `D₂₄` frame and an odd basepoint
aligned to the concrete Leech generator row `rowInt last`.

We do not claim such a basepoint exists for an arbitrary fixed `σ`; instead, we choose `σ` and the
basepoint simultaneously using tightness of the Type III injection.

Paper reference:
* BS81 Lemma 21, as organized in `paper/Notes/CodingTheory/bs81_lemma21_golay_inputs.tex`.

Lean strategy:
1. Choose `σ` giving `permuteCode σ codeFromLattice = leechParityCode`.
2. Use the *tightness* upgrade (`injMap_surjOn_of_sharp_count`) to pick a Type-III vector whose
   unique `±3` coordinate is at index `σ 0`.
3. Flip signs of the `D₂₄` frame coordinatewise so this Type-III vector has integer coordinates
   exactly `rowInt last (σ.symm ·)` in the gauged frame.
4. Use `codeFromLattice_eq_codeFromLattice_signFlip` to keep the same `σ` for code alignment.
-/
public theorem exists_perm24_equiv_leechParityCode_and_basepoint
    (Cset : Set ℝ²⁴)
    (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg Cset)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn Cset 24) :
    ∃ σ : Equiv (Fin 24) (Fin 24), ∃ s : Fin 24 → Bool,
      let hDn' : Uniqueness.BS81.Thm15.Lemma20.ContainsDn Cset 24 := signFlip hDn s
      permuteCode (n := 24) σ (CodeFromLattice.codeFromLattice (C := Cset) hDn') =
          Shell4IsometryLeechParityCode.leechParityCode ∧
        OddBasepointRowLast (Cset := Cset) hDn' σ := by
  have hGolay :
      Uniqueness.BS81.CodingTheory.IsExtendedBinaryGolayCode
        (CodeFromLattice.codeFromLattice (C := Cset) hDn) :=
    isExtendedBinaryGolayCode_codeFromLattice (C := Cset) hEq hDn
  let codeC := CodeFromLattice.codeFromLattice (C := Cset) hDn
  rcases
      Shell4IsometryAux.exists_perm24_equiv_leechParityCode_of_isExtendedBinaryGolayCode
        (C := codeC) hGolay with
    ⟨σ, hσ⟩
  -- Choose a Type-III basepoint `u₀` and its integer coordinates `z₀`.
  rcases CodeIsGolayCountFinal.exists_typeIII_basepoint (C := Cset) hEq hDn with
    ⟨u0, hu0, z0, hz0, hz0Pat⟩
  -- Use tightness/surjectivity to pick a Type-III vector whose special index is `σ 0`.
  have hsurj :=
    injMap_surjOn_of_sharp_count (C := Cset) (hEq := hEq) (hDn := hDn) u0 hu0 z0 hz0 hz0Pat
  have hp_mem :
      (σ 0, (0 : BinWord 24)) ∈
        (Set.univ : Set (Fin 24)) ×ˢ codeC := by
    exact ⟨by simp, (CodeFromLattice.codeFromLattice_linear (C := Cset) hDn).1⟩
  rcases hsurj (σ 0, (0 : BinWord 24)) hp_mem with ⟨y, hyIII, hyMap⟩
  -- Extract integer coordinates `zy` for `y`.
  set zy : Fin 24 → ℤ := Classical.choose hyIII.2
  have hzy : ∀ i, scaledCoord hDn.e i y = (zy i : ℝ) :=
    (Classical.choose_spec hyIII.2).1
  have hzyPat : isPattern3 zy := (Classical.choose_spec hyIII.2).2
  -- The special index of `zy` is `σ 0`.
  have hj : specialIdx zy hzyPat = σ 0 := by
    have hfst : (injMap (C := Cset) hDn z0 y).1 = (σ 0 : Fin 24) := by
      simpa using! congrArg Prod.fst hyMap
    have : (injMap (C := Cset) hDn z0 y).1 = specialIdx zy hzyPat := by
      simp [injMap, hyIII, zy]
    exact this.symm.trans hfst
  -- Define the sign gauge so `y` has coordinates `(-3, 1, ..., 1)` with the `-3` at index `σ 0`.
  let s : Fin 24 → Bool := fun i =>
    if hi : i = σ 0 then decide (zy i = (3 : ℤ)) else decide (zy i = (-1 : ℤ))
  let hDn' : Uniqueness.BS81.Thm15.Lemma20.ContainsDn Cset 24 := signFlip hDn s
  have hσ' :
      permuteCode (n := 24) σ (CodeFromLattice.codeFromLattice (C := Cset) hDn') =
          Shell4IsometryLeechParityCode.leechParityCode := by
    -- `codeFromLattice` is invariant under sign flips of the frame.
    have hcodeEq :
        CodeFromLattice.codeFromLattice (C := Cset) hDn' =
          CodeFromLattice.codeFromLattice (C := Cset) hDn := by
      simpa [hDn'] using! (codeFromLattice_eq_codeFromLattice_signFlip (C := Cset) (hDn := hDn) s)
    simpa [hcodeEq] using! hσ
  -- Relate `scaledCoord` in the flipped frame to the original `scaledCoord`.
  have hscaled :
      ∀ i : Fin 24, scaledCoord hDn'.e i y = (sign (s i)) * scaledCoord hDn.e i y := by
    intro i
    -- expand definitions of `scaledCoord`/`coord` and `hDn'.e`
    simp [hDn', signFlip, scaledCoord, coord, real_inner_smul_left]
    ac_rfl
  have hyCoord :
      ∀ i : Fin 24,
        scaledCoord hDn'.e i y =
          (rowInt last (σ.symm i) : ℝ) := by
    intro i
    have hz : scaledCoord hDn.e i y = (zy i : ℝ) := hzy i
    have hz' : scaledCoord hDn'.e i y = (sign (s i)) * (zy i : ℝ) := by
      simp [hscaled i, hz]
    by_cases hi : i = σ 0
    · subst hi
      -- at the special index, `zy = ±3` and we choose the sign so the value becomes `-3`.
      have hpm3 : zy (σ 0) = 3 ∨ zy (σ 0) = -3 := by
        simpa [hj] using! (specialIdx_spec zy hzyPat).1
      rcases hpm3 with h3 | hN3
      · simp [hz', s, sign, row_last_apply, h3]
      · simp [hz', s, sign, row_last_apply, hN3]
    · -- off the special index, `zy = ±1` and we choose the sign so the value becomes `1`.
      have hpm1 : zy i = 1 ∨ zy i = -1 := by
        -- use the `isPattern3` value restriction, excluding the `±3` cases by uniqueness
        have huniq : ∀ i : Fin 24, (zy i = 3 ∨ zy i = -3) → i = specialIdx zy hzyPat :=
          (specialIdx_spec zy hzyPat).2
        have hvals := hzyPat.2 i
        rcases hvals with h1 | hrest
        · exact Or.inl h1
        rcases hrest with hN1 | hrest
        · exact Or.inr hN1
        rcases hrest with h3 | hN3
        · exfalso
          have : i = σ 0 := by
            have : i = specialIdx zy hzyPat := huniq i (by grind)
            simpa [hj] using! this
          exact (hi this).elim
        · exfalso
          have : i = σ 0 := by
            have : i = specialIdx zy hzyPat := huniq i (by grind)
            simpa [hj] using! this
          exact (hi this).elim
      have hrow :
          rowInt last (σ.symm i) = (1 : ℤ) := by
        have : σ.symm i ≠ 0 := by
          intro h0
          have : i = σ 0 := by simpa using! congrArg σ h0
          exact hi this
        simp [row_last_apply, this]
      rcases hpm1 with h1 | hN1
      · simp [hz', s, sign, hi, hrow, h1]
      · simp [hz', s, sign, hi, hrow, hN1]
  have base : OddBasepointRowLast (Cset := Cset) hDn' σ := by
    refine ⟨y, ?_, hyCoord⟩
    -- `y ∈ TypeIII ⊆ shell4 ⊆ latticeL`
    exact hyIII.1.1
  exact ⟨σ, s, hσ', base⟩
end Shell4IsometryGaugeFix

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
