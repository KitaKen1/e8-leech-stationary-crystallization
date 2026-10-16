-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayDefs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeFromLattice


/-!
# Gauge operations on a `ContainsDn` frame

This file defines the basic "gauge" operations on the `Dₙ` frame data `ContainsDn C n` used in the
shell-to-Leech bridge (BS81 Lemma 21): reindexing the frame by a permutation and flipping signs
coordinatewise.

We record how these operations interact with `scaledCoord` and with the extracted code
`CodeFromLattice.codeFromLattice`.

## Main definitions
* `Shell4IsometryDnFrameGauge.sign`
* `Shell4IsometryDnFrameGauge.signFlip`

## Main statement
* `Shell4IsometryDnFrameGauge.codeFromLattice_eq_codeFromLattice_signFlip`

-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps

noncomputable section

open scoped RealInnerProductSpace

open Uniqueness.BS81
open Uniqueness.BS81.CodingTheory
open Uniqueness.BS81.Thm15.Lemma21

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace Shell4IsometryDnFrameGauge

open Uniqueness.BS81.Thm15.Lemma20

/-!
### Basic sign gadget
-/

/-- The sign `-1` (if `b = true`) or `1` (if `b = false`). -/
@[expose] public def sign (b : Bool) : ℝ := if b then (-1 : ℝ) else 1

@[simp] lemma sign_false : sign false = (1 : ℝ) := by simp [sign]
@[simp] lemma sign_true : sign true = (-1 : ℝ) := by simp [sign]

@[simp] lemma abs_sign (b : Bool) : |sign b| = (1 : ℝ) := by
  cases b <;> simp [sign]

@[simp] lemma sign_mul_self (b : Bool) : sign b * sign b = (1 : ℝ) := by
  cases b <;> simp [sign]

/-!
### `ContainsDn` gauge operations (as explicit constructors)
-/

/-- Reindex a `Dₙ` frame by a permutation of coordinates. -/
def reindex
    {C : Set ℝ²⁴} {n : ℕ} (hDn : ContainsDn C n) (π : Equiv (Fin n) (Fin n)) :
    ContainsDn C n where
  e := fun i => hDn.e (π i)
  ortho := Orthonormal.comp hDn.ortho π π.injective
  minVec_mem := by
    intro i j hij
    have hij' : π i ≠ π j := by
      intro hEq
      exact hij (π.injective hEq)
    simpa using! hDn.minVec_mem (π i) (π j) hij'

/-- Flip signs of the `Dₙ` frame coordinatewise (the "sign gauge"). -/
@[expose] public def signFlip
    {C : Set ℝ²⁴} {n : ℕ} (hDn : ContainsDn C n) (s : Fin n → Bool) :
    ContainsDn C n where
  e := fun i => (sign (s i)) • hDn.e i
  ortho := by
    refine ⟨?_, ?_⟩
    · intro i
      calc
        ‖sign (s i) • hDn.e i‖ = ‖sign (s i)‖ * ‖hDn.e i‖ := by simp [norm_smul]
        _ = (1 : ℝ) := by simp [abs_sign, hDn.ortho.1 i]
    · intro i j hij
      have h0 : (⟪hDn.e i, hDn.e j⟫ : ℝ) = 0 := hDn.ortho.2 hij
      cases hs_i : s i <;> cases hs_j : s j <;>
        simp [sign, hs_i, hs_j, h0, inner_neg_left, inner_neg_right]
  minVec_mem := by
    intro i j hij
    have hmem := hDn.minVec_mem i j hij
    have hplus : (Real.sqrt 2 • (hDn.e i + hDn.e j)) ∈ latticeShell4 C := hmem.1
    have hminus : (Real.sqrt 2 • (hDn.e i - hDn.e j)) ∈ latticeShell4 C := hmem.2
    have hplus_neg : -(Real.sqrt 2 • (hDn.e i + hDn.e j)) ∈ latticeShell4 C :=
      latticeShell4_neg_mem (C := C) hplus
    have hminus_neg : -(Real.sqrt 2 • (hDn.e i - hDn.e j)) ∈ latticeShell4 C :=
      latticeShell4_neg_mem (C := C) hminus
    -- Case split on the two sign choices. Each case is a rewrite to `hplus/hminus` up to negation.
    cases hs_i : s i <;> cases hs_j : s j
    · exact ⟨by simpa [sign, hs_i, hs_j] using! hplus, by simpa [sign, hs_i, hs_j] using! hminus⟩
    · exact ⟨by
        simpa [sign, hs_i, hs_j, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using! hminus,
      by
        simpa [sign, hs_i, hs_j, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using! hplus⟩
    · exact ⟨by
        simpa [sign, hs_i, hs_j, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using! hminus_neg,
      by
        simpa [sign, hs_i, hs_j, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using! hplus_neg⟩
    · exact ⟨by
        simpa [sign, hs_i, hs_j, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using! hplus_neg,
      by
        simpa [sign, hs_i, hs_j, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using! hminus_neg⟩

/-!
### Coordinate lemmas under sign flips / reindexing
-/

lemma scaledCoord_sign_smul (e : Fin 24 → ℝ²⁴) (s : Fin 24 → Bool) (i : Fin 24) (x : ℝ²⁴) :
    scaledCoord (fun j => (sign (s j)) • e j) i x = (sign (s i)) * scaledCoord e i x := by
  cases hs : s i <;>
    simp [scaledCoord, coord, sign, hs]

/-!
### `codeFromLattice` behavior under gauge changes
-/

lemma zmod2_div2_neg_eq_of_even {t : ℤ} (ht : Even t) :
    ((((-t) / 2 : ℤ) : ZMod 2)) = (((t / 2 : ℤ) : ZMod 2)) := by
  have hdiv : (-t) / 2 = -(t / 2) := Int.neg_ediv_of_dvd ht.two_dvd
  simp [hdiv]

/-- `codeFromLattice` is invariant under sign flips of the `ContainsDn` frame. -/
public theorem codeFromLattice_eq_codeFromLattice_signFlip
    (C : Set ℝ²⁴)
    (hDn : ContainsDn C 24) (s : Fin 24 → Bool) :
    CodeFromLattice.codeFromLattice (C := C) (signFlip hDn s) =
      CodeFromLattice.codeFromLattice (C := C) hDn := by
  ext c
  constructor
  · rintro ⟨x, hxL, z, hzCoord, hzEven, hc⟩
    let z' : Fin 24 → ℤ := fun i => if s i then -z i else z i
    refine ⟨x, hxL, z', ?_, ?_, ?_⟩
    · intro i
      have hzEq : sign (s i) * scaledCoord hDn.e i x = (z i : ℝ) := by
        simpa [signFlip, scaledCoord_sign_smul (e := hDn.e) (s := s)] using! hzCoord i
      have hzEq' : scaledCoord hDn.e i x = sign (s i) * (z i : ℝ) := by
        have h :
            sign (s i) * (sign (s i) * scaledCoord hDn.e i x) = sign (s i) * (z i : ℝ) := by
          simpa using! congrArg (fun t => sign (s i) * t) hzEq
        rw [← mul_assoc, sign_mul_self, one_mul] at h
        exact h
      cases hs : s i <;> simpa [z', hs, sign] using! hzEq'
    · intro i
      cases hs : s i
      · simpa [z', hs] using! hzEven i
      · simpa [z', hs] using! (hzEven i).neg
    · intro i
      cases hs : s i
      · simpa [z', hs] using! hc i
      · simpa [z', hs, zmod2_div2_neg_eq_of_even (t := z i) (hzEven i)] using! hc i
  · rintro ⟨x, hxL, z, hzCoord, hzEven, hc⟩
    let z' : Fin 24 → ℤ := fun i => if s i then -z i else z i
    refine ⟨x, hxL, z', ?_, ?_, ?_⟩
    · intro i
      have hsc :
          scaledCoord (signFlip hDn s).e i x = sign (s i) * scaledCoord hDn.e i x := by
        simpa [signFlip] using!
          (scaledCoord_sign_smul (e := hDn.e) (s := s) (i := i) (x := x))
      cases hs : s i <;> simp [z', hsc, hs, sign, hzCoord i]
    · intro i
      cases hs : s i
      · simpa [z', hs] using! hzEven i
      · simpa [z', hs] using! (hzEven i).neg
    · intro i
      cases hs : s i
      · simpa [z', hs] using! hc i
      · simpa [z', hs, zmod2_div2_neg_eq_of_even (t := z i) (hzEven i)] using! hc i

theorem codeFromLattice_reindex_eq_permuteCode
    (C : Set ℝ²⁴)
    (hDn : ContainsDn C 24) (π : Equiv (Fin 24) (Fin 24)) :
    CodeFromLattice.codeFromLattice (C := C) (reindex hDn π) =
      permuteCode (n := 24) π (CodeFromLattice.codeFromLattice (C := C) hDn) := by
  ext c
  constructor
  · rintro ⟨x, hxL, z, hzCoord, hzEven, hc⟩
    refine ⟨(fun i => c (π.symm i)), ?_, ?_⟩
    · refine ⟨x, hxL, (fun i => z (π.symm i)), ?_, ?_, ?_⟩
      · intro i
        have : scaledCoord (reindex hDn π).e (π.symm i) x = (z (π.symm i) : ℝ) := hzCoord (π.symm i)
        simpa [reindex, scaledCoord, coord] using! this
      · intro i
        simpa using! hzEven (π.symm i)
      · intro i
        simpa using! hc (π.symm i)
    · funext i
      simp [permuteWord]
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨x, hxL, z, hzCoord, hzEven, hc⟩
    refine ⟨x, hxL, (fun i => z (π i)), ?_, ?_, ?_⟩
    · intro i
      have : scaledCoord hDn.e (π i) x = (z (π i) : ℝ) := hzCoord (π i)
      simpa [reindex] using! this
    · intro i
      simpa using! hzEven (π i)
    · intro i
      simpa [permuteWord] using! hc (π i)

end Shell4IsometryDnFrameGauge

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
