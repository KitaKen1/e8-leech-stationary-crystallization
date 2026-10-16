-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeLIntegral
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IntegerCoords
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Defs
public import Mathlib.Algebra.Group.Int.Even
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16.MinNorm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Code extracted from `latticeL`

We define the binary code `codeFromLattice` associated to the lattice
`latticeL C = span_ℤ (2 • C)` appearing in BS81 Lemma 21.

A word `c : 𝔽₂^{24}` lies in `codeFromLattice` if it is obtained by reducing an even integer
coordinate vector of some `x ∈ latticeL C` in the `D₂₄` frame from Lemma 20:
`c i = ((z i / 2 : ℤ) : ZMod 2)`.

## Main definitions
* `CodeFromLattice.codeFromLattice`

## Main statements
* `CodeFromLattice.codeFromLattice_linear`

## References
The construction matches the "coordinate reduction" step in
`paper/Notes/CodingTheory/bs81_lemma21_golay_inputs.tex`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Set

open Uniqueness.BS81.CodingTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace CodeFromLattice

lemma scaledCoord_add (e : Fin 24 → ℝ²⁴) (i : Fin 24) (x y : ℝ²⁴) :
    scaledCoord e i (x + y) = scaledCoord e i x + scaledCoord e i y := by
  simp [scaledCoord, coord, inner_add_right, mul_add]

lemma scaledCoord_smul (e : Fin 24 → ℝ²⁴) (i : Fin 24) (r : ℝ) (x : ℝ²⁴) :
    scaledCoord e i (r • x) = r * scaledCoord e i x := by
  simp [scaledCoord, coord, real_inner_smul_right, mul_left_comm]

/-- Integer coordinates (`√8`-scaled) for vectors in `latticeL C`, in the `D₂₄` frame. -/
theorem exists_integer_coords_of_latticeL
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    {x : ℝ²⁴} (hx : x ∈ (latticeL C : Set ℝ²⁴)) :
    ∃ z : Fin 24 → ℤ,
      (∀ i : Fin 24, scaledCoord hDn.e i x = (z i : ℝ)) ∧
        (∀ i j : Fin 24, Even (z i + z j)) := by
  have hEq : Uniqueness.BS81.EqCase24 C :=
    Uniqueness.BS81.Thm14.EqCase24Pkg.toEqCase24 (C := C) h
  have hminL : ∀ (i j : Fin 24), i ≠ j →
      (Real.sqrt 2 • (hDn.e i + hDn.e j)) ∈ (latticeL C : Set ℝ²⁴) ∧
        (Real.sqrt 2 • (hDn.e i - hDn.e j)) ∈ (latticeL C : Set ℝ²⁴) := by
    intro i j hij
    have hplus : (Real.sqrt 2 • (hDn.e i + hDn.e j)) ∈ latticeShell4 C :=
      (hDn.minVec_mem i j hij).1
    have hminus : (Real.sqrt 2 • (hDn.e i - hDn.e j)) ∈ latticeShell4 C :=
      (hDn.minVec_mem i j hij).2
    exact ⟨hplus.1, hminus.1⟩
  have hplus : ∀ i : Fin 24, ∃ m : ℤ,
      (⟪(Real.sqrt 2) • (hDn.e i + hDn.e (jOf i)), x⟫ : ℝ) = (m : ℝ) := by
    intro i
    have hv : (Real.sqrt 2 • (hDn.e i + hDn.e (jOf i))) ∈ (latticeL C : Set ℝ²⁴) :=
      (hminL i (jOf i) (i_ne_jOf i)).1
    exact inner_latticeL_int C hEq hv hx
  have hminus : ∀ i : Fin 24, ∃ m : ℤ,
      (⟪(Real.sqrt 2) • (hDn.e i - hDn.e (jOf i)), x⟫ : ℝ) = (m : ℝ) := by
    intro i
    have hv : (Real.sqrt 2 • (hDn.e i - hDn.e (jOf i))) ∈ (latticeL C : Set ℝ²⁴) :=
      (hminL i (jOf i) (i_ne_jOf i)).2
    exact inner_latticeL_int C hEq hv hx
  choose mplus hmplus using hplus
  choose mminus hmminus using hminus
  let z : Fin 24 → ℤ := fun i => mplus i + mminus i
  have hzCoord : ∀ i : Fin 24, scaledCoord hDn.e i x = (z i : ℝ) :=
    fun i =>
      scaledCoord_eq_int_add_of_inner_sqrt2_add_sub
        hDn.e i (jOf i) x (mplus i) (mminus i) (hmplus i) (hmminus i)
  have hinner : ∀ i j : Fin 24, i ≠ j → ∃ m : ℤ,
      (⟪(Real.sqrt 2) • (hDn.e i + hDn.e j), x⟫ : ℝ) = (m : ℝ) := by
    intro i j hij
    have hv : (Real.sqrt 2 • (hDn.e i + hDn.e j)) ∈ (latticeL C : Set ℝ²⁴) :=
      (hminL i j hij).1
    exact inner_latticeL_int C hEq hv hx
  refine ⟨z, hzCoord, ?_⟩
  exact even_z_add_z_of_scaledCoord_eq_int (e := hDn.e) (x := x) (z := z) hzCoord hinner

/-- The extracted code: mod-2 reduction of the even coordinate sublattice. -/
@[expose]
public def codeFromLattice
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) : Code 24 :=
  {c : BinWord 24 |
    ∃ x : ℝ²⁴,
      x ∈ (latticeL C : Set ℝ²⁴) ∧
        ∃ z : Fin 24 → ℤ,
          (∀ i : Fin 24, scaledCoord hDn.e i x = (z i : ℝ)) ∧
            (∀ i : Fin 24, Even (z i)) ∧
              (∀ i : Fin 24, c i = ((z i / 2 : ℤ) : ZMod 2))}

lemma codeFromLattice_zero_mem (C : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    (0 : BinWord 24) ∈ codeFromLattice (C := C) hDn := by
  refine ⟨0, by simp, ?_⟩
  refine ⟨0, ?_, ?_, ?_⟩
  · intro i
    simp [scaledCoord, coord]
  · intro i
    exact ⟨0, by simp⟩
  · intro i
    simp

lemma codeFromLattice_add_mem
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    {c₁ c₂ : BinWord 24}
    (hc₁ : c₁ ∈ codeFromLattice (C := C) hDn)
    (hc₂ : c₂ ∈ codeFromLattice (C := C) hDn) :
    (fun i => c₁ i + c₂ i) ∈ codeFromLattice (C := C) hDn := by
  rcases hc₁ with ⟨x₁, hx₁L, z₁, hz₁, hz₁E, hc₁z⟩
  rcases hc₂ with ⟨x₂, hx₂L, z₂, hz₂, hz₂E, hc₂z⟩
  refine ⟨x₁ + x₂, ?_, z₁ + z₂, ?_, ?_, ?_⟩
  · -- membership in the lattice
    exact add_mem hx₁L hx₂L
  · intro i
    -- coordinate additivity
    simp [scaledCoord_add, hz₁ i, hz₂ i, Int.cast_add]
  · intro i
    rcases hz₁E i with ⟨a, ha⟩
    rcases hz₂E i with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    simp [ha, hb, add_left_comm, add_comm]
  · intro i
    -- `((z₁+z₂)/2 : ZMod 2) = (z₁/2 : ZMod 2) + (z₂/2 : ZMod 2)` for even integers
    rcases hz₁E i with ⟨a, ha⟩
    rcases hz₂E i with ⟨b, hb⟩
    -- rewrite via `z = 2 * a`
    have hdiv1 : (z₁ i / 2 : ℤ) = a := by
      -- `2 * a / 2 = a`
      simpa [ha, two_mul] using! (Int.mul_ediv_cancel_left a (two_ne_zero : (2 : ℤ) ≠ 0))
    have hdiv2 : (z₂ i / 2 : ℤ) = b := by
      simpa [hb, two_mul] using! (Int.mul_ediv_cancel_left b (two_ne_zero : (2 : ℤ) ≠ 0))
    have hdiv12 : ((z₁ i + z₂ i) / 2 : ℤ) = a + b := by
      -- `(2a + 2b)/2 = a+b`
      calc
        ((z₁ i + z₂ i) / 2 : ℤ) = ((2 * a + 2 * b) / 2 : ℤ) := by simp [ha, hb, two_mul]
        _ = ((2 * (a + b)) / 2 : ℤ) := by
              have : (2 * a + 2 * b : ℤ) = 2 * (a + b) := by ring
              simp [this]
        _ = a + b := by
          simpa [two_mul] using!
            (Int.mul_ediv_cancel_left (a + b) (two_ne_zero : (2 : ℤ) ≠ 0))
    simp [hc₁z i, hc₂z i, hdiv1, hdiv2, hdiv12, Int.cast_add]

/-- The extracted code is linear (closed under `0` and addition). -/
public theorem codeFromLattice_linear
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    IsLinearCode (codeFromLattice (C := C) hDn) := by
  refine ⟨codeFromLattice_zero_mem (C := C) hDn, ?_⟩
  intro x y hx hy
  exact codeFromLattice_add_mem (C := C) hDn hx hy

end CodeFromLattice

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
