-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL

/-!
# Induction data for BS81 Lemma 20

This file defines the structure `ContainsDn C n`, which packages an embedded copy of the root
lattice `Dₙ` inside `L := span_ℤ (2 • C)`:
an orthonormal frame `e : Fin n → ℝ²⁴` together with the membership of the minimal vectors
`√2 (e i ± e j)` in the shell `latticeShell4 C`.

## Main definition
* `ContainsDn`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- An embedded copy of `Dₙ` inside `latticeL C`, given by an orthonormal frame `e₁,...,eₙ`
and the associated minimal vectors `√2 (±e_i ± e_j)` living in `latticeShell4 C`. -/
public structure ContainsDn (C : Set ℝ²⁴) (n : ℕ) where
  e : Fin n → ℝ²⁴
  ortho : Orthonormal ℝ e
  minVec_mem :
    ∀ (i j : Fin n), i ≠ j →
      (Real.sqrt 2 • (e i + e j)) ∈ latticeShell4 C ∧
      (Real.sqrt 2 • (e i - e j)) ∈ latticeShell4 C

/-- Negation preserves membership in the shell `latticeShell4 C`. -/
public lemma latticeShell4_neg_mem {C : Set ℝ²⁴} {v : ℝ²⁴} (hv : v ∈ latticeShell4 C) :
    -v ∈ latticeShell4 C :=
  ⟨(latticeL C).neg_mem hv.1, by simpa [norm_neg] using! hv.2⟩

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20
