-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Defs
public import Mathlib.Algebra.Module.Submodule.Basic

/-!
# The lattice `L` and its norm-`4` shell

We define the lattice `latticeL C := span_ℤ (2 • C)` associated to a code `C ⊆ ℝ²⁴`, together with
its norm-`4` shell `latticeShell4 C`. We also record lightweight helper lemmas used in the
Bannai-Sloane argument in BS81 Theorem 15.

## Main definitions
* `Uniqueness.BS81.latticeL`
* `Uniqueness.BS81.latticeShell4`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81

noncomputable section

open scoped RealInnerProductSpace Pointwise

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The set `2 • C` as a subset of `ℝ²⁴`. -/
@[expose] public def twoCodeVectors (C : Set ℝ²⁴) : Set ℝ²⁴ :=
  (fun u : ℝ²⁴ => (2 : ℝ) • u) '' C

/-- BS81's lattice `L := span_ℤ (2 • C)`. -/
@[expose] public def latticeL (C : Set ℝ²⁴) : Submodule ℤ ℝ²⁴ :=
  Submodule.span ℤ (twoCodeVectors C)

/-- The norm-4 shell of `latticeL C`. (Recall `‖2u‖^2 = 4` for unit vectors `u`.) -/
@[expose] public def latticeShell4 (C : Set ℝ²⁴) : Set ℝ²⁴ :=
  {v : ℝ²⁴ | v ∈ (latticeL C : Set ℝ²⁴) ∧ ‖v‖ ^ 2 = (4 : ℝ)}

lemma twoCodeVectors_subset_latticeL (C : Set ℝ²⁴) :
    twoCodeVectors C ⊆ (latticeL C : Set ℝ²⁴) := by
  intro v hv
  exact Submodule.subset_span hv

lemma smul_mem_twoCodeVectors {C : Set ℝ²⁴} {u : ℝ²⁴} (hu : u ∈ C) :
    (2 : ℝ) • u ∈ twoCodeVectors C :=
  ⟨u, hu, rfl⟩

/-- If `u ∈ C`, then `2 • u` belongs to `latticeL C` (as a subset of `ℝ²⁴`). -/
public lemma smul_mem_latticeL {C : Set ℝ²⁴} {u : ℝ²⁴} (hu : u ∈ C) :
    (2 : ℝ) • u ∈ (latticeL C : Set ℝ²⁴) :=
  twoCodeVectors_subset_latticeL C (smul_mem_twoCodeVectors (C := C) hu)

/-- If `u ∈ C` is a unit vector, then `2 • u` lies in `latticeShell4 C`. -/
public lemma smul_mem_latticeShell4_of_norm_one {C : Set ℝ²⁴} {u : ℝ²⁴}
    (hu : u ∈ C) (hnorm : ‖u‖ = (1 : ℝ)) :
    (2 : ℝ) • u ∈ latticeShell4 C := by
  refine ⟨smul_mem_latticeL (C := C) hu, ?_⟩
  -- `‖2u‖^2 = 4` when `‖u‖ = 1`.
  simpa [norm_smul, hnorm] using! (by norm_num : ((2 : ℝ) ^ 2) = (4 : ℝ))

end

end SpherePacking.Dim24.Uniqueness.BS81
