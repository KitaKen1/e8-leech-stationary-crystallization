-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.EqCase24Support

/-!
# Basic consequences of `EqCase24`

This file collects small lemmas that follow directly from the BS81 equality-case data `EqCase24`,
without unfolding the distance-distribution definition every time. These facts are used repeatedly
in later combinatorial arguments.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open scoped RealInnerProductSpace

/-- In the equality case, the `t=1` fiber is exactly `{u}`. -/
lemma distSet_eq_singleton_of_inner_one
    (C : Set ℝ²⁴) (hEq : EqCase24 C) (u : ℝ²⁴) (hu : u ∈ C) :
    distSet C u (1 : ℝ) = {u} := by
  rcases hEq.distCount_eq hu with ⟨h1, _, _, _, _, _, _⟩
  have hcard : Set.ncard (distSet C u (1 : ℝ)) = 1 := by
    simpa [distCount, distSet] using! h1
  rcases Set.ncard_eq_one.mp hcard with ⟨a, ha⟩
  have hnormu : ‖u‖ = (1 : ℝ) := hEq.code.norm_one hu
  have hu_mem : u ∈ distSet C u (1 : ℝ) := by
    refine ⟨hu, ?_⟩
    simp [hnormu]
  have ha_eq : a = u := by
    have : u ∈ ({a} : Set ℝ²⁴) := by simpa [ha] using! hu_mem
    simpa using! this.symm
  simp [ha, ha_eq]

/-- In the equality case, the `t=-1` fiber is exactly `{-u}`. -/
lemma distSet_eq_singleton_of_inner_neg_one
    (C : Set ℝ²⁴) (hEq : EqCase24 C) (u : ℝ²⁴) (hu : u ∈ C) :
    distSet C u (-1 : ℝ) = {-u} := by
  rcases hEq.distCount_eq hu with ⟨_, hneg1, _, _, _, _, _⟩
  have hcard : Set.ncard (distSet C u (-1 : ℝ)) = 1 := by
    simpa [distCount, distSet] using! hneg1
  rcases Set.ncard_eq_one.mp hcard with ⟨a, ha⟩
  have ha_mem : a ∈ distSet C u (-1 : ℝ) := by
    simp [ha]
  have haC : a ∈ C := ha_mem.1
  have hinner : (⟪u, a⟫ : ℝ) = (-1 : ℝ) := ha_mem.2
  have hnormu : ‖u‖ = (1 : ℝ) := hEq.code.norm_one hu
  have hnorma : ‖a‖ = (1 : ℝ) := hEq.code.norm_one haC
  have h' : u = -a := (inner_eq_neg_one_iff_of_norm_eq_one hnormu hnorma).1 hinner
  have ha_eq : a = -u := by
    have : -u = a := by simpa using! congrArg Neg.neg h'
    simp [this]
  simp [ha, ha_eq]

/-- The equality case forces closure under negation. -/
public lemma neg_mem_of_eqCase24
    (C : Set ℝ²⁴) (hEq : EqCase24 C) (u : ℝ²⁴) (hu : u ∈ C) :
    -u ∈ C := by
  have hset : distSet C u (-1 : ℝ) = {-u} :=
    distSet_eq_singleton_of_inner_neg_one (C := C) hEq u hu
  have hmem : -u ∈ distSet C u (-1 : ℝ) := by
    simp [hset]
  exact hmem.1

attribute [grind →] neg_mem_of_eqCase24

end SpherePacking.Dim24.Uniqueness.BS81
