-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerDefs
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.Basic

/-!
# Derived Steiner systems

The weight-8 words of the (extended) Golay code yield the Witt design `S(5,8,24)`. Fixing two
coordinates (e.g. `0` and `1`) and puncturing yields the derived design `S(3,6,22)`.

This file provides the basic combinatorial plumbing relating blocks in `Fin 24` containing
`{0,1}` to `6`-subsets of `Fin 22` via `Fin.addNatEmb 2`.

## Main definitions
* `drop2`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

/--
Drop the first two coordinates `0` and `1` of a block `B : Finset (Fin 24)`, reindexing the
remaining points as `Fin 22` via `Fin.addNatEmb 2`.
-/
@[expose] public def drop2 (B : Finset (Fin 24)) : Finset (Fin 22) :=
  Finset.univ.filter fun i : Fin 22 => (Fin.addNatEmb 2 i) ∈ B

/-- Membership in `drop2 B` is membership in `B` after embedding into `Fin 24`. -/
@[simp] public lemma mem_drop2 (B : Finset (Fin 24)) (i : Fin 22) :
    i ∈ drop2 B ↔ (Fin.addNatEmb 2 i) ∈ B := by
  simp [drop2]

/-- The embedding `Fin.addNatEmb 2 : Fin 22 ↪ Fin 24` never hits `0`. -/
public lemma emb22_ne_zero (i : Fin 22) : (Fin.addNatEmb 2 i : Fin 24) ≠ 0 := by
  intro h
  have hval0 : ((Fin.addNatEmb 2 i : Fin 24) : ℕ) = ((0 : Fin 24) : ℕ) := congrArg Fin.val h
  have h2 : ((Fin.addNatEmb 2 i : Fin 24) : ℕ) = (i : ℕ) + 2 := rfl
  have h3 : ((0 : Fin 24) : ℕ) = 0 := rfl
  omega

/-- The embedding `Fin.addNatEmb 2 : Fin 22 ↪ Fin 24` never hits `1`. -/
public lemma emb22_ne_one (i : Fin 22) : (Fin.addNatEmb 2 i : Fin 24) ≠ 1 := by
  intro h
  have hval0 : ((Fin.addNatEmb 2 i : Fin 24) : ℕ) = ((1 : Fin 24) : ℕ) := congrArg Fin.val h
  have h2 : ((Fin.addNatEmb 2 i : Fin 24) : ℕ) = (i : ℕ) + 2 := rfl
  have h3 : ((1 : Fin 24) : ℕ) = 1 := rfl
  omega

private lemma two_le_val_of_ne_zero_one (j : Fin 24) (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
    2 ≤ (j : ℕ) := by
  by_contra h
  have hjle : (j : ℕ) ≤ 1 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hjle with h0 | h1
  · exact hj0 (Fin.ext (by simp [h0]))
  · exact hj1 (Fin.ext (by simp [h1]))

private lemma mem_erase01 (B : Finset (Fin 24)) (j : Fin 24) :
    j ∈ (B.erase 0).erase 1 ↔ j ≠ 1 ∧ j ≠ 0 ∧ j ∈ B := by
  simp [Finset.mem_erase, and_assoc, and_comm]

private lemma map_drop2_eq_erase01 (B : Finset (Fin 24)) :
    (drop2 B).map (Fin.addNatEmb 2) = (B.erase 0).erase 1 := by
  ext j
  constructor
  · intro hj
    rcases Finset.mem_map.1 hj with ⟨i, hi, rfl⟩
    have hiB : (Fin.addNatEmb 2 i : Fin 24) ∈ B := (mem_drop2 B i).1 hi
    simp [hiB, emb22_ne_zero, emb22_ne_one]
  · intro hj
    rcases (mem_erase01 (B := B) (j := j)).1 hj with ⟨hj1, hj0, hjB⟩
    have hj2 : 2 ≤ (j : ℕ) := two_le_val_of_ne_zero_one j hj0 hj1
    let i : Fin 22 := Fin.subNat 2 j hj2
    have hij : (Fin.addNatEmb 2 i : Fin 24) = j := by
      rw [Fin.addNatEmb_apply]
      exact Fin.addNat_subNat (n := 22) (m := 2) (i := j) hj2
    have hi : i ∈ drop2 B := by
      -- `Fin.addNatEmb 2 i = j` and `j ∈ B`
      apply (mem_drop2 B i).2
      simpa [hij] using! hjB
    exact Finset.mem_map.2 ⟨i, hi, hij⟩

/--
If a block `B` has cardinality `8` and contains `0` and `1`, then dropping those two points yields
a `6`-subset of `Fin 22`.
-/
public lemma card_drop2_of_card_eq_eight (B : Finset (Fin 24))
    (hB : B.card = 8) (h0 : (0 : Fin 24) ∈ B) (h1 : (1 : Fin 24) ∈ B) :
    (drop2 B).card = 6 := by
  have hcard_erase : ((B.erase 0).erase 1).card = 6 := by
    simp_all
  have hcard_drop2 : (drop2 B).card = ((B.erase 0).erase 1).card := by
    simpa using! congrArg Finset.card (map_drop2_eq_erase01 B)
  calc
    (drop2 B).card = ((B.erase 0).erase 1).card := hcard_drop2
    _ = 6 := hcard_erase

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
