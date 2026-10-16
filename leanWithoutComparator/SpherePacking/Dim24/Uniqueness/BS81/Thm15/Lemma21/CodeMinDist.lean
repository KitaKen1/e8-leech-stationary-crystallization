-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Defs

/-!
# Minimum distance for linear binary codes

`minDist C` is defined as the infimum of Hamming distances between distinct words in `C`.
For a linear binary code, distances are weights of sums, so lower bounds on the weight of nonzero
words translate into lower bounds on `minDist`.

## Main statements
* `CodingTheory.minDist_le_weight_of_nonzero_mem`
* `CodingTheory.le_minDist_of_linear_of_weight_ge`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped BigOperators
open Uniqueness.BS81.CodingTheory

namespace CodingTheory

private lemma eq_of_add_eq_zero {n : ℕ} {x y : BinWord n}
    (h : (fun i => x i + y i) = 0) : x = y := by
  funext i
  have : x i = -y i :=
    (add_eq_zero_iff_eq_neg).1 (by simpa using! congrArg (fun f : BinWord n => f i) h)
  simpa [ZMod.neg_eq_self_mod_two] using! this

/-- In a linear code, `minDist` is bounded above by the weight of any nonzero codeword. -/
public theorem minDist_le_weight_of_nonzero_mem
    {n : ℕ} (C : Code n) (hlin : IsLinearCode C)
    {w : BinWord n} (hw : w ∈ C) (hw0 : w ≠ 0) :
    minDist C ≤ weight w := by
  have h0 : (0 : BinWord n) ∈ C := hlin.1
  -- `weight w` occurs as the distance between `w` and `0`.
  have hmem :
      weight w ∈ {d : ℕ | ∃ x y : BinWord n, x ∈ C ∧ y ∈ C ∧ x ≠ y ∧ hammingDist x y = d} := by
    refine ⟨w, 0, hw, h0, ?_, ?_⟩
    · exact hw0
    · simp [hammingDist]
  exact Nat.sInf_le hmem

/-- A uniform lower bound on weights of nonzero words gives a lower bound on `minDist`. -/
public theorem le_minDist_of_linear_of_weight_ge
    {n : ℕ} (C : Code n) (hlin : IsLinearCode C) (d : ℕ)
    (hwt : ∀ c : BinWord n, c ∈ C → c ≠ 0 → d ≤ weight c)
    (hne : ∃ c : BinWord n, c ∈ C ∧ c ≠ 0) :
    d ≤ minDist C := by
  -- Use `Nat.sInf_mem` to pick witnesses realizing `minDist C`.
  dsimp [minDist]
  set D : Set ℕ :=
    {d' : ℕ | ∃ x y : BinWord n, x ∈ C ∧ y ∈ C ∧ x ≠ y ∧ hammingDist x y = d'} with hD
  have hDne : D.Nonempty := by
    rcases hne with ⟨c, hcC, hc0⟩
    refine ⟨hammingDist c 0, ?_⟩
    refine ⟨c, 0, hcC, hlin.1, hc0, rfl⟩
  have hmem : sInf D ∈ D := Nat.sInf_mem hDne
  rcases hmem with ⟨x, y, hx, hy, hxy, hdist⟩
  have hw_mem : (fun i => x i + y i) ∈ C := hlin.2 x y hx hy
  have hw0 : (fun i => x i + y i) ≠ 0 := by
    intro h0
    apply hxy
    exact eq_of_add_eq_zero (n := n) (x := x) (y := y) h0
  have hle : d ≤ hammingDist x y := by
    simpa [hammingDist] using! hwt (fun i => x i + y i) hw_mem hw0
  -- conclude using `hdist : hammingDist x y = sInf D`
  simpa [hdist, hD] using! hle

end CodingTheory

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
