-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
### Range-shift lemmas for finite sums

These are reindexing identities for sums over `Finset.range N` where the summand uses a shifted
index such as `k + 1` or `k + 2`.
-/

noncomputable section

namespace SpherePacking.Dim24.AppendixA

open scoped BigOperators

/--
Reindex a range sum whose summand uses `f (k+2) * x^k`
into a sum over `i` with exponent `i-2`. -/
public lemma sum_shift2_eq (N : ℕ) (x : ℝ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, (if k + 2 < N then f (k + 2) * x ^ k else 0)) =
      ∑ i ∈ Finset.range N, (if 2 ≤ i then f i * x ^ (i - 2) else 0) := by
  cases N with
  | zero => simp
  | succ N =>
      cases N with
      | zero => simp
      | succ m =>
          have hN : Nat.succ (Nat.succ m) = m + 2 := by
            simp [Nat.succ_eq_add_one, Nat.add_assoc]
          let g : ℕ → ℝ := fun k => if k + 2 < m + 2 then f (k + 2) * x ^ k else 0
          have hmainL :
              Finset.sum (Finset.range m) g =
                Finset.sum (Finset.range m) (fun k => f (k + 2) * x ^ k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hklt : k < m := by simpa [Finset.mem_range] using! hk
            have hk' : k + 2 < m + 2 := Nat.add_lt_add_right hklt 2
            dsimp [g]
            rw [if_pos hk']
          have htailL : Finset.sum (Finset.range 2) (fun k => g (m + k)) = 0 := by
            simp [g]
          have hL :
              Finset.sum (Finset.range (m + 2)) g =
                Finset.sum (Finset.range m) (fun k => f (k + 2) * x ^ k) := by
            have hsplitL := (Finset.sum_range_add (f := g) (n := m) (m := 2))
            calc
              Finset.sum (Finset.range (m + 2)) g =
                  Finset.sum (Finset.range m) g +
                    Finset.sum (Finset.range 2) (fun k => g (m + k)) := by
                    simpa using! hsplitL
              _ = Finset.sum (Finset.range m) (fun k => f (k + 2) * x ^ k) + 0 := by
                    simp [hmainL, htailL]
              _ = Finset.sum (Finset.range m) (fun k => f (k + 2) * x ^ k) := by simp
          let hfun : ℕ → ℝ := fun i => if 2 ≤ i then f i * x ^ (i - 2) else 0
          have hheadR : Finset.sum (Finset.range 2) hfun = 0 := by
            simp [Finset.sum_range_succ, hfun]
          have htailR :
              Finset.sum (Finset.range m) (fun k => hfun (2 + k)) =
                Finset.sum (Finset.range m) (fun k => f (k + 2) * x ^ k) := by
            lia
          have hR :
              Finset.sum (Finset.range (m + 2)) hfun =
                Finset.sum (Finset.range m) (fun k => f (k + 2) * x ^ k) := by
            have hsplitR := (Finset.sum_range_add (f := hfun) (n := 2) (m := m))
            calc
              Finset.sum (Finset.range (m + 2)) hfun =
                  Finset.sum (Finset.range 2) hfun +
                    Finset.sum (Finset.range m) (fun k => hfun (2 + k)) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! hsplitR
              _ = 0 + Finset.sum (Finset.range m) (fun k => f (k + 2) * x ^ k) := by
                    simp [hheadR, htailR]
              _ = Finset.sum (Finset.range m) (fun k => f (k + 2) * x ^ k) := by simp
          grind only

/--
Reindex a range sum whose summand uses `f (k+1) * x^k`
into a sum over `i` with exponent `i-1`. -/
public lemma sum_shift1_eq (N : ℕ) (x : ℝ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, (if k + 1 < N then f (k + 1) * x ^ k else 0)) =
      ∑ i ∈ Finset.range N, (if 1 ≤ i then f i * x ^ (i - 1) else 0) := by
  cases N with
  | zero => simp
  | succ m =>
      let g : ℕ → ℝ := fun k => if k + 1 < m + 1 then f (k + 1) * x ^ k else 0
      have hL : (∑ k ∈ Finset.range (m + 1), g k) = ∑ k ∈ Finset.range m, f (k + 1) * x ^ k := by
        have hsplit := (Finset.sum_range_add (f := g) (n := m) (m := 1))
        have hmain : (∑ k ∈ Finset.range m, g k) = ∑ k ∈ Finset.range m, f (k + 1) * x ^ k := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hklt : k < m := by simpa [Finset.mem_range] using! hk
          simp [g, hklt]
        calc
          (∑ k ∈ Finset.range (m + 1), g k) =
              (∑ k ∈ Finset.range m, g k) + ∑ k ∈ Finset.range 1, g (m + k) := hsplit
          _ = (∑ k ∈ Finset.range m, f (k + 1) * x ^ k) + ∑ k ∈ Finset.range 1, g (m + k) := by
              simp [hmain]
          _ = ∑ k ∈ Finset.range m, f (k + 1) * x ^ k := by
              simp [g]
      let h : ℕ → ℝ := fun i => if 1 ≤ i then f i * x ^ (i - 1) else 0
      have hR : (∑ i ∈ Finset.range (m + 1), h i) = ∑ k ∈ Finset.range m, f (k + 1) * x ^ k := by
        have hsplit : (∑ i ∈ Finset.range (m + 1), h i) =
            (∑ i ∈ Finset.range 1, h i) + ∑ k ∈ Finset.range m, h (1 + k) := by
          simpa [Nat.one_add, Nat.succ_eq_add_one, add_assoc] using!
            (Finset.sum_range_add (f := h) (n := 1) (m := m))
        have hhead : (∑ i ∈ Finset.range 1, h i) = 0 := by
          simp [h]
        have htail :
            (∑ k ∈ Finset.range m, h (1 + k)) = ∑ k ∈ Finset.range m, f (k + 1) * x ^ k := by
          lia
        calc
          (∑ i ∈ Finset.range (m + 1), h i) =
              (∑ i ∈ Finset.range 1, h i) + ∑ k ∈ Finset.range m, h (1 + k) := by
                simpa using! hsplit
          _ = 0 + ∑ k ∈ Finset.range m, h (1 + k) := by
              rw [hhead]
          _ = ∑ k ∈ Finset.range m, f (k + 1) * x ^ k := by
              simp [htail]
      grind only

end SpherePacking.Dim24.AppendixA
