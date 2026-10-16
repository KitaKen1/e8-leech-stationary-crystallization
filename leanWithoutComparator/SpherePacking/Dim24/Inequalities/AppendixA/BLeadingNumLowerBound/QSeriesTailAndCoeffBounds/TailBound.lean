-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.RSeriesTailBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable


/-!
### Generic tail bound for `qseries` with polynomially bounded coefficients

This is the analytic backbone behind the `PolynomialSum(...)` checks in `appendix.txt`: once
coefficients satisfy a bound `|aₙ| ≤ C (n+1)^k`, the `q`-tail is bounded by `C * ∑ powGeomTerm`.
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA


/-- Summability of the geometric-polynomial majorant `powGeomTerm (q t) k`. -/
public lemma summable_powGeomTerm_q (t : ℝ) (ht0 : 0 < t) (k : ℕ) :
    Summable (fun n : ℕ => powGeomTerm (q t) k n) := by
  -- Reduce to the standard summability of `n^k * r^n` for `‖r‖ < 1`, then shift indices.
  set r0 : ℝ := q t
  have hr0_pos : 0 < r0 := by
    -- `q t = exp(-2πt)`.
    simp [r0, q, Real.exp_pos]
  have hr0_nonneg : 0 ≤ r0 := hr0_pos.le
  have hr0_lt_one : r0 < 1 := by
    have hneg : (-2 * Real.pi * t) < 0 := by nlinarith [Real.pi_pos, ht0]
    simpa [r0, q] using! (Real.exp_lt_one_iff.2 hneg)
  have hr0_norm : ‖r0‖ < 1 := by
    simpa [Real.norm_of_nonneg hr0_nonneg] using! hr0_lt_one
  have hs_pow : Summable (fun n : ℕ => ((n : ℝ) ^ k : ℝ) * r0 ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hr0_norm
  have hs_shift :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * r0 ^ (n + 1)) := by
    simpa [Nat.cast_add, Nat.cast_one] using!
      (summable_nat_add_iff 1 (f := fun n : ℕ => ((n : ℝ) ^ k : ℝ) * r0 ^ n)).2 hs_pow
  have hs_shift' :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * r0 ^ n) := by
    have hs1 :
        Summable (fun n : ℕ => (1 / r0) * (((n + 1 : ℕ) : ℝ) ^ k * r0 ^ (n + 1))) :=
      hs_shift.mul_left (1 / r0)
    refine hs1.congr ?_
    intro n
    field_simp [hr0_pos.ne']
    ring
  simpa [powGeomTerm, r0] using! hs_shift'

/-- Tail bound for a `qseries` with polynomially bounded rational coefficients. -/
public lemma norm_qseries_tail_le_of_coeffBound (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t)
    (a : ℕ → ℚ) (C : ℝ) (k N : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    ‖∑' m : ℕ, (a (N + m) : ℂ) * qterm (it t ht0) (N + m)‖ ≤
      C * (∑' m : ℕ, powGeomTerm (q t) k (N + m)) := by
  -- Notation.
  set z : ℍ := it t ht0
  let f : ℕ → ℂ := fun n => (a n : ℂ) * qterm z n
  have hf_summable : Summable (fun n : ℕ => ‖f n‖) := by
    -- Use the generic Appendix A summability lemma.
    exact summable_norm_qseries_of_coeffBound t ht0 ht a C k ha
  have hf_tail_summable : Summable (fun m : ℕ => ‖f (N + m)‖) := by
    -- Shift summability by `N`.
    have hs' : Summable (fun m : ℕ => ‖f (m + N)‖) :=
      (summable_nat_add_iff N (f := fun n => ‖f n‖)).2 hf_summable
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using! hs'
  have hnorm_tsum :
      ‖∑' m : ℕ, f (N + m)‖ ≤ ∑' m : ℕ, ‖f (N + m)‖ := by
    simpa using! (norm_tsum_le_tsum_norm hf_tail_summable)
  have hterm_le : ∀ m : ℕ, ‖f (N + m)‖ ≤ C * powGeomTerm (q t) k (N + m) := by
    intro m
    -- Expand `f` and bound using `ha`.
    have hnorm_q : ‖qterm z (N + m)‖ = (q t) ^ (N + m) := by
      -- `qterm(it t) = q(t)^n`.
      simpa [z] using! (norm_qterm_it (t := t) (ht := ht0) (n := N + m))
    have hq0 : 0 ≤ q t := (Real.exp_pos _).le
    calc
      ‖f (N + m)‖ = ‖(a (N + m) : ℂ)‖ * ‖qterm z (N + m)‖ := by
        simp [f, z]
      _ = |(a (N + m) : ℝ)| * (q t) ^ (N + m) := by simp [hnorm_q]
      _ ≤ (C * (((N + m + 1 : ℕ) : ℝ) ^ k)) * (q t) ^ (N + m) := by
            exact mul_le_mul_of_nonneg_right (ha (N + m)) (pow_nonneg hq0 _)
      _ = C * powGeomTerm (q t) k (N + m) := by
            have hcast : ((N + m + 1 : ℕ) : ℝ) = (N + m : ℝ) + 1 := by
              simp [Nat.cast_add, Nat.cast_one, add_assoc]
            simp [powGeomTerm, hcast, mul_assoc]
  -- Compare the `tsum` of norms to the `powGeomTerm` majorant.
  have hs_majorant : Summable (fun m : ℕ => C * powGeomTerm (q t) k (N + m)) := by
    have hs0 : Summable (fun m : ℕ => powGeomTerm (q t) k (N + m)) := by
      have hs := summable_powGeomTerm_q (t := t) (ht0 := ht0) (k := k)
      have hs' : Summable (fun m : ℕ => powGeomTerm (q t) k (m + N)) :=
        (summable_nat_add_iff N (f := fun n => powGeomTerm (q t) k n)).2 hs
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using! hs'
    exact hs0.mul_left C
  have hsum_le :
      (∑' m : ℕ, ‖f (N + m)‖) ≤ ∑' m : ℕ, C * powGeomTerm (q t) k (N + m) := by
    -- `‖f‖` is nonnegative and dominated termwise by the majorant.
    refine hasSum_le (fun m => hterm_le m) ?_ hs_majorant.hasSum
    · exact hf_tail_summable.hasSum
  -- Pull out the constant `C` and conclude.
  have hCmul :
      (∑' m : ℕ, C * powGeomTerm (q t) k (N + m)) =
        C * (∑' m : ℕ, powGeomTerm (q t) k (N + m)) := by
    simp [tsum_mul_left]
  calc
    ‖∑' m : ℕ, (a (N + m) : ℂ) * qterm (it t ht0) (N + m)‖
        = ‖∑' m : ℕ, f (N + m)‖ := by simp [f, z]
    _ ≤ ∑' m : ℕ, ‖f (N + m)‖ := hnorm_tsum
    _ ≤ ∑' m : ℕ, C * powGeomTerm (q t) k (N + m) := hsum_le
    _ = C * (∑' m : ℕ, powGeomTerm (q t) k (N + m)) := hCmul

end SpherePacking.Dim24.AppendixA
