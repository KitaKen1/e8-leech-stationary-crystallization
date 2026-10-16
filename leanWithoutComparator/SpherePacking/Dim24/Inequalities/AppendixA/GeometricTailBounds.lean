/-
Geometric-series tail bounds used in Appendix A truncation arguments.

This file provides a lightweight alternative to the `MonomialSum`/`PolynomialSum` computations in
`appendix.txt`: instead of a closed form for `∑ n^k q^n`, we bound the tail by proving that the
terms form a geometric progression up to a uniform ratio.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas


/-!
Geometric-series tail bounds for terms of the form `(n + 1)^k * q^n`.

The key step is a uniform bound on successive ratios of `powGeomTerm`, expressed by
`powGeomRatio`. This yields computable tail estimates for series of the form
`∑' m, powGeomTerm q k (N + m)`, including the convenient specialization
`tsum_powGeomTerm_tail_le_two_mul` when the ratio is at most `1/2`.
-/


open scoped BigOperators Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- The basic term `(n+1)^k * q^n` that appears when bounding coefficients by polynomials in `n`. -/
@[expose]
public def powGeomTerm (q : ℝ) (k : ℕ) (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ k) * q ^ n

/-- A uniform bound on successive ratios of `powGeomTerm` starting at `N`. -/
@[expose]
public def powGeomRatio (q : ℝ) (k N : ℕ) : ℝ :=
  q * (((N + 2 : ℝ) / (N + 1 : ℝ)) ^ k)

/-- Nonnegativity of `powGeomRatio` when `q ≥ 0`. -/
public lemma powGeomRatio_nonneg (q : ℝ) (k N : ℕ) (hq : 0 ≤ q) : 0 ≤ powGeomRatio q k N := by
  dsimp [powGeomRatio]
  exact mul_nonneg hq (pow_nonneg (by positivity) _)

/-- Monotonicity of `powGeomRatio` in the parameter `q`. -/
public lemma powGeomRatio_mono_left {q q' : ℝ} (hq : q ≤ q') (k N : ℕ) :
    powGeomRatio q k N ≤ powGeomRatio q' k N := by
  have hnonneg : 0 ≤ (((N + 2 : ℝ) / (N + 1 : ℝ)) ^ k) := by positivity
  simpa [powGeomRatio] using! (mul_le_mul_of_nonneg_right hq hnonneg)

/-- Nonnegativity of `powGeomTerm` when `q ≥ 0`. -/
public lemma powGeomTerm_nonneg (q : ℝ) (k n : ℕ) (hq : 0 ≤ q) : 0 ≤ powGeomTerm q k n := by
  dsimp [powGeomTerm]
  exact mul_nonneg (by positivity) (pow_nonneg hq _)

lemma add_two_div_add_one_eq_one_add_one_div (n : ℕ) :
    ((n + 2 : ℝ) / (n + 1 : ℝ)) = 1 + (1 / (n + 1 : ℝ)) := by
  field_simp [(by positivity : (n + 1 : ℝ) ≠ 0)]
  ring

lemma add_two_div_add_one_le_of_le {N n : ℕ} (hn : N ≤ n) :
    ((n + 2 : ℝ) / (n + 1 : ℝ)) ≤ ((N + 2 : ℝ) / (N + 1 : ℝ)) := by
  have hdiv : (1 / (n + 1 : ℝ)) ≤ (1 / (N + 1 : ℝ)) := by
    refine one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N + 1 : ℝ)) ?_
    exact_mod_cast Nat.succ_le_succ hn
  simpa [add_two_div_add_one_eq_one_add_one_div] using! add_le_add_left hdiv 1

/-- For `n ≥ N`, successive terms of `powGeomTerm` decrease geometrically with ratio
`powGeomRatio q k N`. -/
lemma powGeomTerm_succ_le_mul_ratio (q : ℝ) (k N n : ℕ) (hq : 0 ≤ q) (hn : N ≤ n) :
    powGeomTerm q k (n + 1) ≤ powGeomRatio q k N * powGeomTerm q k n := by
  have hratio :
      (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ k) ≤ (((N + 2 : ℝ) / (N + 1 : ℝ)) ^ k) := by
    have hbase :
        ((n + 2 : ℝ) / (n + 1 : ℝ)) ≤ ((N + 2 : ℝ) / (N + 1 : ℝ)) :=
      add_two_div_add_one_le_of_le hn
    have hnonneg : (0 : ℝ) ≤ ((n + 2 : ℝ) / (n + 1 : ℝ)) := by positivity
    exact pow_le_pow_left₀ hnonneg hbase _
  have hsplit :
      powGeomTerm q k (n + 1) =
        powGeomTerm q k n * (q * (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ k)) := by
    dsimp [powGeomTerm]
    have hpow :
        ((n + 2 : ℝ) ^ k) =
          ((n + 1 : ℝ) ^ k) * (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ k) := by
      calc
        ((n + 2 : ℝ) ^ k) = (((n + 1 : ℝ) * ((n + 2 : ℝ) / (n + 1 : ℝ))) ^ k) := by
          have hmul : (n + 1 : ℝ) * ((n + 2 : ℝ) / (n + 1 : ℝ)) = (n + 2 : ℝ) := by
            simpa using! (mul_div_cancel₀ (n + 2 : ℝ) (by positivity : (n + 1 : ℝ) ≠ 0))
          simp [hmul]
        _ = ((n + 1 : ℝ) ^ k) * (((n + 2 : ℝ) / (n + 1 : ℝ)) ^ k) := by simp [mul_pow]
    rw [pow_succ]
    have hcast :
        (↑(n + 1) + (1 : ℝ)) = (↑n + (2 : ℝ)) := by
      simp [Nat.cast_add, Nat.cast_one, add_assoc]
      ring
    have hcastPow : (↑(n + 1) + (1 : ℝ)) ^ k = (↑n + (2 : ℝ)) ^ k :=
      congrArg (fun x => x ^ k) hcast
    rw [hcastPow, hpow]
    ac_rfl
  have hmul :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hratio hq) (powGeomTerm_nonneg q k n hq)
  simpa [powGeomRatio, hsplit, mul_assoc, mul_left_comm, mul_comm] using! hmul

/--
Geometric bound for terms after an index shift: for `m` steps past `N`, the term is bounded by the
initial value times `(powGeomRatio q k N)^m`.
-/
public lemma powGeomTerm_add_le (q : ℝ) (k N m : ℕ) (hq : 0 ≤ q) :
    powGeomTerm q k (N + m) ≤ powGeomTerm q k N * (powGeomRatio q k N) ^ m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hstep :
          powGeomTerm q k (N + m + 1) ≤
            powGeomRatio q k N * powGeomTerm q k (N + m) := by
        -- Apply the ratio lemma at index `n = N + m`.
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using!
          (powGeomTerm_succ_le_mul_ratio (q := q) (k := k) (N := N) (n := N + m) hq
            (Nat.le_add_right N m))
      -- Combine with the induction hypothesis.
      have hρ0 : 0 ≤ powGeomRatio q k N := powGeomRatio_nonneg (q := q) (k := k) (N := N) hq
      -- Rearrange.
      calc
        powGeomTerm q k (N + m + 1)
            ≤ powGeomRatio q k N * powGeomTerm q k (N + m) := hstep
        _ ≤ powGeomRatio q k N * (powGeomTerm q k N * (powGeomRatio q k N) ^ m) := by
            exact mul_le_mul_of_nonneg_left ih hρ0
        _ = powGeomTerm q k N * (powGeomRatio q k N) ^ (m + 1) := by
            simp [pow_succ, mul_assoc, mul_comm]

/-- A computable tail bound for `∑_{n≥N} (n+1)^k q^n` based on a uniform ratio bound. -/
public theorem tsum_powGeomTerm_tail_le (q : ℝ) (k N : ℕ) (hq : 0 ≤ q)
    (hρ : powGeomRatio q k N < 1) :
    (∑' m : ℕ, powGeomTerm q k (N + m)) ≤ powGeomTerm q k N / (1 - powGeomRatio q k N) := by
  set ρ : ℝ := powGeomRatio q k N
  have hρ0 : 0 ≤ ρ := by simpa [ρ] using! powGeomRatio_nonneg (q := q) (k := k) (N := N) hq
  have hdom : ∀ m : ℕ, powGeomTerm q k (N + m) ≤ powGeomTerm q k N * ρ ^ m := by
    intro m
    simpa [ρ] using! (powGeomTerm_add_le (q := q) (k := k) (N := N) (m := m) hq)
  have hgeom_summable : Summable (fun m : ℕ => powGeomTerm q k N * ρ ^ m) :=
    (summable_geometric_of_lt_one hρ0 hρ).mul_left (powGeomTerm q k N)
  have htail_summable : Summable (fun m : ℕ => powGeomTerm q k (N + m)) := by
    refine Summable.of_nonneg_of_le (fun m => powGeomTerm_nonneg q k (N + m) hq) hdom hgeom_summable
  have hle_tsum :
      (∑' m : ℕ, powGeomTerm q k (N + m)) ≤ ∑' m : ℕ, powGeomTerm q k N * ρ ^ m :=
    hasSum_le hdom htail_summable.hasSum hgeom_summable.hasSum
  have hgeom_eval :
      (∑' m : ℕ, powGeomTerm q k N * ρ ^ m) = powGeomTerm q k N * (1 - ρ)⁻¹ := by
    simp [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ]
  simpa [hgeom_eval, ρ, div_eq_mul_inv] using! hle_tsum

/-- Special case of `tsum_powGeomTerm_tail_le` when `powGeomRatio q k N ≤ 1/2`. -/
public theorem tsum_powGeomTerm_tail_le_two_mul (q : ℝ) (k N : ℕ) (hq : 0 ≤ q)
    (hρ : powGeomRatio q k N ≤ (1 : ℝ) / 2) :
    (∑' m : ℕ, powGeomTerm q k (N + m)) ≤ 2 * powGeomTerm q k N := by
  have hρ' : powGeomRatio q k N < 1 := lt_of_le_of_lt hρ (by norm_num)
  have htail := tsum_powGeomTerm_tail_le (q := q) (k := k) (N := N) hq hρ'
  have hden : (1 : ℝ) / 2 ≤ 1 - powGeomRatio q k N := by
    refine (le_sub_iff_add_le).2 ?_
    have h2 : (1 : ℝ) / 2 + (1 : ℝ) / 2 = (1 : ℝ) := by norm_num
    have hsum' :
        (1 : ℝ) / 2 + powGeomRatio q k N ≤ (1 : ℝ) / 2 + (1 : ℝ) / 2 :=
      add_le_add_right hρ ((1 : ℝ) / 2)
    exact le_trans hsum' (le_of_eq h2)
  have hhalf_pos : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  have hinv_le : (1 / (1 - powGeomRatio q k N)) ≤ 2 := by
    have : (1 / (1 - powGeomRatio q k N)) ≤ (1 / ((1 : ℝ) / 2)) := by
      simpa [one_div] using! (one_div_le_one_div_of_le hhalf_pos hden)
    simpa using! this
  have hpowGeom_nonneg : 0 ≤ powGeomTerm q k N := powGeomTerm_nonneg (q := q) (k := k) (n := N) hq
  have hdiv_le :
      powGeomTerm q k N / (1 - powGeomRatio q k N) ≤ 2 * powGeomTerm q k N := by
    have hmul := mul_le_mul_of_nonneg_left hinv_le hpowGeom_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! hmul
  exact htail.trans hdiv_le

end

end SpherePacking.Dim24.AppendixA
