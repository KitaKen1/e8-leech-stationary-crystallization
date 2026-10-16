/- Bounds on powers of `r t` used in the remainder estimate. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PhiDeltaQSeries.Identities
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.DeltaCoeffBounds
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.TailBounds
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
### Power conversions for the remainder bound

These are elementary inequalities converting `q`/`r` powers and reducing the high powers
(`r^100`, `r^98`) down to a factor of `(r t)^12` with explicit constants.
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA

private lemma pow23_sq_le_pow2_29 : (23 : ℝ) ^ (2 : ℕ) ≤ (2 : ℝ) ^ (29 : ℕ) := by
  norm_num

private lemma oneDiv23_pow86_eq_23sq_mul_oneDiv23_pow88 :
    ((1 : ℝ) / 23) ^ (86 : ℕ) = (23 : ℝ) ^ (2 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) := by
  norm_num

private lemma r_pow_le_one_div_23_pow (t : ℝ) (ht : 1 ≤ t) (n : ℕ) :
    (r t) ^ n ≤ ((1 : ℝ) / 23) ^ n :=
  pow_le_pow_left₀ (Real.exp_pos _).le (r_le_one_div_23 (t := t) ht) n

/-- Convert `q`-powers to `r`-powers using `q = r^2`: `q(t)^50 = r(t)^100`. -/
public lemma q_pow_50_eq_r_pow_100 (t : ℝ) : (q t) ^ (50 : ℕ) = (r t) ^ (100 : ℕ) := by
  simpa [q_eq_r_sq] using! (pow_mul (r t) 2 50).symm

private lemma q_pow_49_eq_r_pow_98 (t : ℝ) : (q t) ^ (49 : ℕ) = (r t) ^ (98 : ℕ) := by
  simpa [q_eq_r_sq] using! (pow_mul (r t) 2 49).symm

/-- For `t ≥ 1`, bound `t^2 * r(t)^100` by an explicit constant times `r(t)^12`. -/
public lemma t_sq_mul_rpow100_le (t : ℝ) (ht : 1 ≤ t) :
    t ^ (2 : ℕ) * (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := by
  have hq : t ^ (2 : ℕ) * (q t) ^ 50 ≤ ((1 / 23 : ℝ) ^ (2 : ℕ)) * (r t) ^ (98 : ℕ) := by
    simpa using! (t_sq_mul_q_pow_le (t := t) (ht := ht) (n := 50) (by decide))
  have hr86 : (r t) ^ (86 : ℕ) ≤ ((1 : ℝ) / 23) ^ (86 : ℕ) :=
    r_pow_le_one_div_23_pow (t := t) ht 86
  have hr98 : (r t) ^ (98 : ℕ) = (r t) ^ (12 : ℕ) * (r t) ^ (86 : ℕ) := by
    simpa [pow_add, mul_assoc] using! (pow_add (r t) 12 86)
  calc
    t ^ (2 : ℕ) * (r t) ^ (100 : ℕ) = t ^ (2 : ℕ) * (q t) ^ (50 : ℕ) := by
      simp [q_pow_50_eq_r_pow_100]
    _ ≤ ((1 / 23 : ℝ) ^ (2 : ℕ)) * (r t) ^ (98 : ℕ) := hq
    _ = ((1 / 23 : ℝ) ^ (2 : ℕ)) * ((r t) ^ (12 : ℕ) * (r t) ^ (86 : ℕ)) := by simp [hr98]
    _ ≤ ((1 / 23 : ℝ) ^ (2 : ℕ)) * ((r t) ^ (12 : ℕ) * ((1 / 23 : ℝ) ^ (86 : ℕ))) := by
          gcongr
    _ = ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := by ring_nf

/-- For `t ≥ 1`, bound `t * r(t)^100` by an explicit constant times `r(t)^12`. -/
public lemma t_mul_rpow100_le (t : ℝ) (ht : 1 ≤ t) :
    t * (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := by
  have hq : t * (q t) ^ 50 ≤ ((1 / 23 : ℝ)) * (r t) ^ (99 : ℕ) := by
    simpa using! (t_mul_q_pow_le (t := t) (ht := ht) (n := 50) (by decide))
  have hr87 : (r t) ^ (87 : ℕ) ≤ ((1 : ℝ) / 23) ^ (87 : ℕ) :=
    r_pow_le_one_div_23_pow (t := t) ht 87
  have hr99 : (r t) ^ (99 : ℕ) = (r t) ^ (12 : ℕ) * (r t) ^ (87 : ℕ) := by
    simpa [pow_add, mul_assoc] using! (pow_add (r t) 12 87)
  calc
    t * (r t) ^ (100 : ℕ) = t * (q t) ^ (50 : ℕ) := by simp [q_pow_50_eq_r_pow_100]
    _ ≤ ((1 / 23 : ℝ)) * (r t) ^ (99 : ℕ) := hq
    _ = ((1 / 23 : ℝ)) * ((r t) ^ (12 : ℕ) * (r t) ^ (87 : ℕ)) := by simp [hr99]
    _ ≤ ((1 / 23 : ℝ)) * ((r t) ^ (12 : ℕ) * ((1 / 23 : ℝ) ^ (87 : ℕ))) := by
          gcongr
    _ = ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := by ring_nf

/-- For `t ≥ 1`, bound `r(t)^100` by an explicit constant times `r(t)^12`. -/
public lemma rpow100_le_oneDiv23Pow88_rpow12 (t : ℝ) (ht : 1 ≤ t) :
    (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := by
  have hr88 : (r t) ^ (88 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) :=
    r_pow_le_one_div_23_pow (t := t) ht 88
  calc
    (r t) ^ (100 : ℕ) = (r t) ^ (12 : ℕ) * (r t) ^ (88 : ℕ) := by
      simpa [pow_add, mul_assoc] using! (pow_add (r t) 12 88)
    _ ≤ (r t) ^ (12 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) := by
          gcongr
    _ = ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := by ring_nf

private lemma norm_qterm_it_49_eq (t : ℝ) (ht0 : 0 < t) :
    ‖qterm (it t ht0) 49‖ = (r t) ^ (98 : ℕ) := by
  simpa [q_pow_49_eq_r_pow_98] using! norm_qterm_it (t := t) (ht := ht0) (n := 49)

/-- Bound the norm of the term appearing in the remainder estimate for the `Δ^2` truncation. -/
public lemma norm_missingDeltaTerm_le (t : ℝ) (ht0 : 0 < t) :
    ‖(coeffDeltaSq 50 : ℂ) * qterm (it t ht0) 49‖ ≤
      CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ) := by
  have hcoeff : ‖(coeffDeltaSq 50 : ℂ)‖ ≤ CdeltaSq * (51 : ℝ) ^ (29 : ℕ) := by
    simpa using! (abs_coeffDeltaSq_le (n := 50))
  have hqt : ‖qterm (it t ht0) 49‖ = (r t) ^ (98 : ℕ) := by
    simpa using! (norm_qterm_it_49_eq (t := t) (ht0 := ht0))
  have hC : 0 ≤ CdeltaSq * (51 : ℝ) ^ (29 : ℕ) := by
    dsimp [CdeltaSq, Cdelta]
    positivity
  calc
    ‖(coeffDeltaSq 50 : ℂ) * qterm (it t ht0) 49‖
        = ‖(coeffDeltaSq 50 : ℂ)‖ * ‖qterm (it t ht0) 49‖ := by simp
    _ ≤ (CdeltaSq * (51 : ℝ) ^ (29 : ℕ)) * (r t) ^ (98 : ℕ) := by
          refine mul_le_mul hcoeff ?_ (norm_nonneg _) hC
          simp [hqt]
    _ = CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ) := by ring_nf

/-- For `t ≥ 1`, bound `r(t)^98` by an explicit constant times `r(t)^12`. -/
public lemma rpow98_le_twoPow29_oneDiv23Pow88_rpow12 (t : ℝ) (ht : 1 ≤ t) :
    (r t) ^ (98 : ℕ) ≤ (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := by
  have hr86 : (r t) ^ (86 : ℕ) ≤ ((1 : ℝ) / 23) ^ (86 : ℕ) :=
    r_pow_le_one_div_23_pow (t := t) ht 86
  have hr86' : (r t) ^ (86 : ℕ) ≤ (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) := by
    calc
      (r t) ^ (86 : ℕ) ≤ ((1 : ℝ) / 23) ^ (86 : ℕ) := hr86
      _ = (23 : ℝ) ^ (2 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) :=
            oneDiv23_pow86_eq_23sq_mul_oneDiv23_pow88
      _ ≤ (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) := by
        exact mul_le_mul_of_nonneg_right pow23_sq_le_pow2_29 (by positivity)
  calc
    (r t) ^ (98 : ℕ) = (r t) ^ (12 : ℕ) * (r t) ^ (86 : ℕ) := by
      simpa [pow_add, mul_assoc] using! (pow_add (r t) 12 86)
    _ ≤ (r t) ^ (12 : ℕ) * ((2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hr86' (pow_nonneg (Real.exp_pos _).le _)
    _ = (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := by
          ring_nf

/-- For `t ≥ 1`, bound `t * r(t)^98` by an explicit constant times `r(t)^12`. -/
public lemma t_mul_rpow98_le_twoPow29_oneDiv23Pow88_rpow12 (t : ℝ) (ht : 1 ≤ t) :
    t * (r t) ^ (98 : ℕ) ≤ (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := by
  have hr0 : 0 ≤ r t := (Real.exp_pos _).le
  have htr : t * r t ≤ (1 / 23 : ℝ) := AppendixA.t_mul_r_le_one_div_23 (t := t) ht
  have hr85 : (r t) ^ (85 : ℕ) ≤ ((1 : ℝ) / 23) ^ (85 : ℕ) :=
    r_pow_le_one_div_23_pow (t := t) ht 85
  have h86 :
      ((1 : ℝ) / 23) ^ (86 : ℕ) ≤ (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) := by
    calc
      ((1 : ℝ) / 23) ^ (86 : ℕ)
          =
            (23 : ℝ) ^ (2 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) :=
        oneDiv23_pow86_eq_23sq_mul_oneDiv23_pow88
      _ ≤ (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) :=
            mul_le_mul_of_nonneg_right pow23_sq_le_pow2_29 (by positivity)
  calc
    t * (r t) ^ (98 : ℕ) = (t * r t) * (r t) ^ (97 : ℕ) := by
      simp [pow_succ, mul_left_comm, mul_comm]
    _ ≤ ((1 / 23 : ℝ)) * (r t) ^ (97 : ℕ) :=
          mul_le_mul_of_nonneg_right htr (pow_nonneg hr0 _)
    _ = ((1 / 23 : ℝ)) * ((r t) ^ (12 : ℕ) * (r t) ^ (85 : ℕ)) := by
      simpa [pow_add, mul_assoc] using! congrArg (fun x => ((1 / 23 : ℝ)) * x) (pow_add (r t) 12 85)
    _ ≤ ((1 / 23 : ℝ)) * ((r t) ^ (12 : ℕ) * ((1 / 23 : ℝ) ^ (85 : ℕ))) := by
          gcongr
    _ = ((1 / 23 : ℝ) ^ (86 : ℕ)) * (r t) ^ (12 : ℕ) := by ring_nf
    _ ≤ ((2 : ℝ) ^ (29 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ))) * (r t) ^ (12 : ℕ) :=
          mul_le_mul_of_nonneg_right h86 (pow_nonneg hr0 _)
    _ = (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := by ring_nf

end SpherePacking.Dim24.AppendixA
