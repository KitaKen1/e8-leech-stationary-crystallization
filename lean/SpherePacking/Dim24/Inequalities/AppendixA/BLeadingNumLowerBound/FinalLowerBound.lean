/- Final lower bound for the exact truncation sum. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.EvenReindex
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.DeltaCoeffBounds
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffMatchingComputations
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable


/-!
# A `q`-series shift identity for `Δ(it)^2`

To control the `Δ(it)^2` factor in Appendix A, we use the `q`-series expansion of `Δ(it)^2` and a
simple shift identity: multiplying by `exp(2*pi*t)` removes the leading `q` factor and shifts the
coefficients by one index.

This is the main `Δ^2` bookkeeping lemma used in the final truncation argument.

## Main statements
* `exp_two_pi_mul_Delta_sq_eq_qseries_shift`
-/


open scoped BigOperators
open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA


lemma coeffE4Cube_zero : coeffE4Cube 0 = 1 := by simp [coeffE4Cube, coeffE4Sq, conv, coeffE4]

lemma coeffE6Sq_zero : coeffE6Sq 0 = 1 := by simp [coeffE6Sq, conv, coeffE6]

lemma coeffDelta_zero : coeffDelta 0 = 0 := by simp [coeffDelta, coeffE4Cube_zero, coeffE6Sq_zero]

lemma coeffDeltaSq_zero : coeffDeltaSq 0 = 0 := by simp [coeffDeltaSq, conv, coeffDelta_zero]

/--
Shift the `q`-series for `Δ(it)^2` by multiplying with `exp(2*pi*t)`.

Concretely, this rewrites `exp(2*pi*t) * Δ(it)^2` as the `q`-series with coefficients
`coeffDeltaSq (n+1)`.
-/
public lemma exp_two_pi_mul_Delta_sq_eq_qseries_shift (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    (Real.exp (2 * Real.pi * t) : ℂ) * (Δ (it t ht0)) ^ (2 : ℕ) =
      qseries (fun n : ℕ => (coeffDeltaSq (n + 1) : ℂ)) (it t ht0) := by
  set z : ℍ := it t ht0
  have hΔsq_series : (Δ z) ^ (2 : ℕ) = qseries (fun n : ℕ => (coeffDeltaSq n : ℂ)) z := by
    simpa [z] using! (Delta_sq_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  -- `exp(2πt) = (q t)⁻¹`.
  have hexp : (Real.exp (2 * Real.pi * t) : ℂ) = (q t : ℂ)⁻¹ := by
    have h :
        Real.exp (2 * Real.pi * t) = (Real.exp (-(2 * Real.pi * t)))⁻¹ := by
      simpa using! (congrArg Inv.inv (Real.exp_neg (2 * Real.pi * t))).symm
    simpa [q] using! congrArg (fun x : ℝ => (x : ℂ)) h
  -- Split `qseries` at `n=0`, then shift using `q⁻¹ * qterm(it) (m+1) = qterm(it) m`.
  let e : ℕ → ℂ := fun n => (coeffDeltaSq n : ℂ) * qterm z n
  have he_summable : Summable e := by
    have he_norm : Summable (fun n : ℕ => ‖e n‖) := by
      have hcoeff :
          ∀ n : ℕ,
            |(coeffDeltaSq n : ℝ)| ≤ CdeltaSq * (((n + 1 : ℕ) : ℝ) ^ (29 : ℕ)) := by
        intro n
        simpa using! (abs_coeffDeltaSq_le (n := n))
      exact summable_norm_qseries_of_coeffBound t ht0 ht coeffDeltaSq CdeltaSq 29 hcoeff
    exact Summable.of_norm he_norm
  have hsplit1 :
      qseries (fun n : ℕ => (coeffDeltaSq n : ℂ)) z = e 0 + ∑' m : ℕ, e (m + 1) := by
    simpa [qseries, e] using! (he_summable.sum_add_tsum_nat_add 1).symm
  have hzero : e 0 = 0 := by
    simp [e, coeffDeltaSq_zero]
  have hqterm : ∀ m : ℕ, (q t : ℂ)⁻¹ * qterm z (m + 1) = qterm z m := by
    intro m
    have hqne : (q t : ℂ) ≠ 0 := by
      have : (0 : ℝ) < q t := Real.exp_pos _
      exact_mod_cast (ne_of_gt this)
    -- Use `qterm_it` and cancel `q` against `q⁻¹`.
    simp [z, qterm_it, pow_succ', hqne, inv_mul_cancel_left₀]
  have hshift :
      (q t : ℂ)⁻¹ * qseries (fun n : ℕ => (coeffDeltaSq n : ℂ)) z =
        qseries (fun n : ℕ => (coeffDeltaSq (n + 1) : ℂ)) z := by
    calc
      (q t : ℂ)⁻¹ * qseries (fun n : ℕ => (coeffDeltaSq n : ℂ)) z
          = (q t : ℂ)⁻¹ * (e 0 + ∑' m : ℕ, e (m + 1)) := by
              simpa [qseries, e] using! congrArg (fun s => (q t : ℂ)⁻¹ * s) hsplit1
      _ = (q t : ℂ)⁻¹ * (∑' m : ℕ, e (m + 1)) := by simp [hzero]
      _ = ∑' m : ℕ, (q t : ℂ)⁻¹ * e (m + 1) := by
            simpa using!
              (tsum_mul_left (a := (q t : ℂ)⁻¹) (f := fun m : ℕ => e (m + 1))).symm
      _ = ∑' m : ℕ, (coeffDeltaSq (m + 1) : ℂ) * qterm z m := by
            refine tsum_congr ?_
            intro m
            calc
              (q t : ℂ)⁻¹ * e (m + 1)
                  = (q t : ℂ)⁻¹ * ((coeffDeltaSq (m + 1) : ℂ) * qterm z (m + 1)) := by
                      simp [e]
              _ = (coeffDeltaSq (m + 1) : ℂ) * ((q t : ℂ)⁻¹ * qterm z (m + 1)) := by
                      ring_nf
              _ = (coeffDeltaSq (m + 1) : ℂ) * qterm z m := by
                      simp [hqterm m]
      _ = qseries (fun n : ℕ => (coeffDeltaSq (n + 1) : ℂ)) z := by
            simp [qseries]
  calc
    (Real.exp (2 * Real.pi * t) : ℂ) * (Δ z) ^ (2 : ℕ)
        = (q t : ℂ)⁻¹ * qseries (fun n : ℕ => (coeffDeltaSq n : ℂ)) z := by
              simp [hexp, hΔsq_series]
    _ = qseries (fun n : ℕ => (coeffDeltaSq (n + 1) : ℂ)) z := hshift
    _ = qseries (fun n : ℕ => (coeffDeltaSq (n + 1) : ℂ)) (it t ht0) := by simp [z]


end SpherePacking.Dim24.AppendixA
