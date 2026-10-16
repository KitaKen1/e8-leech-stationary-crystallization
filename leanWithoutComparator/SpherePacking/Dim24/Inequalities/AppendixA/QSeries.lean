-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.Finset.NatAntidiagonal

/-!
Basic `q`-series infrastructure used in Appendix A truncation arguments.

This file provides small reusable definitions/lemmas (`qterm`, `qseries`, convolution via
`Finset.antidiagonal`, and evaluation on the positive imaginary axis).

It is intentionally lightweight: more specialized truncation estimates live in dedicated files.
-/


open scoped BigOperators
open UpperHalfPlane

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- The basic term `q^n = exp(2π i n z)` in `q`-series. -/
@[expose]
public def qterm (z : ℍ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (z : ℂ))

/-- The `q`-series `∑ aₙ q^n` at `z`. -/
@[expose]
public def qseries (a : ℕ → ℂ) (z : ℍ) : ℂ :=
  ∑' n : ℕ, a n * qterm z n

/-- Convolution of coefficient functions (Cauchy product coefficients). -/
@[expose]
public def conv (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

/-- Multiplicativity of `qterm`: `qterm z m * qterm z n = qterm z (m + n)`. -/
public lemma qterm_mul (z : ℍ) (m n : ℕ) : qterm z m * qterm z n = qterm z (m + n) := by
  simpa [qterm, Nat.cast_add, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using!
    (Complex.exp_add
      (2 * Real.pi * Complex.I * (m : ℂ) * (z : ℂ))
      (2 * Real.pi * Complex.I * (n : ℂ) * (z : ℂ))).symm

/-- Evaluate `qterm` at `z = it t`: `qterm (it t) n = (q t)^n` with `q t = exp(-2πt)`. -/
public lemma qterm_it (t : ℝ) (ht : 0 < t) (n : ℕ) :
    qterm (it t ht) n = (q t : ℂ) ^ n := by
  have hq : Complex.exp (-(2 * Real.pi * t : ℝ) : ℂ) = (q t : ℂ) := by simp [q]
  have harg :
      2 * Real.pi * Complex.I * (n : ℂ) * ((it t ht : ℍ) : ℂ) =
        n * (-(2 * Real.pi * t : ℝ) : ℂ) := by
    simp [it, mul_assoc, mul_left_comm, mul_comm, I_mul_I_mul]
  calc
    qterm (it t ht) n = Complex.exp (n * (-(2 * Real.pi * t : ℝ) : ℂ)) := by
      simp [qterm, harg]
    _ = Complex.exp (-(2 * Real.pi * t : ℝ) : ℂ) ^ n := by
      simpa using! (Complex.exp_nat_mul (-(2 * Real.pi * t : ℝ) : ℂ) n)
    _ = (q t : ℂ) ^ n := by simpa using! congrArg (fun z : ℂ => z ^ n) hq

/-- Norm computation on the imaginary axis: `‖qterm (it t) n‖ = (q t)^n`. -/
public lemma norm_qterm_it (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ‖qterm (it t ht) n‖ = (q t) ^ n := by
  have hq0 : 0 ≤ q t := (Real.exp_pos _).le
  simp [qterm_it (t := t) (ht := ht) (n := n), norm_pow, abs_of_nonneg hq0]

end

end SpherePacking.Dim24.AppendixA
