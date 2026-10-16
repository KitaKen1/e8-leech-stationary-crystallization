-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.EvenU.BProfileZeros
public import SpherePacking.Dim24.MagicFunction.F.BKernelAsymptotics
public import SpherePacking.Dim24.MagicFunction.F.Laplace.KernelTools
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.LeadingCorrection
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingBounds.BKernelSubLeadingBound
public import SpherePacking.Dim24.MagicFunction.F.ProfileComplex.B
public import SpherePacking.Dim24.MagicFunction.F.Laplace.TopologyDomains
public import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Tactic.NormNumI
public import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import SpherePacking.ForMathlib.ExpPiIMulMulI
public import SpherePacking.Dim24.MagicFunction.Radial
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


/-!
# Laplace identity helpers for `aProfile`

This file collects basic exponential and trigonometric rewrite lemmas used in later Laplace
manipulations for the dimension-24 `a`-profile.

## Main statements
* `LaplaceTmp.LaplaceA.exp_pi_I_mul_mul_I_eq_real_exp`
* `LaplaceTmp.LaplaceA.exp_pi_mul_I_add_exp_neg_pi_mul_I_sub_two`
* `LaplaceTmp.LaplaceA.Φ₅'_imag_axis_eq_laplace`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceA

noncomputable section

/-
## Laplace identity helpers for `aProfile`

These lemmas mirror the dimension-8 development (`MagicFunction.g.CohnElkies.LaplaceA`) but are
specialized to the dimension-24 integrands built from `varphi`.
-/

open RealIntegrals.ComplexIntegrands


/-- Rewrite the exponential factor `exp (π * I * u * (t * I))` as `exp (-π * u * t)`. -/
public lemma exp_pi_I_mul_mul_I_eq_real_exp (u t : ℝ) :
    Complex.exp (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
      Complex.exp (-Real.pi * u * t : ℂ) := by
  simpa [Complex.ofReal_exp] using!
    (SpherePacking.ForMathlib.exp_pi_I_mul_mul_I_eq_real_exp (u := u) (t := t))

/-- Trigonometric identity: `e^{iπu} + e^{-iπu} - 2 = -4 * sin(πu/2)^2`. -/
public lemma exp_pi_mul_I_add_exp_neg_pi_mul_I_sub_two (u : ℝ) :
    Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ) =
      -((4 * (Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
  -- This is the standard identity `e^{iθ} + e^{-iθ} - 2 = -4 sin^2(θ/2)`.
  have htrig :
      (2 : ℂ) - Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) -
            Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) =
        ((2 - 2 * Real.cos (Real.pi * u) : ℝ) : ℂ) := by
    let z : ℂ := ((Real.pi * u : ℝ) : ℂ)
    have hz : Complex.cos z = (Real.cos (Real.pi * u) : ℂ) := by simp [z]
    have hsum :
        Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I) = (2 : ℂ) * Complex.cos z :=
      Eq.symm (Complex.two_cos z)
    calc
      (2 : ℂ) - Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I))
          = (2 : ℂ) - (Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) := by
              ring_nf
      _ = (2 : ℂ) - (2 : ℂ) * Complex.cos z :=
            sub_right_inj.mpr hsum
      _ = ((2 - 2 * Real.cos (Real.pi * u) : ℝ) : ℂ) := by
            simp [hz, sub_eq_add_neg]
  have hhalf :
      (2 - 2 * Real.cos (Real.pi * u) : ℝ) = 4 * (Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) := by
    have hsin :
        (Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) = 1 / 2 - Real.cos (Real.pi * u) / 2 := by
      have : (2 : ℝ) * (Real.pi * u / 2) = Real.pi * u := by ring
      simpa [pow_two, this] using! (Real.sin_sq_eq_half_sub (x := Real.pi * u / 2))
    calc
      (2 - 2 * Real.cos (Real.pi * u) : ℝ) = 4 * (1 / 2 - Real.cos (Real.pi * u) / 2) := by ring
      _ = 4 * (Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) := by simp [hsin]
  have hrew :
      Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
          Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ) =
        -((2 : ℂ) - Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) -
            Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I))) := by
    ring
  rw [hrew, htrig]
  exact neg_inj.mpr (congrArg Complex.ofReal hhalf)

lemma Φ₅'_imag_axis (u t : ℝ) (ht : 0 < t) :
    Φ₅' u ((t : ℂ) * Complex.I) =
      -((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht) *
        Complex.exp (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  -- Rewrite the `-1/z` argument as `i/t`.
  have harg : (-1 : ℂ) / ((t : ℂ) * Complex.I) = (Complex.I : ℂ) * ((1 / t : ℝ) : ℂ) := by
    have htI : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero htne Complex.I_ne_zero
    refine (div_eq_iff htI).2 ?_
    -- Clear denominators: `(-1) = (I * (1/t)) * (t*I)`.
    have ht' : 0 < (1 / t : ℝ) := one_div_pos.2 ht
    simp [mul_left_comm, mul_comm, one_div, htne, Complex.I_mul_I]
  have ht' : 0 < (1 / t : ℝ) := one_div_pos.2 ht
  -- Evaluate `varphi'` at `i/t` via the upper half-plane point `iOverT t ht`.
  have hvarphi' : varphi' ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)) = varphi (iOverT t ht) := by
    -- `iOverT t ht` is definitionally `it (1/t)`.
    simp [iOverT, it, varphi', ht, mul_comm]
  -- Expand `Φ₅'` and simplify powers of `I`.
  have hI10 : (Complex.I : ℂ) ^ (10 : ℕ) = (-1 : ℂ) := by
    norm_num1
  -- Turn `varphi' (-1/(t*I))` into `varphi' (I*(1/t))`.
  have hvarphi'' : varphi' ((-1 : ℂ) / ((t : ℂ) * Complex.I)) = varphi (iOverT t ht) := by
    simpa [harg] using! hvarphi'
  have hvarphi''' : varphi' ((-1 : ℂ) / (Complex.I * (t : ℂ))) = varphi (iOverT t ht) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using! hvarphi''
  simp [Φ₅', hvarphi''', mul_pow, hI10, mul_left_comm, mul_comm]

/-- Expression for `Φ₅'` on the imaginary axis as a Laplace-type integrand. -/
public lemma Φ₅'_imag_axis_eq_laplace (u t : ℝ) (ht : 0 < t) :
    Φ₅' u ((t : ℂ) * Complex.I) =
      -((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht) * Complex.exp (-Real.pi * u * t : ℂ) := by
  simpa [exp_pi_I_mul_mul_I_eq_real_exp (u := u) (t := t)] using!
    (Φ₅'_imag_axis (u := u) (t := t) ht)

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceA
