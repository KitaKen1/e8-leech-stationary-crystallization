-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.ModularForms.Varphi
public import SpherePacking.ModularForms.ResToImagAxis
public import Mathlib.Analysis.Complex.Exponential
public import SpherePacking.Integration.Measure
public import SpherePacking.Integration.SmoothIntegralIciOne


/-!
# Preamble for the `I₆'` tail integral

This file introduces the basic integrands and elementary bounds used to control and
differentiate the tail integral `I₆'` (the only integral over `t ∈ Set.Ici 1`).

## Main definitions
* `s` - the open set `(-1, ∞)` in the `x` variable
* `coeff`, `g`, `gN` - the building blocks of the integrand

## Main statements
* `coeff_norm`
* `g_norm_bound`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace Schwartz

open MeasureTheory Filter Topology

namespace I6Smooth

/-!
## Differentiating under the `I₆'` integral
-/

/-- The open set `s = (-1, ∞)` where we differentiate the tail integral in `x`. -/
@[expose] public def s : Set ℝ := Set.Ioi (-1 : ℝ)

/-- `s` is open. -/
public lemma isOpen_s : IsOpen s := isOpen_Ioi

/-- The complex coefficient appearing in the exponential factor of the tail integrand. -/
@[expose] public def coeff (t : ℝ) : ℂ := Integration.SmoothIntegralIciOne.coeff t

/-- The basic tail integrand built from `varphi(it)` and the exponential factor. -/
@[expose] public def g (x t : ℝ) : ℂ :=
  Integration.SmoothIntegralIciOne.g (hf := varphi.resToImagAxis) x t

/-- The integrand `gN n x t = (coeff t) ^ n * g x t` used for iterated differentiation in `x`. -/
@[expose] public def gN (n : ℕ) (x t : ℝ) : ℂ :=
  Integration.SmoothIntegralIciOne.gN (hf := varphi.resToImagAxis) n x t

/-- For `t ≥ 1`, the coefficient has norm `π t`. -/
public lemma coeff_norm (t : ℝ) (ht : t ∈ Set.Ici (1 : ℝ)) : ‖coeff t‖ = Real.pi * t := by
  simpa [coeff] using! (Integration.SmoothIntegralIciOne.coeff_norm (t := t) ht)

/-- A basic norm bound for the integrand `g x t`. -/
public lemma g_norm_bound (x : ℝ) (t : ℝ) :
    ‖g x t‖ ≤ ‖varphi.resToImagAxis t‖ * Real.exp (-Real.pi * x * t) := by
  simpa [g] using!
    (Integration.SmoothIntegralIciOne.g_norm_bound (hf := varphi.resToImagAxis) (x := x) (t := t))

end Schwartz.I6Smooth
end

end SpherePacking.Dim24
