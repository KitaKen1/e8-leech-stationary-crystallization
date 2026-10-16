/-
Auxiliary definitions for the dimension-24 +1 Fourier eigenfunction `a` (profile and integrals).
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.ModularForms.Varphi
public import SpherePacking.Dim24.MagicFunction.A.VarphiBounds
public import SpherePacking.ModularForms.ResToImagAxis
public import SpherePacking.ForMathlib.RadialSchwartz.OneSided
public import SpherePacking.MagicFunction.IntegralParametrisations
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# Prelude for `a`

Auxiliary definitions for the dimension-24 `+1` Fourier eigenfunction `a` (profile and integrals).

## Main definitions
* `varphi'`
* `RealIntegrals.I₁'`, `RealIntegrals.I₂'`, `RealIntegrals.I₃'`
* `RealIntegrals.I₄'`, `RealIntegrals.I₅'`, `RealIntegrals.I₆'`
* `aProfile`

## Total extension of `varphi` to `ℂ`

We use a total extension `varphi' : ℂ → ℂ` which agrees with `varphi : ℍ → ℂ` on the upper half
plane and is `0` otherwise, matching the approach in the existing dimension-8 and dim-24 `b`
developments.
-/

open scoped UpperHalfPlane
open Complex
open MagicFunction.Parametrisations intervalIntegral

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section


/-- Total extension of `varphi` to a function on `ℂ`, equal to `0` outside the upper half-plane. -/
@[expose] public def varphi' (z : ℂ) : ℂ := if hz : 0 < z.im then varphi ⟨z, hz⟩ else 0

/-- On points `z` with `0 < im z`, the extension `varphi'` agrees with `varphi`. -/
@[simp] public lemma varphi'_def {z : ℂ} (hz : 0 < z.im) : varphi' z = varphi ⟨z, hz⟩ := by
  simp [varphi', hz]

/-- On `ℍ`, the extension `varphi'` agrees with `varphi`. -/
@[simp] public lemma varphi'_coe_upperHalfPlane (z : ℍ) : varphi' (z : ℂ) = varphi z := by
  simp [varphi', UpperHalfPlane.im_pos z]

/-- The extension `varphi'` is a measurable function on `ℂ`. -/
public lemma measurable_varphi' : Measurable (varphi' : ℂ → ℂ) := by
  let s : Set ℂ := {z : ℂ | 0 < z.im}
  have hs : MeasurableSet s := by
    simpa [s] using!
      (isOpen_lt (continuous_const : Continuous fun _ : ℂ => (0 : ℝ))
        Complex.continuous_im).measurableSet
  have hf : Measurable fun z : s => varphi (⟨(z : ℂ), z.property⟩ : ℍ) :=
    (varphi_holo'.continuous.comp (by
      fun_prop)).measurable
  simpa [varphi', s] using! (Measurable.dite (s := s) hf measurable_const hs)

/-!
## Real-integral decomposition of the one-variable profile

We follow the contour integral decomposition in `dim_24.tex`, eq. (2.7) / (2.8) (`eq:conta`),
rewritten as a sum of integrals over the standard parametrizations `z₁', ..., z₆'`.

Here `u` corresponds to the paper's `r^2` in the exponential `exp(π i r^2 z)`.
-/

namespace RealIntegrals

/-! ### Complex integrands -/

namespace ComplexIntegrands

variable (u : ℝ)

/-- Complex integrand for the contour piece parametrized by `z₁'`. -/
@[expose] public def Φ₁' : ℂ → ℂ := fun z =>
  varphi' (-1 / (z + 1)) * (z + 1) ^ (10 : ℕ) * cexp (Real.pi * Complex.I * (u : ℂ) * z)

/-- Alias of `Φ₁'` used for the contour piece parametrized by `z₂'`. -/
@[expose] public def Φ₂' : ℂ → ℂ := Φ₁' u

/-- Complex integrand for the contour piece parametrized by `z₃'`. -/
@[expose] public def Φ₃' : ℂ → ℂ := fun z =>
  varphi' (-1 / (z - 1)) * (z - 1) ^ (10 : ℕ) * cexp (Real.pi * Complex.I * (u : ℂ) * z)

/-- Alias of `Φ₃'` used for the contour piece parametrized by `z₄'`. -/
@[expose] public def Φ₄' : ℂ → ℂ := Φ₃' u

/-- Complex integrand for the contour piece parametrized by `z₅'`. -/
@[expose] public def Φ₅' : ℂ → ℂ := fun z =>
  varphi' (-1 / z) * z ^ (10 : ℕ) * cexp (Real.pi * Complex.I * (u : ℂ) * z)

/-- Complex integrand for the contour piece parametrized by `z₆'`. -/
@[expose] public def Φ₆' : ℂ → ℂ := fun z =>
  varphi' z * cexp (Real.pi * Complex.I * (u : ℂ) * z)

end ComplexIntegrands

/-! ### Real integrands (parametrized along `z₁', ..., z₆'`) -/

namespace RealIntegrands

open ComplexIntegrands

variable (u : ℝ)

/-- Real integrand along `z₁'` for the profile decomposition. -/
@[expose] public def Φ₁ : ℝ → ℂ := fun t => (Complex.I : ℂ) * Φ₁' u (z₁' t)

/-- Real integrand along `z₂'` for the profile decomposition. -/
@[expose] public def Φ₂ : ℝ → ℂ := fun t => Φ₂' u (z₂' t)

/-- Real integrand along `z₃'` for the profile decomposition. -/
@[expose] public def Φ₃ : ℝ → ℂ := fun t => (Complex.I : ℂ) * Φ₃' u (z₃' t)

/-- Real integrand along `z₄'` for the profile decomposition. -/
@[expose] public def Φ₄ : ℝ → ℂ := fun t => (-1 : ℂ) * Φ₄' u (z₄' t)

/-- Real integrand along `z₅'` for the profile decomposition. -/
@[expose] public def Φ₅ : ℝ → ℂ := fun t => (Complex.I : ℂ) * Φ₅' u (z₅' t)

/-- Real integrand along `z₆'` for the profile decomposition. -/
@[expose] public def Φ₆ : ℝ → ℂ := fun t => (Complex.I : ℂ) * Φ₆' u (z₆' t)

end RealIntegrands

open RealIntegrands

/-! ### Real integrals -/

/-- The first contour integral `I₁'` in the profile decomposition. -/
@[expose] public def I₁' (u : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, Φ₁ u t

/-- The second contour integral `I₂'` in the profile decomposition. -/
@[expose] public def I₂' (u : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, Φ₂ u t

/-- The third contour integral `I₃'` in the profile decomposition. -/
@[expose] public def I₃' (u : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, Φ₃ u t

/-- The fourth contour integral `I₄'` in the profile decomposition. -/
@[expose] public def I₄' (u : ℝ) : ℂ := ∫ t in (0 : ℝ)..1, Φ₄ u t

/-- The fifth contour integral `I₅'` in the profile decomposition. -/
@[expose] public def I₅' (u : ℝ) : ℂ := (-2 : ℂ) * ∫ t in (0 : ℝ)..1, Φ₅ u t

/-- The sixth contour integral `I₆'` in the profile decomposition. -/
@[expose] public def I₆' (u : ℝ) : ℂ := (2 : ℂ) * ∫ t in Set.Ici (1 : ℝ), Φ₆ u t

/-- The profile function defined as the sum `I₁' + I₂' + I₃' + I₄' + I₅' + I₆'`. -/
@[expose] public def a' (u : ℝ) : ℂ := I₁' u + I₂' u + I₃' u + I₄' u + I₅' u + I₆' u

end RealIntegrals

/-- One-variable profile used for the radial Schwartz function: `u ↦ a'(u)`. -/
@[expose] public def aProfile (u : ℝ) : ℂ := RealIntegrals.a' u

end

end SpherePacking.Dim24
