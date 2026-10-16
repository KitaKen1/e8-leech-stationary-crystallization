module
public import SpherePacking.Dim24.Inequalities.Defs
public import SpherePacking.Dim24.ModularForms.Psi.Defs
public import SpherePacking.Dim24.ModularForms.Varphi


/-!
# Laplace kernels

This file defines the kernels used in the Laplace representation of the magic function, along
with totalized versions for use as integrands on `ℝ`.

## Main definitions
* `AKernel`, `AKernel0`
* `BKernel0`
* `BleadingCorrection`
-/

namespace SpherePacking.Dim24

noncomputable section

open UpperHalfPlane

/-- The kernel `A(t)` in the Laplace representation of `f` (paper (4.2)). -/
@[expose]
public def AKernel (t : ℝ) (ht : 0 < t) : ℂ :=
  ((Real.pi : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)
    - (1 / ((65520 : ℂ) * (Real.pi : ℂ))) * ψI (it t ht)

/-- Totalized version of `AKernel` for use as an integrand on `ℝ`. -/
@[expose]
public def AKernel0 (t : ℝ) : ℂ :=
  if ht : 0 < t then AKernel t ht else 0

/-- Totalized version of `BKernel` for use as an integrand on `ℝ`. -/
@[expose]
public def BKernel0 (t : ℝ) : ℂ :=
  if ht : 0 < t then BKernel t ht else 0

/-- Closed form of the leading-term contribution
`∫₁^∞ ((1/39) t e^{2πt} - (10/(117π)) e^{2πt}) e^{-π r² t} dt`
appearing in `dim_24.tex` (around lines 694-705), written as a function of `r²`. -/
@[expose]
public def BleadingCorrection (r2 : ℝ) : ℂ :=
  Complex.ofReal
    ((((10 : ℝ) - 3 * Real.pi) * (2 - r2) + 3) /
          (117 * (Real.pi ^ (2 : ℕ)) * (r2 - 2) ^ (2 : ℕ)) *
        Real.exp (-Real.pi * (r2 - 2)))

end

end SpherePacking.Dim24
