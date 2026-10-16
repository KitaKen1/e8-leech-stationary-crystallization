module
public import SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Transform
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Ptilde

/-!
# Definitions for the `eq:avalues` remainder integral

This file introduces the explicit function `pPaper`, its Laplace transform `pTildeIntegral`,
the full remainder integrand `avaluesRemainderIntegrandFull`, and the remainder integral
`avaluesRemainderIntegral` from the paper's equation `eq:avalues`.

## Main definitions
* `pPaper`
* `pTildeIntegral`
* `avaluesRemainderIntegrandFull`
* `avaluesRemainderIntegral`

## Implementation notes
This file is split out so that auxiliary files can import these definitions without creating
`public import` cycles.
-/


namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex MeasureTheory Set

/-- The explicit function `p(t)` from `dim_24.tex` (equation `eq:phip`). -/
@[expose] public def pPaper (t : ℝ) : ℂ :=
  (-(864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (4 * Real.pi * t) : ℂ) +
    ((725760 : ℂ) / (π : ℂ)) * (t : ℂ) * (Real.exp (2 * Real.pi * t) : ℂ) +
      (-(2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (2 * Real.pi * t) : ℂ) +
        ((113218560 : ℂ) / (π : ℂ)) * (t : ℂ) +
          (-(223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))

/-- Laplace transform of `pPaper` (paper: `\tilde p(r)`), as a function of `u = r^2`. -/
@[expose] public def pTildeIntegral (u : ℝ) : ℂ :=
  if 4 < u then
    ∫ t : ℝ in Set.Ioi (0 : ℝ), pPaper t * (Real.exp (-Real.pi * u * t) : ℂ)
  else 0

/-- Remainder integrand for the `eq:avalues` remainder, as a function on all `ℝ`. -/
@[expose] public def avaluesRemainderIntegrandFull (u t : ℝ) : ℂ :=
  if ht : 0 < t then
    ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) - pPaper t) * (Real.exp (-Real.pi * u * t) : ℂ)
  else 0

/-- The analytic remainder integral from `eq:avalues`, as a function of `u = r^2`. -/
@[expose] public def avaluesRemainderIntegral (u : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi (0 : ℝ), avaluesRemainderIntegrandFull u t

end SpecialValuesDerivTwoLaurent

end
end SpherePacking.Dim24
