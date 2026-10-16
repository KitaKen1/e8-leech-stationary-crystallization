module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.CoeffExp

/-!
# Definitions for the Laurent bridge at `u = 2`

This file is intentionally small: it only defines the main constants and the renormalized profile
that appears in the Laurent expansion near `u = 2` for the paper's equation `eq:avalues`
(`dim_24.tex`).

## Main definitions
* `constA2_av`
* `fProfile`
* `remTwo`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex

/-- The constant term `aProfile(2) = 725760 i / π` from the paper.

Named `constA2_av` to avoid clashes with the file-constant in
`DerivTwoLaurent/ExistsLaurent.lean`.
-/
@[expose] public def constA2_av : ℂ := ((725760 : ℂ) * Complex.I / (π : ℂ))

/-- Renormalized profile: `(aProfile u - constA2) / (I * coeffExp u)`. -/
@[expose] public def fProfile (u : ℝ) : ℂ :=
  (aProfile u - constA2_av) / ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u)

/--
The remainder term after extracting the pole `B/(u-2)`. This is the function whose limit at `2⁺`
drives the Laurent expansion.
-/
@[expose] public def remTwo (u : ℝ) : ℂ := fProfile u - (B / ((u - 2 : ℝ) : ℂ))

end SpecialValuesDerivTwoLaurent

end

end SpherePacking.Dim24
