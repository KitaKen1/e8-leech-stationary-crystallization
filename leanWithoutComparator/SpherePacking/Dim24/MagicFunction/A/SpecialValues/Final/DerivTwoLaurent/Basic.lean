module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivDefs
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi2
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Constants for the Laurent expansion at `u = 2`

This file records the coefficient `l` of `q^{-1}` in `varphi₂` (as in `dim_24.tex`) and the
corresponding residue `B = l / π` that appears as the residue of the simple pole at `u = 2`.

## Main definitions
* `l`
* `B`

## Main statements
* `B_eq_l_div_pi`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex MeasureTheory Set
open RealIntegrals

/-- The `q^{-1}` coefficient in `varphi₂` (paper after (2.16)): `2218752 / π^2`. -/
@[expose] public def l : ℂ := (2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))

/-- The residue constant for the `u = 2` pole: `B = l / π = 2218752 / π^3`. -/
@[expose] public def B : ℂ := (2218752 : ℂ) / ((π : ℂ) ^ (3 : ℕ))

/-- Relation between the two residue constants: `B = l / π`. -/
public lemma B_eq_l_div_pi : B = l / (π : ℂ) := by
  simp [B, l, div_eq_mul_inv, pow_succ, mul_assoc]

end SpecialValuesDerivTwoLaurent

end

end SpherePacking.Dim24
