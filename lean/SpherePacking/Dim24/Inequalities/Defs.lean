-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.ModularForms.Varphi
public import SpherePacking.Dim24.ModularForms.Psi.Defs


/-!
# Basic definitions for imaginary-axis inequalities (Dim24)

This file isolates the upper-half-plane points `it` and `i/t`, and the Laplace kernel `B(t)` used
in the dimension-24 imaginary-axis inequalities.

## Main definitions
* `iOverT`
* `BKernel`

## Main statements
* `S_smul_it`

Paper reference: `dim_24.tex`, Appendix A and Section 4.
-/


open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

/-- The point `i/t` in the upper half-plane. -/
@[expose]
public def iOverT (t : ℝ) (ht : 0 < t) : ℍ :=
  it (t := 1 / t) (by simpa using! (one_div_pos.2 ht))

/-- The modular group element `S` sends `i t` to `i / t`. -/
public lemma S_smul_it (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • it t ht = iOverT t ht := by
  have ht0 : (t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht)
  rw [UpperHalfPlane.modular_S_smul]
  ext1
  have hinv : (-((Complex.I : ℂ) * (t : ℂ)))⁻¹ = (Complex.I : ℂ) * (t : ℂ)⁻¹ := by
    simp [mul_comm]
  simp [iOverT, it, one_div, hinv]

/-- The kernel `B(t)` from the Laplace representation of `\hat f` (paper Section 4). -/
@[expose]
public def BKernel (t : ℝ) (ht : 0 < t) : ℂ :=
  ((Real.pi : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ 10 * varphi (iOverT t ht)
    + (1 / ((65520 : ℂ) * (Real.pi : ℂ))) * ψI (it t ht)

end SpherePacking.Dim24
