-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.ModularForms.JacobiTheta


/-!
# The functions `ψI`, `ψS`, `ψT` for `Γ(2)`

This file defines the functions `ψI`, `ψS`, `ψT` used in the dimension-24 argument.

## References
* `dim_24.tex`, Section 3 (`sec:b`), equations (3.1)-(3.3).
-/


namespace SpherePacking.Dim24

noncomputable section

open scoped Real ModularForm
open UpperHalfPlane Complex ModularGroup MatrixGroups

/-- The point `it ∈ ℍ` on the positive imaginary axis. -/
@[expose]
public def it (t : ℝ) (ht : 0 < t) : ℍ :=
  ⟨Complex.I * (t : ℂ), by simpa using! ht⟩

/-- `ψ_I` from `dim_24.tex` (eq. (3.1)),
expressed using `Θ₂,Θ₃,Θ₄` from `JacobiTheta.lean`. -/
@[expose]
public def ψI (z : ℍ) : ℂ :=
  (7 * (Θ₄ z) ^ 20 * (Θ₂ z) ^ 8
        + 7 * (Θ₄ z) ^ 24 * (Θ₂ z) ^ 4
        + 2 * (Θ₄ z) ^ 28) / (Δ z) ^ 2

/-- `ψ_S := ψ_I |_{-10} S`. -/
@[expose]
public def ψS : ℍ → ℂ := ψI ∣[-10] S

/-- `ψ_T := ψ_I |_{-10} T`. -/
@[expose]
public def ψT : ℍ → ℂ := ψI ∣[-10] T

end

end SpherePacking.Dim24
