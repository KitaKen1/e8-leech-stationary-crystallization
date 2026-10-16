-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Tactic.NormNumI


/-!
# Imaginary-axis transform

Imaginary-axis reduction identity for `varphi` used in the `t ≤ 1` case.

Paper reference: `dim_24.tex`, Appendix A, proof of Lemma `phinonpos` (using equation (2.9)).

## Main statements
* `tPow10_varphi_iOverT`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

/-- The `10/t` identity used to treat the `t ≤ 1` case:
`t^{10} varphi(i/t) = t^2 varphi(it) - i t varphi₁(it) - varphi₂(it)`.

Paper reference: equation (2.9) in `dim_24.tex`. -/
public theorem tPow10_varphi_iOverT (t : ℝ) (ht : 0 < t) :
    (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) =
      (t : ℂ) ^ (2 : ℕ) * varphi (it t ht)
        - Complex.I * (t : ℂ) * varphi₁ (it t ht) - varphi₂ (it t ht) := by
  /- Proof sketch:
  Specialize `varphi_S_transform` at `z = it t` and rewrite `S • (it t)` as `iOverT t`.
  Then clear denominators by multiplying by `z^2` and compute powers of `z = i t`. -/
  have hS := varphi_S_transform (z := it t ht)
  have hS' :
      ((it t ht : ℂ) ^ (8 : ℕ)) * varphi (iOverT t ht) =
        varphi (it t ht) + varphi₁ (it t ht) / (it t ht) +
          varphi₂ (it t ht) / ((it t ht : ℂ) ^ 2) := by
    simpa [S_smul_it (t := t) ht] using! hS
  have ht0 : (t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht)
  have hz0 : (it t ht : ℂ) ≠ 0 := by
    -- `it t = i * t` and `t ≠ 0`.
    simpa [it] using! mul_ne_zero (by simp : (Complex.I : ℂ) ≠ 0) ht0
  -- Clear denominators in `hS'` to get
  -- `z^10 * varphi(i/t) = z^2 * varphi(z) + z * varphi₁(z) + varphi₂(z)`.
  have hclear :
      ((it t ht : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht) =
        ((it t ht : ℂ) ^ (2 : ℕ)) * varphi (it t ht)
          + (it t ht : ℂ) * varphi₁ (it t ht) + varphi₂ (it t ht) := by
    -- Clear denominators in `hS'`.
    have htmp := hS'
    field_simp [hz0] at htmp
    have hpow :
        ((it t ht : ℂ) ^ (2 : ℕ)) * ((it t ht : ℂ) ^ (8 : ℕ)) = (it t ht : ℂ) ^ (10 : ℕ) := by
      simpa [pow_add] using! (pow_add (it t ht : ℂ) 2 8).symm
    -- Re-associate the LHS and use `hpow` to rewrite `z^2 * z^8` as `z^10`.
    simpa [mul_assoc, mul_add, add_mul, pow_two, hpow] using! htmp
  -- Compute powers of `z = i * t` and rearrange signs to match the `t`-only statement.
  have hI10 : (Complex.I : ℂ) ^ (10 : ℕ) = (-1 : ℂ) := by
    norm_num1
  have hI2 : (Complex.I : ℂ) ^ (2 : ℕ) = (-1 : ℂ) := by
    norm_num1
  have hz10 : (it t ht : ℂ) ^ (10 : ℕ) = -((t : ℂ) ^ (10 : ℕ)) := by
    calc
      (it t ht : ℂ) ^ (10 : ℕ) = ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) := by simp [it]
      _ = (Complex.I : ℂ) ^ (10 : ℕ) * (t : ℂ) ^ (10 : ℕ) := by simp [mul_pow]
      _ = (-1 : ℂ) * (t : ℂ) ^ (10 : ℕ) := by simp [hI10]
      _ = -((t : ℂ) ^ (10 : ℕ)) := by simp
  have hz2 : (it t ht : ℂ) ^ (2 : ℕ) = -((t : ℂ) ^ (2 : ℕ)) := by
    calc
      (it t ht : ℂ) ^ (2 : ℕ) = ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ) := by simp [it]
      _ = (Complex.I : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (2 : ℕ) := by simp [mul_pow]
      _ = (-1 : ℂ) * (t : ℂ) ^ (2 : ℕ) := by simp [hI2]
      _ = -((t : ℂ) ^ (2 : ℕ)) := by simp
  have hz1 : (it t ht : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by
    simp [it]
  -- Substitute these into `hclear` and multiply by `-1`.
  grind only
end SpherePacking.Dim24
