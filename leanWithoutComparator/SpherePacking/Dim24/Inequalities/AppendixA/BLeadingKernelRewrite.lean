-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Tactic.NormNumI


/-!
# Rewrite for `BKernel`

In Appendix A (Lemma `Bleadingterms`), the kernel `BKernel t` contains the term
`t^10 * varphi (i/t)`. Using the modular `S` transformation for `varphi`, we rewrite this as a
combination of `varphi (it t)`, `varphi₁ (it t) / it t`, and `varphi₂ (it t) / (it t)^2`.

## Main statements
* `t10_mul_varphi_iOverT_eq`
* `BKernel_eq`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

/-- Identify the `S` action on `it t` with the point `i/t`. -/
lemma S_smul_it_eq_iOverT (t : ℝ) (ht : 0 < t) :
    (ModularGroup.S • it t ht) = iOverT t ht := by
  simpa using! S_smul_it (t := t) ht

/-- Coercion lemma: `((it t) : ℂ)^8 = t^8`. -/
lemma coe_it_pow_eight (t : ℝ) (ht : 0 < t) :
    (((it t ht : ℍ) : ℂ) ^ (8 : ℕ)) = (t : ℂ) ^ (8 : ℕ) := by
  simp [it, mul_pow, show (Complex.I : ℂ) ^ (8 : ℕ) = (1 : ℂ) by norm_num1]

/-- Rewrite the `varphi`-term in `BKernel` using the `S`-transformation of `varphi`. -/
theorem t10_mul_varphi_iOverT_eq (t : ℝ) (ht : 0 < t) :
    (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) =
      (t : ℂ) ^ (2 : ℕ) *
        (varphi (it t ht) + varphi₁ (it t ht) / (it t ht) +
          varphi₂ (it t ht) / ((it t ht : ℍ) : ℂ) ^ 2) := by
  have hS :
      (((it t ht : ℍ) : ℂ) ^ (8 : ℕ)) * varphi (iOverT t ht) =
        varphi (it t ht) + varphi₁ (it t ht) / (it t ht) +
          varphi₂ (it t ht) / ((it t ht : ℍ) : ℂ) ^ 2 := by
    simpa [S_smul_it_eq_iOverT (t := t) ht] using! (varphi_S_transform (z := it t ht))
  have hit8 : (((it t ht : ℍ) : ℂ) ^ (8 : ℕ)) = (t : ℂ) ^ (8 : ℕ) := coe_it_pow_eight (t := t) ht
  have ht10 : (t : ℂ) ^ (10 : ℕ) = (t : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (8 : ℕ) := by
    simpa using! (pow_add (t : ℂ) 2 8)
  calc
    (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)
        = (t : ℂ) ^ (2 : ℕ) * ((((it t ht : ℍ) : ℂ) ^ (8 : ℕ)) * varphi (iOverT t ht)) := by
          simp [ht10, hit8, mul_assoc]
    _ = (t : ℂ) ^ (2 : ℕ) *
          (varphi (it t ht) + varphi₁ (it t ht) / (it t ht) +
            varphi₂ (it t ht) / ((it t ht : ℍ) : ℂ) ^ 2) := by
          simp [hS]

/-- Convenient rewrite for `BKernel` at `t>0` (no real parts yet). -/
public theorem BKernel_eq (t : ℝ) (ht : 0 < t) :
    BKernel t ht =
      ((Real.pi : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (2 : ℕ) *
          (varphi (it t ht) + varphi₁ (it t ht) / (it t ht) +
            varphi₂ (it t ht) / ((it t ht : ℍ) : ℂ) ^ 2)
        + (1 / ((65520 : ℂ) * (Real.pi : ℂ))) * ψI (it t ht) := by
  simp [BKernel, t10_mul_varphi_iOverT_eq (t := t) ht, mul_assoc]

end SpherePacking.Dim24
