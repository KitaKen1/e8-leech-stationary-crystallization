-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingTailReduction
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingKernelRewrite
import SpherePacking.ModularForms.DimensionFormulas
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
import SpherePacking.Dim24.Inequalities.AppendixA.Constants
import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesTailBounds
import SpherePacking.Dim24.Inequalities.AppendixA.RBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Numerator identities for Appendix A

In Appendix A we study the quantity `BleadingNum`, defined from the kernel expression
`(BKernel - leading) * Δ(it)^2`.

To compare this with explicit truncation polynomials, it is convenient to clear the common factor
`Δ(z)^2` in the modular-form pieces and work with explicit Eisenstein/theta numerators.

This file defines the cleared numerators (`varphi_num`, `phi1_num`, `phi2_num`, `psiI_num`) and
packages the resulting expression for `BleadingNum`.

## Main definitions
* `varphi_num`, `phi1_num`, `phi2_num`, `psiI_num`

## Main statements
* `Delta_eq_eisenstein`
* `BleadingNum_eq_num_expr`

-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA

/-!
### `Δ = (E₄^3 - E₆^2)/1728`

The PARI/GP code in `appendix.txt` expands `Δ` via the Ramanujan identity
`Δ = (E₄^3 - E₆^2)/1728`. In this repo, `Δ` is defined by the product formula, and the
identification with the Eisenstein expression is provided by `Delta_E4_eqn`/`Delta_E4_E6_eq`.
-/

/-- Express `Δ` as `(E₄^3 - E₆^2)/1728` (cast to `ℂ`). -/
public lemma Delta_eq_eisenstein (z : ℍ) :
    (Δ z : ℂ) =
      (1 / 1728 : ℂ) *
        ((E₄ z) ^ (3 : ℕ) - (E₆ z) ^ (2 : ℕ)) := by
  simpa [Delta_apply] using!
    (Delta_apply_eq_one_div_1728_mul_E4_pow_three_sub_E6_sq (z := z))

/--
Cleared numerator for the `varphi` term in `BleadingNum`.

This is the Eisenstein expression appearing in PARI/GP (`appendix.txt`) after clearing `Δ(z)^2`.
-/
@[expose] public def varphi_num (z : ℍ) : ℂ :=
  (25 * (E₄ z) ^ 4 - 49 * (E₆ z) ^ 2 * (E₄ z))
      + 48 * (E₆ z) * (E₄ z) ^ 2 * (E₂ z)
      + ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2) * (E₂ z) ^ 2

/--
Cleared numerator for the `phi1` term in `BleadingNum`.

This includes the external factor `(-6)/pi`.
-/
@[expose] public def phi1_num (z : ℍ) : ℂ :=
  (1 / (Real.pi : ℂ)) *
      (-6) * (48 * (E₆ z) * (E₄ z) ^ 2 + 2 * (E₂ z) * ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2))

/--
Cleared numerator for the `phi2` term in `BleadingNum`.

This includes the external factor `(-36)/pi^2`.
-/
@[expose] public def phi2_num (z : ℍ) : ℂ :=
  (-36) * ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2) / ((Real.pi : ℂ) ^ 2)

/-- Cleared numerator for the `psiI` term in `BleadingNum` (written using theta functions). -/
@[expose] public def psiI_num (z : ℍ) : ℂ :=
  7 * (Θ₄ z) ^ 20 * (Θ₂ z) ^ 8 + 7 * (Θ₄ z) ^ 24 * (Θ₂ z) ^ 4 + 2 * (Θ₄ z) ^ 28

/-- Rewrite `varphi₁` as `I * phi1_num / Δ^2`. -/
public lemma varphi₁_eq_I_mul_phi1_num_div_Delta_sq (z : ℍ) :
    varphi₁ z = Complex.I * phi1_num z / (Δ z) ^ 2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
  simp [Dim24.varphi₁, phi1_num, div_eq_mul_inv, sub_eq_add_neg]
  field_simp [hπ, pow_ne_zero 2 hΔ]
  ring

/-- Rewrite `varphi₂` as `phi2_num / Δ^2`. -/
public lemma varphi₂_eq_phi2_num_div_Delta_sq (z : ℍ) :
    varphi₂ z = phi2_num z / (Δ z) ^ 2 := by
  simp [Dim24.varphi₂, phi2_num, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Rewrite `ψI` as `psiI_num / Δ^2`. -/
public lemma ψI_eq_psiI_num_div_Delta_sq (z : ℍ) :
    ψI z = psiI_num z / (Δ z) ^ 2 := by
  simp [Dim24.ψI, psiI_num, div_eq_mul_inv, mul_left_comm, mul_comm]

/--
Rewrite `BleadingNum` in terms of the cleared numerators `varphi_num`, `phi1_num`, `phi2_num`,
and `psiI_num`.
-/
public lemma BleadingNum_eq_num_expr (t : ℝ) (ht0 : 0 < t) :
    BleadingNum t ht0 =
      ((Real.pi : ℂ) / (28304640 : ℂ)) *
            ((t : ℂ) ^ (2 : ℕ) * varphi_num (it t ht0) + (t : ℂ) * phi1_num (it t ht0) -
              phi2_num (it t ht0))
        + (1 / ((65520 : ℂ) * Real.pi)) * psiI_num (it t ht0)
        - (BleadingLeadingTerm t : ℂ) * (Δ (it t ht0)) ^ (2 : ℕ) := by
  have hBK :
      BKernel t ht0 =
        ((Real.pi : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (2 : ℕ) *
            (varphi (it t ht0) + varphi₁ (it t ht0) / (it t ht0) +
              varphi₂ (it t ht0) / ((it t ht0 : ℍ) : ℂ) ^ 2)
          + (1 / ((65520 : ℂ) * Real.pi)) * ψI (it t ht0) := by
    simpa using! (BKernel_eq (t := t) ht0)
  set z : ℍ := it t ht0 with hzdef
  have hzc : (z : ℂ) = Complex.I * (t : ℂ) := by
    -- `↑(it t ht0) = I * t`.
    simp [hzdef, it]
  have htne : (t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht0)
  have hz_ne : (z : ℂ) ≠ 0 := by
    simpa [hzc] using! (mul_ne_zero Complex.I_ne_zero htne)
  have hΔne : (Δ z : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (Δ_ne_zero z)
  have hIdiv : (Complex.I : ℂ) / (z : ℂ) = (1 : ℂ) / (t : ℂ) := by
    -- `I / (I*t) = 1/t`.
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    calc
      (Complex.I : ℂ) / (z : ℂ) = (Complex.I : ℂ) / (Complex.I * (t : ℂ)) := by simp [hzc]
      _ = (1 : ℂ) / (t : ℂ) := by
            field_simp [hI, htne]
  have hz2 : (z : ℂ) ^ (2 : ℕ) = -((t : ℂ) ^ (2 : ℕ)) := by
    simp [hzc, pow_two]
    ring_nf
    simp [Complex.I_sq]
  simp only [BleadingNum, hBK, z, sub_eq_add_neg, mul_add, add_mul, mul_assoc, add_assoc,
    add_left_comm, add_comm, one_div, mul_inv_rev]
  have hvarphi : varphi z * (Δ z) ^ (2 : ℕ) = varphi_num z := by
    simp [Dim24.varphi, varphi_num, div_eq_mul_inv, hΔne, mul_assoc, mul_left_comm, mul_comm]
  have hphi1 : varphi₁ z * (Δ z) ^ (2 : ℕ) = Complex.I * phi1_num z := by
    simp [varphi₁_eq_I_mul_phi1_num_div_Delta_sq, div_eq_mul_inv, hΔne]
  have hphi2 : varphi₂ z * (Δ z) ^ (2 : ℕ) = phi2_num z := by
    simp [varphi₂_eq_phi2_num_div_Delta_sq, div_eq_mul_inv, hΔne]
  have hpsi : ψI z * (Δ z) ^ (2 : ℕ) = psiI_num z := by
    simp [ψI_eq_psiI_num_div_Delta_sq, div_eq_mul_inv, hΔne]
  grind only


end SpherePacking.Dim24.AppendixA
