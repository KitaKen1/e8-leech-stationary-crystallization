/-
Setup for the `I₁+I₂` permutation argument (definitions, Mobius map).
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.GaussianFourier
public import SpherePacking.Contour.MobiusInv.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import SpherePacking.ForMathlib.ScalarOneForm


/-!
# Setup for the `I₁/I₂` permutation argument

This is the dim-24 analogue of the dim-8 `a`-eigenfunction contour/Fubini proof.
We reduce to a contour identity for the curve integrals, obtained by substituting
`mobiusInv : z ↦ -1/z` and deforming inside a convex wedge domain.

## Main definitions
* `Φ₁'`, `Φ₃'`
* `Φ₁_fourier`

## Main statement
* `Φ₁_fourier_eq_deriv_mul`
-/

open Complex Real

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.AFourier
open MeasureTheory Set Complex Real Filter
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold

noncomputable section

open MagicFunction.Parametrisations
open scoped Interval

lemma varphi'_add_one (z : ℂ) : varphi' (z + 1) = varphi' z := by
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa using! hz
    let zH : ℍ := ⟨z, hz⟩
    have hzH' : (⟨z + 1, hz'⟩ : ℍ) = (1 : ℝ) +ᵥ zH := by
      ext1
      -- `↑((1 : ℝ) +ᵥ zH) = (1 : ℂ) + z`, so this is just commutativity of addition in `ℂ`.
      simpa [zH, UpperHalfPlane.coe_vadd] using! (add_comm (z : ℂ) (1 : ℂ))
    have hper : varphi ⟨z + 1, hz'⟩ = varphi zH := by
      simpa [hzH'] using! (Dim24.varphi_periodic (z := zH))
    simp [varphi', hz, hper, zH]
  · have hz' : ¬ 0 < (z + 1).im := by simpa using! hz
    simp [varphi', hz]

/-- The upper half-plane integrand `Φ₁'` for the curve-integral representation of `I₁'`. -/
@[expose] public def Φ₁' (r : ℝ) (z : ℂ) : ℂ :=
  varphi' (-1 / (z + 1)) * (z + 1) ^ (10 : ℕ) * cexp ((π : ℂ) * I * (r : ℂ) * z)

/-- The upper half-plane integrand `Φ₃'` for the curve-integral representation of `I₃'`. -/
@[expose] public def Φ₃' (r : ℝ) (z : ℂ) : ℂ :=
  varphi' (-1 / (z - 1)) * (z - 1) ^ (10 : ℕ) * cexp ((π : ℂ) * I * (r : ℂ) * z)

/--
A Fourier-modified version of `Φ₁'` that appears after evaluating the inner Gaussian integral.
-/
@[expose] public def Φ₁_fourier (r : ℝ) (z : ℂ) : ℂ :=
  varphi' (-1 / (z + 1)) * (z + 1) ^ (10 : ℕ) *
    (((I : ℂ) / z) ^ (12 : ℕ)) * cexp ((π : ℂ) * I * (r : ℂ) * (-1 / z))

/-- Transformation rule for `Φ₁_fourier` under the Mobius inversion `mobiusInv : z ↦ -1/z`. -/
public lemma Φ₁_fourier_eq_deriv_mul (r : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Φ₁_fourier r z = (deriv mobiusInv z) * Φ₃' r (mobiusInv z) := by
  have hz0 : z ≠ 0 := by
    intro hz0
    have : z.im = 0 := by simp [hz0]
    exact (lt_irrefl (0 : ℝ)) (this ▸ hz)
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have : (z + 1).im = 0 := by simpa using! congrArg Complex.im h
    have : z.im = 0 := by simpa using! this
    exact (lt_irrefl (0 : ℝ)) (this ▸ hz)
  have hderiv : deriv mobiusInv z = (1 : ℂ) / z ^ (2 : ℕ) := deriv_mobiusInv (z := z)
  have hsub : mobiusInv z - 1 = -(z + 1) / z := mobiusInv_sub_one (z := z) hz0
  have harg1 :
      (-1 : ℂ) / (mobiusInv z - 1) = z / (z + 1) := by
    calc
      (-1 : ℂ) / (mobiusInv z - 1) = (-1 : ℂ) * (mobiusInv z - 1)⁻¹ := by
        simp [div_eq_mul_inv]
      _ = (-1 : ℂ) * (-(z + 1) / z)⁻¹ := by simp [hsub]
      _ = (-1 : ℂ) * (z / (-(z + 1))) := by simp [inv_div]
      _ = z / (z + 1) := by
        field_simp [hz1]
  have harg2 : (-1 : ℂ) / (z + 1) + 1 = z / (z + 1) := by
    field_simp [hz1]
    ring_nf
  have harg : (-1 : ℂ) / (mobiusInv z - 1) = (-1 : ℂ) / (z + 1) + 1 :=
    harg1.trans harg2.symm
  have hvarphi :
      varphi' ((-1 : ℂ) / (mobiusInv z - 1)) = varphi' ((-1 : ℂ) / (z + 1)) := by
    -- Use `1`-periodicity of `varphi'`.
    simpa [harg] using! (varphi'_add_one (z := ((-1 : ℂ) / (z + 1))))
  have hpow :
      (mobiusInv z - 1) ^ (10 : ℕ) = (z + 1) ^ (10 : ℕ) / z ^ (10 : ℕ) := by
    -- Rewrite the `S`-substitution algebraically, using that `10` is even.
    rw [hsub]
    ring
  have hI : ((I : ℂ) / z) ^ (12 : ℕ) = (1 : ℂ) / z ^ (12 : ℕ) := by
    -- `I^12 = 1`.
    have hI12 : (I : ℂ) ^ (12 : ℕ) = 1 := by
      rw [show (12 : ℕ) = 4 * 3 by decide]
      rw [pow_mul]
      simp [Complex.I_pow_four]
    calc
      ((I : ℂ) / z) ^ (12 : ℕ) = (I : ℂ) ^ (12 : ℕ) / z ^ (12 : ℕ) := by
        simpa using! (div_pow (I : ℂ) z (12 : ℕ))
      _ = (1 : ℂ) / z ^ (12 : ℕ) := by simp [hI12]
  have hexp :
      cexp ((π : ℂ) * I * (r : ℂ) * (mobiusInv z)) =
        cexp ((π : ℂ) * I * (r : ℂ) * (-1 / z)) := by
    simp [mobiusInv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hz2 : (z ^ (2 : ℕ) : ℂ) ≠ 0 := pow_ne_zero 2 hz0
  have hz10 : (z ^ (10 : ℕ) : ℂ) ≠ 0 := pow_ne_zero 10 hz0
  have hz12 : (z ^ (12 : ℕ) : ℂ) ≠ 0 := pow_ne_zero 12 hz0
  have hfac :
      varphi' (-1 / (z + 1)) * (z + 1) ^ (10 : ℕ) * (((I : ℂ) / z) ^ (12 : ℕ)) =
        (deriv mobiusInv z) *
          (varphi' (-1 / (mobiusInv z - 1)) * (mobiusInv z - 1) ^ (10 : ℕ)) := by
    -- Substitute the periodicity identity and the `S`-transform algebra for the powers of `z`.
    -- This is the weight `10` factor together with `deriv mobiusInv z = 1 / z^2` giving `z^12`.
    -- (Compare `SpherePacking/Dim24/MagicFunction/B/Eigen.lean`, `Ψ₁_fourier_eq_neg_deriv_mul`.)
    rw [hI, hderiv]
    rw [hvarphi, hpow]
    field_simp [hz2, hz10, hz12]
  calc
    Φ₁_fourier r z =
        (varphi' (-1 / (z + 1)) * (z + 1) ^ (10 : ℕ) * (((I : ℂ) / z) ^ (12 : ℕ))) *
          cexp ((π : ℂ) * I * (r : ℂ) * (-1 / z)) := by
            simp [Φ₁_fourier, mul_assoc, mul_left_comm, mul_comm]
    _ =
        ((deriv mobiusInv z) *
            (varphi' (-1 / (mobiusInv z - 1)) * (mobiusInv z - 1) ^ (10 : ℕ))) *
          cexp ((π : ℂ) * I * (r : ℂ) * (-1 / z)) := by
            simp [hfac]
    _ =
        (deriv mobiusInv z) *
          ((varphi' (-1 / (mobiusInv z - 1)) * (mobiusInv z - 1) ^ (10 : ℕ)) *
            cexp ((π : ℂ) * I * (r : ℂ) * (-1 / z))) := by
            ac_rfl
    _ =
        (deriv mobiusInv z) *
          ((varphi' (-1 / (mobiusInv z - 1)) * (mobiusInv z - 1) ^ (10 : ℕ)) *
            cexp ((π : ℂ) * I * (r : ℂ) * (mobiusInv z))) := by
            simp [hexp]
    _ = (deriv mobiusInv z) * Φ₃' r (mobiusInv z) := by
            simp [Φ₃', mul_assoc, mul_left_comm, mul_comm]


end

end SpherePacking.Dim24.AFourier
