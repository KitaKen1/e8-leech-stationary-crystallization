/-
Laplace/contour identities used to prove the Leech-radius zeros of the +1 eigenfunction `a`.

This file is imported by `A/Zeros.lean`.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Defs


/-!
# The segment identity for `I₁' + I₃' + I₅'`

This is the dimension-24 analogue of the corresponding lemma in the dimension-8 development
(`MagicFunction.g.CohnElkies.LaplaceA`).

## Main statement
* `LaplaceZeros.I₁'_add_I₃'_add_I₅'_eq_imag_axis`
-/


namespace SpherePacking.Dim24

noncomputable section

open MagicFunction.Parametrisations
open RealIntegrals RealIntegrals.ComplexIntegrands
open scoped Interval

namespace LaplaceZeros


lemma Φ₁'_shift_left (u t : ℝ) :
    Φ₁' u ((-1 : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (-((Real.pi * u : ℝ) : ℂ) * Complex.I) * Φ₅' u ((t : ℂ) * Complex.I) := by
  simp [Φ₁', Φ₅', mul_add, add_assoc, mul_assoc, mul_left_comm, mul_comm,
    div_eq_mul_inv, Complex.exp_add]

lemma Φ₃'_shift_right (u t : ℝ) :
    Φ₃' u ((1 : ℂ) + (t : ℂ) * Complex.I) =
      Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * Φ₅' u ((t : ℂ) * Complex.I) := by
  simp [Φ₃', Φ₅', mul_add, mul_assoc, mul_left_comm, mul_comm,
    div_eq_mul_inv, Complex.exp_add]

/-- Express `I₁' u + I₃' u + I₅' u` as a scalar multiple of the imaginary-axis segment integral. -/
public lemma I₁'_add_I₃'_add_I₅'_eq_imag_axis (u : ℝ) :
    RealIntegrals.I₁' u + RealIntegrals.I₃' u + RealIntegrals.I₅' u =
      (Complex.I : ℂ) *
        ((Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
      (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I))) := by
  let V0 : ℂ := ∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)
  have hV0 : V0 = ∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I) := rfl
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have htIcc {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) 1) : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le h01] using! ht
  have hI1 :
      RealIntegrals.I₁' u =
        (Complex.I : ℂ) * Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * V0 := by
    have hparam :
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₁' u (z₁' t)) =
            ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₁' u ((-1 : ℂ) + (t : ℂ) * Complex.I) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := htIcc ht
      simp [z₁'_eq_of_mem (t := t) ht', mul_comm]
    have hshift :
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₁' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
          (Complex.I : ℂ) * Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) *
            (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) := by
      calc
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₁' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
            ∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) *
                (Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) *
                  Φ₅' u ((t : ℂ) * Complex.I)) := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              simp [Φ₁'_shift_left (u := u) (t := t), mul_assoc]
        _ =
            (Complex.I : ℂ) * Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) *
              (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) := by
              simp [mul_assoc]
    simpa [RealIntegrals.I₁', RealIntegrands.Φ₁, hV0, mul_assoc] using! (hparam.trans hshift)
  have hI3 :
      RealIntegrals.I₃' u =
        (Complex.I : ℂ) * Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * V0 := by
    have hparam :
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₃' u (z₃' t)) =
            ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₃' u ((1 : ℂ) + (t : ℂ) * Complex.I) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := htIcc ht
      simp [z₃'_eq_of_mem (t := t) ht', mul_comm]
    have hshift :
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₃' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
          (Complex.I : ℂ) * Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) *
            (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) := by
      calc
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₃' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
            ∫ t in (0 : ℝ)..1,
              (Complex.I : ℂ) *
                (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) *
                  Φ₅' u ((t : ℂ) * Complex.I)) := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              simp [Φ₃'_shift_right (u := u) (t := t), mul_assoc]
        _ =
            (Complex.I : ℂ) * Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) *
              (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) := by
              simp [mul_assoc]
    simpa [RealIntegrals.I₃', RealIntegrands.Φ₃, hV0, mul_assoc] using! (hparam.trans hshift)
  have hI5 : RealIntegrals.I₅' u = (-2 : ℂ) * (Complex.I : ℂ) * V0 := by
    have hparam :
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₅' u (z₅' t)) =
            ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₅' u ((t : ℂ) * Complex.I) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := htIcc ht
      simp [z₅'_eq_of_mem (t := t) ht', mul_comm]
    have :
        RealIntegrals.I₅' u =
          (-2 : ℂ) * ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₅' u ((t : ℂ) * Complex.I) := by
      simp [RealIntegrals.I₅', RealIntegrands.Φ₅, hparam]
    calc
      RealIntegrals.I₅' u =
          (-2 : ℂ) * ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₅' u ((t : ℂ) * Complex.I) := this
      _ = (-2 : ℂ) * ((Complex.I : ℂ) * V0) := by
          simp [hV0, intervalIntegral.integral_const_mul]
      _ = (-2 : ℂ) * (Complex.I : ℂ) * V0 := by ring_nf
  grind only

end LaplaceZeros
end

end SpherePacking.Dim24
