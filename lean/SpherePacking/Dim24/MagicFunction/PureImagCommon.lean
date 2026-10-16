-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.ModularForms.Delta.ImagAxis
public import SpherePacking.MagicFunction.IntegralParametrisations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


/-!
# Pure imaginary axis conjugation helpers

This file collects conjugation identities and an involution `negConjH` of the upper half-plane.
These lemmas are shared by the "pure imaginary axis" arguments in `MagicFunction/A` and
`MagicFunction/B`.

## Main definitions
* `negConjH`

## Main statements
* `z₃'_eq_neg_conj_z₁'`
* `z₄'_eq_neg_conj_z₂'`
* `conj_intervalIntegral`
* `conj_Δ`
-/

open scoped ComplexConjugate Interval UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

open MagicFunction.Parametrisations

/-- Conjugation relation between the contour parametrisations `z₃'` and `z₁'`. -/
public lemma z₃'_eq_neg_conj_z₁' (t : ℝ) : z₃' t = -conj (z₁' t) := by
  simp [z₁', z₃', z₁, z₃, Set.IccExtend, map_add, map_mul, add_comm]

/-- Conjugation relation between the contour parametrisations `z₄'` and `z₂'`. -/
public lemma z₄'_eq_neg_conj_z₂' (t : ℝ) : z₄' t = -conj (z₂' t) := by
  simp [z₂', z₄', z₂, z₄, Set.IccExtend, sub_eq_add_neg, add_comm]

/-- The parametrisation `z₅' t` is purely imaginary: it equals `-conj (z₅' t)`. -/
public lemma z₅'_eq_neg_conj (t : ℝ) : z₅' t = -conj (z₅' t) := by
  simp [z₅', z₅, Set.IccExtend]

/-- The parametrisation `z₆' t` is purely imaginary: it equals `-conj (z₆' t)`. -/
public lemma z₆'_eq_neg_conj (t : ℝ) : z₆' t = -conj (z₆' t) := by
  simp [z₆', z₆, Set.IciExtend]

/-- Complex conjugation commutes with interval integrals. -/
public lemma conj_intervalIntegral {f : ℝ → ℂ} {a b : ℝ} :
    conj (∫ t in a..b, f t) = ∫ t in a..b, conj (f t) := by
  simp [intervalIntegral, integral_conj, map_sub]

/-- The involution of `ℍ` given by `z ↦ -conj z`. -/
@[expose]
public def negConjH (z : ℍ) : ℍ :=
  ⟨-conj (z : ℂ), by
    -- `(-conj z).im = z.im`.
    simpa [Complex.conj_im] using! z.2⟩

/-- Coercion to `ℂ` for `negConjH`. -/
public lemma negConjH_coe (z : ℍ) : (negConjH z : ℂ) = -conj (z : ℂ) := rfl

/-- Conjugation fixes the real number `2`. -/
public lemma conj_two : conj (2 : ℂ) = (2 : ℂ) := by
  simpa using! (Complex.conj_natCast 2)

/-- `starRingEnd` acts trivially on natural-number casts into `ℂ`. -/
@[simp] public lemma starRingEnd_natCast (n : ℕ) : (starRingEnd ℂ) (n : ℂ) = (n : ℂ) := by simp

/-- `starRingEnd` acts trivially on integer casts into `ℂ`. -/
@[simp] public lemma starRingEnd_intCast (n : ℤ) : (starRingEnd ℂ) (n : ℂ) = (n : ℂ) := by simp

/-- If `x` has vanishing imaginary part, then `conj x = x`. -/
public lemma conj_eq_of_im_eq_zero {x : ℂ} (hx : x.im = 0) : conj x = x :=
  (Complex.conj_eq_iff_im (z := x)).2 hx

/-- Conjugation commutes with the complex exponential `cexp`. -/
public lemma conj_cexp (x : ℂ) : conj (Complex.exp x) = Complex.exp (conj x) :=
  (Complex.exp_conj (x := x)).symm

/-- Conjugation commutes with infinite products indexed by `ℕ`. -/
public lemma conj_tprod_nat (f : ℕ → ℂ) : conj (∏' n : ℕ, f n) = ∏' n : ℕ, conj (f n) := by
  -- `Function.LeftInverse.map_tprod` handles both the multipliable and non-multipliable cases.
  simpa using!
    (Function.LeftInverse.map_tprod (f := f) (g := (starRingEnd ℂ))
      (hg := Complex.continuous_conj) (hg' := Complex.continuous_conj)
      (hgg' := starRingEnd_self_apply (R := ℂ)))

/-- Conjugation relation for the modular discriminant `Δ` on the upper half-plane. -/
public lemma conj_Δ (z : ℍ) : conj (Δ z) = Δ (negConjH z) := by
  -- Unfold the product formula for `Δ` and push conjugation through `cexp` and `∏'`.
  have hArg0 :
      conj (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I * (negConjH z : ℂ) := by
    simp [negConjH_coe, conj_two, mul_assoc, mul_left_comm, mul_comm]
  have hArg (n : ℕ) :
      conj (2 * (Real.pi : ℂ) * Complex.I * (n + 1) * (z : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I * (n + 1) * (negConjH z : ℂ) := by
    simp [negConjH_coe, conj_two, mul_assoc, mul_left_comm, mul_comm]
  have hmul (n : ℕ) :
      conj ((1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n + 1) * (z : ℂ))) ^ 24) =
        (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n + 1) * (negConjH z : ℂ))) ^ 24 := by
    simp [conj_cexp, hArg n, map_sub]
  -- Assemble.
  simp [Δ, conj_cexp, conj_tprod_nat, hArg0, hmul, map_mul, negConjH_coe]

end

end SpherePacking.Dim24
