/-
Change-of-variables setup for the `I₅/I₆` permutation.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12ContourDeformation

/-!
# Change of variables for the `I₅/I₆` permutation

We follow the change-of-variables strategy from the dimension-8 development:
rewrite `RealIntegrals.I₅'` as an `Ici 1` integral with the reciprocal map `t ↦ 1/t`, then swap
integrals and evaluate the inner Gaussian Fourier transform.

## Main definition
* `PermI56.g`

## Main statement
* `PermI56.complete_change_of_variables`
-/

open Complex Real

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.AFourier
open MeasureTheory Set Complex Real Filter
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold

noncomputable section

namespace PermI56

open Complex Real Set MeasureTheory Filter intervalIntegral
open scoped Interval
open MagicFunction.Parametrisations

def f : ℝ → ℝ := fun t ↦ 1 / t

def f' : ℝ → ℝ := fun t ↦ -1 / t ^ (2 : ℕ)

/--
The auxiliary integrand on `s ≥ 1` obtained from `I₅'` after the change of variables `t ↦ 1/t`.
-/
@[expose] public def g : ℝ → ℝ → ℂ := fun r s ↦ (-I : ℂ) * varphi' (I * (s : ℂ)) * (s ^ (-12 : ℤ)) *
  cexp ((-π : ℂ) * (r : ℂ) / (s : ℂ))

lemma I₅'_eq_Ioc (r : ℝ) :
    RealIntegrals.I₅' r = (-2 : ℂ) * ∫ t in Ioc (0 : ℝ) 1, RealIntegrals.RealIntegrands.Φ₅ r t := by
  -- `intervalIntegral` is defined via the set integral over `uIoc`.
  simp [RealIntegrals.I₅', intervalIntegral_eq_integral_uIoc]

lemma changing_domain (r : ℝ) :
    ∫ s in Ici (1 : ℝ), g r s = ∫ s in f '' (Ioc (0 : ℝ) (1 : ℝ)), g r s := by
  congr
  ext x
  constructor <;> intro hx
  · refine ⟨x⁻¹, ?_, ?_⟩
    · simp only [mem_Ici] at hx ⊢
      have hx1 : (1 : ℝ) ≤ x := hx
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      refine ⟨by positivity, (inv_le_one₀ hx0).2 hx1⟩
    · rw [f, div_inv_eq_mul, one_mul]
  · obtain ⟨y, hy₁, hy₂⟩ := hx
    rw [← hy₂, f]
    simp only [one_div, mem_Ici]
    exact one_le_inv_iff₀.mpr hy₁

lemma changing_variables (r : ℝ) :
    ∫ (s : ℝ) in f '' (Ioc (0 : ℝ) (1 : ℝ)), g r s =
      ∫ (t : ℝ) in Ioc (0 : ℝ) (1 : ℝ), |f' t| • g r (f t) :=
  integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
    (fun x hx => by
      have hx0 : x ≠ 0 := ne_of_gt hx.1
      change HasDerivWithinAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) (Ioc 0 1) x
      simpa [one_div, div_eq_mul_inv, mul_assoc] using!
        (hasDerivWithinAt_inv (x := x) hx0 (Ioc 0 1)))
    (by
      change InjOn (fun t : ℝ => 1 / t) (Ioc (0 : ℝ) (1 : ℝ))
      intro x _ y _ hf
      simpa [one_div] using! (inv_inj.mp (by simpa [one_div] using! hf)))
    (g r)

lemma writing_as_intervalIntegral (r : ℝ) :
    ∫ (t : ℝ) in Ioc (0 : ℝ) (1 : ℝ), |f' t| • g r (f t) =
      ∫ t in (0 : ℝ)..1, |f' t| • g r (f t) := by
  simp [intervalIntegral_eq_integral_uIoc]

lemma core_identity (A T V : ℂ)
    (hcexp : cexp (I * (I * A)) = cexp (-A))
    (hI11 : (I : ℂ) ^ 11 = -I)
    (hpow : T ^ (12 : ℕ) * (T ^ (2 : ℕ))⁻¹ = T ^ (10 : ℕ)) :
    I * (cexp (I * (I * A)) * (I ^ (10 : ℕ) * (T ^ (10 : ℕ) * V))) =
      -(I * (cexp (-A) * (T ^ (12 : ℕ) * ((T ^ (2 : ℕ))⁻¹ * V)))) := by
  grind only

lemma reconciling_change_of_variables (r : ℝ) :
    RealIntegrals.I₅' r = (-2 : ℂ) * ∫ t in Ioc (0 : ℝ) (1 : ℝ), |f' t| • g r (f t) := by
  simp only [I₅'_eq_Ioc, f, f', g, mul_assoc]
  congr 1
  refine setIntegral_congr_ae₀ nullMeasurableSet_Ioc ?_
  refine ae_of_all _ ?_
  intro t ht
  have ht0 : 0 < t := ht.1
  have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht0)
  have habst : (|t| : ℝ) = t := abs_of_pos ht0
  have hz : z₅' t = (I : ℂ) * (t : ℂ) := by
    have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
    simpa using! (z₅'_eq_of_mem (t := t) htIcc)
  have habs : |(-1 / t ^ (2 : ℕ))| = (1 / t ^ (2 : ℕ)) := by
    rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]
  have harg : (-1 / (z₅' t) : ℂ) = (I : ℂ) / (t : ℂ) := by
    -- `-1 / (I * t) = I / t`.
    rw [hz]
    field_simp [ht0', Complex.I_ne_zero]
    simp
  have hI11 : (Complex.I : ℂ) ^ 11 = -Complex.I := by
    calc
      (Complex.I : ℂ) ^ 11 = (Complex.I : ℂ) ^ (11 % 4) := by
        simpa using! (Complex.I_pow_eq_pow_mod 11)
      _ = (Complex.I : ℂ) ^ 3 := by norm_num
      _ = -Complex.I := by simp
  have hpow :
      ((t : ℂ)⁻¹) ^ (2 : ℕ) * (t : ℂ) ^ (12 : ℕ) = (t : ℂ) ^ (10 : ℕ) := by
    grind only
  -- Now unfold `Φ₅` and the transformed kernel, using `z₅' t = I*t` and `-1/(z₅' t) = I/t`.
  -- The resulting equality is a straightforward algebraic simplification.
  have h1tC : ((1 / t : ℝ) : ℂ) = (t : ℂ)⁻¹ := by
    simp [div_eq_mul_inv]
  have hdiv_inv :
      (-((Real.pi : ℂ) * (r : ℂ))) / ((1 / t : ℝ) : ℂ) =
        (-((Real.pi : ℂ) * (r : ℂ))) * (t : ℂ) := by
    simp [div_eq_mul_inv, mul_assoc]
  -- Unfold both sides and reduce to commutative products.
  simp only [RealIntegrals.RealIntegrands.Φ₅, RealIntegrals.ComplexIntegrands.Φ₅', hz,
    div_eq_mul_inv,
    mul_inv_rev, inv_I, mul_neg, mul_comm, mul_one, neg_neg, mul_pow, mul_assoc, mul_left_comm,
    abs_neg, abs_inv, abs_pow, habst, ofReal_inv, Int.reduceNeg, zpow_neg, inv_zpow', inv_inv,
    neg_mul, smul_neg, real_smul, ofReal_pow]
  -- Remaining algebraic identity.
  have hcexp :
      cexp (I * (I * (↑r * (↑t * ↑π)))) = cexp (-(↑r * (↑t * ↑π))) := by
    have hmul :
        (I : ℂ) * (I * (↑r * (↑t * ↑π))) = -(↑r * (↑t * ↑π)) := by
      calc
        (I : ℂ) * (I * (↑r * (↑t * ↑π))) =
            ((I : ℂ) * I) * (↑r * (↑t * ↑π)) := by
              simpa using! (mul_assoc (I : ℂ) I (↑r * (↑t * ↑π))).symm
        _ = (-1 : ℂ) * (↑r * (↑t * ↑π)) := by simp
        _ = -(↑r * (↑t * ↑π)) := by simp
    simp [hmul]
  have hinvpow : ((t : ℂ)⁻¹) ^ (2 : ℕ) = ((t : ℂ) ^ (2 : ℕ))⁻¹ := by simp
  have hpow2 : (t : ℂ) ^ (12 : ℕ) * ((t : ℂ) ^ (2 : ℕ))⁻¹ = (t : ℂ) ^ (10 : ℕ) := by
    grind only
  -- Close the goal using the isolated identity.
  simpa using!
    (core_identity (A := (↑r * (↑t * ↑π))) (T := (t : ℂ)) (V := varphi' (I * ((t : ℂ)⁻¹)))
      (hcexp := by simpa using! hcexp) (hI11 := hI11) (hpow := hpow2))

/-- Rewrite `I₅'` as an integral over `s ∈ Ici 1` using the reciprocal change of variables. -/
public theorem complete_change_of_variables (r : ℝ) :
    RealIntegrals.I₅' r = (-2 : ℂ) * ∫ s in Ici (1 : ℝ), g r s := by
  rw [reconciling_change_of_variables, ← changing_variables, ← changing_domain]

end PermI56

end

end SpherePacking.Dim24.AFourier
