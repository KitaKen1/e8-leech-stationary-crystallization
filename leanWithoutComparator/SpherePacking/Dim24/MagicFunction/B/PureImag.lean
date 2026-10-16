-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
import SpherePacking.Dim24.MagicFunction.PureImagCommon
import SpherePacking.Dim24.ModularForms.Psi.Relations


/-!
# Pure-imaginary valuedness of `b`

This file proves a conjugation identity for `bProfile`, showing `conj (bProfile u) = -bProfile u`.
As a consequence, the dim-24 magic function `b` takes values in `iℝ` (equivalently, has real part
`0`).

## Main statements
* `b_mapsTo_pureImag`
-/

open Complex
open MeasureTheory
open scoped ComplexConjugate

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

open UpperHalfPlane
open MagicFunction.Parametrisations

lemma conj_four : conj (4 : ℂ) = (4 : ℂ) := by
  simpa using! (Complex.conj_natCast 4)

lemma conj_seven : conj (7 : ℂ) = (7 : ℂ) := by
  simpa using! (Complex.conj_natCast 7)

lemma conj_Θ₄ (z : ℍ) : conj (Θ₄ z) = Θ₄ (negConjH z) := by
  -- `Θ₄` is a specialization of `jacobiTheta₂` which has a clean conjugation lemma.
  simp [Θ₄_as_jacobiTheta₂, negConjH_coe, jacobiTheta₂_conj, conj_two]

lemma conj_Θ₂ (z : ℍ) : conj (Θ₂ z) = Θ₂ (negConjH z) := by
  -- Reduce to the conjugation lemma for `jacobiTheta₂` and the exponential conjugation lemma.
  simp [Θ₂_as_jacobiTheta₂, negConjH_coe, jacobiTheta₂_conj, jacobiTheta₂_neg_left, conj_cexp,
    conj_two, conj_four, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]

lemma conj_ψI (z : ℍ) : conj (ψI z) = ψI (negConjH z) := by
  simp [ψI, conj_Θ₂, conj_Θ₄, conj_Δ, conj_two, conj_seven]

lemma conj_ψT (z : ℍ) : conj (ψT z) = ψT (negConjH z) := by
  -- `ψT z = ψI(z+1)`; conjugation shifts by `-1`, and we use 2-periodicity of `ψI`.
  have hT : ψT z = ψI ((1 : ℝ) +ᵥ z) := by
    simp [ψT, modular_slash_T_apply]
  have hT' : ψT (negConjH z) = ψI ((1 : ℝ) +ᵥ negConjH z) := by
    simp [ψT, modular_slash_T_apply]
  have hneg : negConjH ((1 : ℝ) +ᵥ z) = (-1 : ℝ) +ᵥ negConjH z := by
    ext
    simp [negConjH, add_comm]
  -- Turn `-1` into `+1` via 2-periodicity of `ψI`.
  have hshift :
      ψI ((-1 : ℝ) +ᵥ negConjH z) = ψI ((1 : ℝ) +ᵥ negConjH z) := by
    -- Add `2` and rewrite `2 +ᵥ (-1 +ᵥ w)` as `1 +ᵥ w`.
    have hper := SpherePacking.Dim24.ψI_periodic_two (z := ((-1 : ℝ) +ᵥ negConjH z))
    simp_all
  calc
    conj (ψT z) = conj (ψI ((1 : ℝ) +ᵥ z)) := by simp [hT]
    _ = ψI (negConjH ((1 : ℝ) +ᵥ z)) := by simp [conj_ψI]
    _ = ψI ((-1 : ℝ) +ᵥ negConjH z) := by simp [hneg]
    _ = ψI ((1 : ℝ) +ᵥ negConjH z) := hshift
    _ = ψT (negConjH z) := by simp [hT']

lemma conj_ψS (z : ℍ) : conj (ψS z) = ψS (negConjH z) := by
  -- Work with the explicit formula coming from `modular_slash_S_apply`.
  have hzSpos : 0 < (-(z : ℂ)⁻¹).im := by
    simpa [inv_neg] using! z.im_inv_neg_coe_pos
  set zS : ℍ := UpperHalfPlane.mk (-(z : ℂ)⁻¹) hzSpos
  have hzSpos' : 0 < (-(negConjH z : ℂ)⁻¹).im := by
    simpa [inv_neg] using! (negConjH z).im_inv_neg_coe_pos
  set zS' : ℍ := UpperHalfPlane.mk (-(negConjH z : ℂ)⁻¹) hzSpos'
  have hS : ψS z = ψI zS * (z : ℂ) ^ (10 : ℤ) := by
    have h := modular_slash_S_apply (f := ψI) (k := (-10 : ℤ)) (z := z)
    have h0 :
        ψS z =
          ψI (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) * (z : ℂ) ^ (10 : ℤ) := by
      simpa [ψS, neg_neg] using! h
    have hmk : ψI (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) = ψI zS := by
      have : UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos = zS := by
        ext
        simp [zS, inv_neg]
      exact congrArg ψI this
    calc
      ψS z = ψI (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) * (z : ℂ) ^ (10 : ℤ) := h0
      _ = ψI zS * (z : ℂ) ^ (10 : ℤ) := by rw [hmk]
  have hS' : ψS (negConjH z) = ψI zS' * (negConjH z : ℂ) ^ (10 : ℤ) := by
    have h := modular_slash_S_apply (f := ψI) (k := (-10 : ℤ)) (z := negConjH z)
    have h0 :
        ψS (negConjH z) =
          ψI (UpperHalfPlane.mk (-(negConjH z) : ℂ)⁻¹ (negConjH z).im_inv_neg_coe_pos) *
            (negConjH z : ℂ) ^ (10 : ℤ) := by
      simpa [ψS, neg_neg] using! h
    have hmk :
        ψI (UpperHalfPlane.mk (-(negConjH z) : ℂ)⁻¹ (negConjH z).im_inv_neg_coe_pos) = ψI zS' := by
      have : UpperHalfPlane.mk (-(negConjH z) : ℂ)⁻¹ (negConjH z).im_inv_neg_coe_pos = zS' := by
        ext
        simp [zS', inv_neg]
      exact congrArg ψI this
    calc
      ψS (negConjH z) =
          ψI (UpperHalfPlane.mk (-(negConjH z) : ℂ)⁻¹ (negConjH z).im_inv_neg_coe_pos) *
            (negConjH z : ℂ) ^ (10 : ℤ) := h0
      _ = ψI zS' * (negConjH z : ℂ) ^ (10 : ℤ) := by rw [hmk]
  have hpow :
      conj ((z : ℂ) ^ (10 : ℤ)) = ((negConjH z : ℂ) ^ (10 : ℤ)) := by
    have h10even : Even (10 : ℕ) := by decide
    -- Rewrite `zpow` as `pow` since the exponent is nonnegative, then use that `10` is even.
    simp [negConjH_coe, zpow_ofNat, map_pow, h10even.neg_pow]
  have hzSconj : negConjH zS = zS' := by
    ext
    simp [zS, zS', negConjH_coe, inv_neg, map_neg]
  have hpow' : (starRingEnd ℂ) (z : ℂ) ^ 10 = (negConjH z : ℂ) ^ 10 := by
    simpa only [map_pow, zpow_ofNat] using hpow
  -- Now compute conjugation of the right-hand side.
  rw [hS, hS']
  simp [map_mul, conj_ψI, hpow, hpow', hzSconj]

lemma conj_ψI' (z : ℂ) : conj (ψI' z) = ψI' (-(conj z)) := by
  by_cases hz : 0 < z.im
  · simp [ψI', hz, Complex.conj_im, conj_ψI, negConjH]
  · simp [ψI', hz, Complex.conj_im]

lemma conj_ψT' (z : ℂ) : conj (ψT' z) = ψT' (-(conj z)) := by
  by_cases hz : 0 < z.im
  · -- On the upper half-plane, `ψT` is defined and satisfies the `negConj` relation.
    simp [ψT', hz, Complex.conj_im, conj_ψT, negConjH]
  · simp [ψT', hz, Complex.conj_im]

lemma conj_ψS' (z : ℂ) : conj (ψS' z) = ψS' (-(conj z)) := by
  by_cases hz : 0 < z.im
  · simp [ψS', hz, Complex.conj_im, conj_ψS, negConjH]
  · simp [ψS', hz, Complex.conj_im]

lemma conj_J₁' (u : ℝ) : conj (RealIntegrals.J₁' u) = -RealIntegrals.J₃' u := by
  -- Pair the `z₁'` and `z₃'` contour pieces via `z₃' = -conj(z₁')`.
  rw [RealIntegrals.J₁', RealIntegrals.J₃', conj_intervalIntegral]
  -- Put the outer `-` as a negation of the integrand.
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have hz : -(conj (z₁' t)) = z₃' t := by
    simpa using! (z₃'_eq_neg_conj_z₁' (t := t)).symm
  have hz' : conj (z₁' t) = -z₃' t := by
    have h := congrArg (fun w : ℂ => -w) hz
    simpa [neg_neg] using! h
  -- Simplify conjugation and rewrite using `z₃'`.
  -- `ht` is unused but required by `integral_congr`.
  simp [conj_ψT', conj_cexp, hz', map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_assoc, mul_left_comm, mul_comm]

lemma conj_J₂' (u : ℝ) : conj (RealIntegrals.J₂' u) = -RealIntegrals.J₄' u := by
  -- Pair the `z₂'` and `z₄'` contour pieces via `z₄' = -conj(z₂')`.
  rw [RealIntegrals.J₂', RealIntegrals.J₄', conj_intervalIntegral]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have hz : -(conj (z₂' t)) = z₄' t := by
    simpa using! (z₄'_eq_neg_conj_z₂' (t := t)).symm
  have hz' : conj (z₂' t) = -z₄' t := by
    have h := congrArg (fun w : ℂ => -w) hz
    simpa [neg_neg] using! h
  simp [conj_ψT', conj_cexp, hz', map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_assoc, mul_left_comm, mul_comm]

lemma conj_J₅' (u : ℝ) : conj (RealIntegrals.J₅' u) = -RealIntegrals.J₅' u := by
  -- The `z₅'` path is fixed by `z ↦ -conj z`, and the prefactor `I` flips sign under conjugation.
  -- Isolate the contour integral.
  set I :
      ℂ :=
        ∫ t in (0 : ℝ)..1,
          (Complex.I : ℂ) * ψI' (z₅' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₅' t) with hIdef
  have hI : conj I = -I := by
    -- Push conjugation inside and simplify the integrand.
    rw [hIdef, conj_intervalIntegral]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have hz : -(conj (z₅' t)) = z₅' t := by
      simpa using! (z₅'_eq_neg_conj (t := t)).symm
    have hz' : conj (z₅' t) = -z₅' t := by
      have h := congrArg (fun w : ℂ => -w) hz
      simpa [neg_neg] using! h
    simp [conj_ψI', conj_cexp, hz', map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_assoc, mul_left_comm, mul_comm]
  -- Assemble `J₅' = (-2) * I`.
  have hIint :
      conj
          (∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₅' t)) =
        -∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₅' t) := by
    simpa [hIdef] using! hI
  -- Now compute conjugation of the scalar multiple.
  -- (Avoid `simp` re-ordering the integrand inside the integral.)
  rw [RealIntegrals.J₅']
  calc
    conj ((-2 : ℂ) * ∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₅' t))
        =
        conj (-2 : ℂ) * conj (∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₅' t)) := by
          simp [map_mul]
    _ = (-2 : ℂ) * (-(∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₅' t))) := by
          simp [conj_two, hIint]
    _ = -((-2 : ℂ) * ∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₅' t)) := by
          ring

lemma conj_J₆' (u : ℝ) : conj (RealIntegrals.J₆' u) = -RealIntegrals.J₆' u := by
  -- Same for the tail integral on `t ≥ 1`.
  -- Isolate the tail integral.
  set I :
      ℂ :=
        ∫ t in Set.Ici (1 : ℝ),
          (Complex.I : ℂ) * ψS' (z₆' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₆' t) with hIdef
  have hI : conj I = -I := by
    -- Move conjugation inside the set integral.
    have hconj :
        conj I =
          ∫ t in Set.Ici (1 : ℝ),
            conj
              ((Complex.I : ℂ) * ψS' (z₆' t) *
                cexp (Real.pi * Complex.I * (u : ℂ) * z₆' t)) := by
      simpa [hIdef] using!
        (integral_conj
            (μ := (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))))
            (f := fun t : ℝ =>
              (Complex.I : ℂ) * ψS' (z₆' t) *
                cexp (Real.pi * Complex.I * (u : ℂ) * z₆' t))).symm
    -- Show the integrand is negated by conjugation.
    rw [hconj]
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    have hz : -(conj (z₆' t)) = z₆' t := by
      simpa using! (z₆'_eq_neg_conj (t := t)).symm
    have hz' : conj (z₆' t) = -z₆' t := by
      have h := congrArg (fun w : ℂ => -w) hz
      simpa [neg_neg] using! h
    -- `hz` rewrites the `ψS'`-input, `hz'` rewrites the exponential argument.
    simp [conj_ψS', conj_cexp, hz', map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_assoc, mul_left_comm, mul_comm]
  -- Assemble `J₆' = (-2) * I`.
  have hIint :
      conj
          (∫ t in Set.Ici (1 : ℝ),
            (Complex.I : ℂ) * ψS' (z₆' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₆' t)) =
        -∫ t in Set.Ici (1 : ℝ),
            (Complex.I : ℂ) * ψS' (z₆' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₆' t) := by
    simpa [hIdef] using! hI
  rw [RealIntegrals.J₆']
  calc
    conj ((-2 : ℂ) * ∫ t in Set.Ici (1 : ℝ),
            (Complex.I : ℂ) * ψS' (z₆' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₆' t))
        =
        conj (-2 : ℂ) * conj (∫ t in Set.Ici (1 : ℝ),
            (Complex.I : ℂ) * ψS' (z₆' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₆' t)) := by
          simp [map_mul]
    _ =
        (-2 : ℂ) * (-(∫ t in Set.Ici (1 : ℝ),
            (Complex.I : ℂ) * ψS' (z₆' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₆' t))) := by
          simp [conj_two, hIint]
    _ = -((-2 : ℂ) * ∫ t in Set.Ici (1 : ℝ),
            (Complex.I : ℂ) * ψS' (z₆' t) * cexp (Real.pi * Complex.I * (u : ℂ) * z₆' t)) := by
          ring

lemma conj_bProfile (u : ℝ) : conj (bProfile u) = -bProfile u := by
  -- `bProfile` is the sum of the six contour pieces; pair them under conjugation.
  have conj_eq_neg_swap {a b : ℂ} (h : conj a = -b) : conj b = -a := by
    have : a = -conj b := by
      simpa [Complex.conj_conj, map_neg] using! congrArg conj h
    have : -a = conj b := by
      simpa using! congrArg (fun z : ℂ => -z) this
    simpa using! this.symm
  have hJ3 : conj (RealIntegrals.J₃' u) = -RealIntegrals.J₁' u :=
    conj_eq_neg_swap (conj_J₁' (u := u))
  have hJ4 : conj (RealIntegrals.J₄' u) = -RealIntegrals.J₂' u :=
    conj_eq_neg_swap (conj_J₂' (u := u))
  -- Now sum and re-associate.
  unfold bProfile RealIntegrals.b'
  -- Simplify conjugation termwise and finish with commutativity/associativity.
  simp [map_add, conj_J₁' (u := u), conj_J₂' (u := u), hJ3, hJ4, conj_J₅' (u := u),
    conj_J₆' (u := u), add_assoc, add_left_comm, add_comm]

/-- The dim-24 magic function `b` is purely imaginary-valued. -/
public theorem b_mapsTo_pureImag : ∀ x : ℝ²⁴, (b x).re = 0 := by
  intro x
  -- Reduce to the one-variable profile `bProfile`.
  have hb : b x = bProfile (‖x‖ ^ 2) := by
    simp [b]
  -- Use `conj z = -z` to force `re z = 0`.
  have hconj : conj (bProfile (‖x‖ ^ 2)) = -bProfile (‖x‖ ^ 2) :=
    conj_bProfile (u := ‖x‖ ^ 2)
  have hre : (bProfile (‖x‖ ^ 2)).re = 0 := by
    have : (bProfile (‖x‖ ^ 2)).re = -(bProfile (‖x‖ ^ 2)).re := by
      simpa [Complex.conj_re] using! congrArg Complex.re hconj
    linarith
  simp [hb, hre]

end

end SpherePacking.Dim24
