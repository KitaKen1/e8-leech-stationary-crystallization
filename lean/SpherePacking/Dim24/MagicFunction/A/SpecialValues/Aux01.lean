-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Prelude


/-!
# Strip cancellation for `I₆'`

This file introduces auxiliary functions on the horizontal line `im = 1` used in the even-`u`
evaluation of `aProfile`. It rewrites `I₂'` and `I₄'` as period integrals of a single function
`F`, and packages the strip finite-difference integrand `f0`.

## Main definitions
* `SpecialValuesAux.zI`
* `SpecialValuesAux.F`
* `SpecialValuesAux.f0`

## Main statements
* `SpecialValuesAux.I₂'_as_F`, `SpecialValuesAux.I₄'_as_F`
* `SpecialValuesAux.aProfile_even_reduction`
* `SpecialValuesAux.f0_add_one_sub`
-/


open scoped Manifold
open Complex Real

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

open MagicFunction.Parametrisations RealIntegrals intervalIntegral Complex MeasureTheory Set Filter
open UpperHalfPlane
open scoped Topology
open scoped UpperHalfPlane

/-- The point `x + i` on the horizontal line `im = 1`. -/
@[expose] public def zI (x : ℝ) : ℂ := (x : ℂ) + Complex.I

/-- The imaginary part of `zI x` is `1`. -/
@[simp] public lemma zI_im (x : ℝ) : (zI x).im = 1 := by simp [zI]

/-- `zI x` lies in the upper half-plane. -/
public lemma zI_im_pos (x : ℝ) : 0 < (zI x).im := by simp [zI]

/-- The point `zI x` belongs to `UpperHalfPlane.upperHalfPlaneSet`. -/
public lemma zI_mem_upperHalfPlane_set (x : ℝ) : zI x ∈ UpperHalfPlane.upperHalfPlaneSet :=
  zI_im_pos x

/-- An auxiliary integrand used to rewrite `I₂'` and `I₄'` as period integrals. -/
@[expose] public def F (u : ℝ) (z : ℂ) : ℂ :=
  varphi' (-1 / z) * z ^ (10 : ℕ) * expU u z

/-- Shift formula for `expU u` under `z ↦ z - 1`. -/
public lemma expU_sub_one (u : ℝ) (z : ℂ) :
    expU u (z - 1) = expU u z * (expU u 1)⁻¹ := by
  have hne : expU u 1 ≠ 0 := by simp [expU]
  -- `expU u (z - 1) = expU u ((z - 1) + 1) * (expU u 1)⁻¹`.
  simpa [sub_eq_add_neg, add_assoc] using! (expU_add_one_mul_inv (u := u) (z := z - 1) hne)

/-- Rewrite `I₂'` as a horizontal period integral of `F` on the line `im = 1`. -/
public lemma I₂'_as_F (u : ℝ) :
    I₂' u = (expU u 1)⁻¹ * ∫ x in (0 : ℝ)..1, F u (zI x) := by
  rw [I₂']
  -- Rewrite the integrand on the integration interval.
  have hcongr :
      (∫ x in (0 : ℝ)..1, RealIntegrands.Φ₂ u x) =
        ∫ x in (0 : ℝ)..1, (expU u 1)⁻¹ * F u (zI x) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! hx
    have hz2p : z₂' x + 1 = zI x := by
      simp [zI, z₂'_eq_of_mem (t := x) hxIcc, add_comm, add_left_comm]
    have hz2 : z₂' x = zI x - 1 := by
      -- `z₂' x = -1 + x + I = (x + I) - 1`.
      simp [zI, z₂'_eq_of_mem (t := x) hxIcc, sub_eq_add_neg, add_assoc, add_comm]
    -- Convert the exponential shift into a `cexp` identity (kept explicit to avoid normalization
    -- issues).
    have hcexp :
        cexp (Complex.I * (u : ℂ) * ((π : ℂ) * z₂' x)) =
          (cexp (Complex.I * (u : ℂ) * (π : ℂ)))⁻¹ *
            cexp (Complex.I * (u : ℂ) * ((π : ℂ) * zI x)) := by
      -- `z₂' x = zI x - 1`, and `exp( a*(z-1)) = exp(-a) * exp(a*z)`.
      rw [hz2]
      have harg :
          Complex.I * (u : ℂ) * ((π : ℂ) * (zI x - 1)) =
            -(Complex.I * (u : ℂ) * (π : ℂ)) + Complex.I * (u : ℂ) * ((π : ℂ) * zI x) := by
        ring
      calc
        cexp (Complex.I * (u : ℂ) * ((π : ℂ) * (zI x - 1))) =
            cexp (-(Complex.I * (u : ℂ) * (π : ℂ)) + Complex.I * (u : ℂ) * ((π : ℂ) * zI x)) := by
              simp [harg]
        _ =
            cexp (-(Complex.I * (u : ℂ) * (π : ℂ))) *
              cexp (Complex.I * (u : ℂ) * ((π : ℂ) * zI x)) := by
              simpa using!
                (Complex.exp_add (-(Complex.I * (u : ℂ) * (π : ℂ)))
                  (Complex.I * (u : ℂ) * ((π : ℂ) * zI x)))
        _ =
            (cexp (Complex.I * (u : ℂ) * (π : ℂ)))⁻¹ *
              cexp (Complex.I * (u : ℂ) * ((π : ℂ) * zI x)) := by
              simp [Complex.exp_neg, mul_assoc]
    -- Multiply `hcexp` by the common factor to match the unfolded `Φ₂`/`F` expressions.
    have hmul :=
      congrArg (fun w : ℂ => w * (zI x ^ (10 : ℕ) * varphi' (-1 / zI x))) hcexp
    -- Now unfold `Φ₂` and `F` and rewrite `z₂' x + 1 = zI x`.
    -- The goal becomes the multiplication-by-`hmul` instance of the exponential identity.
    simpa [RealIntegrands.Φ₂, ComplexIntegrands.Φ₂', ComplexIntegrands.Φ₁', F, hz2p,
      expU, mul_assoc, mul_left_comm, mul_comm] using! hmul
  -- Pull out the constant `(expU u 1)⁻¹`.
  calc
    I₂' u = ∫ x in (0 : ℝ)..1, RealIntegrands.Φ₂ u x := by rfl
    _ = ∫ x in (0 : ℝ)..1, (expU u 1)⁻¹ * F u (zI x) := hcongr
    _ = (expU u 1)⁻¹ * ∫ x in (0 : ℝ)..1, F u (zI x) := by
          simp [intervalIntegral.integral_const_mul]

/-- Rewrite `I₄'` as a horizontal period integral of `F` on the shifted line `im = 1`. -/
public lemma I₄'_as_F (u : ℝ) :
    I₄' u = -(expU u 1) * ∫ x in (0 : ℝ)..1, F u (zI x - 1) := by
  rw [I₄']
  have hcongr :
      (∫ x in (0 : ℝ)..1, RealIntegrands.Φ₄ u x) =
        ∫ x in (0 : ℝ)..1, (-1 : ℂ) * (expU u 1) * F u (zI (1 - x) - 1) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! hx
    have hz4m : z₄' x - 1 = zI (1 - x) - 1 := by
      simp [zI, z₄'_eq_of_mem (t := x) hxIcc, sub_eq_add_neg, add_assoc, add_comm]
    have hz4p : z₄' x = (zI (1 - x) - 1) + 1 := by
      -- `1 - x + I = (-x + I) + 1`.
      simp [zI, z₄'_eq_of_mem (t := x) hxIcc, sub_eq_add_neg, add_assoc, add_comm]
    have hcexp :
        cexp (Complex.I * (u : ℂ) * ((π : ℂ) * z₄' x)) =
          cexp (Complex.I * (u : ℂ) * (π : ℂ)) *
            cexp (Complex.I * (u : ℂ) * ((π : ℂ) * (zI (1 - x) - 1))) := by
      -- Rewrite `z₄' x` as `(zI (1 - x) - 1) + 1` and split the exponential using `exp_add`.
      have harg :
          Complex.I * (u : ℂ) * ((π : ℂ) * z₄' x) =
            Complex.I * (u : ℂ) * (π : ℂ) + Complex.I * (u : ℂ) * ((π : ℂ) * (zI (1 - x) - 1)) := by
        -- `z₄' x = (zI (1 - x) - 1) + 1`.
        have hz : z₄' x = (zI (1 - x) - 1) + 1 := by simpa [add_assoc] using! hz4p
        -- Then it is a polynomial identity in `ℂ`.
        simpa [hz] using! (by ring : _
          = (Complex.I * (u : ℂ) * (π : ℂ) +
              Complex.I * (u : ℂ) * ((π : ℂ) * (zI (1 - x) - 1))))
      calc
        cexp (Complex.I * (u : ℂ) * ((π : ℂ) * z₄' x)) =
            cexp
              (Complex.I * (u : ℂ) * (π : ℂ) +
                Complex.I * (u : ℂ) * ((π : ℂ) * (zI (1 - x) - 1))) := by
              simpa using! congrArg cexp harg
        _ =
            cexp (Complex.I * (u : ℂ) * (π : ℂ)) *
              cexp (Complex.I * (u : ℂ) * ((π : ℂ) * (zI (1 - x) - 1))) := by
              simpa using!
                (Complex.exp_add (Complex.I * (u : ℂ) * (π : ℂ))
                  (Complex.I * (u : ℂ) * ((π : ℂ) * (zI (1 - x) - 1))))
    have hmul :=
      congrArg
        (fun w : ℂ =>
          w * ((zI (1 - x) - 1) ^ (10 : ℕ) * varphi' (-1 / (zI (1 - x) - 1))))
        hcexp
    simpa [RealIntegrands.Φ₄, ComplexIntegrands.Φ₄', ComplexIntegrands.Φ₃', F, hz4m,
      expU, mul_assoc, mul_left_comm, mul_comm] using! hmul
  -- Rewrite the integral using the substitution `x ↦ 1 - x` to obtain `zI x - 1`.
  have hsub :
      (∫ x in (0 : ℝ)..1, F u (zI (1 - x) - 1)) = ∫ x in (0 : ℝ)..1, F u (zI x - 1) := by
    have h :=
      (intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => F u (zI x - 1))
        (a := (0 : ℝ)) (b := (1 : ℝ)) (d := (1 : ℝ)))
    -- The left-hand side of `h` is `∫ x in 0..1, F u (zI (1-x) - 1)`.
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, zI] using! h
  -- Assemble and simplify.
  -- `I₄' u = ∫ (-1) * (...)`, so rewrite as `-(expU u 1) * ∫ ...`.
  simp_all

/-- For even `u` (i.e. `expU u 1 = 1`), the odd contour pieces cancel in `aProfile u`. -/
public lemma aProfile_even_reduction (u : ℝ) (hu : expU u 1 = 1) :
    aProfile u = I₂' u + I₄' u + I₆' u := by
  have h135 : (I₁' u + I₃' u + I₅' u : ℂ) = 0 := I₁'_I₃'_I₅'_sum_of_even (u := u) hu
  -- Unfold `aProfile` and regroup.
  dsimp [aProfile, RealIntegrals.a']
  calc
    I₁' u + I₂' u + I₃' u + I₄' u + I₅' u + I₆' u =
        (I₁' u + I₃' u + I₅' u) + (I₂' u + I₄' u + I₆' u) := by ac_rfl
    _ = I₂' u + I₄' u + I₆' u := by simp [h135, add_assoc]


/-- An auxiliary integrand whose strip finite difference cancels `I₆'` at even `u`. -/
@[expose] public def f0 (u : ℝ) (z : ℂ) : ℂ :=
  varphi' z * (((2 : ℂ) * z) - 1) * expU u z

/-- The unit-shift finite difference of `f0` on the imaginary axis. -/
public lemma f0_add_one_sub (u : ℝ) (hu : expU u 1 = 1) (t : ℝ) (ht : 0 < t) :
    f0 u ((1 : ℂ) + (t : ℂ) * Complex.I) - f0 u ((t : ℂ) * Complex.I) =
      (2 : ℂ) * (varphi' ((t : ℂ) * Complex.I) * expU u ((t : ℂ) * Complex.I)) := by
  have htIm : 0 < (((t : ℂ) * Complex.I) : ℂ).im := by simpa [mul_assoc] using! ht
  let zH : UpperHalfPlane := ⟨(t : ℂ) * Complex.I, htIm⟩
  have htIm1 : 0 < (((t : ℂ) * Complex.I) + 1).im := by simpa using! htIm
  let zH1 : UpperHalfPlane := ⟨(t : ℂ) * Complex.I + 1, htIm1⟩
  have hvadd : ((1 : ℝ) +ᵥ zH : UpperHalfPlane) = zH1 := by
    ext1
    simp [zH, zH1, add_comm]
  have hperVarphi : varphi' (((t : ℂ) * Complex.I) + 1) = varphi' ((t : ℂ) * Complex.I) := by
    -- Reduce to periodicity of `varphi` on `ℍ`.
    have h := varphi_periodic (z := zH)
    have h' : varphi zH1 = varphi zH := by simpa [hvadd] using! h
    -- Unfold `varphi'` on both sides (both points have positive imaginary part).
    simp [varphi', zH, zH1, h', ht]
  have hperExp : expU u (((t : ℂ) * Complex.I) + 1) = expU u ((t : ℂ) * Complex.I) := by
    simpa [add_assoc] using! (expU_add_one (u := u) hu (z := (t : ℂ) * Complex.I))
  -- Expand and simplify.
  have hzadd : (1 : ℂ) + (t : ℂ) * Complex.I = (t : ℂ) * Complex.I + 1 := by ring
  simp [f0, hzadd, hperVarphi, hperExp]
  ring_nf

/-- Norm of the exponential weight `expU u` on the imaginary axis. -/
public lemma norm_expU_mul_I (u t : ℝ) :
    ‖expU u ((t : ℂ) * Complex.I)‖ = Real.exp (-Real.pi * u * t) := by
  unfold expU
  have harg :
      (Real.pi : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I) = (-Real.pi * u * t : ℂ) := by
    calc
      (Real.pi : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I) =
          (Real.pi : ℂ) * (u : ℂ) * (t : ℂ) * (Complex.I * Complex.I) := by
            ac_rfl
      _ = (Real.pi : ℂ) * (u : ℂ) * (t : ℂ) * (-1 : ℂ) := by
            simp [Complex.I_mul_I]
      _ = (-Real.pi * u * t : ℂ) := by
            ring
  calc
    ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I))‖ =
        ‖Complex.exp (-Real.pi * u * t : ℂ)‖ := by simp [harg]
    _ = Real.exp ((-Real.pi * u * t : ℂ).re) := by
          simpa using! (Complex.norm_exp (-Real.pi * u * t : ℂ))
    _ = Real.exp (-Real.pi * u * t) := by simp

/-- Complex differentiability of `varphi ∘ UpperHalfPlane.ofComplex` on `{z : ℂ | 0 < z.im}`. -/
public lemma differentiableOn_varphiOfComplex :
    DifferentiableOn ℂ (fun z : ℂ => varphi (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
  let s : Set ℂ := {z : ℂ | 0 < z.im}
  -- Building blocks on `{Im>0}`.
  have hE2 : DifferentiableOn ℂ (E₂ ∘ UpperHalfPlane.ofComplex) s :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₂_holo')
  have hE4 : DifferentiableOn ℂ ((E₄ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) s :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₄.holo')
  have hE6 : DifferentiableOn ℂ ((E₆ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) s :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₆.holo')
  have hΔ : DifferentiableOn ℂ (Δ ∘ UpperHalfPlane.ofComplex) s := by
    simpa [Delta_apply] using!
      (UpperHalfPlane.mdifferentiable_iff.mp
        (Delta.holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => Delta z)))
  -- Convenience: pointwise versions.
  let E2c : ℂ → ℂ := fun z => E₂ (UpperHalfPlane.ofComplex z)
  let E4c : ℂ → ℂ := fun z => E₄ (UpperHalfPlane.ofComplex z)
  let E6c : ℂ → ℂ := fun z => E₆ (UpperHalfPlane.ofComplex z)
  let Δc : ℂ → ℂ := fun z => Δ (UpperHalfPlane.ofComplex z)
  have hE2c : DifferentiableOn ℂ E2c s := by simpa [E2c, Function.comp_def] using! hE2
  have hE4c : DifferentiableOn ℂ E4c s := by simpa [E4c, Function.comp_def] using! hE4
  have hE6c : DifferentiableOn ℂ E6c s := by simpa [E6c, Function.comp_def] using! hE6
  have hΔc : DifferentiableOn ℂ Δc s := by simpa [Δc, Function.comp_def] using! hΔ
  -- Powers.
  have hE4_2 : DifferentiableOn ℂ (fun z : ℂ => (E4c z) ^ (2 : ℕ)) s := hE4c.pow 2
  have hE4_3 : DifferentiableOn ℂ (fun z : ℂ => (E4c z) ^ (3 : ℕ)) s := hE4c.pow 3
  have hE4_4 : DifferentiableOn ℂ (fun z : ℂ => (E4c z) ^ (4 : ℕ)) s := hE4c.pow 4
  have hE6_2 : DifferentiableOn ℂ (fun z : ℂ => (E6c z) ^ (2 : ℕ)) s := hE6c.pow 2
  have hE2_2 : DifferentiableOn ℂ (fun z : ℂ => (E2c z) ^ (2 : ℕ)) s := hE2c.pow 2
  have hΔ_2 : DifferentiableOn ℂ (fun z : ℂ => (Δc z) ^ (2 : ℕ)) s := hΔc.pow 2
  have hΔ2_ne : ∀ z : ℂ, z ∈ s → (Δc z) ^ (2 : ℕ) ≠ 0 := by
    intro z hz
    have hz' : 0 < z.im := hz
    have hof : UpperHalfPlane.ofComplex z = ⟨z, hz'⟩ :=
      UpperHalfPlane.ofComplex_apply_of_im_pos hz'
    have hΔ0 : Δ (⟨z, hz'⟩ : ℍ) ≠ 0 := Δ_ne_zero (⟨z, hz'⟩ : ℍ)
    simpa [Δc, hof] using! (pow_ne_zero 2 hΔ0)
  -- Numerator and denominator of `varphi (ofComplex z)` (written on the `ofComplex` side).
  let num : ℂ → ℂ := fun z : ℂ =>
    ((25 : ℂ) * (E4c z) ^ (4 : ℕ) - (49 : ℂ) * (E6c z) ^ (2 : ℕ) * (E4c z))
        + (48 : ℂ) * (E6c z) * (E4c z) ^ (2 : ℕ) * (E2c z)
        + ((-49 : ℂ) * (E4c z) ^ (3 : ℕ) + (25 : ℂ) * (E6c z) ^ (2 : ℕ)) * (E2c z) ^ (2 : ℕ)
  have hterm1 : DifferentiableOn ℂ (fun z : ℂ => (25 : ℂ) * (E4c z) ^ (4 : ℕ)) s :=
    (hE4_4.const_mul (25 : ℂ))
  have hterm2 : DifferentiableOn ℂ (fun z : ℂ => (49 : ℂ) * (E6c z) ^ (2 : ℕ) * (E4c z)) s := by
    have h49E6 : DifferentiableOn ℂ (fun z : ℂ => (49 : ℂ) * (E6c z) ^ (2 : ℕ)) s :=
      hE6_2.const_mul (49 : ℂ)
    -- `mul` gives a pointwise product; expand it so the parenthesization matches.
    simpa [Pi.mul_def, mul_assoc] using! h49E6.mul hE4c
  have hterm3 :
      DifferentiableOn ℂ (fun z : ℂ => (48 : ℂ) * (E6c z) * (E4c z) ^ (2 : ℕ) * (E2c z)) s := by
    have h48E6 : DifferentiableOn ℂ (fun z : ℂ => (48 : ℂ) * E6c z) s :=
      hE6c.const_mul (48 : ℂ)
    -- Same: expand the pointwise multiplication introduced by `mul`.
    simpa [Pi.mul_def, mul_assoc, mul_left_comm, mul_comm] using! (h48E6.mul hE4_2).mul hE2c
  have hterm4 :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          ((-49 : ℂ) * (E4c z) ^ (3 : ℕ) + (25 : ℂ) * (E6c z) ^ (2 : ℕ)) *
            (E2c z) ^ (2 : ℕ))
        s := by
    have hpoly :
        DifferentiableOn ℂ
          (fun z : ℂ => (-49 : ℂ) * (E4c z) ^ (3 : ℕ) + (25 : ℂ) * (E6c z) ^ (2 : ℕ)) s :=
      (hE4_3.const_mul (-49 : ℂ)).add (hE6_2.const_mul (25 : ℂ))
    exact hpoly.mul hE2_2
  have hnum : DifferentiableOn ℂ num s := by
    have h12 :
        DifferentiableOn ℂ
          (fun z : ℂ => (25 : ℂ) * (E4c z) ^ (4 : ℕ) - (49 : ℂ) * (E6c z) ^ (2 : ℕ) * (E4c z)) s :=
      hterm1.sub hterm2
    have h123 : DifferentiableOn ℂ (fun z : ℂ => ((25 : ℂ) * (E4c z) ^ (4 : ℕ) -
        (49 : ℂ) * (E6c z) ^ (2 : ℕ) * (E4c z)) +
          (48 : ℂ) * (E6c z) * (E4c z) ^ (2 : ℕ) * (E2c z)) s :=
      h12.add hterm3
    exact DifferentiableOn.fun_add h123 hterm4
  have hdiv : DifferentiableOn ℂ (fun z : ℂ => num z / (Δc z) ^ (2 : ℕ)) s :=
    hnum.div hΔ_2 (by
      intro z hz
      simpa [Δc] using! hΔ2_ne z hz)
  -- Now unfold `varphi` and use `hdiv`.
  assumption


end SpecialValuesAux

end

end SpherePacking.Dim24
