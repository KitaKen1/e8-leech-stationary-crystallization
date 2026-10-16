-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.Values
import SpherePacking.Dim24.MagicFunction.A.LaplaceZeros
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import SpherePacking.ForMathlib.IntegrablePowMulExp

/-!
# Definitions for derivative computations

This file introduces auxiliary quantities on the imaginary axis used in the evaluation and
differentiation of the profile `aProfile` in dimension `24`. The key objects are the split
vertical integrals `Vseg` and `Vtail`, the exponential coefficient `coeffExp`, and the
decomposition of `Vtail` into a singular term `tailSing` and an integrable remainder `tailRem`.

## Main definitions
* `SpecialValuesDeriv.Vseg`, `SpecialValuesDeriv.Vtail`, `SpecialValuesDeriv.W`
* `SpecialValuesDeriv.coeffExp`
* `SpecialValuesDeriv.tailRemIntegrand`, `SpecialValuesDeriv.tailRem`

## Main statements
* `SpecialValuesDeriv.aProfile_eq_factorization_of_lt`
* `SpecialValuesDeriv.Vtail_eq_tailRem_add_tailSing`
-/

open scoped Real
open scoped Topology
open Complex Real
open Filter

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDeriv

open scoped Real Topology
open Filter Complex MeasureTheory Set intervalIntegral
open RealIntegrals RealIntegrals.ComplexIntegrands

/-- The vertical segment integral of `Φ₅'` over `t ∈ (0,1)`, on the imaginary axis. -/
@[expose] public def Vseg (u : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)

/-- The vertical tail integral of `Φ₅'` over `t ∈ (1,∞)`, on the imaginary axis. -/
@[expose] public def Vtail (u : ℝ) : ℂ :=
  ∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)

/-- The full vertical integral `W u = Vseg u + Vtail u`. -/
@[expose] public def W (u : ℝ) : ℂ := Vseg u + Vtail u

/-- The exponential coefficient `exp(π i u) + exp(-π i u) - 2` appearing in the profile. -/
@[expose] public def coeffExp (u : ℝ) : ℂ :=
  Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
      Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)

lemma cexp_pi_I_mul_u_mul_imag (u t : ℝ) :
    Complex.exp (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
      (Real.exp (-Real.pi * u * t) : ℂ) := by
  have h :
      (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) = ((-Real.pi * u * t : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp
  rw [h]
  simp [Complex.ofReal_exp]

/-- The constant `864 / π^2` used for the principal part of `varphi₂` in the `q`-expansion. -/
@[expose] public def c864 : ℂ := (864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))

/-- The `q`-parameter `q z = exp(2π i z)`. -/
@[expose] public def q (z : ℂ) : ℂ := SpecialValuesVarphi₁Limits.q z

lemma q_ne_zero (z : ℂ) : q z ≠ 0 := SpecialValuesVarphi₁Limits.q_ne_zero z

/-- On the imaginary axis, `q (t i) = exp(-2π t)`. -/
public lemma q_imag_axis (t : ℝ) :
    q ((t : ℂ) * Complex.I) = (Real.exp (-2 * Real.pi * t) : ℂ) := by
  unfold q SpecialValuesVarphi₁Limits.q
  have h :
      (2 * (π : ℂ) * Complex.I * ((t : ℂ) * Complex.I)) = ((-2 * Real.pi * t : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp
  rw [h]
  simp [Complex.ofReal_exp]

/-- The residual term of `varphi₂` after subtracting the principal part `c864 / q^2`. -/
@[expose] public def varphi₂Residual (z : UpperHalfPlane) : ℂ :=
  ((Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) - c864) / q (z : ℂ)

lemma varphi₂_eq_c864_div_q_sq_add_residual_div_q (z : UpperHalfPlane) :
    Dim24.varphi₂ z = c864 / (q (z : ℂ)) ^ (2 : ℕ) + varphi₂Residual z / q (z : ℂ) := by
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  have hzq2 : (q (z : ℂ)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hzq
  unfold varphi₂Residual
  -- Clear denominators `q` and `q^2`.
  field_simp [hzq, hzq2]
  ring

lemma Φ₅'_imag_axis_rewrite (u t : ℝ) (ht : 0 < t) :
    Φ₅' u ((t : ℂ) * Complex.I) =
      ((((t : ℂ) * Complex.I) ^ (2 : ℕ)) * varphi ⟨(t : ℂ) * Complex.I, by
            simpa [Complex.mul_I_im] using! ht⟩ +
          (((t : ℂ) * Complex.I) * varphi₁ ⟨(t : ℂ) * Complex.I, by
            simpa [Complex.mul_I_im] using! ht⟩) +
          varphi₂ ⟨(t : ℂ) * Complex.I, by
            simpa [Complex.mul_I_im] using! ht⟩) *
        (Real.exp (-Real.pi * u * t) : ℂ) := by
  set z : ℂ := (t : ℂ) * Complex.I
  have hz : 0 < z.im := by
    simpa [z, Complex.mul_I_im] using! ht
  set zH : UpperHalfPlane := ⟨z, hz⟩
  let zHS : UpperHalfPlane := ModularGroup.S • zH
  have hScoe : ((zHS : UpperHalfPlane) : ℂ) = (-1 : ℂ) / z := by
    have h1 :
        ((ModularGroup.S • zH : UpperHalfPlane) : ℂ) = (-(zH : ℂ))⁻¹ := by
      simpa using!
        congrArg (fun w : UpperHalfPlane => (w : ℂ)) (UpperHalfPlane.modular_S_smul zH)
    have h1' : ((zHS : UpperHalfPlane) : ℂ) = (-(zH : ℂ))⁻¹ := by
      simpa [zHS] using! h1
    calc
      ((zHS : UpperHalfPlane) : ℂ) = (-(zH : ℂ))⁻¹ := h1'
      _ = (-1 : ℂ) / (zH : ℂ) := by simp [div_eq_mul_inv]
      _ = (-1 : ℂ) / z := by simp [zH, z]
  have hvarphiS : varphi' ((-1 : ℂ) / z) = varphi zHS := by
    simpa [hScoe] using! (varphi'_coe_upperHalfPlane (z := zHS))
  have hcore :
      varphi' ((-1 : ℂ) / z) * z ^ (10 : ℕ) =
        z ^ (2 : ℕ) * varphi zH + z * varphi₁ zH + varphi₂ zH := by
    have hmain := SpecialValuesAux.varphi_S_transform_mul_pow10 (z := zH)
    calc
      varphi' ((-1 : ℂ) / z) * z ^ (10 : ℕ) = z ^ (10 : ℕ) * varphi zHS := by
        simp [hvarphiS, mul_comm]
      _ = z ^ (2 : ℕ) * varphi zH + z * varphi₁ zH + varphi₂ zH := by
        simpa [zH, z, zHS] using! hmain
  have hexp :
      cexp (Real.pi * Complex.I * (u : ℂ) * z) = (Real.exp (-Real.pi * u * t) : ℂ) := by
    simpa [z] using! (cexp_pi_I_mul_u_mul_imag (u := u) (t := t))
  -- Unfold `Φ₅'` and rewrite the modular part and exponential.
  have hΦ :
      Φ₅' u z =
        (varphi' ((-1 : ℂ) / z) * z ^ (10 : ℕ)) * cexp (Real.pi * Complex.I * (u : ℂ) * z) := by
    simp [ComplexIntegrands.Φ₅', Φ₅', mul_assoc]
  -- Normalize `z` back to `(t : ℂ) * I`.
  -- (Avoid `mul_comm` here so the `cexp` argument stays in the form needed for `hexp`.)
  lia
 
/-- For `u > 4`, the contour decomposition of `aProfile u` factors as `I * coeffExp u * W u`. -/
public lemma aProfile_eq_factorization_of_lt (u : ℝ) (hu : 4 < u) :
    aProfile u = (Complex.I : ℂ) * (coeffExp u * W u) := by
  have h135 := LaplaceZeros.I₁'_add_I₃'_add_I₅'_eq_imag_axis (u := u)
  have h246 := LaplaceZerosTail.TailDeform.I₂'_add_I₄'_add_I₆'_eq_imag_axis (u := u) hu
  -- Expand `aProfile` and group into the two blocks.
  dsimp [aProfile, RealIntegrals.a']
  calc
    RealIntegrals.I₁' u + RealIntegrals.I₂' u + RealIntegrals.I₃' u + RealIntegrals.I₄' u +
          RealIntegrals.I₅' u + RealIntegrals.I₆' u =
        (RealIntegrals.I₁' u + RealIntegrals.I₃' u + RealIntegrals.I₅' u) +
          (RealIntegrals.I₂' u + RealIntegrals.I₄' u + RealIntegrals.I₆' u) := by
          ac_rfl
    _ =
        (Complex.I : ℂ) * (coeffExp u * Vseg u) + (Complex.I : ℂ) * (coeffExp u * Vtail u) := by
          simp [h135, h246, coeffExp, Vseg, Vtail, mul_assoc]
    _ = (Complex.I : ℂ) * (coeffExp u * W u) := by
          simp [W, mul_add]

end SpecialValuesDeriv

namespace SpecialValuesDeriv

open scoped Real Topology
open Filter Complex MeasureTheory Set

/-- The identity `sin x = x * sinc x`. -/
public lemma sin_eq_mul_sinc (x : ℝ) : Real.sin x = x * Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx, Real.sinc]
  · have : Real.sinc x = Real.sin x / x := Real.sinc_of_ne_zero hx
    -- `x * (sin x / x) = sin x`.
    simp [this, mul_div_cancel₀ _ hx]

/-- Rewrite `coeffExp` in terms of `Real.cos`: `coeffExp u = (2 cos(π u) - 2)`. -/
public lemma coeffExp_eq_two_mul_cos_sub_two (u : ℝ) :
    coeffExp u = ((2 * Real.cos (Real.pi * u) - 2 : ℝ) : ℂ) := by
  -- Use `2*cos x = exp(x*i) + exp(-x*i)` and specialize to a real argument.
  set x : ℂ := ((Real.pi * u : ℝ) : ℂ)
  have htwo :
      Complex.exp (x * Complex.I) + Complex.exp (-(x * Complex.I)) = (2 : ℂ) * Complex.cos x := by
    have h := (Complex.two_cos (x := x)).symm
    have hneg' : (-x) * Complex.I = -(x * Complex.I) := by ring
    simpa [hneg', mul_assoc] using! h
  have hcos : Complex.cos x = (Real.cos (Real.pi * u) : ℂ) := by
    simp [x]
  -- Rewrite the second exponential as `exp (-x * I)`.
  have hneg : -(((Real.pi * u : ℝ) : ℂ) * Complex.I) = (-x) * Complex.I := by
    simp [x, mul_assoc]
  -- Finish.
  calc
    coeffExp u =
        (Complex.exp (x * Complex.I) + Complex.exp (-(x * Complex.I))) - (2 : ℂ) := by
          simp [coeffExp, x, sub_eq_add_neg, add_assoc]
    _ = (2 : ℂ) * (Real.cos (Real.pi * u) : ℂ) - (2 : ℂ) := by
          simp [htwo, hcos]
    _ = ((2 * Real.cos (Real.pi * u) - 2 : ℝ) : ℂ) := by
          push_cast
          ring

lemma coeffExp_eq_neg_pi_sq_mul_sq_mul_sinc_sq (u : ℝ) :
    coeffExp u =
      (-((Real.pi : ℂ) ^ (2 : ℕ))) * ((u - 4) ^ (2 : ℕ) : ℂ) *
        (((Real.sinc (Real.pi * (u - 4) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
  -- First rewrite in terms of `sin (πu/2)`.
  have hreal :
      (2 * Real.cos (Real.pi * u) - 2) =
        -(Real.pi ^ (2 : ℕ)) * (u - 4) ^ (2 : ℕ) *
          (Real.sinc (Real.pi * (u - 4) / 2)) ^ (2 : ℕ) := by
    -- `2*cos(πu) - 2 = -4 * sin(πu/2)^2`.
    have hcos2 :
        2 * Real.cos (Real.pi * u) - 2 = -4 * (Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) := by
      set y : ℝ := Real.pi * u / 2
      have hcos : Real.cos (Real.pi * u) = Real.cos (2 * y) := by
        simp [y, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
      -- Use `cos (2y) = 2*cos^2 y - 1`, then `sin^2 y = 1 - cos^2 y`.
      have hcos' : Real.cos (2 * y) = 2 * (Real.cos y) ^ (2 : ℕ) - 1 := by
        -- `cos_two_mul` is `cos (2y) = 2*cos^2 y - 1`.
        simpa [pow_two] using! (Real.cos_two_mul y)
      have hsinSq : (Real.sin y) ^ (2 : ℕ) = 1 - (Real.cos y) ^ (2 : ℕ) := by
        -- Rearranged from `sin^2 + cos^2 = 1`.
        exact Real.sin_sq y
      calc
        2 * Real.cos (Real.pi * u) - 2
            = 2 * Real.cos (2 * y) - 2 := by simp [hcos]
        _ = 2 * (2 * (Real.cos y) ^ (2 : ℕ) - 1) - 2 := by simp [hcos']
        _ = 4 * (Real.cos y) ^ (2 : ℕ) - 4 := by ring
        _ = -4 * (1 - (Real.cos y) ^ (2 : ℕ)) := by ring
        _ = -4 * (Real.sin y) ^ (2 : ℕ) := by simp [hsinSq]
    -- Periodicity: `sin(πu/2) = sin(π(u-4)/2)`.
    have hsinPer :
        Real.sin (Real.pi * u / 2) = Real.sin (Real.pi * (u - 4) / 2) := by
      have hshift : Real.pi * u / 2 = Real.pi * (u - 4) / 2 + 2 * Real.pi := by ring
      rw [hshift]
      exact Real.sin_add_two_pi (Real.pi * (u - 4) / 2)
    -- Replace the sine by `sinc`.
    set x : ℝ := Real.pi * (u - 4) / 2
    have hsinSinc : Real.sin x = x * Real.sinc x := sin_eq_mul_sinc x
    -- Put everything together.
    grind only
  -- Cast the real identity into `ℂ` and rewrite the RHS in the chosen form.
  have hcast :
      (coeffExp u : ℂ) =
        ((-(Real.pi ^ (2 : ℕ)) * (u - 4) ^ (2 : ℕ) *
              (Real.sinc (Real.pi * (u - 4) / 2)) ^ (2 : ℕ)) : ℝ) := by
    -- `coeffExp u` is already a complex number; use `coeffExp_eq_two_mul_cos_sub_two` and `hreal`.
    -- (The RHS is real, so we coerce it into `ℂ` below.)
    simp [coeffExp_eq_two_mul_cos_sub_two u, hreal]
  -- Normalize: `((a : ℝ) : ℂ) = (a : ℂ)` and `(π^2 : ℂ) = (π : ℂ)^2`.
  -- Also rewrite `((u-4)^(2:ℕ) : ℂ)` as a cast.
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using! hcast

/-- As `u → 4⁺`, the quotient `coeffExp u / (u - 4)^2` tends to `-π^2`. -/
public lemma tendsto_coeffExp_div_sq_nhdsGT_four :
    Tendsto (fun u : ℝ => coeffExp u / ((u - 4) ^ (2 : ℕ) : ℂ)) (𝓝[>] (4 : ℝ))
      (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)))) := by
  -- For `u>4`, rewrite the ratio using the explicit `sinc` factorization.
  have hEq :
      (fun u : ℝ => coeffExp u / ((u - 4) ^ (2 : ℕ) : ℂ)) =ᶠ[𝓝[>] (4 : ℝ)]
        fun u : ℝ => (-((Real.pi : ℂ) ^ (2 : ℕ))) *
          (((Real.sinc (Real.pi * (u - 4) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    -- On `u>4`, we have `u-4 ≠ 0`, so we can safely cancel the factor `(u-4)^2`.
    refine (eventually_nhdsWithin_iff.2 ?_)
    refine Filter.Eventually.of_forall ?_
    intro u hu
    have hne : ((u - 4) ^ (2 : ℕ) : ℂ) ≠ 0 := by
      have hne' : u - 4 ≠ 0 := by
        have : (4 : ℝ) < u := by simpa [Set.mem_Ioi] using! hu
        linarith
      exact_mod_cast pow_ne_zero 2 hne'
    have hrew := coeffExp_eq_neg_pi_sq_mul_sq_mul_sinc_sq u
    -- Divide by `(u-4)^2`.
    grind only
  -- `Real.sinc` is continuous with value `1` at `0`, so the RHS tends to `-π^2`.
  have hlin : Tendsto (fun u : ℝ => Real.pi * (u - 4) / 2) (𝓝[>] (4 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hsub : Tendsto (fun u : ℝ => u - 4) (𝓝[>] (4 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hsub0 : Tendsto (fun u : ℝ => u - 4) (𝓝 (4 : ℝ)) (𝓝 (0 : ℝ)) := by
        have hcont : ContinuousAt (fun u : ℝ => u - 4) (4 : ℝ) := by fun_prop
        simpa using! hcont.tendsto
      exact tendsto_nhdsWithin_of_tendsto_nhds hsub0
    -- Multiply by constants.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using!
      (tendsto_const_nhds.mul hsub).mul tendsto_const_nhds
  have hsinc :
      Tendsto (fun u : ℝ => Real.sinc (Real.pi * (u - 4) / 2)) (𝓝[>] (4 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hsinc0 : Tendsto Real.sinc (𝓝 (0 : ℝ)) (𝓝 (Real.sinc (0 : ℝ))) :=
      (Real.continuous_sinc.continuousAt : ContinuousAt Real.sinc (0 : ℝ)).tendsto
    simpa using! hsinc0.comp hlin
  have hsinc2 :
      Tendsto (fun u : ℝ => (Real.sinc (Real.pi * (u - 4) / 2)) ^ (2 : ℕ)) (𝓝[>] (4 : ℝ))
        (𝓝 ((1 : ℝ) ^ (2 : ℕ))) := hsinc.pow 2
  have hsinc2' :
      Tendsto
          (fun u : ℝ =>
            (((Real.sinc (Real.pi * (u - 4) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
          (𝓝[>] (4 : ℝ)) (𝓝 (((1 : ℝ) ^ (2 : ℕ) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto).comp hsinc2
  have hmul :
      Tendsto
          (fun u : ℝ =>
            (-((Real.pi : ℂ) ^ (2 : ℕ))) *
              (((Real.sinc (Real.pi * (u - 4) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
          (𝓝[>] (4 : ℝ)) (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)) * (((1 : ℝ) ^ (2 : ℕ) : ℝ) : ℂ))) :=
    (tendsto_const_nhds.mul hsinc2')
  have hmul' :
      Tendsto
          (fun u : ℝ =>
            (-((Real.pi : ℂ) ^ (2 : ℕ))) *
              (((Real.sinc (Real.pi * (u - 4) / 2)) ^ (2 : ℕ) : ℝ) : ℂ))
          (𝓝[>] (4 : ℝ)) (𝓝 (-((Real.pi : ℂ) ^ (2 : ℕ)))) := by
    simpa using! hmul
  exact Tendsto.congr' hEq.symm hmul'

lemma ofReal_exp_mul (a b : ℝ) :
    (Real.exp a : ℂ) * (Real.exp b : ℂ) = (Real.exp (a + b) : ℂ) := by
  have ha : (Real.exp a : ℂ) = Complex.exp (a : ℂ) := by
    simp
  have hb : (Real.exp b : ℂ) = Complex.exp (b : ℂ) := by
    simp
  calc
    (Real.exp a : ℂ) * (Real.exp b : ℂ) = Complex.exp (a : ℂ) * Complex.exp (b : ℂ) := by
      simp [ha, hb]
    _ = Complex.exp ((a : ℂ) + (b : ℂ)) :=
      (Complex.exp_add (a : ℂ) (b : ℂ)).symm
    _ = (Real.exp (a + b) : ℂ) := by
      -- Rewrite `(a : ℂ) + (b : ℂ)` as `((a + b : ℝ) : ℂ)` and use `Complex.ofReal_exp`.
      norm_num

lemma ofReal_exp_inv (a : ℝ) : (Real.exp a : ℂ)⁻¹ = (Real.exp (-a) : ℂ) := by
  -- `exp (-a) = (exp a)⁻¹` in `ℝ`, and the coercion `ℝ → ℂ` preserves inverses of nonzero reals.
  simp [Real.exp_neg]

lemma q_imag_axis_eq_cexp (t : ℝ) :
    q ((t : ℂ) * Complex.I) = Complex.exp ((-2 * Real.pi * t : ℝ) : ℂ) := by
  simpa [Complex.ofReal_exp] using! (q_imag_axis t)

lemma q_imag_axis_sq (t : ℝ) :
    (q ((t : ℂ) * Complex.I)) ^ (2 : ℕ) = (Real.exp (-4 * Real.pi * t) : ℂ) := by
  have hq : q ((t : ℂ) * Complex.I) = Complex.exp ((-2 * Real.pi * t : ℝ) : ℂ) :=
    q_imag_axis_eq_cexp t
  calc
    (q ((t : ℂ) * Complex.I)) ^ (2 : ℕ) = (Complex.exp ((-2 * Real.pi * t : ℝ) : ℂ)) ^ (2 : ℕ) := by
      simp [hq]
    _ = Complex.exp (((-2 * Real.pi * t : ℝ) : ℂ) + ((-2 * Real.pi * t : ℝ) : ℂ)) := by
      simp [pow_two, Complex.exp_add]
    _ = Complex.exp ((-4 * Real.pi * t : ℝ) : ℂ) := by
      congr 1
      push_cast
      ring
    _ = (Real.exp (-4 * Real.pi * t) : ℂ) := by
      simp [Complex.ofReal_exp]

lemma q_imag_axis_sq_inv (t : ℝ) :
    ((q ((t : ℂ) * Complex.I)) ^ (2 : ℕ))⁻¹ = (Real.exp (4 * Real.pi * t) : ℂ) := by
  -- Convert `q^2` to a complex exponential, invert via `Complex.exp_neg`, and return to `Real.exp`.
  have hq2' :
      (q ((t : ℂ) * Complex.I)) ^ (2 : ℕ) = Complex.exp ((-4 * Real.pi * t : ℝ) : ℂ) := by
    have hq2 : (q ((t : ℂ) * Complex.I)) ^ (2 : ℕ) = (Real.exp (-4 * Real.pi * t) : ℂ) :=
      q_imag_axis_sq t
    simp_all
  have hinv :
      (Complex.exp ((-4 * Real.pi * t : ℝ) : ℂ))⁻¹ = Complex.exp ((4 * Real.pi * t : ℝ) : ℂ) := by
    -- Apply `inv` to `exp_neg` at `x = (4πt : ℂ)`.
    have h := congrArg (fun z : ℂ => z⁻¹) (Complex.exp_neg ((4 * Real.pi * t : ℝ) : ℂ))
    simpa [inv_inv] using! h
  simp_all

lemma sing_piece_eq (u t : ℝ) :
    (c864 / (q ((t : ℂ) * Complex.I)) ^ (2 : ℕ)) * (Real.exp (-Real.pi * u * t) : ℂ) =
      c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
  have hq2inv : ((q ((t : ℂ) * Complex.I)) ^ (2 : ℕ))⁻¹ = (Real.exp (4 * Real.pi * t) : ℂ) :=
    q_imag_axis_sq_inv t
  have hsum : 4 * Real.pi * t + (-Real.pi * u * t) = -Real.pi * (u - 4) * t := by ring
  have hmul :
      (Real.exp (4 * Real.pi * t) : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ) =
        (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
    -- Combine exponentials using `Complex.exp_add` on the coerced real exponents.
    have hmul0 :
        (Real.exp (4 * Real.pi * t) : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ) =
          Complex.exp ((4 * Real.pi * t + (-Real.pi * u * t) : ℝ) : ℂ) := by
      -- Convert the real exponentials into complex exponentials and use `exp_add`.
      have h1 : (Real.exp (4 * Real.pi * t) : ℂ) = Complex.exp ((4 * Real.pi * t : ℝ) : ℂ) := by
        simp
      have h2 : (Real.exp (-Real.pi * u * t) : ℂ) = Complex.exp ((-Real.pi * u * t : ℝ) : ℂ) := by
        simp
      simpa [h1, h2] using!
        (Complex.exp_add ((4 * Real.pi * t : ℝ) : ℂ) ((-Real.pi * u * t : ℝ) : ℂ)).symm
    calc
      (Real.exp (4 * Real.pi * t) : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ) =
          Complex.exp ((4 * Real.pi * t + (-Real.pi * u * t) : ℝ) : ℂ) := hmul0
      _ = Complex.exp ((-Real.pi * (u - 4) * t : ℝ) : ℂ) := by
          exact Complex.ext (congrArg re (congrArg cexp (congrArg ofReal hsum)))
            (congrArg im (congrArg cexp (congrArg ofReal hsum)))
      _ = (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
          simp [Complex.ofReal_exp]
  calc
    (c864 / (q ((t : ℂ) * Complex.I)) ^ (2 : ℕ)) * (Real.exp (-Real.pi * u * t) : ℂ) =
        (c864 * ((q ((t : ℂ) * Complex.I)) ^ (2 : ℕ))⁻¹) * (Real.exp (-Real.pi * u * t) : ℂ) := by
          simp [div_eq_mul_inv, mul_assoc]
    _ = c864 * ((Real.exp (4 * Real.pi * t) : ℂ) * (Real.exp (-Real.pi * u * t) : ℂ)) := by
          simp [hq2inv, mul_assoc]
    _ = c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
          exact congrArg (fun z : ℂ => c864 * z) hmul

def singInt (u : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi (1 : ℝ), Real.exp (-Real.pi * (u - 4) * t)

lemma tendsto_mul_singInt_nhdsGT_four :
    Tendsto (fun u : ℝ => (u - 4) * singInt u) (𝓝[>] (4 : ℝ)) (𝓝 (1 / Real.pi)) := by
  -- For `u > 4`, compute the Laplace integral explicitly and take the limit `u → 4+`.
  have hEv :
      (fun u : ℝ => (u - 4) * singInt u) =ᶠ[𝓝[>] (4 : ℝ)]
        fun u : ℝ => Real.exp (-Real.pi * (u - 4)) / Real.pi := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : 4 < u := hu
    have ha : (-Real.pi * (u - 4)) < 0 := by
      have : 0 < u - 4 := sub_pos.2 hu'
      nlinarith [Real.pi_pos]
    -- First compute the integral in `ℝ`, then coerce to `ℂ`.
    have hIreal :
        (∫ t : ℝ in Set.Ioi (1 : ℝ), Real.exp ((-Real.pi * (u - 4)) * t)) =
          -Real.exp ((-Real.pi * (u - 4)) * (1 : ℝ)) / (-Real.pi * (u - 4)) :=
      integral_exp_mul_Ioi (a := (-Real.pi * (u - 4))) ha (c := (1 : ℝ))
    have hI : singInt u =
        -Real.exp ((-Real.pi * (u - 4)) * (1 : ℝ)) / (-Real.pi * (u - 4)) := by
      simpa [singInt] using! hIreal
    grind only
  refine (Tendsto.congr' hEv.symm ?_)
  -- Now take the limit of the explicit expression.
  have hsub0 : Tendsto (fun u : ℝ => u - 4) (𝓝 (4 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using! ((tendsto_id : Tendsto (fun u : ℝ => u) (𝓝 (4 : ℝ)) (𝓝 (4 : ℝ))).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (4 : ℝ)) (𝓝 (4 : ℝ)) (𝓝 (4 : ℝ))))
  have hsub : Tendsto (fun u : ℝ => u - 4) (𝓝[>] (4 : ℝ)) (𝓝 (0 : ℝ)) :=
    hsub0.mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun u : ℝ => (-Real.pi) * (u - 4)) (𝓝[>] (4 : ℝ)) (𝓝 (0 : ℝ)) := by
    have htconst :
        Tendsto (fun _ : ℝ => (-Real.pi)) (𝓝[>] (4 : ℝ)) (𝓝 (-Real.pi)) :=
      tendsto_const_nhds
    simpa using! (htconst.mul hsub)
  have hExp :
      Tendsto (fun u : ℝ => Real.exp (-Real.pi * (u - 4))) (𝓝[>] (4 : ℝ)) (𝓝 (Real.exp 0)) :=
    (Real.continuous_exp.tendsto 0).comp hlin
  have hfinal :
      Tendsto (fun u : ℝ => Real.exp (-Real.pi * (u - 4)) / Real.pi) (𝓝[>] (4 : ℝ))
        (𝓝 ((Real.exp 0) / Real.pi)) := hExp.div_const Real.pi
  simpa using! hfinal

def singIntC (u : ℝ) : ℂ := (singInt u : ℂ)

/-- The singular contribution to `Vtail`, obtained from the principal part of `varphi₂`. -/
public def tailSing (u : ℝ) : ℂ := c864 * singIntC u

/-- As `u → 4⁺`, the product `(u - 4) * tailSing u` tends to `c864 / π`. -/
public lemma tendsto_mul_tailSing_nhdsGT_four :
    Tendsto (fun u : ℝ => ((u - 4 : ℝ) : ℂ) * tailSing u) (𝓝[>] (4 : ℝ)) (𝓝 (c864 / (π : ℂ))) := by
  -- Rewrite the left-hand side in terms of the real product `(u-4) * singInt u`.
  have hprod :
      Tendsto (fun u : ℝ => (((u - 4) * singInt u : ℝ) : ℂ)) (𝓝[>] (4 : ℝ))
        (𝓝 ((1 / Real.pi : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (1 / Real.pi)).comp tendsto_mul_singInt_nhdsGT_four
  have hlim :
      Tendsto (fun u : ℝ => c864 * (((u - 4) * singInt u : ℝ) : ℂ)) (𝓝[>] (4 : ℝ))
        (𝓝 (c864 * ((1 / Real.pi : ℝ) : ℂ))) :=
    tendsto_const_nhds.mul hprod
  -- `((u-4):ℂ) * tailSing u = c864 * (((u-4) * singInt u) : ℂ)` and `c864 * (1/π) = c864 / π`.
  simpa [tailSing, singIntC, div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using! hlim

end SpecialValuesDeriv

namespace SpecialValuesDeriv

open scoped Real Topology
open Filter Complex MeasureTheory Set

/-- The remainder integrand on the tail `(1,∞)` after removing the singular term from `Φ₅'`. -/
@[expose] public def tailRemIntegrand (u t : ℝ) : ℂ :=
  if ht : 0 < t then
    let zH : UpperHalfPlane := ⟨(t : ℂ) * Complex.I, by simpa [Complex.mul_I_im] using! ht⟩
    let z : ℂ := (t : ℂ) * Complex.I
    ((z ^ (2 : ℕ)) * varphi zH + z * varphi₁ zH + varphi₂Residual zH / q z) *
      (Real.exp (-Real.pi * u * t) : ℂ)
  else
    0

/-- The tail remainder term, defined by integrating `tailRemIntegrand` over `(1,∞)`. -/
@[expose] public def tailRem (u : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi (1 : ℝ), tailRemIntegrand u t

/-- A continuous function to `ℂ` on a compact space has bounded norm. -/
public lemma exists_bound_norm_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : X → ℂ} (hf : Continuous f) :
    ∃ M : ℝ, ∀ x : X, ‖f x‖ ≤ M := by
  have hcomp : IsCompact (Set.range f) := isCompact_range hf
  have hbound : Bornology.IsBounded (Set.range f) := hcomp.isBounded
  rcases hbound.subset_closedBall (c := (0 : ℂ)) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro x
  have hx : f x ∈ Set.range f := ⟨x, rfl⟩
  have hx' : f x ∈ Metric.closedBall (0 : ℂ) M := hM hx
  simpa [Metric.mem_closedBall, dist_eq_norm] using! hx'

/-- Continuity of `q : ℂ → ℂ`. -/
public lemma continuous_q : Continuous q := by
  -- `q(z) = exp(2π i z)` is continuous.
  unfold q SpecialValuesVarphi₁Limits.q
  fun_prop

/-- Continuity of `z ↦ q (z : ℂ)` on the upper half-plane. -/
public lemma continuous_qH : Continuous fun z : UpperHalfPlane => q (z : ℂ) :=
  continuous_q.comp UpperHalfPlane.continuous_coe

/-- Continuity of `varphi₂ : ℍ → ℂ`. -/
public lemma continuous_varphi₂ : Continuous (Dim24.varphi₂ : UpperHalfPlane → ℂ) := by
  let f : UpperHalfPlane → ℂ := fun z =>
    (-36 : ℂ) * ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) *
      ((π : ℂ) ^ (2 : ℕ) * (Δ z) ^ (2 : ℕ))⁻¹
  have hf : Continuous f := by
    have hE4 : Continuous (E₄ : UpperHalfPlane → ℂ) := E₄.holo'.continuous
    have hE6 : Continuous (E₆ : UpperHalfPlane → ℂ) := E₆.holo'.continuous
    have hΔ : Continuous (Δ : UpperHalfPlane → ℂ) := SpecialValuesAux.continuous_Δ
    have hΔ2 : Continuous fun z : UpperHalfPlane => (Δ z) ^ (2 : ℕ) := hΔ.pow 2
    have hden : Continuous fun z : UpperHalfPlane => (π : ℂ) ^ (2 : ℕ) * (Δ z) ^ (2 : ℕ) :=
      continuous_const.mul hΔ2
    have hden_ne : ∀ z : UpperHalfPlane, (π : ℂ) ^ (2 : ℕ) * (Δ z) ^ (2 : ℕ) ≠ 0 := by
      intro z
      refine mul_ne_zero ?_ ?_
      · exact pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
      · exact pow_ne_zero 2 (Δ_ne_zero z)
    have hdenInv : Continuous fun z : UpperHalfPlane => ((π : ℂ) ^ (2 : ℕ) * (Δ z) ^ (2 : ℕ))⁻¹ :=
      Continuous.inv₀ hden hden_ne
    have hpoly : Continuous fun z : UpperHalfPlane =>
        (-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ) := by
      have h1 : Continuous fun z : UpperHalfPlane => (-49 : ℂ) * (E₄ z) ^ (3 : ℕ) :=
        continuous_const.mul (hE4.pow 3)
      have h2 : Continuous fun z : UpperHalfPlane => (25 : ℂ) * (E₆ z) ^ (2 : ℕ) :=
        continuous_const.mul (hE6.pow 2)
      simpa [add_assoc] using! h1.add h2
    have hnum : Continuous fun z : UpperHalfPlane =>
        (-36 : ℂ) * ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) :=
      continuous_const.mul hpoly
    exact Continuous.fun_mul hnum hdenInv
  assumption

/-- Continuity of `varphi₂Residual : ℍ → ℂ`. -/
public lemma continuous_varphi₂Residual : Continuous (varphi₂Residual : UpperHalfPlane → ℂ) := by
  -- `varphi₂Residual` is a rational expression in `varphi₂` and `q`.
  have hq2 : Continuous fun z : UpperHalfPlane => (q (z : ℂ)) ^ (2 : ℕ) := continuous_qH.pow 2
  have hnum :
      Continuous
        (fun z : UpperHalfPlane => (Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) - c864) :=
    (continuous_varphi₂.mul hq2).sub continuous_const
  have hden_ne : ∀ z : UpperHalfPlane, q (z : ℂ) ≠ 0 := by
    intro z
    exact q_ne_zero (z : ℂ)
  have hdenInv : Continuous fun z : UpperHalfPlane => (q (z : ℂ))⁻¹ :=
    Continuous.inv₀ continuous_qH hden_ne
  have hmain :
      Continuous
        (fun z : UpperHalfPlane =>
          ((Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) - c864) * (q (z : ℂ))⁻¹) :=
    hnum.mul hdenInv
  simpa [varphi₂Residual, div_eq_mul_inv, mul_assoc] using! hmain

end SpecialValuesDeriv

namespace SpecialValuesDeriv

open scoped Real Topology
open Filter Complex MeasureTheory Set intervalIntegral
open RealIntegrals RealIntegrals.ComplexIntegrands

/-- Unfold `tailRemIntegrand` on the branch `t > 0`. -/
public lemma tailRemIntegrand_eq_of_pos {u t : ℝ} (ht : 0 < t) :
    tailRemIntegrand u t =
      let zH : UpperHalfPlane := ⟨(t : ℂ) * Complex.I, by simpa [Complex.mul_I_im] using! ht⟩
      let z : ℂ := (t : ℂ) * Complex.I
      ((z ^ (2 : ℕ)) * varphi zH + z * varphi₁ zH + varphi₂Residual zH / q z) *
        (Real.exp (-Real.pi * u * t) : ℂ) := by
  simp [tailRemIntegrand, ht]

/-- On the tail `t > 1`, rewrite `tailRemIntegrand` as `Φ₅'` minus the singular exponential term. -/
public lemma tailRemIntegrand_eq_sub_sing (u t : ℝ) (ht : 1 < t) :
    tailRemIntegrand u t =
      Φ₅' u ((t : ℂ) * Complex.I) - c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  set zH : UpperHalfPlane := ⟨(t : ℂ) * Complex.I, by simpa [Complex.mul_I_im] using! ht0⟩
  set z : ℂ := (t : ℂ) * Complex.I
  have hΦ : Φ₅' u z =
      (z ^ (2 : ℕ) * varphi zH + z * varphi₁ zH + varphi₂ zH) *
        (Real.exp (-Real.pi * u * t) : ℂ) := by
    simpa [z, zH, add_assoc] using! (Φ₅'_imag_axis_rewrite (u := u) (t := t) ht0)
  have hvarphi₂ :
      varphi₂ zH = c864 / (q z) ^ (2 : ℕ) + varphi₂Residual zH / q z := by
    simpa [z] using! (varphi₂_eq_c864_div_q_sq_add_residual_div_q (z := zH))
  -- Identify the remainder piece with `tailRemIntegrand`.
  have hrem :
      tailRemIntegrand u t =
        (z ^ (2 : ℕ) * varphi zH + z * varphi₁ zH + varphi₂Residual zH / q z) *
          (Real.exp (-Real.pi * u * t) : ℂ) := by
    simp [tailRemIntegrand_eq_of_pos (u := u) (t := t) ht0, zH, z]
  -- The singular piece is exactly the `c864/q^2` term.
  have hsing :
      (c864 / (q z) ^ (2 : ℕ)) * (Real.exp (-Real.pi * u * t) : ℂ) =
        c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
    simpa [z] using! (sing_piece_eq (u := u) (t := t))
  -- Now `Φ₅' = tailRemIntegrand + (c864/q^2)*exp(-π u t)`.
  grind only

/-- Integrability of `tailRemIntegrand u` on `(1,∞)` for `u > 4`. -/
public lemma integrable_tailRemIntegrand (u : ℝ) (hu : 4 < u) :
    Integrable (fun t : ℝ => tailRemIntegrand u t) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  have hIntΦ : Integrable (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) μ :=
    LaplaceZerosTail.TailDeform.integrable_imag_axis_Φ₅' (u := u) hu
  let b : ℝ := Real.pi * (u - 4)
  have hb : 0 < b := by
    simpa [b] using! (mul_pos Real.pi_pos (sub_pos.2 hu))
  have hIntExpOn₀ :
      IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Set.Ici (1 : ℝ)) volume := by
    simpa [pow_zero] using!
      (ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := b) hb)
  have hIntExpOn :
      IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * (u - 4) * t)) (Set.Ici (1 : ℝ)) volume := by
    refine IntegrableOn.congr_fun hIntExpOn₀ ?_ measurableSet_Ici
    intro t ht
    have : (-b) * t = (-Real.pi) * (u - 4) * t := by
      simp [b, mul_assoc]
    simp [mul_assoc, this]
  have hIntExp : Integrable (fun t : ℝ => Real.exp (-Real.pi * (u - 4) * t)) μ := by
    have h' :
        IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * (u - 4) * t)) (Set.Ioi (1 : ℝ)) volume :=
      hIntExpOn.mono_set (by
        intro t ht
        exact le_of_lt (by simpa [Set.mem_Ioi] using! ht))
    simpa [MeasureTheory.IntegrableOn, μ] using! h'
  have hIntExpC : Integrable (fun t : ℝ => (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) μ := by
    simpa [Complex.ofRealCLM_apply] using! (Complex.ofRealCLM.integrable_comp hIntExp)
  have hIntSing :
      Integrable (fun t : ℝ => c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) μ :=
    hIntExpC.const_mul c864
  have hAE :
      (fun t : ℝ => tailRemIntegrand u t) =ᵐ[μ]
        fun t : ℝ =>
          Φ₅' u ((t : ℂ) * Complex.I) - c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 1 < t := by simpa [Set.mem_Ioi] using! ht
    exact tailRemIntegrand_eq_sub_sing (u := u) (t := t) ht'
  have hIntDiff :
      Integrable
          (fun t : ℝ =>
            Φ₅' u ((t : ℂ) * Complex.I) - c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) μ :=
    hIntΦ.sub hIntSing
  exact (hIntDiff.congr hAE.symm)

/-- For `u > 4`, split `Vtail u` into the integrable remainder `tailRem u` plus the singular term
`tailSing u`. -/
public lemma Vtail_eq_tailRem_add_tailSing (u : ℝ) (hu : 4 < u) :
    Vtail u = tailRem u + tailSing u := by
  -- Work with the restricted measure on `(1,∞)`.
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  have hIntΦ : Integrable (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) μ :=
    LaplaceZerosTail.TailDeform.integrable_imag_axis_Φ₅' (u := u) hu
  -- The singular term is integrable for `u>4`.
  let b : ℝ := Real.pi * (u - 4)
  have hb : 0 < b := by
    simpa [b] using! (mul_pos Real.pi_pos (sub_pos.2 hu))
  have hIntExpOn₀ :
      IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Set.Ici (1 : ℝ)) volume := by
    simpa [pow_zero] using!
      (ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := b) hb)
  have hIntExpOn :
      IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * (u - 4) * t)) (Set.Ici (1 : ℝ)) volume := by
    refine IntegrableOn.congr_fun hIntExpOn₀ ?_ measurableSet_Ici
    intro t ht
    have : (-b) * t = (-Real.pi) * (u - 4) * t := by
      simp [b, mul_assoc]
    simp [mul_assoc, this]
  have hIntExp : Integrable (fun t : ℝ => Real.exp (-Real.pi * (u - 4) * t)) μ := by
    have h' :
        IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * (u - 4) * t)) (Set.Ioi (1 : ℝ)) volume :=
      hIntExpOn.mono_set (by
        intro t ht
        exact le_of_lt (by simpa [Set.mem_Ioi] using! ht))
    simpa [MeasureTheory.IntegrableOn, μ] using! h'
  have hIntExpC : Integrable (fun t : ℝ => (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) μ := by
    simpa [Complex.ofRealCLM_apply] using! (Complex.ofRealCLM.integrable_comp hIntExp)
  have hIntSing :
      Integrable (fun t : ℝ => c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) μ :=
    hIntExpC.const_mul c864
  -- Almost-everywhere rewrite of `tailRemIntegrand` on `(1,∞)`.
  have hAE :
      (fun t : ℝ => tailRemIntegrand u t) =ᵐ[μ]
        fun t : ℝ =>
          Φ₅' u ((t : ℂ) * Complex.I) - c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 1 < t := by simpa [Set.mem_Ioi] using! ht
    exact tailRemIntegrand_eq_sub_sing (u := u) (t := t) ht'
  have hIntDiff :
      Integrable
          (fun t : ℝ =>
            Φ₅' u ((t : ℂ) * Complex.I) - c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) μ :=
    hIntΦ.sub hIntSing
  have hIntRem : Integrable (fun t : ℝ => tailRemIntegrand u t) μ := hIntDiff.congr hAE.symm
  -- Rewrite `tailRem u` as an integral of a difference.
  have hRem :
      tailRem u =
        ∫ t : ℝ in Set.Ioi (1 : ℝ),
          (Φ₅' u ((t : ℂ) * Complex.I) - c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) := by
    have := MeasureTheory.integral_congr_ae hAE
    -- `this` already has the right direction.
    simpa [tailRem, μ] using! this
  -- Compute this integral as a difference of integrals.
  have hRem' :
      tailRem u =
        (∫ t : ℝ in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) -
          ∫ t : ℝ in Set.Ioi (1 : ℝ), c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
    have hsub :=
      (MeasureTheory.integral_sub (f := fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I))
        (g := fun t : ℝ => c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) hIntΦ hIntSing)
    -- Replace the LHS by `tailRem u` using `hRem`.
    simpa [hRem] using! hsub
  -- Identify the singular integral with `tailSing u`.
  have hSing :
      (∫ t : ℝ in Set.Ioi (1 : ℝ), c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) =
        tailSing u := by
    -- Pull out `c864` and use `integral_ofReal` on the restricted measure `μ`.
    have hcast :
        (∫ t : ℝ in Set.Ioi (1 : ℝ), (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) = singIntC u := by
      -- `integral_ofReal` converts the `ℂ`-integral of a real-valued function
      -- into the cast of the `ℝ`-integral.
      have h :=
        (integral_ofReal (μ := μ) (𝕜 := ℂ) (f := fun t : ℝ => Real.exp (-Real.pi * (u - 4) * t)))
      -- Rewrite both sides as set integrals with `volume`.
      simpa [singIntC, singInt, μ] using! h
    calc
      (∫ t : ℝ in Set.Ioi (1 : ℝ), c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) =
          c864 * ∫ t : ℝ in Set.Ioi (1 : ℝ), (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
            simp [MeasureTheory.integral_const_mul, mul_assoc]
      _ = c864 * singIntC u := by
            simpa using! congrArg (fun z : ℂ => c864 * z) hcast
      _ = tailSing u := by simp [tailSing]
  -- Solve for `Vtail u`.
  have hV : Vtail u = ∫ t : ℝ in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I) := rfl
  -- From `tailRem = ∫ Φ₅' - ∫ sing` we get `∫ Φ₅' = tailRem + ∫ sing`.
  have : (∫ t : ℝ in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
      tailRem u + ∫ t : ℝ in Set.Ioi (1 : ℝ), c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ) := by
    -- Rearrange `hRem'` in the additive group `ℂ`.
    have hA :
        tailRem u + (∫ t : ℝ in Set.Ioi (1 : ℝ), c864 * (Real.exp (-Real.pi * (u - 4) * t) : ℂ)) =
          ∫ t : ℝ in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I) :=
      (eq_sub_iff_add_eq).1 hRem'
    simpa using! hA.symm
  -- Conclude.
  rw [hV, this, hSing]

end SpecialValuesDeriv


end

end SpherePacking.Dim24
