-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import SpherePacking.Dim24.MagicFunction.F.Laplace.KernelTools


/-!
# Leading correction for the Laplace B-kernel

This file defines the explicit leading term subtracted from `BKernel` on the tail `t ≥ 1` and
evaluates its Laplace transform in the convergent range `u > 2`.

## Main definitions
* `BleadBase`
* `Blead`

## Main statement
* `integral_Ioi_one_Blead_mul_exp_neg_pi`
-/

namespace SpherePacking.Dim24.LaplaceBleading

noncomputable section

open scoped Real
open scoped Topology

open Filter Set MeasureTheory Real

/-- The scalar part of the leading term subtracted from `BKernel` on the tail `t ≥ 1`. -/
@[expose] public def BleadBase (t : ℝ) : ℝ :=
  (1 / 39 : ℝ) * t - (10 / (117 * Real.pi) : ℝ)

/-- The full leading term `((1/39) t - 10/(117π)) e^{2π t}`. -/
@[expose] public def Blead (t : ℝ) : ℝ :=
  BleadBase t * Real.exp (2 * Real.pi * t)

lemma integral_Ioi_one_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    (∫ t : ℝ in Ioi (1 : ℝ), Real.exp (-c * t)) = Real.exp (-c) / c := by
  simpa [neg_mul, mul_assoc, div_eq_mul_inv] using!
    (integral_exp_mul_Ioi (a := -c) (by linarith) (c := (1 : ℝ)))

lemma integral_Ioi_one_mul_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    (∫ t : ℝ in Ioi (1 : ℝ), t * Real.exp (-c * t)) =
      Real.exp (-c) * (1 / c + 1 / c ^ (2 : ℕ)) := by
  -- Choose a primitive with derivative `-t * exp(-c*t)`.
  let g : ℝ → ℝ := fun t => (t / c + 1 / c ^ (2 : ℕ)) * Real.exp (-c * t)
  have hgderiv : ∀ t ∈ Ici (1 : ℝ), HasDerivAt g (-(t * Real.exp (-c * t))) t := by
    intro t ht
    have hc0 : c ≠ 0 := ne_of_gt hc
    -- Differentiate `g(t) = h(t) * exp(-c*t)` where `h(t) = t/c + 1/c^2`.
    have hlin : HasDerivAt (fun t : ℝ => t / c + 1 / c ^ (2 : ℕ)) (1 / c) t := by
      have hdiv : HasDerivAt (fun t : ℝ => t / c) (1 / c) t := by
        -- `t / c = (1/c) * t`.
        simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using!
          (hasDerivAt_id t).const_mul (1 / c)
      -- Avoid function addition bookkeeping by using the `add_const` lemma.
      simpa using! (hdiv.add_const (1 / c ^ (2 : ℕ)))
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-c * t)) ((-c) * Real.exp (-c * t)) t := by
      -- `d/dt exp(-c*t) = (-c) * exp(-c*t)`.
      -- Use the derivative chain `t ↦ t * c ↦ -(t * c) ↦ exp (-(t*c))`, then commute factors.
      have h :=
        ((hasDerivAt_id t).const_mul c).neg.exp
      -- `h` proves `HasDerivAt (fun t ↦ exp (-(t*c))) (exp (-(t*c)) * (-c)) t`.
      simpa [mul_assoc, mul_left_comm, mul_comm] using! h
    have hprod :
        HasDerivAt
          (fun t : ℝ => (t / c + 1 / c ^ (2 : ℕ)) * Real.exp (-c * t))
          ((1 / c) * Real.exp (-c * t) +
            (t / c + 1 / c ^ (2 : ℕ)) * ((-c) * Real.exp (-c * t))) t :=
      hlin.mul hexp
    -- Simplify the derivative expression to `-(t * exp(-c*t))`.
    have hsimp :
        (1 / c) * Real.exp (-c * t) +
              (t / c + 1 / c ^ (2 : ℕ)) * ((-c) * Real.exp (-c * t)) =
            -(t * Real.exp (-c * t)) := by
      field_simp [hc0]
      ring
    have hprod' := hprod.congr_deriv hsimp
    simpa [g] using! hprod'
  have hgneg : ∀ t ∈ Ioi (1 : ℝ), (-(t * Real.exp (-c * t))) ≤ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by norm_num) (le_of_lt ht)
    have hexp0 : 0 ≤ Real.exp (-c * t) := (Real.exp_pos _).le
    have hmul : 0 ≤ t * Real.exp (-c * t) := mul_nonneg ht0 hexp0
    simpa using! (neg_nonpos.2 hmul)
  have hgtendsto : Tendsto g atTop (𝓝 (0 : ℝ)) := by
    -- Each term in `g` is a polynomial times an exponentially decaying factor.
    have hc' : 0 < c := hc
    have h1 : Tendsto (fun t : ℝ => t * Real.exp (-c * t)) atTop (𝓝 (0 : ℝ)) := by
      simpa [Real.rpow_one]
        using! (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (1 : ℝ)) (b := c) hc')
    have h2 : Tendsto (fun t : ℝ => Real.exp (-c * t)) atTop (𝓝 (0 : ℝ)) := by
      -- Use `s = 0` in the general `x^s * exp(-b*x) → 0` lemma.
      simpa [Real.rpow_zero, one_mul] using!
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (0 : ℝ)) (b := c) hc')
    -- Rewrite `g` as `((t/c + const) * exp(-c*t)) = (t/c)*exp(-c*t) + const*exp(-c*t)`.
    have hdecomp :
        (fun t : ℝ => (t / c + 1 / c ^ (2 : ℕ)) * Real.exp (-c * t)) =
          (fun t : ℝ => (t / c) * Real.exp (-c * t) + (1 / c ^ (2 : ℕ)) * Real.exp (-c * t)) := by
      funext t
      ring
    -- Show both summands tend to `0`.
    have h3 : Tendsto (fun t : ℝ => (t / c) * Real.exp (-c * t)) atTop (𝓝 (0 : ℝ)) := by
      -- `(t/c) * exp(-c*t) = (1/c) * (t * exp(-c*t))`.
      have : (fun t : ℝ => (t / c) * Real.exp (-c * t)) =
          fun t : ℝ => (1 / c) * (t * Real.exp (-c * t)) := by
        grind only
      rw [this]
      simpa [mul_assoc] using! (tendsto_const_nhds.mul h1)
    have h4 : Tendsto (fun t : ℝ => (1 / c ^ (2 : ℕ)) * Real.exp (-c * t)) atTop (𝓝 (0 : ℝ)) := by
      simpa using! (tendsto_const_nhds.mul h2)
    have :
        Tendsto
          (fun t : ℝ =>
            (t / c) * Real.exp (-c * t) + (1 / c ^ (2 : ℕ)) * Real.exp (-c * t))
          atTop (𝓝 (0 + 0)) :=
      h3.add h4
    simpa [g, hdecomp] using! this
  -- Integrate the derivative on `(1,∞)` and solve for the target integral.
  have hint :
      ∫ t : ℝ in Ioi (1 : ℝ), (-(t * Real.exp (-c * t))) = (0 : ℝ) - g 1 := by
    exact integral_Ioi_of_hasDerivAt_of_nonpos' hgderiv hgneg hgtendsto
  have : (∫ t : ℝ in Ioi (1 : ℝ), t * Real.exp (-c * t)) = g 1 := by
    have hneg :
        -∫ t : ℝ in Ioi (1 : ℝ), t * Real.exp (-c * t) = (0 : ℝ) - g 1 := by
      simpa [MeasureTheory.integral_neg] using! hint
    have hneg' : -∫ t : ℝ in Ioi (1 : ℝ), t * Real.exp (-c * t) = -g 1 := by
      simpa using! hneg
    have := congrArg Neg.neg hneg'
    simpa using! this
  -- Simplify `g 1`.
  -- `simp` leaves `c⁻¹ * exp(-c) + (c^2)⁻¹ * exp(-c)`; rewrite as a factored form.
  grind only

/-- Evaluate the tail integral of the exponential leading term
(valid in the convergent range `2 < u`). -/
public lemma integral_Ioi_one_Blead_mul_exp_neg_pi (u : ℝ) (hu : 2 < u) :
    (∫ t in Ioi (1 : ℝ), (Blead t) * Real.exp (-Real.pi * u * t)) =
      ((10 - 3 * Real.pi) * (2 - u) + 3) /
          (117 * (Real.pi ^ (2 : ℕ)) * (u - 2) ^ (2 : ℕ)) *
        Real.exp (-Real.pi * (u - 2)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc : 0 < Real.pi * (u - 2) := by nlinarith
  -- Rewrite the integrand as `((1/39)*t - 10/(117π)) * exp(-π(u-2)t)`.
  have hrew :
      (fun t : ℝ => Blead t * Real.exp (-Real.pi * u * t)) =
        fun t : ℝ => BleadBase t * Real.exp (-(Real.pi * (u - 2)) * t) := by
    funext t
    have hexp :
        Real.exp (2 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
          Real.exp (-(Real.pi * (u - 2)) * t) := by
      have h1 :
          (2 * Real.pi * t) + (-(Real.pi * u * t)) = (-(Real.pi * (u - 2))) * t := by ring
      calc
        Real.exp (2 * Real.pi * t) * Real.exp (-Real.pi * u * t)
            = Real.exp ((2 * Real.pi * t) + (-Real.pi * u * t)) :=
                (Real.exp_add (2 * Real.pi * t) (-Real.pi * u * t)).symm
        _ = Real.exp ((-(Real.pi * (u - 2))) * t) := by simp [h1]
    -- Reassociate and substitute the combined exponential factor.
    calc
      Blead t * Real.exp (-Real.pi * u * t)
          = BleadBase t * (Real.exp (2 * Real.pi * t) * Real.exp (-Real.pi * u * t)) := by
              -- only associativity, avoid `simp`'s cancellation lemmas
              simp [Blead, mul_assoc]
      _ = BleadBase t * Real.exp (-(Real.pi * (u - 2)) * t) := by
            simpa [mul_assoc] using! congrArg (fun x => BleadBase t * x) hexp
  simp_rw [hrew]
  -- Evaluate the two basic tail integrals and assemble the coefficients.
  have h0 :
      (∫ t : ℝ in Ioi (1 : ℝ), Real.exp (-(Real.pi * (u - 2)) * t)) =
        Real.exp (-(Real.pi * (u - 2))) / (Real.pi * (u - 2)) := by
    simpa [mul_assoc, neg_mul] using!
      integral_Ioi_one_exp_neg_mul (c := Real.pi * (u - 2)) hc
  have h1 :
      (∫ t : ℝ in Ioi (1 : ℝ), t * Real.exp (-(Real.pi * (u - 2)) * t)) =
        Real.exp (-(Real.pi * (u - 2))) *
          (1 / (Real.pi * (u - 2)) + 1 / (Real.pi * (u - 2)) ^ (2 : ℕ)) := by
    simpa [mul_assoc, neg_mul] using!
      integral_Ioi_one_mul_exp_neg_mul (c := Real.pi * (u - 2)) hc
  have hpi0 : Real.pi ≠ 0 := ne_of_gt hpi
  have hu2 : u - 2 ≠ 0 := by linarith
  have hc0 : Real.pi * (u - 2) ≠ 0 := mul_ne_zero hpi0 hu2
  have hInt_exp :
      IntegrableOn (fun t : ℝ => Real.exp (-(Real.pi * (u - 2)) * t)) (Ioi (1 : ℝ)) volume := by
    -- `n=0` case of the standard exponential decay integrability lemma.
    simpa [pow_zero, one_mul, mul_assoc] using!
      (LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic.integrableOn_pow_mul_exp_neg_mul_Ioi_one
        (n := 0) (b := Real.pi * (u - 2)) hc)
  have hInt_tExp :
      IntegrableOn (fun t : ℝ => t * Real.exp (-(Real.pi * (u - 2)) * t)) (Ioi (1 : ℝ)) volume := by
    -- `n=1` case.
    simpa [pow_one, mul_assoc] using!
      (LaplaceTmp.LaplaceFourierCont.LaplaceBKernelAnalytic.integrableOn_pow_mul_exp_neg_mul_Ioi_one
        (n := 1) (b := Real.pi * (u - 2)) hc)
  -- Normalization lemma for the exponential factor:
  -- we often see both `-(π*(u-2))*t` and `-(π*((u-2)*t))`.
  have hexpAssoc (t : ℝ) :
      Real.exp (-(Real.pi * ((u - 2) * t))) = Real.exp (-(Real.pi * (u - 2)) * t) := by
    congr 1
    ring
  have hsplit :
      (∫ t : ℝ in Ioi (1 : ℝ), BleadBase t * Real.exp (-(Real.pi * (u - 2)) * t)) =
        (1 / 39 : ℝ) * (∫ t : ℝ in Ioi (1 : ℝ), t * Real.exp (-(Real.pi * (u - 2)) * t)) -
          (10 / (117 * Real.pi) : ℝ) *
            (∫ t : ℝ in Ioi (1 : ℝ), Real.exp (-(Real.pi * (u - 2)) * t)) := by
    -- Use linearity of the integral on the restricted measure.
    let μ : Measure ℝ := volume.restrict (Ioi (1 : ℝ))
    have hI_t : Integrable (fun t : ℝ => t * Real.exp (-(Real.pi * (u - 2)) * t)) μ := by
      simpa [μ, MeasureTheory.IntegrableOn] using! hInt_tExp
    have hI_e : Integrable (fun t : ℝ => Real.exp (-(Real.pi * (u - 2)) * t)) μ := by
      simpa [μ, MeasureTheory.IntegrableOn] using! hInt_exp
    set a : ℝ := (1 / 39 : ℝ)
    set b : ℝ := (10 / (117 * Real.pi) : ℝ)
    have hI_a : Integrable (fun t : ℝ => a * (t * Real.exp (-(Real.pi * (u - 2)) * t))) μ :=
      hI_t.const_mul a
    have hI_b : Integrable (fun t : ℝ => b * Real.exp (-(Real.pi * (u - 2)) * t)) μ :=
      hI_e.const_mul b
    have hpoint :
        (fun t : ℝ => BleadBase t * Real.exp (-(Real.pi * (u - 2)) * t)) =
          (fun t : ℝ => a * (t * Real.exp (-(Real.pi * (u - 2)) * t)) -
            b * Real.exp (-(Real.pi * (u - 2)) * t)) := by
      funext t
      simp [BleadBase, a, b, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm,
        mul_comm]
    have hsub :
        (∫ t, (a * (t * Real.exp (-(Real.pi * (u - 2)) * t)) -
              b * Real.exp (-(Real.pi * (u - 2)) * t)) ∂μ) =
          (∫ t, a * (t * Real.exp (-(Real.pi * (u - 2)) * t)) ∂μ) -
            (∫ t, b * Real.exp (-(Real.pi * (u - 2)) * t) ∂μ) := by
      simpa using! (MeasureTheory.integral_sub hI_a hI_b)
    have hA :
        (∫ t, a * (t * Real.exp (-(Real.pi * (u - 2)) * t)) ∂μ) =
          a * (∫ t, t * Real.exp (-(Real.pi * (u - 2)) * t) ∂μ) :=
      integral_const_mul a fun a => a * rexp (-(π * (u - 2)) * a)
    have hB :
        (∫ t, b * Real.exp (-(Real.pi * (u - 2)) * t) ∂μ) =
          b * (∫ t, Real.exp (-(Real.pi * (u - 2)) * t) ∂μ) :=
      integral_const_mul b fun a => rexp (-(π * (u - 2)) * a)
    lia
  have hsplit' :
      (∫ t : ℝ in Ioi (1 : ℝ), BleadBase t * Real.exp (-(Real.pi * (u - 2)) * t)) =
        (1 / 39 : ℝ) *
            (Real.exp (-(Real.pi * (u - 2))) *
              (1 / (Real.pi * (u - 2)) + 1 / (Real.pi * (u - 2)) ^ (2 : ℕ))) -
          (10 / (117 * Real.pi) : ℝ) *
            (Real.exp (-(Real.pi * (u - 2))) / (Real.pi * (u - 2))) := by
    -- Substitute the evaluated tail integrals into `hsplit`.
    lia
  -- Finish by rewriting the integral via `hsplit'` and simplifying the remaining scalar identity.
  rw [hsplit']
  field_simp [hpi0, hu2]
  ring_nf

end

end SpherePacking.Dim24.LaplaceBleading
