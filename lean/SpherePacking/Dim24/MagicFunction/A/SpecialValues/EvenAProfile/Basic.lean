-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi2
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi1C


/-!
# Even special values `u = 2,4`

We evaluate the even special values by moving the period integral to height `m → ∞` using the
rectangle identity `SpecialValuesAux.strip_identity_varphi₁_mul_expU`, and then applying the
`atImInfty` limit of `varphi₁(z) * exp(2π i z)`.

## Main statements
* `SpecialValuesEvenAProfile.intervalIntegrable_varphi₁'_mul_expU`
* `SpecialValuesEvenAProfile.integral_varphi₁'_height_one`
* `SpecialValuesEvenAProfile.integral_varphi₁'_mul_expU_two_height_one`
-/

open scoped Real

namespace SpherePacking.Dim24

noncomputable section


namespace SpecialValuesEvenAProfile

open scoped Interval Real Topology
open Filter Complex UpperHalfPlane intervalIntegral MeasureTheory Set

/-- Interval integrability of `x ↦ varphi₁' (x + m i) * expU u (x + m i)` for `m > 0`. -/
public lemma intervalIntegrable_varphi₁'_mul_expU (u : ℝ) {m : ℝ} (hm0 : 0 < m) :
    IntervalIntegrable
        (fun x : ℝ =>
          SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
            SpecialValuesAux.expU u ((x : ℂ) + m * Complex.I))
        volume (0 : ℝ) 1 := by
  let f : ℝ → ℂ := fun x => (x : ℂ) + (m : ℂ) * Complex.I
  have hf : Continuous f := (continuous_ofReal.add continuous_const)
  have hfIm : ∀ x : ℝ, 0 < (f x).im := by
    intro x
    simpa [f, Complex.add_im] using! hm0
  let zH : ℝ → ℍ := fun x => ⟨f x, hfIm x⟩
  have hzH : Continuous zH := by
    simpa [zH] using! Continuous.upperHalfPlaneMk hf hfIm
  have hvarphi : Continuous fun x : ℝ => varphi₁ (zH x) :=
    SpecialValuesAux.continuous_varphi₁.comp hzH
  have hexp : Continuous fun x : ℝ => SpecialValuesAux.expU u (f x) := by
    -- `expU` is `Complex.exp` of an affine-linear function.
    unfold SpecialValuesAux.expU
    fun_prop
  have hcont : Continuous fun x : ℝ => (varphi₁ (zH x)) * SpecialValuesAux.expU u (f x) :=
    hvarphi.mul hexp
  have hEq :
      (fun x : ℝ =>
          SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
            SpecialValuesAux.expU u ((x : ℂ) + m * Complex.I)) =
        fun x : ℝ => (varphi₁ (zH x)) * SpecialValuesAux.expU u (f x) := by
    funext x
    simp [SpecialValuesAux.varphi₁', f, zH, hm0]
  simpa [hEq, f] using! (hcont.intervalIntegrable (μ := volume) (0 : ℝ) 1)

/-!
### The special value `aProfile 0`

We show that the height integral of `varphi₁` tends to the constant term of the `q`-expansion.
The pole term `c₁/q` integrates to `0` over one period in `re z`.
-/

lemma integral_cexp_neg_two_pi_mul_I :
    (∫ x : ℝ in (0 : ℝ)..1, cexp ((-2 * Real.pi * Complex.I) * (x : ℂ))) = (0 : ℂ) := by
  -- Use the primitive `exp(c*t)/c` and evaluate at the endpoints.
  let c : ℂ := -2 * (Real.pi : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    have h2 : (-2 : ℂ) ≠ 0 := by norm_num
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt Real.pi_pos)
    have hmul : ((-2 : ℂ) * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero h2 hpi
    dsimp [c]
    exact mul_ne_zero hmul Complex.I_ne_zero
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => cexp (c * (t : ℂ)) / c) (cexp (c * (x : ℂ))) x := by
    intro x hx
    have hmul : HasDerivAt (fun z : ℂ => c * z) c (x : ℂ) := by
      simpa using! (hasDerivAt_const_mul (x := (x : ℂ)) c)
    have hexp : HasDerivAt (fun z : ℂ => cexp (c * z)) (cexp (c * (x : ℂ)) * c) (x : ℂ) := by
      simpa using! (Complex.hasDerivAt_exp (c * (x : ℂ))).comp (x : ℂ) hmul
    have hexpR : HasDerivAt (fun t : ℝ => cexp (c * (t : ℂ))) (cexp (c * (x : ℂ)) * c) x :=
      hexp.comp_ofReal
    simpa [div_eq_mul_inv, mul_assoc, hc] using! hexpR.mul_const (c⁻¹)
  have hint :
      (∫ x : ℝ in (0 : ℝ)..1, cexp (c * (x : ℂ))) =
        (cexp (c * ((1 : ℝ) : ℂ)) / c) - (cexp (c * ((0 : ℝ) : ℂ)) / c) := by
    have hcont :
        IntervalIntegrable (fun x : ℝ => cexp (c * (x : ℂ))) MeasureTheory.volume (0 : ℝ) 1 := by
      have hcont' : Continuous fun x : ℝ => cexp (c * (x : ℂ)) := by fun_prop
      exact hcont'.intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
    simpa using!
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => cexp (c * (t : ℂ)) / c)
        (f' := fun x : ℝ => cexp (c * (x : ℂ))) hderiv hcont)
  have hc0 : cexp (c * ((0 : ℝ) : ℂ)) = (1 : ℂ) := by simp [c]
  have hc1 : cexp (c * ((1 : ℝ) : ℂ)) = (1 : ℂ) := by
    -- `exp (-2π i) = 1`.
    have : c = (-1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      simp [c, mul_left_comm, mul_comm]
    -- Use the integer periodicity lemma.
    simpa [c, this, mul_assoc] using! (Complex.exp_int_mul_two_pi_mul_I (-1))
  have hc1c : cexp c = (1 : ℂ) := by
    simpa using! hc1
  -- Finish.
  have : (∫ x : ℝ in (0 : ℝ)..1, cexp (c * (x : ℂ))) = 0 := by
    -- Evaluate the primitive: `(1/c) - (1/c) = 0`.
    -- Use the simplified endpoint identity `cexp c = 1`.
    rw [hint]
    simp [hc1c, div_eq_mul_inv]
  simpa [c] using! this

lemma inv_q_line (m x : ℝ) :
    (SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I))⁻¹ =
      cexp ((2 * (π : ℂ)) * (m : ℂ)) * cexp ((-2 * (π : ℂ) * Complex.I) * (x : ℂ)) := by
  -- Unfold `q` and compute `q(x+mi) = exp(-2π m) * exp(2π i x)`, then invert.
  unfold SpecialValuesVarphi₁Limits.q
  have hinv :
      (cexp (2 * (π : ℂ) * Complex.I * ((x : ℂ) + (m : ℂ) * Complex.I)))⁻¹ =
        cexp (-(2 * (π : ℂ) * Complex.I * ((x : ℂ) + (m : ℂ) * Complex.I))) := by
    simpa using!
      (Complex.exp_neg (2 * (π : ℂ) * Complex.I * ((x : ℂ) + (m : ℂ) * Complex.I))).symm
  -- Rewrite the negated exponent and split the exponential of a sum.
  -- The key computation is `-(2π i * (m i)) = 2π m`.
  rw [hinv]
  have hexp :
      -(2 * (π : ℂ) * Complex.I * ((x : ℂ) + (m : ℂ) * Complex.I)) =
        (2 * (π : ℂ) * (m : ℂ)) + (-2 * (π : ℂ) * Complex.I) * (x : ℂ) := by
    ring_nf
    simp [mul_assoc, mul_left_comm, mul_comm, add_comm]
  rw [hexp]
  simp [Complex.exp_add, mul_assoc]

lemma integral_const_div_q (c₁ : ℂ) (m : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..1, c₁ / SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I)) =
      (0 : ℂ) := by
  -- Reduce to the integral of `exp(-2π i x)`.
  have hq :
      (fun x : ℝ => (SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I))⁻¹) =
        fun x : ℝ =>
          cexp ((2 * (π : ℂ)) * (m : ℂ)) * cexp ((-2 * (π : ℂ) * Complex.I) * (x : ℂ)) := by
    funext x
    simpa using! (inv_q_line (m := m) (x := x))
  have hInt :
      (∫ x : ℝ in (0 : ℝ)..1, cexp ((-2 * (π : ℂ) * Complex.I) * (x : ℂ))) = (0 : ℂ) := by
    simpa using! integral_cexp_neg_two_pi_mul_I
  -- Pull out the constant factors.
  calc
    (∫ x : ℝ in (0 : ℝ)..1, c₁ / SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I)) =
        (∫ x : ℝ in (0 : ℝ)..1,
          c₁ * (SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I))⁻¹) := by
          simp [div_eq_mul_inv]
    _ = c₁ * ∫ x : ℝ in (0 : ℝ)..1, (SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I))⁻¹ := by
          simp [intervalIntegral.integral_const_mul]
    _ = c₁ * ∫ x : ℝ in (0 : ℝ)..1,
          cexp ((2 * (π : ℂ)) * (m : ℂ)) * cexp ((-2 * (π : ℂ) * Complex.I) * (x : ℂ)) := by
          simp [hq]
    _ = c₁ * (cexp ((2 * (π : ℂ)) * (m : ℂ)) *
          ∫ x : ℝ in (0 : ℝ)..1, cexp ((-2 * (π : ℂ) * Complex.I) * (x : ℂ))) := by
          simp [intervalIntegral.integral_const_mul, mul_assoc]
    _ = c₁ * (cexp ((2 * (π : ℂ)) * (m : ℂ)) * (0 : ℂ)) := by
          rw [hInt]
    _ = 0 := by
          simp

lemma tendsto_top_varphi₁'_zero :
    Tendsto
      (fun m : ℝ =>
        ∫ x : ℝ in (0 : ℝ)..1, SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I))
      atTop (𝓝 ((113218560 : ℂ) * Complex.I / (π : ℂ))) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  let c₁ : ℂ := (725760 : ℂ) * Complex.I / (π : ℂ)
  let c₀ : ℂ := (113218560 : ℂ) * Complex.I / (π : ℂ)
  have hBall :
      {z : ℍ | ‖Dim24.varphi₁ z - c₁ / SpecialValuesVarphi₁Limits.q (z : ℂ) - c₀‖ < ε / 2} ∈
        atImInfty := by
    refine Filter.mem_of_superset (Filter.mem_map.mp
      (SpecialValuesVarphi₁Limits.tendsto_varphi₁_sub_const_div_q (Metric.ball_mem_nhds _ hε2)))
      fun z hz => ?_
    simpa [c₁, c₀, Metric.mem_ball, dist_eq_norm] using hz
  rcases (UpperHalfPlane.atImInfty_mem _).1 hBall with ⟨A, hA⟩
  refine ⟨max A 1, ?_⟩
  intro m hm
  have hmA : A ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_right _ _) hm
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  -- Pointwise bound on `varphi₁' - c₁/q - c₀`.
  have hbound :
      ∀ x ∈ Ι (0 : ℝ) 1,
        ‖SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) -
              c₁ / SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I) - c₀‖ ≤
            ε / 2 := by
    intro x hx
    let zH : ℍ := ⟨(x : ℂ) + (m : ℂ) * Complex.I, by simpa [Complex.add_im] using! hm0⟩
    have hz : A ≤ zH.im := by
      simpa [zH, UpperHalfPlane.im, Complex.add_im] using! hmA
    have hmem : ‖Dim24.varphi₁ zH - c₁ / SpecialValuesVarphi₁Limits.q (zH : ℂ) - c₀‖ < ε / 2 := by
      simpa using! hA zH hz
    -- Identify `varphi₁'` with `varphi₁` on the upper half plane.
    have hEq : SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) = Dim24.varphi₁ zH := by
      -- `varphi₁'` uses the positive-imaginary branch since `m > 0`.
      simp [SpecialValuesAux.varphi₁', zH, hm0, Complex.add_im]
    have :
        ‖SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) -
              c₁ / SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I) - c₀‖ <
            ε / 2 := by
      simpa [hEq, zH] using! hmem
    exact le_of_lt this
  -- Use that the pole term integrates to `0` over one period.
  have hPole :
      (∫ x : ℝ in (0 : ℝ)..1, c₁ / SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I)) =
        (0 : ℂ) :=
    integral_const_div_q (c₁ := c₁) (m := m)
  -- Bound the integral of the error term.
  have hnorm :
      ‖∫ x : ℝ in (0 : ℝ)..1,
          (SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) -
                c₁ / SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I) - c₀)‖ ≤
        ε / 2 := by
    have h :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ)) hbound
    simpa using! h
  -- Put everything together.
  have hsub :
      (∫ x : ℝ in (0 : ℝ)..1, SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I)) - c₀ =
        ∫ x : ℝ in (0 : ℝ)..1,
          (SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) -
                c₁ / SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I) - c₀) := by
    -- Expand the RHS and cancel the pole integral using `hPole`.
    let vLine : ℝ → ℂ := fun x : ℝ => SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I)
    let pole : ℝ → ℂ := fun x : ℝ => c₁ / SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I)
    have hIntVar : IntervalIntegrable vLine volume (0 : ℝ) 1 := by
      -- This is `intervalIntegrable_varphi₁'_mul_expU` with `u=0`
      -- (the exponential factor is constant).
      simpa [vLine, SpecialValuesAux.expU, mul_one] using!
        (intervalIntegrable_varphi₁'_mul_expU (u := (0 : ℝ)) (m := m) hm0)
    have hIntPole : IntervalIntegrable pole volume (0 : ℝ) 1 := by
      -- Use the explicit formula for `q` on the vertical line `x + m i`
      -- to reduce to continuity of `cexp`.
      let g : ℝ → ℂ := fun t : ℝ =>
        c₁ * (cexp ((2 * (π : ℂ)) * (m : ℂ)) * cexp ((-2 * (π : ℂ) * Complex.I) * (t : ℂ)))
      have hEq : pole = g := by
        funext t
        -- Keep the `m * I` order so that `inv_q_line` applies by definitional equality.
        calc
          pole t =
              c₁ * (SpecialValuesVarphi₁Limits.q ((t : ℂ) + m * Complex.I))⁻¹ := by
                simp [pole, div_eq_mul_inv]
          _ =
              c₁ * (cexp ((2 * (π : ℂ)) * (m : ℂ)) *
                cexp ((-2 * (π : ℂ) * Complex.I) * (t : ℂ))) := by
                simp [inv_q_line, mul_assoc]
          _ = g t := by
                simp [g, mul_assoc]
      have hcontg : Continuous g := by
        -- `g` is a product of constants and `cexp` of an affine function.
        dsimp [g]
        fun_prop
      have hIntg : IntervalIntegrable g volume (0 : ℝ) 1 := by
        simpa using! (hcontg.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)))
      simpa [hEq] using! hIntg
    have hIntConst : IntervalIntegrable (fun _x : ℝ => c₀) volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    -- Use linearity to expand `∫ (varphi₁' - pole - c₀)`.
    have hsub' :=
      (intervalIntegral.integral_sub (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun x : ℝ => vLine x - pole x) (g := fun _x : ℝ => c₀)
        (IntervalIntegrable.sub hIntVar hIntPole) hIntConst)
    have hsub'' :
        (∫ x : ℝ in (0 : ℝ)..1, vLine x - pole x) - c₀ =
          ∫ x : ℝ in (0 : ℝ)..1, (vLine x - pole x - c₀) := by
      simpa [sub_eq_add_neg, add_assoc] using! hsub'.symm
    -- Replace the `∫(varphi₁' - pole)` term by `∫ varphi₁'` using `hPole`.
    have hPole0 : (∫ x : ℝ in (0 : ℝ)..1, pole x) = (0 : ℂ) := by
      simpa [pole] using! hPole
    have hIntSub :
        (∫ x : ℝ in (0 : ℝ)..1, vLine x - pole x) = (∫ x : ℝ in (0 : ℝ)..1, vLine x) := by
      -- `∫ (f - g) = ∫ f - ∫ g`.
      have hsubInt :=
        (intervalIntegral.integral_sub (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun x : ℝ => vLine x) (g := fun x : ℝ => pole x) hIntVar hIntPole)
      -- Simplify using `hPole0`.
      simpa [hPole0, sub_eq_add_neg] using! hsubInt
    -- Finish.
    simpa [hIntSub] using! hsub''
  -- Now bound the distance to `c₀`.
  have hdist :
      dist (∫ x : ℝ in (0 : ℝ)..1, SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I)) c₀ < ε := by
    have :
        ‖(∫ x : ℝ in (0 : ℝ)..1, SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I)) - c₀‖ ≤
          ε / 2 := by
      simpa [hsub] using! hnorm
    have :
        ‖(∫ x : ℝ in (0 : ℝ)..1, SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I)) - c₀‖ <
          ε := by
      exact lt_of_le_of_lt this (half_lt_self hε)
    simpa [dist_eq_norm] using! this
  simpa [Metric.ball, dist_eq_norm, c₀] using! hdist

/-- The period integral of `varphi₁'` at height `1` (corresponding to `u = 0`). -/
public lemma integral_varphi₁'_height_one :
    (∫ x : ℝ in (0 : ℝ)..1,
        SpecialValuesAux.varphi₁' ((x : ℂ) + (1 : ℝ) * Complex.I)) =
      ((113218560 : ℂ) * Complex.I / (π : ℂ)) := by
  let bottom : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..1, SpecialValuesAux.varphi₁' ((x : ℂ) + (1 : ℝ) * Complex.I)
  let top : ℝ → ℂ := fun m : ℝ =>
    ∫ x : ℝ in (0 : ℝ)..1, SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I)
  have hu : SpecialValuesAux.expU (0 : ℝ) (1 : ℂ) = 1 := by
    simp [SpecialValuesAux.expU]
  have hEq : (fun m : ℝ => bottom) =ᶠ[atTop] top := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    have h := SpecialValuesAux.strip_identity_varphi₁_mul_expU (u := (0 : ℝ)) hu (m := m) hm
    -- `expU 0 = 1`, so the identity is exactly the equality of `varphi₁'` integrals.
    simpa [bottom, top, SpecialValuesAux.expU, mul_one] using! h
  have hTop :
      Tendsto top atTop (𝓝 ((113218560 : ℂ) * Complex.I / (π : ℂ))) :=
    tendsto_top_varphi₁'_zero
  have hBot : Tendsto (fun _m : ℝ => bottom) atTop (𝓝 ((113218560 : ℂ) * Complex.I / (π : ℂ))) :=
    hTop.congr' hEq.symm
  have : bottom = ((113218560 : ℂ) * Complex.I / (π : ℂ)) := by
    simpa using! tendsto_const_nhds_iff.mp hBot
  simpa [bottom] using! this

lemma tendsto_top_varphi₁'_mul_expU_two :
    Tendsto
      (fun m : ℝ =>
        ∫ x : ℝ in (0 : ℝ)..1,
          SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
            SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I))
      atTop (𝓝 ((725760 : ℂ) * Complex.I / (π : ℂ))) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  -- Use the `atImInfty` limit uniformly in `re z`.
  have hBall :
      {z : ℍ | ‖Dim24.varphi₁ z * SpecialValuesVarphi₁Limits.q (z : ℂ)
            - ((725760 : ℂ) * Complex.I / (π : ℂ))‖ < ε / 2} ∈ atImInfty := by
    refine Filter.mem_of_superset (Filter.mem_map.mp
      (SpecialValuesVarphi₁Limits.tendsto_varphi₁_mul_q (Metric.ball_mem_nhds _ hε2)))
      fun z hz => ?_
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  rcases (UpperHalfPlane.atImInfty_mem _).1 hBall with ⟨A, hA⟩
  refine ⟨max A 1, ?_⟩
  intro m hm
  have hmA : A ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_right _ _) hm
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  -- Pointwise bound on the integrand on `x ∈ [0,1]`.
  have hbound :
      ∀ x ∈ Ι (0 : ℝ) 1,
        ‖SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
              SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I)
            - ((725760 : ℂ) * Complex.I / (π : ℂ))‖ ≤ ε / 2 := by
    intro x hx
    let zH : ℍ := ⟨(x : ℂ) + (m : ℂ) * Complex.I, by simpa [Complex.add_im] using! hm0⟩
    have hz : A ≤ zH.im := by
      simpa [zH, UpperHalfPlane.im, Complex.add_im] using! hmA
    have hmem :
        ‖Dim24.varphi₁ zH * SpecialValuesVarphi₁Limits.q (zH : ℂ)
            - ((725760 : ℂ) * Complex.I / (π : ℂ))‖ < ε / 2 := by
      have := hA zH hz
      simpa using! this
    have hEq :
        SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
            SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I) =
          Dim24.varphi₁ zH * SpecialValuesVarphi₁Limits.q (zH : ℂ) := by
      simp [SpecialValuesAux.varphi₁', SpecialValuesAux.expU, SpecialValuesVarphi₁Limits.q, zH, hm0,
        mul_assoc, mul_left_comm, mul_comm]
    rw [hEq]
    exact hmem.le
  -- Rewrite the difference of integrals as the integral of the difference.
  have hInt :
      IntervalIntegrable
        (fun x : ℝ =>
          SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
            SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I))
        MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_varphi₁'_mul_expU (u := (2 : ℝ)) (m := m) hm0
  have hIntConst :
      IntervalIntegrable (fun _x : ℝ => ((725760 : ℂ) * Complex.I / (π : ℂ)))
        MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hsub :
      (∫ x : ℝ in (0 : ℝ)..1,
            SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
              SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I)) -
          ((725760 : ℂ) * Complex.I / (π : ℂ)) =
        ∫ x : ℝ in (0 : ℝ)..1,
          (SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
              SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I) -
            ((725760 : ℂ) * Complex.I / (π : ℂ))) := by
    have h :=
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun x : ℝ =>
          SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
            SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I))
        (g := fun _x : ℝ => ((725760 : ℂ) * Complex.I / (π : ℂ))) hInt hIntConst).symm
    simpa using! h
  have hdist :
      dist
          (∫ x : ℝ in (0 : ℝ)..1,
              SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
                SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I))
          ((725760 : ℂ) * Complex.I / (π : ℂ)) < ε := by
    have hnorm :
        ‖∫ x : ℝ in (0 : ℝ)..1,
            (SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
                SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I) -
              ((725760 : ℂ) * Complex.I / (π : ℂ)))‖ ≤
          (ε / 2) * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ)) hbound
    have hnorm' :
        ‖∫ x : ℝ in (0 : ℝ)..1,
            (SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
                SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I) -
              ((725760 : ℂ) * Complex.I / (π : ℂ)))‖ ≤ ε / 2 := by
      simpa using! hnorm
    have :
        ‖(∫ x : ℝ in (0 : ℝ)..1,
              SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
                SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I)) -
            ((725760 : ℂ) * Complex.I / (π : ℂ))‖ ≤ ε / 2 := by
      simpa [hsub] using! hnorm'
    rw [dist_eq_norm]
    exact lt_of_le_of_lt this (half_lt_self hε)
  simpa [Metric.ball, dist_eq_norm] using! hdist

/-- The period integral of `varphi₁' * expU 2` at height `1` (the even special value `u = 2`). -/
public lemma integral_varphi₁'_mul_expU_two_height_one :
    (∫ x : ℝ in (0 : ℝ)..1,
        SpecialValuesAux.varphi₁' ((x : ℂ) + (1 : ℝ) * Complex.I) *
          SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + (1 : ℝ) * Complex.I)) =
      (725760 : ℂ) * Complex.I / (π : ℂ) := by
  let bottom : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..1,
      SpecialValuesAux.varphi₁' ((x : ℂ) + (1 : ℝ) * Complex.I) *
        SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + (1 : ℝ) * Complex.I)
  let top : ℝ → ℂ := fun m : ℝ =>
    ∫ x : ℝ in (0 : ℝ)..1,
      SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
        SpecialValuesAux.expU (2 : ℝ) ((x : ℂ) + m * Complex.I)
  have hu : SpecialValuesAux.expU (2 : ℝ) (1 : ℂ) = 1 := by
    -- `exp(2π i) = 1`.
    simpa [SpecialValuesAux.expU, mul_assoc, mul_left_comm, mul_comm] using!
      (Complex.exp_nat_mul_two_pi_mul_I 1)
  have hEq : (fun m : ℝ => bottom) =ᶠ[atTop] top := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    have h := SpecialValuesAux.strip_identity_varphi₁_mul_expU (u := (2 : ℝ)) hu (m := m) hm
    simpa [bottom, top] using! h
  have hTop : Tendsto top atTop (𝓝 ((725760 : ℂ) * Complex.I / (π : ℂ))) :=
    tendsto_top_varphi₁'_mul_expU_two
  have hBot : Tendsto (fun _m : ℝ => bottom) atTop (𝓝 ((725760 : ℂ) * Complex.I / (π : ℂ))) :=
    hTop.congr' hEq.symm
  have : bottom = (725760 : ℂ) * Complex.I / (π : ℂ) := by
    simpa using! tendsto_const_nhds_iff.mp hBot
  simpa [bottom] using! this

end SpecialValuesEvenAProfile

end

end SpherePacking.Dim24
