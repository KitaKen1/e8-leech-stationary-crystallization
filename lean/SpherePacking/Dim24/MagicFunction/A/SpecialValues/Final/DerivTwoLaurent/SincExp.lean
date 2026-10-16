-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Second-order expansion of `Real.sinc` at `0`

The main analytic statement is the limit
`Tendsto (fun x ↦ (invSq (Real.sinc x) - 1) / x^2) (𝓝[≠] 0) (𝓝 (1/3))`.
This is the input used to show that the correction factor in the `u = 2` cancellation has a
removable singularity.

## Main definitions
* `invSq`

## Main statements
* `tendsto_inv_sinc_sq_sub_one_div_sq`
* `tendsto_inv_sinc_sq_sub_one_div_sq_scaled`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Asymptotics

lemma taylorWithinEval_sin_three (x : ℝ) :
    taylorWithinEval Real.sin 3 Set.univ (0 : ℝ) x = x - x ^ (3 : ℕ) / 6 := by
  -- Expand the Taylor polynomial by definition, and compute the needed iterated derivatives at `0`.
  simp [taylor_within_apply, iteratedDerivWithin_univ]
  ring_nf

lemma tendsto_sin_sub_taylor_three_div_cube :
    Tendsto
      (fun x : ℝ => (Real.sin x - (x - x ^ (3 : ℕ) / 6)) / x ^ (3 : ℕ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hs : Convex ℝ (Set.univ : Set ℝ) := convex_univ
  have h0 : (0 : ℝ) ∈ (Set.univ : Set ℝ) := trivial
  have hcont : ContDiffOn ℝ 3 Real.sin (Set.univ : Set ℝ) := by
    simpa using! (Real.contDiff_sin.contDiffOn : ContDiffOn ℝ 3 Real.sin (Set.univ : Set ℝ))
  have htaylor :
      Tendsto
        (fun x : ℝ =>
          (Real.sin x - taylorWithinEval Real.sin 3 (Set.univ : Set ℝ) (0 : ℝ) x) /
            (x - (0 : ℝ)) ^ (3 : ℕ))
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using!
      (Real.taylor_tendsto (f := Real.sin) (x₀ := (0 : ℝ)) (n := 3)
        (s := (Set.univ : Set ℝ)) hs h0 hcont)
  have htaylor' :
      Tendsto
        (fun x : ℝ =>
          (Real.sin x - taylorWithinEval Real.sin 3 (Set.univ : Set ℝ) (0 : ℝ) x) /
            x ^ (3 : ℕ))
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using! htaylor
  have htaylorNE :
      Tendsto
        (fun x : ℝ =>
          (Real.sin x - taylorWithinEval Real.sin 3 (Set.univ : Set ℝ) (0 : ℝ) x) /
            x ^ (3 : ℕ))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    htaylor'.mono_left nhdsWithin_le_nhds
  have hEq :
      (fun x : ℝ =>
            (Real.sin x - taylorWithinEval Real.sin 3 (Set.univ : Set ℝ) (0 : ℝ) x) /
              x ^ (3 : ℕ)) =ᶠ[𝓝[≠] (0 : ℝ)]
        fun x : ℝ => (Real.sin x - (x - x ^ (3 : ℕ) / 6)) / x ^ (3 : ℕ) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    -- Unfold the Taylor polynomial and evaluate the iterated derivatives at `0`.
    simp [taylor_within_apply, iteratedDerivWithin_univ]
    ring_nf
  exact htaylorNE.congr' hEq

lemma tendsto_sinc_sub_one_div_sq :
    Tendsto (fun x : ℝ => (Real.sinc x - 1) / x ^ (2 : ℕ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-(1 : ℝ) / 6)) := by
  have hstep :
      Tendsto (fun x : ℝ => (Real.sin x - x) / x ^ (3 : ℕ))
        (𝓝[≠] (0 : ℝ)) (𝓝 (-(1 : ℝ) / 6)) := by
    have ht := tendsto_sin_sub_taylor_three_div_cube
    have hEv :
        (fun x : ℝ => (Real.sin x - x) / x ^ (3 : ℕ)) =ᶠ[𝓝[≠] (0 : ℝ)]
          fun x : ℝ =>
            (-(1 : ℝ) / 6) + (Real.sin x - (x - x ^ (3 : ℕ) / 6)) / x ^ (3 : ℕ) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx3 : x ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hx
      -- Clear denominators using `div_eq_iff`.
      apply (div_eq_iff hx3).2
      -- Multiply out and cancel the remainder term.
      calc
        Real.sin x - x =
            (-(1 : ℝ) / 6) * x ^ (3 : ℕ) + (Real.sin x - (x - x ^ (3 : ℕ) / 6)) := by
              ring
        _ = (-(1 : ℝ) / 6) * x ^ (3 : ℕ) +
              ((Real.sin x - (x - x ^ (3 : ℕ) / 6)) / x ^ (3 : ℕ)) * x ^ (3 : ℕ) := by
              -- rewrite the remainder as `(remainder / x^3) * x^3`
              simp [hx3]
        _ =
            (-(1 : ℝ) / 6 + (Real.sin x - (x - x ^ (3 : ℕ) / 6)) / x ^ (3 : ℕ)) *
              x ^ (3 : ℕ) := by
              ring
    have hsum :
        Tendsto
          (fun x : ℝ =>
            (-(1 : ℝ) / 6) + (Real.sin x - (x - x ^ (3 : ℕ) / 6)) / x ^ (3 : ℕ))
          (𝓝[≠] (0 : ℝ)) (𝓝 (-(1 : ℝ) / 6)) := by
      simpa using! (tendsto_const_nhds.add ht)
    exact (hsum.congr' hEv.symm)
  have hEv :
      (fun x : ℝ => (Real.sinc x - 1) / x ^ (2 : ℕ)) =ᶠ[𝓝[≠] (0 : ℝ)]
        fun x : ℝ => (Real.sin x - x) / x ^ (3 : ℕ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hs : Real.sinc x = Real.sin x / x := Real.sinc_of_ne_zero hx
    -- Rewrite `sin x / x - 1` as `(sin x - x) / x`, then use `div_div`.
    rw [hs, div_sub_one hx]
    -- `((a / x) / x^2) = a / (x * x^2) = a / x^3`.
    simp [div_div, pow_succ, mul_assoc]
  exact (hstep.congr' hEv.symm)

/-- Square of the inverse, used to package expressions like `(1 / (Real.sinc x))^2`. -/
@[expose] public def invSq (x : ℝ) : ℝ := (x⁻¹) ^ (2 : ℕ)

/-- Second-order expansion of `(Real.sinc x)⁻¹` squared at `x = 0`. -/
theorem tendsto_inv_sinc_sq_sub_one_div_sq :
    Tendsto (fun x : ℝ => (invSq (Real.sinc x) - 1) / x ^ (2 : ℕ))
      (𝓝[≠] (0 : ℝ)) (𝓝 ((1 : ℝ) / 3)) := by
  -- Limit for `(sinc x - 1)/x^2`.
  have hlimSinc :
      Tendsto (fun x : ℝ => (Real.sinc x - 1) / x ^ (2 : ℕ))
        (𝓝[≠] (0 : ℝ)) (𝓝 (-(1 : ℝ) / 6)) :=
    tendsto_sinc_sub_one_div_sq
  -- `sinc x → 1` along `𝓝[≠]0`.
  have hsinc :
      Tendsto Real.sinc (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have : Tendsto Real.sinc (𝓝 (0 : ℝ)) (𝓝 (Real.sinc 0)) :=
      (Real.continuous_sinc.continuousAt.tendsto : _)
    simpa [Real.sinc_zero] using! this.mono_left nhdsWithin_le_nhds
  -- Linearization of `invSq` at `1`.
  have hderInv : HasDerivAt (fun x : ℝ => x⁻¹) (-(1 : ℝ)) (1 : ℝ) := by
    simpa using! (hasDerivAt_inv (x := (1 : ℝ)) (by norm_num))
  have hderInvSq : HasDerivAt invSq (-(2 : ℝ)) (1 : ℝ) := by
    simpa [invSq] using! (hderInv.pow 2)
  have hlin :
      (fun z : ℝ =>
          invSq z - invSq (1 : ℝ) - (z - (1 : ℝ)) • (-(2 : ℝ))) =o[𝓝 (1 : ℝ)]
        fun z : ℝ => z - (1 : ℝ) := by
    exact (hasDerivAt_iff_isLittleO.1 hderInvSq)
  -- Compose the linearization with `sinc`.
  have hlin' :
      (fun x : ℝ =>
          invSq (Real.sinc x) - 1 + (2 : ℝ) * (Real.sinc x - 1)) =o[𝓝[≠] (0 : ℝ)]
        fun x : ℝ => Real.sinc x - 1 := by
    have hcomp := hlin.comp_tendsto hsinc
    have hcomp' :
        (fun x : ℝ =>
            invSq (Real.sinc x) - invSq (1 : ℝ) -
              (Real.sinc x - (1 : ℝ)) • (-(2 : ℝ))) =o[𝓝[≠] (0 : ℝ)]
          fun x : ℝ => Real.sinc x - (1 : ℝ) := by
      simpa [Function.comp] using! hcomp
    refine hcomp'.congr ?_ ?_
    · intro x
      simp [invSq, sub_eq_add_neg, add_left_comm, add_comm, smul_eq_mul, mul_comm]
    · intro x
      simp [sub_eq_add_neg, add_comm]
  -- From the existence of the limit, we get `(sinc x - 1) = O(x^2)`.
  have hBigO :
      (fun x : ℝ => Real.sinc x - 1) =O[𝓝[≠] (0 : ℝ)] fun x : ℝ => x ^ (2 : ℕ) := by
    -- Use boundedness of the quotient near its limit.
    let L : ℝ := (-(1 : ℝ) / 6)
    have hBound :
        ∀ᶠ x in 𝓝[≠] (0 : ℝ),
          ‖(Real.sinc x - 1) / x ^ (2 : ℕ)‖ ≤ ‖L‖ + 1 := by
      have hball : Metric.ball L 1 ∈ 𝓝 L := Metric.ball_mem_nhds _ (by norm_num)
      have hEv := (hlimSinc.eventually hball)
      filter_upwards [hEv] with x hx
      have hx' : ‖(Real.sinc x - 1) / x ^ (2 : ℕ) - L‖ < (1 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm] using! hx
      have htri :
          ‖(Real.sinc x - 1) / x ^ (2 : ℕ)‖ ≤
            ‖(Real.sinc x - 1) / x ^ (2 : ℕ) - L‖ + ‖L‖ := by
        -- `a = (a - L) + L`
        simpa [sub_eq_add_neg, add_assoc] using!
          (norm_add_le ((Real.sinc x - 1) / x ^ (2 : ℕ) - L) L)
      linarith
    refine Asymptotics.IsBigO.of_bound (‖(-(1 : ℝ) / 6)‖ + 1) ?_
    filter_upwards [hBound, self_mem_nhdsWithin] with x hxB hx0
    have hx2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx0
    -- `‖f x‖ = ‖(f x / g x) * g x‖ ≤ ‖f x / g x‖ * ‖g x‖`.
    calc
      ‖Real.sinc x - 1‖ = ‖((Real.sinc x - 1) / x ^ (2 : ℕ)) * x ^ (2 : ℕ)‖ := by
        simpa [mul_assoc] using! (congrArg norm (div_mul_cancel₀ (Real.sinc x - 1) hx2)).symm
      _ = ‖(Real.sinc x - 1) / x ^ (2 : ℕ)‖ * ‖x ^ (2 : ℕ)‖ := by
        simp [norm_mul]
      _ ≤ (‖(-(1 : ℝ) / 6)‖ + 1) * ‖x ^ (2 : ℕ)‖ := by
        gcongr
  -- The remainder term is `o(x^2)`.
  have hRem :
      (fun x : ℝ =>
          invSq (Real.sinc x) - 1 + (2 : ℝ) * (Real.sinc x - 1)) =o[𝓝[≠] (0 : ℝ)]
      fun x : ℝ => x ^ (2 : ℕ) :=
    hlin'.trans_isBigO hBigO
  have hRemT :
      Tendsto
        (fun x : ℝ => (invSq (Real.sinc x) - 1 + (2 : ℝ) * (Real.sinc x - 1)) / x ^ (2 : ℕ))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    IsLittleO.tendsto_div_nhds_zero hRem
  -- Main term: `(-2) * ((sinc x - 1)/x^2) → 1/3`.
  have hMain :
      Tendsto (fun x : ℝ => (-(2 : ℝ)) * ((Real.sinc x - 1) / x ^ (2 : ℕ)))
        (𝓝[≠] (0 : ℝ)) (𝓝 ((1 : ℝ) / 3)) := by
    have hMain0 :
        Tendsto (fun x : ℝ => (-(2 : ℝ)) * ((Real.sinc x - 1) / x ^ (2 : ℕ)))
          (𝓝[≠] (0 : ℝ)) (𝓝 ((-(2 : ℝ)) * (-(1 : ℝ) / 6))) :=
      tendsto_const_nhds.mul hlimSinc
    have hval : (-(2 : ℝ)) * (-(1 : ℝ) / 6) = (1 : ℝ) / 3 := by
      ring_nf
    simpa [hval] using! hMain0
  have hEv :
      (fun x : ℝ => (invSq (Real.sinc x) - 1) / x ^ (2 : ℕ)) =ᶠ[𝓝[≠] (0 : ℝ)]
        fun x : ℝ =>
          (-(2 : ℝ)) * ((Real.sinc x - 1) / x ^ (2 : ℕ)) +
            (invSq (Real.sinc x) - 1 + (2 : ℝ) * (Real.sinc x - 1)) / x ^ (2 : ℕ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx0
    ring
  have hSum :
      Tendsto
        (fun x : ℝ =>
          (-(2 : ℝ)) * ((Real.sinc x - 1) / x ^ (2 : ℕ)) +
            (invSq (Real.sinc x) - 1 + (2 : ℝ) * (Real.sinc x - 1)) / x ^ (2 : ℕ))
        (𝓝[≠] (0 : ℝ)) (𝓝 ((1 : ℝ) / 3)) := by
    simpa using! (hMain.add hRemT)
  exact hSum.congr' hEv.symm

/--
Scaled version of `tendsto_inv_sinc_sq_sub_one_div_sq`, obtained by the change of variables
`x ↦ c * x`.
-/
public theorem tendsto_inv_sinc_sq_sub_one_div_sq_scaled {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun x : ℝ => (invSq (Real.sinc (c * x)) - 1) / x ^ (2 : ℕ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (c ^ (2 : ℕ) / 3)) := by
  -- First compose the base limit along the map `x ↦ c*x` into the punctured neighborhood.
  have hk0 : Tendsto (fun x : ℝ => c * x) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun x : ℝ => c * x) ?_ ?_
    · have : Tendsto (fun x : ℝ => c * x) (𝓝 (0 : ℝ)) (𝓝 (c * (0 : ℝ))) := by
        simpa using!
          (tendsto_const_nhds.mul
            (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))))
      simpa using! this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx0
      simpa [Set.mem_compl_singleton_iff] using! mul_ne_zero hc hx0
  have hcomp :
      Tendsto (fun x : ℝ => (invSq (Real.sinc (c * x)) - 1) / (c * x) ^ (2 : ℕ))
        (𝓝[≠] (0 : ℝ)) (𝓝 ((1 : ℝ) / 3)) := by
    simpa [Function.comp] using! (tendsto_inv_sinc_sq_sub_one_div_sq.comp hk0)
  have hEv :
      (fun x : ℝ => (invSq (Real.sinc (c * x)) - 1) / x ^ (2 : ℕ)) =ᶠ[𝓝[≠] (0 : ℝ)]
        fun x : ℝ => c ^ (2 : ℕ) * ((invSq (Real.sinc (c * x)) - 1) / (c * x) ^ (2 : ℕ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx0
    grind only [= Set.mem_compl_iff, = Set.mem_singleton_iff]
  have hmul :
      Tendsto
        (fun x : ℝ =>
          c ^ (2 : ℕ) * ((invSq (Real.sinc (c * x)) - 1) / (c * x) ^ (2 : ℕ)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (c ^ (2 : ℕ) * ((1 : ℝ) / 3))) :=
    tendsto_const_nhds.mul hcomp
  have hmul' :
      Tendsto
        (fun x : ℝ =>
          c ^ (2 : ℕ) * ((invSq (Real.sinc (c * x)) - 1) / (c * x) ^ (2 : ℕ)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (c ^ (2 : ℕ) / 3)) := by
    simpa [div_eq_mul_inv, mul_assoc] using! hmul
  exact hmul'.congr' hEv.symm

end SpecialValuesDerivTwoLaurent

end
end SpherePacking.Dim24
