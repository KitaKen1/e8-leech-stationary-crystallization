-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.SincAux
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.SincExp

/-!
# The `sinc` correction term for cancelling the double pole at `u = 2`

This file defines the correction factor `sincCorr` used in the cancellation of the double pole at
`u = 2`. The only genuinely hard analytic input is the second-order expansion of `Real.sinc` at
`0`, provided by `SincExp.lean`; everything else is algebra and continuity.

## Main definitions
* `sincCorrCore`
* `sincCorrLimit`
* `sincCorr`

## Main statements
* `continuousAt_sincCorr_two`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex

/-- The value of the correction term at the removable singularity point `u = 2`. -/
@[expose] public def sincCorrLimit : ℂ :=
  ((π : ℂ) ^ (2 : ℕ)) / (12 : ℂ)

/-- The core quotient defining the correction term away from `u = 2`. -/
@[expose] public def sincCorrCore (u : ℝ) : ℂ :=
  (((sincSqC u)⁻¹ - 1) / (((u - 2) ^ (2 : ℕ) : ℝ) : ℂ))

/-- The correction term, defined by updating `sincCorrCore` at `u = 2`. -/
@[expose] public def sincCorr : ℝ → ℂ :=
  Function.update sincCorrCore (2 : ℝ) sincCorrLimit

/-- Away from `u = 2`, the updated function `sincCorr` agrees with `sincCorrCore`. -/
public lemma sincCorr_of_ne_two {u : ℝ} (hu : u ≠ (2 : ℝ)) : sincCorr u = sincCorrCore u := by
  simp [sincCorr, hu]

/-- `sincCorr` is continuous at `u = 2`, so the removable singularity is filled in correctly. -/
public theorem continuousAt_sincCorr_two :
    ContinuousAt sincCorr (2 : ℝ) := by
  have hcore :
      Tendsto sincCorrCore (𝓝[≠] (2 : ℝ)) (𝓝 sincCorrLimit) := by
    have hc : (Real.pi / 2 : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
    have hsub :
        Tendsto (fun u : ℝ => u - 2) (𝓝[≠] (2 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
      have hsub0 : Tendsto (fun u : ℝ => u - 2) (𝓝[≠] (2 : ℝ)) (𝓝 (0 : ℝ)) := by
        have hsub0' : Tendsto (fun u : ℝ => u - 2) (𝓝 (2 : ℝ)) (𝓝 (0 : ℝ)) := by
          simpa using!
            (tendsto_id.sub
              (tendsto_const_nhds :
                Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝 (2 : ℝ)) (𝓝 (2 : ℝ))))
        exact hsub0'.mono_left nhdsWithin_le_nhds
      refine
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (f := fun u : ℝ => u - 2) hsub0 ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      have : u - 2 ≠ 0 := sub_ne_zero.2 hu
      simpa [Set.mem_compl_singleton_iff] using! this
    have hreal :
        Tendsto (fun x : ℝ => (invSq (Real.sinc ((Real.pi / 2) * x)) - 1) / x ^ (2 : ℕ))
          (𝓝[≠] (0 : ℝ)) (𝓝 ((Real.pi / 2) ^ (2 : ℕ) / 3)) :=
      tendsto_inv_sinc_sq_sub_one_div_sq_scaled (c := (Real.pi / 2)) hc
    have hreal' :
        Tendsto
          (fun u : ℝ =>
            (invSq (Real.sinc ((Real.pi / 2) * (u - 2))) - 1) / (u - 2) ^ (2 : ℕ))
          (𝓝[≠] (2 : ℝ)) (𝓝 ((Real.pi / 2) ^ (2 : ℕ) / 3)) := by
      simpa [Function.comp] using! (hreal.comp hsub)
    have hcast :
        Tendsto
          (fun u : ℝ =>
            Complex.ofReal
              ((invSq (Real.sinc ((Real.pi / 2) * (u - 2))) - 1) / (u - 2) ^ (2 : ℕ)))
          (𝓝[≠] (2 : ℝ)) (𝓝 (((Real.pi / 2) ^ (2 : ℕ) / 3 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hreal'
    have hEq :
        sincCorrCore =ᶠ[𝓝[≠] (2 : ℝ)]
          fun u : ℝ =>
            Complex.ofReal
              ((invSq (Real.sinc ((Real.pi / 2) * (u - 2))) - 1) / (u - 2) ^ (2 : ℕ)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hsincArg : sincArg u = (Real.pi / 2) * (u - 2) := by
        simp [sincArg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      simp [sincCorrCore, sincSqC, sincSq, hsincArg, invSq, div_eq_mul_inv]
    have hlim :
        Tendsto sincCorrCore (𝓝[≠] (2 : ℝ))
          (𝓝 (((Real.pi / 2) ^ (2 : ℕ) / 3 : ℝ) : ℂ)) :=
      (hcast.congr' (hEq.symm))
    have hval : (((Real.pi / 2) ^ (2 : ℕ) / 3 : ℝ) : ℂ) = sincCorrLimit := by
      have hvalR : (Real.pi / 2 : ℝ) ^ (2 : ℕ) / 3 = Real.pi ^ (2 : ℕ) / 12 := by
        ring_nf
      simp [sincCorrLimit, hvalR]
    simpa [hval] using! hlim
  have hupdate :
      ContinuousAt (Function.update sincCorrCore (2 : ℝ) sincCorrLimit) (2 : ℝ) :=
    (continuousAt_update_same (f := sincCorrCore) (x := (2 : ℝ)) (y := sincCorrLimit)).2 hcore
  simpa [sincCorr] using! hupdate

end SpecialValuesDerivTwoLaurent

end

end SpherePacking.Dim24
