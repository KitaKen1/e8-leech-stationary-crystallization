-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.EvenAProfile.Basic


/-!
# The special value `u = 4`

This file shows that the period integral of `varphi₁' * expU 4` over one horizontal period at
height `1` vanishes. This is the key input for the even special value computation of `aProfile`
at `u = 4`.

## Main statement
* `SpecialValuesEvenAProfile.integral_varphi₁'_mul_expU_four_height_one`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesEvenAProfile

open scoped Interval Real Topology
open Filter Complex UpperHalfPlane intervalIntegral MeasureTheory Set

lemma tendsto_top_varphi₁'_mul_expU_four :
    Tendsto
      (fun m : ℝ =>
        ∫ x : ℝ in (0 : ℝ)..1,
          SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
            SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I))
      atTop (𝓝 (0 : ℂ)) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hBall :
      {z : ℍ | ‖Dim24.varphi₁ z * (SpecialValuesVarphi₁Limits.q (z : ℂ)) ^ (2 : ℕ)‖ < ε / 2} ∈
        atImInfty := by
    -- Convert the neighborhood statement `ball 0 (ε/2) ∈ map f atImInfty`
    -- into a preimage statement.
    have h :=
      (SpecialValuesVarphi₁Limits.tendsto_varphi₁_mul_q_sq
        (Metric.ball_mem_nhds (0 : ℂ) hε2))
    have hpre :
        {z : ℍ |
            (Dim24.varphi₁ z * (SpecialValuesVarphi₁Limits.q (z : ℂ)) ^ (2 : ℕ)) ∈
              Metric.ball (0 : ℂ) (ε / 2)} ∈ atImInfty :=
      (Filter.mem_map'.1 h)
    simpa [Metric.ball, dist_eq_norm] using! hpre
  rcases (UpperHalfPlane.atImInfty_mem _).1 hBall with ⟨A, hA⟩
  refine ⟨max A 1, ?_⟩
  intro m hm
  have hmA : A ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_right _ _) hm
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  have hbound :
      ∀ x ∈ Ι (0 : ℝ) 1,
        ‖SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
              SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I) - (0 : ℂ)‖ ≤ ε / 2 := by
    intro x hx
    let zH : ℍ := ⟨(x : ℂ) + (m : ℂ) * Complex.I, by simpa [Complex.add_im] using! hm0⟩
    have hz : A ≤ zH.im := by
      simpa [zH, UpperHalfPlane.im, Complex.add_im] using! hmA
    have hmem :
        ‖Dim24.varphi₁ zH * (SpecialValuesVarphi₁Limits.q (zH : ℂ)) ^ (2 : ℕ)‖ < ε / 2 := by
      have := hA zH hz
      simpa using! this
    have hEq :
        SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
            SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I) =
          Dim24.varphi₁ zH * (SpecialValuesVarphi₁Limits.q (zH : ℂ)) ^ (2 : ℕ) := by
      -- `expU 4 z = exp(4π i z) = (exp(2π i z))^2`.
      have hexp :
          SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I) =
            (SpecialValuesVarphi₁Limits.q ((x : ℂ) + m * Complex.I)) ^ (2 : ℕ) := by
        -- Use `exp (2 * a) = exp a ^ 2` with `a = 2π i z`.
        set w : ℂ := (x : ℂ) + m * Complex.I
        have harg :
            ((2 : ℕ) : ℂ) * (2 * Real.pi * Complex.I * w) =
              Real.pi * Complex.I * (4 : ℂ) * w := by
          ring_nf
        have hpow :
            Complex.exp (((2 : ℕ) : ℂ) * (2 * Real.pi * Complex.I * w)) =
              (Complex.exp (2 * Real.pi * Complex.I * w)) ^ (2 : ℕ) := by
          simpa using! (Complex.exp_nat_mul (2 * Real.pi * Complex.I * w) 2)
        calc
          SpecialValuesAux.expU (4 : ℝ) w =
              Complex.exp (Real.pi * Complex.I * (4 : ℂ) * w) := by
                simp [SpecialValuesAux.expU, w, mul_assoc, mul_left_comm, mul_comm]
          _ = Complex.exp (((2 : ℕ) : ℂ) * (2 * Real.pi * Complex.I * w)) := by
                simpa using! congrArg Complex.exp harg.symm
          _ = (Complex.exp (2 * Real.pi * Complex.I * w)) ^ (2 : ℕ) := by
                simpa using! hpow
          _ = (SpecialValuesVarphi₁Limits.q w) ^ (2 : ℕ) := by
                simp [SpecialValuesVarphi₁Limits.q, w, mul_left_comm, mul_comm]
      simp [SpecialValuesAux.varphi₁', zH, hm0, hexp]
    have :
        ‖SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
              SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I) - (0 : ℂ)‖ < ε / 2 := by
      simpa [hEq] using! hmem
    exact le_of_lt this
  have hInt :
      IntervalIntegrable
        (fun x : ℝ =>
          SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
            SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I))
        MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_varphi₁'_mul_expU (u := (4 : ℝ)) (m := m) hm0
  have hIntConst : IntervalIntegrable (fun _x : ℝ => (0 : ℂ)) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hsub :
      (∫ x : ℝ in (0 : ℝ)..1,
            SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
              SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I)) - (0 : ℂ) =
        ∫ x : ℝ in (0 : ℝ)..1,
          (SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
              SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I) - (0 : ℂ)) := by
    have h :=
      (intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun x : ℝ =>
          SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
            SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I))
        (g := fun _x : ℝ => (0 : ℂ)) hInt hIntConst).symm
    norm_num
  have hdist :
      dist
          (∫ x : ℝ in (0 : ℝ)..1,
              SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
                SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I))
          (0 : ℂ) < ε := by
    have hnorm :
        ‖∫ x : ℝ in (0 : ℝ)..1,
            (SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
                SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I) - (0 : ℂ))‖ ≤
          (ε / 2) * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ)) hbound
    have hnorm' :
        ‖∫ x : ℝ in (0 : ℝ)..1,
            (SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
                SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I) - (0 : ℂ))‖ ≤ ε / 2 := by
      simpa using! hnorm
    have :
        ‖(∫ x : ℝ in (0 : ℝ)..1,
              SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
                SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I)) - (0 : ℂ)‖ ≤ ε / 2 := by
      simpa [hsub] using! hnorm'
    rw [dist_eq_norm]
    exact lt_of_le_of_lt this (half_lt_self hε)
  simpa [Metric.ball, dist_eq_norm] using! hdist
 
/-- The period integral of `varphi₁' * expU 4` over `x ∈ (0,1)` at height `1` is `0`. -/
public lemma integral_varphi₁'_mul_expU_four_height_one :
    (∫ x : ℝ in (0 : ℝ)..1,
        SpecialValuesAux.varphi₁' ((x : ℂ) + (1 : ℝ) * Complex.I) *
          SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + (1 : ℝ) * Complex.I)) = (0 : ℂ) := by
  let bottom : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..1,
      SpecialValuesAux.varphi₁' ((x : ℂ) + (1 : ℝ) * Complex.I) *
        SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + (1 : ℝ) * Complex.I)
  let top : ℝ → ℂ := fun m : ℝ =>
    ∫ x : ℝ in (0 : ℝ)..1,
      SpecialValuesAux.varphi₁' ((x : ℂ) + m * Complex.I) *
        SpecialValuesAux.expU (4 : ℝ) ((x : ℂ) + m * Complex.I)
  have hu : SpecialValuesAux.expU (4 : ℝ) (1 : ℂ) = 1 := by
    -- `exp(4π i) = 1`.
    have hbase : Complex.exp (Complex.I * ((Real.pi : ℂ) * ((2 : ℂ) * (2 : ℂ)))) = (1 : ℂ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using! (Complex.exp_nat_mul_two_pi_mul_I 2)
    have h22 : (2 : ℂ) * (2 : ℂ) = (4 : ℂ) := by norm_num
    have hbase' : Complex.exp (Complex.I * ((Real.pi : ℂ) * (4 : ℂ))) = (1 : ℂ) := by
      simpa [h22, mul_assoc] using! hbase
    -- Now unfold `expU` and match `hbase'`.
    simpa [SpecialValuesAux.expU, mul_assoc, mul_left_comm, mul_comm] using! hbase'
  have hEq : (fun m : ℝ => bottom) =ᶠ[atTop] top := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    have h := SpecialValuesAux.strip_identity_varphi₁_mul_expU (u := (4 : ℝ)) hu (m := m) hm
    simpa [bottom, top] using! h
  have hTop : Tendsto top atTop (𝓝 (0 : ℂ)) := tendsto_top_varphi₁'_mul_expU_four
  have hBot : Tendsto (fun _m : ℝ => bottom) atTop (𝓝 (0 : ℂ)) := hTop.congr' hEq.symm
  have : bottom = (0 : ℂ) := by
    simpa using! tendsto_const_nhds_iff.mp hBot
  simpa [bottom] using! this

end SpecialValuesEvenAProfile

end

end SpherePacking.Dim24
