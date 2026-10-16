/-
One-sided Schwartz decay for `I₁'`.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I1Smoothness
import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I1Prelude
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.ExpBounds
import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity


/-!
# Decay of `I₁'`

One-sided Schwartz decay estimates for the profile integral `RealIntegrals.I₁'`.

## Main statements
* `Schwartz.I1Smooth.decay_I₁'`
-/

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

namespace Schwartz

open MeasureTheory Filter Topology

namespace I1Smooth

open RealIntegrals
open MagicFunction.Parametrisations
open Complex Real Set MeasureTheory Filter intervalIntegral
open scoped Interval

open SpherePacking.Integration (μIoo01)

private def μ : Measure ℝ := μIoo01

private instance : IsFiniteMeasure μ := by
  refine ⟨by simp [μ, μIoo01]⟩


/-- One-sided Schwartz decay of `I₁'` on the ray `0 ≤ x`. -/
public theorem decay_I₁' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₁' x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul_sqrt (k := k) (b := 2 * Real.pi)
      (by positivity)
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ, hCφ⟩
  have hCφ0 : 0 ≤ Cφ := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖varphi.resToImagAxis 1‖)
      (b := Real.exp (-(2 * Real.pi) * (1 : ℝ))) (C := Cφ) (norm_nonneg _) (by positivity) ?_
    simpa using! (hCφ 1 (le_rfl : (1 : ℝ) ≤ 1))
  have hxabs : ∀ {x : ℝ}, 0 ≤ x → ‖x‖ = x := by
    intro x hx
    simp [Real.norm_eq_abs, abs_of_nonneg hx]
  have hiterI :
      iteratedDeriv n RealIntegrals.I₁' = fun x : ℝ ↦ I n x :=
    iteratedDeriv_I₁'_eq_integral_gN (n := n)
  let bound : ℝ → ℝ := fun t ↦ ((2 * Real.pi) ^ n) * Cφ * t ^ (10 : ℕ)
  have hμmem : ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 := by
    simpa [μ, μIoo01] using!
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo)
  have hbound_int : Integrable bound μ := by
    -- bound by a constant on a finite measure space.
    let K : ℝ := ((2 * Real.pi) ^ n) * Cφ
    have hK : Integrable (fun _ : ℝ => K) μ := by simp
    have hmeas : AEStronglyMeasurable bound μ := by
      fun_prop
    have hbound_ae : ∀ᵐ t ∂μ, ‖bound t‖ ≤ K := by
      filter_upwards [hμmem] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht.1
      have ht1 : t ≤ 1 := le_of_lt ht.2
      have ht10 : t ^ (10 : ℕ) ≤ (1 : ℝ) := by
        have : t ^ (10 : ℕ) ≤ (1 : ℝ) ^ (10 : ℕ) := pow_le_pow_left₀ ht0 ht1 10
        simpa using! this
      have hK0 : 0 ≤ K := by dsimp [K]; positivity [hCφ0]
      have hnonneg : 0 ≤ bound t := by
        dsimp [bound, K]
        positivity [hCφ0, ht0]
      have hle : bound t ≤ K :=
        mul_le_of_le_one_right hK0 ht10
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hK0] using! hle
    exact Integrable.mono' hK hmeas hbound_ae
  let Kn : ℝ := ∫ t, bound t ∂μ
  refine ⟨Kn * B, ?_⟩
  intro x hx
  have hnorm_iter :
      ‖iteratedFDeriv ℝ n RealIntegrals.I₁' x‖ = ‖iteratedDeriv n RealIntegrals.I₁' x‖ := by
    exact norm_iteratedFDeriv_eq_norm_iteratedDeriv
  have hIrepr : iteratedDeriv n RealIntegrals.I₁' x = I n x := by
    simpa using! congrArg (fun F : ℝ → ℂ => F x) hiterI
  have hIbound : ‖I n x‖ ≤ Kn * Real.exp (-2 * Real.pi * Real.sqrt x) := by
    have hnorm : ‖I n x‖ ≤ ∫ t, ‖gN n x t‖ ∂μ := norm_integral_le_integral_norm _
    have hbound_ae :
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-2 * Real.pi * Real.sqrt x) := by
      filter_upwards [hμmem] with t ht
      have ht0 : 0 < t := ht.1
      have ht0' : 0 ≤ t := le_of_lt ht.1
      have ht1 : t < 1 := ht.2
      have ht1' : t ≤ 1 := le_of_lt ht1
      have hone : (1 : ℝ) ≤ 1 / t := one_le_one_div ht0 ht1'
      have hvarphi :
          ‖varphi.resToImagAxis (1 / t)‖ ≤
            Cφ * Real.exp (-(2 * Real.pi) * (1 / t)) :=
        hCφ (1 / t) hone
      have hEq : varphi' (-1 / (z₁' t + 1)) = varphi.resToImagAxis (1 / t) :=
        varphi'_neg_one_div_z₁'_add_one_eq (t := t) ⟨ht0, ht1'⟩
      have hz : z₁' t + 1 = (Complex.I : ℂ) * (t : ℂ) := by
        have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht0', ht1'⟩
        have hz1 : z₁' t = (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₁'_eq_of_mem (t := t) htIcc)
        simp [hz1, add_left_comm, add_comm]
      have hzt : ‖z₁' t + 1‖ = t := by
        simp [hz, Complex.norm_real, abs_of_nonneg ht0']
      have hpow : ‖(z₁' t + 1) ^ (10 : ℕ)‖ = t ^ (10 : ℕ) := by
        calc
          ‖(z₁' t + 1) ^ (10 : ℕ)‖ = ‖z₁' t + 1‖ ^ (10 : ℕ) := by simp [norm_pow]
          _ = t ^ (10 : ℕ) := by simp [hzt]
      have hh :
          ‖h t‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * (1 / t)) * t ^ (10 : ℕ) := by
        calc
          ‖h t‖ =
              ‖varphi' (-1 / (z₁' t + 1))‖ * ‖(z₁' t + 1) ^ (10 : ℕ)‖ := by
                simp [h]
          _ = ‖varphi' (-1 / (z₁' t + 1))‖ * t ^ (10 : ℕ) := by simp [hpow]
          _ = ‖varphi.resToImagAxis (1 / t)‖ * t ^ (10 : ℕ) := by simp [hEq]
          _ ≤ (Cφ * Real.exp (-(2 * Real.pi) * (1 / t))) * t ^ (10 : ℕ) := by gcongr
          _ = Cφ * Real.exp (-(2 * Real.pi) * (1 / t)) * t ^ (10 : ℕ) := by ring_nf
      have hcexp :
          ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t) := by
        have hcoeff' :
            coeff t = (-((Real.pi : ℂ) * (Complex.I : ℂ))) - (Real.pi : ℂ) * (t : ℂ) := by
          have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht0', ht1'⟩
          simpa [coeff] using! (MagicFunction.Parametrisations.pi_I_mul_z₁'_eq_of_mem (t := t) htIcc)
        have hcoeffRe : (coeff t).re = -Real.pi * t := by
          simp [hcoeff', Complex.sub_re, Complex.mul_re]
        have hzre : ((x : ℂ) * coeff t).re = -Real.pi * x * t := by
          simp [Complex.mul_re, hcoeffRe, mul_left_comm, mul_comm]
        calc
          ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (((x : ℂ) * coeff t).re) := by
                simpa using! (Complex.norm_exp ((x : ℂ) * coeff t))
          _ = Real.exp (-Real.pi * x * t) := by simp [hzre]
      have hcoeff : ‖coeff t‖ ^ n ≤ (2 * Real.pi) ^ n :=
        pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n
      have hgn :
          ‖gN n x t‖ = ‖coeff t‖ ^ n * ‖h t‖ * Real.exp (-Real.pi * x * t) := by
        simp [gN, g, hcexp, norm_pow, mul_left_comm, mul_comm]
      have hExp :
          Real.exp (-Real.pi / t) * Real.exp (-Real.pi * x * t) ≤
            Real.exp (-2 * Real.pi * Real.sqrt x) :=
        SpherePacking.ForMathlib.exp_neg_pi_div_mul_exp_neg_pi_mul_le (x := x) (t := t) hx ht0
      have hexp_le :
          Real.exp (-(2 * Real.pi) * (1 / t)) ≤ Real.exp (-Real.pi / t) := by
        have hle : (-(2 * Real.pi) : ℝ) ≤ (-Real.pi) := by linarith [Real.pi_pos]
        have hinv : 0 ≤ (1 / t : ℝ) := le_of_lt (one_div_pos.2 ht0)
        have harg : (-(2 * Real.pi) * (1 / t) : ℝ) ≤ (-Real.pi) * (1 / t) :=
          mul_le_mul_of_nonneg_right hle hinv
        have harg' : (-(2 * Real.pi) * (1 / t) : ℝ) ≤ (-Real.pi / t) := by
          simpa [div_eq_mul_inv] using! harg
        exact Real.exp_le_exp.2 harg'
      have hh1 : ‖h t‖ ≤ Cφ * Real.exp (-Real.pi / t) * t ^ (10 : ℕ) := by
        have hCT0 : 0 ≤ Cφ * t ^ (10 : ℕ) := by positivity [hCφ0, ht0']
        have hstep :
            Cφ * Real.exp (-(2 * Real.pi) * (1 / t)) * t ^ (10 : ℕ) ≤
              Cφ * Real.exp (-Real.pi / t) * t ^ (10 : ℕ) := by
          have hmono :
              (Cφ * t ^ (10 : ℕ)) * Real.exp (-(2 * Real.pi) * (1 / t)) ≤
                (Cφ * t ^ (10 : ℕ)) * Real.exp (-Real.pi / t) :=
            mul_le_mul_of_nonneg_left hexp_le hCT0
          -- rewrite by commutativity/associativity of `(*)`.
          simpa [mul_assoc, mul_left_comm, mul_comm] using! hmono
        exact hh.trans hstep
      have hgn' :
          ‖gN n x t‖ ≤ bound t * (Real.exp (-Real.pi / t) * Real.exp (-Real.pi * x * t)) := by
        have hgn0 :
            ‖gN n x t‖ = ‖coeff t‖ ^ n * (‖h t‖ * Real.exp (-Real.pi * x * t)) := by
          simpa [mul_assoc] using! hgn
        have hcoeff0 : 0 ≤ ‖coeff t‖ ^ n := by positivity
        have hmul1 :
            ‖h t‖ * Real.exp (-Real.pi * x * t) ≤
              (Cφ * Real.exp (-Real.pi / t) * t ^ (10 : ℕ)) * Real.exp (-Real.pi * x * t) := by
          have :=
            mul_le_mul_of_nonneg_right (a := Real.exp (-Real.pi * x * t)) hh1 (by positivity)
          simpa [mul_assoc, mul_left_comm, mul_comm] using! this
        have hmul2 :
            ‖coeff t‖ ^ n * (‖h t‖ * Real.exp (-Real.pi * x * t)) ≤
              ‖coeff t‖ ^ n *
                ((Cφ * Real.exp (-Real.pi / t) * t ^ (10 : ℕ)) * Real.exp (-Real.pi * x * t)) :=
          mul_le_mul_of_nonneg_left hmul1 hcoeff0
        have hpos :
            0 ≤ (Cφ * Real.exp (-Real.pi / t) * t ^ (10 : ℕ)) * Real.exp (-Real.pi * x * t) := by
          positivity [hCφ0, ht0']
        have hmul3 :
            ‖coeff t‖ ^ n *
                ((Cφ * Real.exp (-Real.pi / t) * t ^ (10 : ℕ)) * Real.exp (-Real.pi * x * t)) ≤
              (2 * Real.pi) ^ n *
                ((Cφ * Real.exp (-Real.pi / t) * t ^ (10 : ℕ)) * Real.exp (-Real.pi * x * t)) :=
          mul_le_mul_of_nonneg_right hcoeff hpos
        grind only
      have hboundt : 0 ≤ bound t := by
        dsimp [bound]
        positivity [hCφ0, ht0']
      exact le_mul_of_le_mul_of_nonneg_left hgn' hExp hboundt
    have hle :
        ∫ t, ‖gN n x t‖ ∂μ ≤ ∫ t, bound t * Real.exp (-2 * Real.pi * Real.sqrt x) ∂μ := by
      have hbound_int' :
          Integrable (fun t ↦ bound t * Real.exp (-2 * Real.pi * Real.sqrt x)) μ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using!
          hbound_int.mul_const (Real.exp (-2 * Real.pi * Real.sqrt x))
      refine integral_mono_of_nonneg ?_ hbound_int' hbound_ae
      exact (Eventually.of_forall fun t => norm_nonneg (gN n x t))
    have hconst :
        (∫ t, bound t * Real.exp (-2 * Real.pi * Real.sqrt x) ∂μ) =
          Kn * Real.exp (-2 * Real.pi * Real.sqrt x) := by
      exact MeasureTheory.integral_mul_const (rexp (-2 * π * √x)) bound
    have : ‖I n x‖ ≤ Kn * Real.exp (-2 * Real.pi * Real.sqrt x) :=
      hnorm.trans (hle.trans_eq hconst)
    simpa [Kn] using! this
  have hpoly : x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x) ≤ B := by
    have : (-(2 * Real.pi) * Real.sqrt x) = -2 * Real.pi * Real.sqrt x := by ring_nf
    simpa [this] using! (hB x hx)
  have hKn0 : 0 ≤ Kn := by
    have hbound0 : ∀ᵐ t ∂μ, 0 ≤ bound t := by
      filter_upwards [hμmem] with t ht
      dsimp [bound]
      positivity [hCφ0, le_of_lt ht.1]
    exact integral_nonneg_of_ae hbound0
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₁' x‖
        = x ^ k * ‖iteratedDeriv n RealIntegrals.I₁' x‖ := by simp [hxabs hx, hnorm_iter]
    _ = x ^ k * ‖I n x‖ := by simp [hIrepr]
    _ ≤ x ^ k * (Kn * Real.exp (-2 * Real.pi * Real.sqrt x)) := by gcongr
    _ = Kn * (x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x)) := by ring_nf
    _ ≤ Kn * B := by
          simpa [mul_assoc] using! (mul_le_mul_of_nonneg_left hpoly hKn0)
    _ = Kn * B := rfl


end Schwartz.I1Smooth
end

end SpherePacking.Dim24
