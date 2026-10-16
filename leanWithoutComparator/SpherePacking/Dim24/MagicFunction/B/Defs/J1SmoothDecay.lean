-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
import SpherePacking.Dim24.MagicFunction.B.Defs.J1SmoothIntegrals
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSDecay
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.ExpBounds
import SpherePacking.Integration.Measure
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity
import SpherePacking.MagicFunction.PsiTPrimeZ1


/-!
# One-sided Schwartz decay for `RealIntegrals.J₁'`

This file proves the polynomially weighted exponential decay bound for iterated derivatives of
`RealIntegrals.J₁'` on `x ≥ 0`. Here `J₁'` is the first contour-integral term in the definition of
the profile `bProfile`.

## Main statements
* `Schwartz.J1Smooth.decay_J₁'`
-/

noncomputable section


namespace SpherePacking.Dim24.Schwartz.J1Smooth

open Set
open MeasureTheory
open scoped Complex

open MagicFunction.Parametrisations
open SpherePacking.Integration (μIoo01)

private def μ : Measure ℝ := μIoo01

private instance : IsFiniteMeasure μ := by
  refine ⟨by simp [μ, μIoo01]⟩


/--
One-sided Schwartz decay for `J₁'`: polynomial weights are dominated by `exp(-2π √x)`
on `x ≥ 0`.
-/
public theorem decay_J₁' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₁' x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul_sqrt (k := k) (b := 2 * Real.pi)
      (by positivity)
  rcases PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with ⟨Cψ, hCψ⟩
  have hCψ0 : 0 ≤ Cψ := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := Cψ) (norm_nonneg _) (by positivity) ?_
    simpa using! (hCψ 1 (le_rfl : (1 : ℝ) ≤ 1))
  have hxabs : ∀ {x : ℝ}, 0 ≤ x → ‖x‖ = x := by
    intro x hx
    simp [Real.norm_eq_abs, abs_of_nonneg hx]
  have hiterJ :
      iteratedDeriv n RealIntegrals.J₁' = fun x : ℝ ↦ I n x :=
    iteratedDeriv_J₁'_eq_integral_gN (n := n)
  let bound : ℝ → ℝ := fun t ↦ ((2 * Real.pi) ^ n) * Cψ * t ^ (10 : ℕ)
  have hμmem : ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 := by
    simpa [μ, μIoo01] using!
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo)
  have hbound_int : Integrable bound μ := by
    have hmeas : AEStronglyMeasurable bound μ := by
      fun_prop
    let K : ℝ := ((2 * Real.pi) ^ n) * Cψ
    have hK : Integrable (fun _ : ℝ => K) μ := by
      simp
    have hbound_ae : ∀ᵐ t ∂μ, ‖bound t‖ ≤ K := by
      filter_upwards [hμmem] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht.1
      have ht1 : t ≤ 1 := le_of_lt ht.2
      have ht10 : t ^ (10 : ℕ) ≤ (1 : ℝ) := by
        have : t ^ (10 : ℕ) ≤ (1 : ℝ) ^ (10 : ℕ) := pow_le_pow_left₀ ht0 ht1 10
        simpa using! this
      have hK0 : 0 ≤ K := by
        dsimp [K]
        positivity [hCψ0]
      have hnonneg : 0 ≤ bound t := by
        dsimp [bound, K]
        exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) n) hCψ0) (pow_nonneg ht0 10)
      have hle : bound t ≤ K :=
        mul_le_of_le_one_right hK0 ht10
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hK0] using! hle
    exact Integrable.mono' hK hmeas hbound_ae
  let Kn : ℝ := ∫ t, bound t ∂μ
  have hKn_nonneg : 0 ≤ Kn := by
    have hbound0 : ∀ᵐ t ∂μ, 0 ≤ bound t := by
      filter_upwards [hμmem] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht.1
      have hconst : 0 ≤ ((2 * Real.pi) ^ n) * Cψ := by positivity [hCψ0]
      exact mul_nonneg hconst (pow_nonneg ht0 10)
    exact integral_nonneg_of_ae hbound0
  refine ⟨Kn * B, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := hx
  have hnorm_iter' :
      ‖iteratedFDeriv ℝ n RealIntegrals.J₁' x‖ = ‖iteratedDeriv n RealIntegrals.J₁' x‖ :=
    norm_iteratedFDeriv_eq_norm_iteratedDeriv
  have hIrepr : iteratedDeriv n RealIntegrals.J₁' x = I n x := by
    simpa using! congrArg (fun F : ℝ → ℂ => F x) hiterJ
  have hIbound : ‖I n x‖ ≤ Kn * Real.exp (-2 * Real.pi * Real.sqrt x) := by
    -- bound the integral defining `I n x`
    have hnorm :
        ‖I n x‖ ≤ ∫ t, ‖gN n x t‖ ∂μ := norm_integral_le_integral_norm _
    have hbound_ae :
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-2 * Real.pi * Real.sqrt x) := by
      filter_upwards [hμmem] with t ht
      have ht0 : 0 < t := ht.1
      have ht0' : 0 ≤ t := le_of_lt ht.1
      have ht1 : t < 1 := ht.2
      have ht1' : t ≤ 1 := le_of_lt ht1
      have hψT : ‖ψT' (z₁' t)‖ ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (10 : ℕ) := by
        simpa using!
          (MagicFunction.norm_modular_rewrite_Ioc_exp_bound
            (k := (10 : ℕ)) (Cψ := Cψ) (ψS := ψS) (ψZ := ψT') (z := z₁')
            (hCψ := hCψ) (hEq := ψT'_z₁'_eq) (t := t) ⟨ht0, ht1'⟩)
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
      have hExp :
          Real.exp (-Real.pi / t) * Real.exp (-Real.pi * x * t) ≤
            Real.exp (-2 * Real.pi * Real.sqrt x) :=
        SpherePacking.ForMathlib.exp_neg_pi_div_mul_exp_neg_pi_mul_le (x := x) (t := t) hx0 ht0
      have hg :
          ‖g x t‖ = ‖ψT' (z₁' t)‖ * Real.exp (-Real.pi * x * t) := by
        simp [g, hcexp, mul_assoc, mul_left_comm, mul_comm]
      have hgn0 :
          ‖gN n x t‖ = ‖coeff t‖ ^ n * ‖ψT' (z₁' t)‖ * Real.exp (-Real.pi * x * t) := by
        simp [gN, hg, mul_assoc, mul_left_comm, mul_comm, norm_pow]
      have hψT' :
          ‖ψT' (z₁' t)‖ * Real.exp (-Real.pi * x * t) ≤
            (Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (10 : ℕ)) *
              Real.exp (-Real.pi * x * t) :=
        mul_le_mul_of_nonneg_right hψT (by positivity)
      let W : ℝ :=
        (Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (10 : ℕ)) * Real.exp (-Real.pi * x * t)
      have hcoeff0 :
          0 ≤ W := by
        positivity
      have hmul :
          ‖coeff t‖ ^ n * (‖ψT' (z₁' t)‖ * Real.exp (-Real.pi * x * t)) ≤
            (2 * Real.pi) ^ n *
              W := by
        have h1 :
            ‖coeff t‖ ^ n * (‖ψT' (z₁' t)‖ * Real.exp (-Real.pi * x * t)) ≤
              ‖coeff t‖ ^ n *
                W :=
          mul_le_mul_of_nonneg_left hψT' (by positivity)
        have hcoeff : ‖coeff t‖ ^ n ≤ (2 * Real.pi) ^ n := by
          exact pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n
        exact le_mul_of_le_mul_of_nonneg_right h1 hcoeff hcoeff0
      have hboundt : 0 ≤ bound t := by
        have hpos : 0 ≤ ((2 * Real.pi) ^ n : ℝ) := pow_nonneg (by positivity) n
        have hpos' : 0 ≤ ((2 * Real.pi) ^ n) * Cψ := mul_nonneg hpos hCψ0
        exact mul_nonneg hpos' (pow_nonneg ht0' 10)
      have hgn :
          ‖gN n x t‖ ≤ bound t * (Real.exp (-Real.pi / t) * Real.exp (-Real.pi * x * t)) := by
        grind only
      exact le_mul_of_le_mul_of_nonneg_left hgn hExp hboundt
    have hle :
        ∫ t, ‖gN n x t‖ ∂μ ≤ ∫ t, bound t * Real.exp (-2 * Real.pi * Real.sqrt x) ∂μ := by
      have hbound_int' :
          Integrable (fun t ↦ bound t * Real.exp (-2 * Real.pi * Real.sqrt x)) μ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using!
          hbound_int.mul_const (Real.exp (-2 * Real.pi * Real.sqrt x))
      refine integral_mono_of_nonneg ?_ hbound_int' hbound_ae
      exact (Filter.Eventually.of_forall fun t => norm_nonneg (gN n x t))
    have hconst :
        (∫ t, bound t * Real.exp (-2 * Real.pi * Real.sqrt x) ∂μ) =
          Kn * Real.exp (-2 * Real.pi * Real.sqrt x) :=
      integral_mul_const (Real.exp (-2 * Real.pi * √x)) bound
    have : ‖I n x‖ ≤ Kn * Real.exp (-2 * Real.pi * Real.sqrt x) :=
      hnorm.trans (hle.trans_eq hconst)
    simpa [Kn] using! this
  have hpoly : x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x) ≤ B := by
    simpa [mul_assoc] using! hB x hx
  have hKn0 : 0 ≤ Kn := hKn_nonneg
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₁' x‖
        = x ^ k * ‖iteratedDeriv n RealIntegrals.J₁' x‖ := by simp [hxabs hx0, hnorm_iter']
    _ = x ^ k * ‖I n x‖ := by simp [hIrepr]
    _ ≤ x ^ k * (Kn * Real.exp (-2 * Real.pi * Real.sqrt x)) := by gcongr
    _ = Kn * (x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x)) := by ring_nf
    _ ≤ Kn * B := by simpa using! (mul_le_mul_of_nonneg_left hpoly hKn0)
    _ = Kn * B := rfl

end SpherePacking.Dim24.Schwartz.J1Smooth

end
