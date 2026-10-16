-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Prelude
import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I6Differentiation
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.ForMathlib.ExpBounds
import SpherePacking.ForMathlib.ContDiffOnByDeriv
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.ForMathlib.DerivHelpers


/-!
# Smoothness and decay of `I₆'`

This file proves smoothness on an open set and one-sided Schwartz decay bounds for the profile
integral `RealIntegrals.I₆'`.

## Main statements
* `Schwartz.I6Smooth.contDiffOn_I₆'_Ioi_neg1`
* `Schwartz.I6Smooth.decay_I₆'`
-/

open scoped ContDiff

namespace SpherePacking.Dim24

noncomputable section

namespace Schwartz

open MeasureTheory Filter Topology

namespace I6Smooth

open SpherePacking.Integration (μIciOne)
open MagicFunction.Parametrisations

theorem contDiffOn_I₆' : ContDiffOn ℝ ∞ SpherePacking.Dim24.RealIntegrals.I₆' s := by
  have hF0 : ContDiffOn ℝ ∞ (F 0) s := by
    simpa using!
      (SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt (F := F) (s := s) isOpen_s
        (fun n x hx => by simpa using! (hasDerivAt_F (n := n) (x := x) hx)) 0)
  have hmul : ContDiffOn ℝ ∞ (fun x : ℝ ↦ (2 : ℂ) * F 0 x) s := by
    simpa using! (contDiffOn_const.mul hF0)
  refine hmul.congr ?_
  intro x hx
  have hEq :
      RealIntegrals.I₆' x = (2 : ℂ) * ∫ t in Set.Ici (1 : ℝ), g x t := by
    have hInt :
        (∫ t in Set.Ici (1 : ℝ), RealIntegrals.RealIntegrands.Φ₆ x t) =
          ∫ t in Set.Ici (1 : ℝ), g x t := by
      refine integral_congr_ae ?_
      refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
      have hz : z₆' t = (Complex.I : ℂ) * t := z₆'_eq_of_mem ht
      have hvarphi' : varphi' (z₆' t) = varphi.resToImagAxis t := by
        simp [hz, varphi', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
      have hcexp :
          Complex.exp (Real.pi * Complex.I * (x : ℂ) * (z₆' t)) =
            Complex.exp ((x : ℂ) * coeff t) := by
        have hz' : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by simpa using! hz
        have harg :
            (Real.pi : ℂ) * (Complex.I : ℂ) * (x : ℂ) * (z₆' t) = (x : ℂ) * coeff t := by
          calc
            (Real.pi : ℂ) * (Complex.I : ℂ) * (x : ℂ) * (z₆' t) =
                (Real.pi : ℂ) * (Complex.I : ℂ) * (x : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) := by
                  simp [hz']
            _ = (Real.pi : ℂ) * (x : ℂ) * (t : ℂ) * ((Complex.I : ℂ) * (Complex.I : ℂ)) := by
                  ac_rfl
            _ = (Real.pi : ℂ) * (x : ℂ) * (t : ℂ) * (-1 : ℂ) := by
                  simp [Complex.I_mul_I]
            _ = (x : ℂ) * ((-Real.pi * t : ℂ)) := by
                  ring_nf
            _ = (x : ℂ) * coeff t := by
                  simp [coeff, SpherePacking.Integration.SmoothIntegralIciOne.coeff, mul_comm]
        simp [harg]
      -- Expand both sides and rewrite the `varphi'` and exponential terms.
      calc
        RealIntegrals.RealIntegrands.Φ₆ x t
            = (Complex.I : ℂ) *
                (varphi' (z₆' t) * Complex.exp (Real.pi * Complex.I * (x : ℂ) * (z₆' t))) := by
              simp [RealIntegrals.RealIntegrands.Φ₆, RealIntegrals.ComplexIntegrands.Φ₆']
          _ = (Complex.I : ℂ) * (varphi.resToImagAxis t * Complex.exp ((x : ℂ) * coeff t)) := by
              simp [hvarphi', hcexp]
          _ = g x t := by
              simp [g, coeff, SpherePacking.Integration.SmoothIntegralIciOne.g,
                SpherePacking.Integration.SmoothIntegralIciOne.coeff]
    have h' := congrArg (fun J : ℂ => (2 : ℂ) * J) hInt
    simpa [RealIntegrals.I₆', mul_assoc, mul_left_comm, mul_comm] using! h'
  have hF0' : F 0 x = ∫ t in Set.Ici (1 : ℝ), g x t := by
    simp [F, gN, g, SpherePacking.Integration.SmoothIntegralIciOne.gN]
  simpa [hF0'] using! hEq

/-- Smoothness of `I₆'` on the open ray `(-1, ∞)`. -/
public theorem contDiffOn_I₆'_Ioi_neg1 :
    ContDiffOn ℝ ∞ RealIntegrals.I₆' (Set.Ioi (-1 : ℝ)) := by
  simpa [s] using! (contDiffOn_I₆' : ContDiffOn ℝ ∞ RealIntegrals.I₆' s)

/-- One-sided Schwartz decay of `I₆'` on the ray `0 ≤ x`. -/
public theorem decay_I₆' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₆' x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul (k := k) (b := Real.pi) Real.pi_pos
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ, hCφ⟩
  have hCφ0 : 0 ≤ Cφ := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖varphi.resToImagAxis 1‖)
      (b := Real.exp (-(2 * Real.pi) * (1 : ℝ))) (C := Cφ) (norm_nonneg _) (by positivity) ?_
    simpa using! (hCφ 1 (le_rfl : (1 : ℝ) ≤ 1))
  let bound : ℝ → ℝ := fun t ↦ (Real.pi ^ n) * (t ^ n * Real.exp (-(2 * Real.pi) * t)) * Cφ
  have hbound_int : Integrable bound μIciOne := by
    have hInt :
        IntegrableOn
          (fun t : ℝ ↦ t ^ n * Real.exp (-(2 * Real.pi) * t))
          (Set.Ici (1 : ℝ)) volume :=
      SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := (2 * Real.pi))
        (by positivity [Real.pi_pos])
    have :
        Integrable (fun t : ℝ ↦ t ^ n * Real.exp (-(2 * Real.pi) * t)) μIciOne := by
      simpa [IntegrableOn, μIciOne] using! hInt
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using!
      this.const_mul ((Real.pi ^ n) * Cφ)
  let Kn : ℝ := ∫ t, bound t ∂μIciOne
  have hKn_nonneg : 0 ≤ Kn := by
    have hnonneg : 0 ≤ᵐ[μIciOne] fun t ↦ bound t := by
      refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
      intro t ht
      have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
      have : 0 ≤ (t ^ n * Real.exp (-(2 * Real.pi) * t)) := by positivity
      have hpi : 0 ≤ (Real.pi ^ n : ℝ) := pow_nonneg Real.pi_pos.le n
      have hbase :
          0 ≤ (Real.pi ^ n) * (t ^ n * Real.exp (-(2 * Real.pi) * t)) :=
        mul_nonneg hpi this
      have hprod :
          0 ≤ (Real.pi ^ n) * (t ^ n * Real.exp (-(2 * Real.pi) * t)) * Cφ := by
        exact mul_nonneg hbase hCφ0
      simpa [bound] using! hprod
    simpa [Kn] using! (integral_nonneg_of_ae hnonneg)
  let C : ℝ := 2 * Kn * B
  refine ⟨C, ?_⟩
  intro x hx
  have hxabs : ‖x‖ = x := by simp [Real.norm_eq_abs, abs_of_nonneg hx]
  have hx_s : x ∈ s := by
    have : (-1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
    simpa [s] using! this
  have hiter : iteratedDeriv n RealIntegrals.I₆' x = G n x := by
    have hfun : RealIntegrals.I₆' = G 0 := by
      funext y
      have hInt :
          (∫ t in Set.Ici (1 : ℝ), RealIntegrals.RealIntegrands.Φ₆ y t) =
            ∫ t in Set.Ici (1 : ℝ), g y t := by
        refine integral_congr_ae ?_
        refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
        have hz : z₆' t = (Complex.I : ℂ) * t := z₆'_eq_of_mem ht
        have hvarphi' : varphi' (z₆' t) = varphi.resToImagAxis t := by
          have : varphi' ((Complex.I : ℂ) * t) = varphi.resToImagAxis t := by
            simp [varphi', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
          simpa [hz] using! this
        have hcexp :
            Complex.exp (Real.pi * Complex.I * (y : ℂ) * (z₆' t)) =
              Complex.exp ((y : ℂ) * coeff t) := by
          have hz' : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by simpa using! hz
          have harg :
              (Real.pi : ℂ) * (Complex.I : ℂ) * (y : ℂ) * (z₆' t) = (y : ℂ) * coeff t := by
            calc
              (Real.pi : ℂ) * (Complex.I : ℂ) * (y : ℂ) * (z₆' t)
                  = (Real.pi : ℂ) * (Complex.I : ℂ) * (y : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) := by
                      simp [hz']
              _ = (Real.pi : ℂ) * (y : ℂ) * (t : ℂ) * ((Complex.I : ℂ) * (Complex.I : ℂ)) := by
                      ac_rfl
              _ = (Real.pi : ℂ) * (y : ℂ) * (t : ℂ) * (-1 : ℂ) := by
                      simp [Complex.I_mul_I]
              _ = (y : ℂ) * ((-Real.pi : ℂ) * (t : ℂ)) := by ring_nf
              _ = (y : ℂ) * coeff t := by
                      simp [coeff, SpherePacking.Integration.SmoothIntegralIciOne.coeff, mul_comm]
          simp [harg]
        calc
          RealIntegrals.RealIntegrands.Φ₆ y t
              = (Complex.I : ℂ) *
                  (varphi' (z₆' t) * Complex.exp (Real.pi * Complex.I * (y : ℂ) * (z₆' t))) := by
                simp [RealIntegrals.RealIntegrands.Φ₆, RealIntegrals.ComplexIntegrands.Φ₆']
          _ = (Complex.I : ℂ) * (varphi.resToImagAxis t * Complex.exp ((y : ℂ) * coeff t)) := by
                simp [hvarphi', hcexp]
          _ = g y t := by
                simp [g, coeff, SpherePacking.Integration.SmoothIntegralIciOne.g,
                  SpherePacking.Integration.SmoothIntegralIciOne.coeff]
      have h' := congrArg (fun J : ℂ => (2 : ℂ) * J) hInt
      simpa [RealIntegrals.I₆', G, F, gN, g, coeff,
        SpherePacking.Integration.SmoothIntegralIciOne.gN,
        mul_assoc, mul_left_comm, mul_comm] using! h'
    have hEq0 : iteratedDeriv n RealIntegrals.I₆' x = iteratedDeriv n (G 0) x := by
      simp [hfun]
    have hG : iteratedDeriv n (G 0) x = G (n + 0) x := (iteratedDeriv_G_eq (n := n) (m := 0)) hx_s
    simpa [Nat.add_zero] using! hEq0.trans hG
  have hnorm_iter' :
      ‖iteratedFDeriv ℝ n RealIntegrals.I₆' x‖ = ‖iteratedDeriv n RealIntegrals.I₆' x‖ := by
    exact norm_iteratedFDeriv_eq_norm_iteratedDeriv
  have hnorm :
      ‖G n x‖ ≤ (2 * Kn) * Real.exp (-Real.pi * x) := by
    -- Bound the integral defining `F n x` and pull out `exp(-π x)` since `t ≥ 1`.
    have hF_le :
        ‖F n x‖ ≤ Kn * Real.exp (-Real.pi * x) := by
      have hbound_ae :
          ∀ᵐ t ∂μIciOne, ‖gN n x t‖ ≤ bound t * Real.exp (-Real.pi * x) := by
        refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := ht
        have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht1
        have hcoeff : ‖coeff t‖ ^ n ≤ (Real.pi * t) ^ n := by
          have : ‖coeff t‖ = Real.pi * t := coeff_norm t ht
          simp [this]
        have hvarphi :
            ‖varphi.resToImagAxis t‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) :=
          hCφ t ht
        have hg' :
            ‖g x t‖ ≤ ‖varphi.resToImagAxis t‖ * Real.exp (-Real.pi * x * t) :=
          g_norm_bound (x := x) (t := t)
        have hexpx : Real.exp (-Real.pi * x * t) ≤ Real.exp (-Real.pi * x) :=
          SpherePacking.ForMathlib.exp_neg_mul_mul_le_exp_neg_mul_of_one_le
            (b := Real.pi) (x := x) (t := t) Real.pi_pos.le hx ht1
        calc
          ‖gN n x t‖ = ‖coeff t‖ ^ n * ‖g x t‖ := by
                simp [gN, g, coeff, SpherePacking.Integration.SmoothIntegralIciOne.gN,
                  SpherePacking.Integration.SmoothIntegralIciOne.g,
                  SpherePacking.Integration.SmoothIntegralIciOne.coeff]
          _ ≤ (Real.pi * t) ^ n * (‖varphi.resToImagAxis t‖ * Real.exp (-Real.pi * x * t)) := by
                gcongr
          _ ≤
              (Real.pi * t) ^ n *
                ((Cφ * Real.exp (-(2 * Real.pi) * t)) * Real.exp (-Real.pi * x)) := by
                have hnonneg : 0 ≤ Real.exp (-Real.pi * x * t) := (Real.exp_pos _).le
                have hleft_nonneg : 0 ≤ (Cφ * Real.exp (-(2 * Real.pi) * t)) := by
                  have : 0 ≤ Real.exp (-(2 * Real.pi) * t) := (Real.exp_pos _).le
                  exact mul_nonneg hCφ0 this
                have h1 :
                    ‖varphi.resToImagAxis t‖ *
                        Real.exp (-Real.pi * x * t) ≤
                      (Cφ * Real.exp (-(2 * Real.pi) * t)) *
                        Real.exp (-Real.pi * x * t) :=
                  mul_le_mul_of_nonneg_right hvarphi hnonneg
                have h2 :
                    (Cφ * Real.exp (-(2 * Real.pi) * t)) *
                        Real.exp (-Real.pi * x * t) ≤
                      (Cφ * Real.exp (-(2 * Real.pi) * t)) *
                        Real.exp (-Real.pi * x) :=
                  mul_le_mul_of_nonneg_left hexpx hleft_nonneg
                have h12 := h1.trans h2
                exact mul_le_mul_of_nonneg_left h12 (by positivity)
          _ = bound t * Real.exp (-Real.pi * x) := by
                ring
      have hle :
          ∫ t, ‖gN n x t‖ ∂μIciOne ≤ ∫ t, bound t * Real.exp (-Real.pi * x) ∂μIciOne := by
        have hbound_int' : Integrable (fun t ↦ bound t * Real.exp (-Real.pi * x)) μIciOne := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using!
            (hbound_int.mul_const (Real.exp (-Real.pi * x)))
        refine integral_mono_of_nonneg ?_ hbound_int' hbound_ae
        exact (Eventually.of_forall fun t => norm_nonneg (gN n x t))
      have hconst :
          (∫ t, bound t * Real.exp (-Real.pi * x) ∂μIciOne) = Kn * Real.exp (-Real.pi * x) := by
        exact integral_mul_const (Real.exp (-Real.pi * x)) bound
      have hnormF : ‖F n x‖ ≤ ∫ t, ‖gN n x t‖ ∂μIciOne := by
        have hgn_int : Integrable (gN n x) μIciOne := gN_integrable (n := n) (x := x) hx_s
        have : F n x = ∫ t, gN n x t ∂μIciOne := by
          simp [F, μIciOne]
        simpa [this] using!
          (MeasureTheory.norm_integral_le_integral_norm (μ := μIciOne) (f := gN n x))
      have : ‖F n x‖ ≤ Kn * Real.exp (-Real.pi * x) :=
        hnormF.trans (hle.trans_eq hconst)
      exact this
    have hG_eq : ‖G n x‖ = (2 : ℝ) * ‖F n x‖ := by
      simp [G]
    linarith
  have hpoly : x ^ k * Real.exp (-Real.pi * x) ≤ B := hB x hx
  have hKn0 : 0 ≤ (2 * Kn) := by nlinarith [hKn_nonneg]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₆' x‖
        = x ^ k * ‖iteratedDeriv n RealIntegrals.I₆' x‖ := by simp [hxabs, hnorm_iter']
    _ = x ^ k * ‖G n x‖ := by simp [hiter]
    _ ≤ x ^ k * ((2 * Kn) * Real.exp (-Real.pi * x)) := by gcongr
    _ = (2 * Kn) * (x ^ k * Real.exp (-Real.pi * x)) := by ring_nf
    _ ≤ (2 * Kn) * B := by simpa using! (mul_le_mul_of_nonneg_left hpoly hKn0)
    _ = C := by simp [C]


end Schwartz.I6Smooth
end

end SpherePacking.Dim24
