-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.J6Derivatives
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSlash
import SpherePacking.ForMathlib.ContDiffOnByDeriv
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.ExpBounds
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.Integration.J6Integrable


/-!
# Smoothness and one-sided Schwartz decay for `RealIntegrals.J₆'`

We rewrite the defining integral of `J₆'` in terms of the parametrized integrand `g` from
`J6Derivatives` and use differentiation under the integral to obtain smoothness on `(-1,∞)` and
one-sided Schwartz decay bounds on `x ≥ 0`.

## Main statements
* `Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1`
* `Schwartz.J6Smooth.decay_J₆'`
-/

noncomputable section

namespace SpherePacking.Dim24.Schwartz.J6Smooth

open Complex Real Set MeasureTheory Filter
open UpperHalfPlane
open MagicFunction.Parametrisations RealIntegrals PsiExpBounds

lemma integral_J6_integrand_eq_integral_g (x : ℝ) :
    (∫ t in Ici (1 : ℝ),
          (Complex.I : ℂ) * ψS' (z₆' t) *
            cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₆' t))) =
      ∫ t in Ici (1 : ℝ), g x t := by
  refine integral_congr_ae ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by simp) ht
  have hz : z₆' t = (Complex.I : ℂ) * t := z₆'_eq_of_mem ht
  have hψ : ψS' (z₆' t) = ψS.resToImagAxis t := by
    have : ψS' ((Complex.I : ℂ) * t) = ψS.resToImagAxis t := by
      simp [ψS', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
    simpa [hz] using! this
  have hcexp :
      cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₆' t)) = cexp ((x : ℂ) * coeff t) := by
    have harg :
        (Real.pi : ℂ) * (Complex.I : ℂ) * (x : ℂ) * (z₆' t) = (x : ℂ) * coeff t := by
      have hz' : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by
        simpa using! hz
      calc
        (Real.pi : ℂ) * (Complex.I : ℂ) * (x : ℂ) * (z₆' t)
            = (Real.pi : ℂ) * (Complex.I : ℂ) * (x : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) := by
                simp [hz']
        _ = (Real.pi : ℂ) * (x : ℂ) * (t : ℂ) * ((Complex.I : ℂ) * (Complex.I : ℂ)) := by
                ac_rfl
        _ = (Real.pi : ℂ) * (x : ℂ) * (t : ℂ) * (-1 : ℂ) := by
                simp [I_mul_I]
        _ = (x : ℂ) * ((-Real.pi : ℂ) * (t : ℂ)) := by ring_nf
        _ = (x : ℂ) * coeff t := by
                simp [coeff]
    simp [harg]
  have hgoal :
      (Complex.I : ℂ) * ψS' (z₆' t) *
          cexp (Real.pi * (Complex.I : ℂ) * (x : ℂ) * (z₆' t)) =
        g x t := by
    rw [hψ, hcexp]
    simp [g, coeff, mul_assoc, mul_comm]
  simpa using! hgoal

/-- The contour-integral term `J₆'` is smooth on the open set `(-1,∞)`. -/
public theorem contDiffOn_J₆'_Ioi_neg1 :
    ContDiffOn ℝ (⊤ : ℕ∞) RealIntegrals.J₆' (Ioi (-1 : ℝ)) := by
  have hJ : ContDiffOn ℝ (⊤ : ℕ∞) RealIntegrals.J₆' s := by
    have hF0 : ContDiffOn ℝ (⊤ : ℕ∞) (F 0) s := by
      simpa using!
        (SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt (F := F) (s := s) isOpen_s
          (fun n x hx => by simpa using! (hasDerivAt_F (n := n) (x := x) hx)) 0)
    have hmul : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ (-2 : ℂ) * F 0 x) s := by
      have hconst : ContDiffOn ℝ (⊤ : ℕ∞) (fun _x : ℝ ↦ (-2 : ℂ)) s := contDiffOn_const
      simpa [mul_assoc] using! hconst.mul hF0
    refine hmul.congr ?_
    intro x hx
    have hEq :
        RealIntegrals.J₆' x = (-2 : ℂ) * ∫ t in Ici (1 : ℝ), g x t := by
      have hInt := integral_J6_integrand_eq_integral_g (x := x)
      have h' := congrArg (fun J : ℂ => (-2 : ℂ) * J) hInt
      simpa [RealIntegrals.J₆', mul_assoc, mul_left_comm, mul_comm] using! h'
    have hF0' : F 0 x = ∫ t in Ici (1 : ℝ), g x t := by
      simp [F, gN, g, coeff]
    simpa [hF0'] using! hEq
  simpa [s] using! hJ

/-- One-sided Schwartz decay for `J₆'` on `x ≥ 0`. -/
public theorem decay_J₆' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul (k := k) (b := Real.pi) Real.pi_pos
  rcases exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with ⟨Cψ, hCψ⟩
  have hCψ0 : 0 ≤ Cψ := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := Cψ) (norm_nonneg _) (by positivity) ?_
    simpa using! (hCψ 1 (le_rfl : (1 : ℝ) ≤ 1))
  let bound : ℝ → ℝ := fun t ↦ (Real.pi ^ n) * (t ^ n * Real.exp (-Real.pi * t)) * Cψ
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  have hbound_int : Integrable bound (μ) := by
    have hInt :
        IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-Real.pi * t)) (Ici (1 : ℝ)) volume :=
      SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := n) (b := Real.pi)
        (by simpa using! Real.pi_pos)
    have : Integrable (fun t : ℝ ↦ t ^ n * Real.exp (-Real.pi * t)) (μ) := by
      simpa [IntegrableOn, μ] using! hInt
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using!
      this.const_mul ((Real.pi ^ n) * Cψ)
  let Kn : ℝ := ∫ t, bound t ∂μ
  have hKn_nonneg : 0 ≤ Kn := by
    have hnonneg : 0 ≤ᵐ[μ] fun t ↦ bound t := by
      refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
      intro t ht
      have ht0 : 0 ≤ t := le_trans (by simp : (0 : ℝ) ≤ 1) ht
      have : 0 ≤ (t ^ n * Real.exp (-Real.pi * t)) := by positivity
      have hpi : 0 ≤ (Real.pi ^ n : ℝ) := pow_nonneg Real.pi_pos.le n
      have : 0 ≤ (Real.pi ^ n) * (t ^ n * Real.exp (-Real.pi * t)) := mul_nonneg hpi this
      have : 0 ≤ (Real.pi ^ n) * (t ^ n * Real.exp (-Real.pi * t)) * Cψ := mul_nonneg this hCψ0
      simpa [bound] using! this
    simpa [Kn] using! (integral_nonneg_of_ae hnonneg)
  let C : ℝ := 2 * Kn * B
  refine ⟨C, ?_⟩
  intro x hx
  have hxabs : ‖x‖ = x := by simp [Real.norm_eq_abs, abs_of_nonneg hx]
  have hx_s : x ∈ s := by
    have : (-1 : ℝ) < x := lt_of_lt_of_le (by simp) hx
    simpa [s] using! this
  have hiter : iteratedDeriv n RealIntegrals.J₆' x = G n x := by
    have hfun : RealIntegrals.J₆' = G 0 := by
      funext y
      have hInt := integral_J6_integrand_eq_integral_g (x := y)
      have h' := congrArg (fun J : ℂ => (-2 : ℂ) * J) hInt
      have hF0' : F 0 y = ∫ t in Ici (1 : ℝ), g y t := by
        simp [F, gN, g, coeff]
      simpa [RealIntegrals.J₆', G, hF0', mul_assoc, mul_left_comm, mul_comm] using! h'
    have hEq0 : iteratedDeriv n RealIntegrals.J₆' x = iteratedDeriv n (G 0) x := by
      simp [hfun]
    have hs : IsOpen s := by simpa [s] using! (isOpen_Ioi : IsOpen (Ioi (-1 : ℝ)))
    have hEqOn :=
      SpherePacking.ForMathlib.eqOn_iteratedDeriv_eq_of_deriv_eq (hs := hs) (G := G)
        (hderiv := fun n x hx => deriv_G (n := n) (x := x) hx)
    have hG : iteratedDeriv n (G 0) x = G (n + 0) x := (hEqOn n 0) hx_s
    simpa [Nat.add_zero] using! hEq0.trans hG
  have hnorm_iter :
      ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖ = ‖iteratedDeriv n RealIntegrals.J₆' x‖ := by
    exact norm_iteratedFDeriv_eq_norm_iteratedDeriv
  have hGbound : ‖G n x‖ ≤ 2 * Kn * Real.exp (-Real.pi * x) := by
    have hx' : x ∈ s := hx_s
    have hFn : ‖F n x‖ ≤ Kn * Real.exp (-Real.pi * x) := by
      have hgn_int : Integrable (gN n x) μ := by
        have hx'' : -1 < x := by simpa [s] using! hx'
        have hmeas0 : AEStronglyMeasurable (gN n x) μ := by
          exact gN_measurable (n := n) (x := x)
        have hmeas :
            AEStronglyMeasurable
              (SpherePacking.Integration.gN_J6_integrand ψS.resToImagAxis n x) μ := by
          assumption
        have hInt :=
          (SpherePacking.Integration.integrable_gN_J6 (f := ψS.resToImagAxis)
            (hBound := PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one)
            (n := n) (x := x) hx'' (hmeas := hmeas))
        assumption
      have hnorm : ‖F n x‖ ≤ ∫ t, ‖gN n x t‖ ∂μ := by
        have : F n x = ∫ t, gN n x t ∂μ := by
          simp [F, μ]
        simpa [this] using! (MeasureTheory.norm_integral_le_integral_norm (μ := μ) (f := gN n x))
      have hbound_ae :
          ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-Real.pi * x) := by
        refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
        intro t ht
        have hx0 : 0 ≤ x := hx
        have hcoeff' : ‖coeff t‖ ^ n ≤ (Real.pi * t) ^ n := by
          have : ‖coeff t‖ = Real.pi * t := coeff_norm t ht
          simp [this]
        have hψ : ‖ψS.resToImagAxis t‖ ≤ Cψ * Real.exp (-Real.pi * t) := hCψ t ht
        have hg : ‖g x t‖ ≤ ‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t) :=
          g_norm_bound (x := x) (t := t)
        have hxexp : Real.exp (-Real.pi * x * t) ≤ Real.exp (-Real.pi * x) :=
          SpherePacking.ForMathlib.exp_neg_mul_mul_le_exp_neg_mul_of_one_le
            (b := Real.pi) (x := x) (t := t) Real.pi_pos.le hx0 (show (1 : ℝ) ≤ t from ht)
        calc
          ‖gN n x t‖ = ‖coeff t‖ ^ n * ‖g x t‖ := by
            simp [gN, g, coeff]
          _ ≤ (Real.pi * t) ^ n * (‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t)) := by
            have ht0 : 0 ≤ t := le_trans (by simp : (0 : ℝ) ≤ 1) ht
            have hpit_nonneg : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht0
            have hpitn_nonneg : 0 ≤ (Real.pi * t) ^ n := pow_nonneg hpit_nonneg n
            have hn : ‖coeff t‖ ^ n * ‖g x t‖ ≤ (Real.pi * t) ^ n * ‖g x t‖ :=
              mul_le_mul_of_nonneg_right hcoeff' (norm_nonneg (g x t))
            exact le_mul_of_le_mul_of_nonneg_left hn hg hpitn_nonneg
          _ ≤ (Real.pi * t) ^ n * ((Cψ * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x)) := by
            have ht0 : 0 ≤ t := le_trans (by simp : (0 : ℝ) ≤ 1) ht
            have hpit_nonneg : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht0
            have hpitn_nonneg : 0 ≤ (Real.pi * t) ^ n := pow_nonneg hpit_nonneg n
            have h0 : 0 ≤ Real.exp (-Real.pi * x * t) := by positivity
            have h1 : 0 ≤ Cψ * Real.exp (-Real.pi * t) :=
              mul_nonneg hCψ0 (Real.exp_nonneg _)
            have hmul :
                ‖ψS.resToImagAxis t‖ * Real.exp (-Real.pi * x * t) ≤
                  (Cψ * Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * x) :=
              mul_le_mul hψ hxexp h0 h1
            exact mul_le_mul_of_nonneg_left hmul hpitn_nonneg
          _ = bound t * Real.exp (-Real.pi * x) := by
            ring
      have hbound_int' : Integrable (fun t ↦ bound t * Real.exp (-Real.pi * x)) μ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using!
          hbound_int.mul_const (Real.exp (-Real.pi * x))
      have hle :
          ∫ t, ‖gN n x t‖ ∂μ ≤ ∫ t, bound t * Real.exp (-Real.pi * x) ∂μ := by
        refine integral_mono_of_nonneg ?_ hbound_int' hbound_ae
        exact (Eventually.of_forall fun t => norm_nonneg (gN n x t))
      have :
          ‖F n x‖ ≤ ∫ t, bound t * Real.exp (-Real.pi * x) ∂μ := hnorm.trans hle
      have hconst :
          (∫ t, bound t * Real.exp (-Real.pi * x) ∂μ) = Kn * Real.exp (-Real.pi * x) := by
        simpa [Kn] using!
          (MeasureTheory.integral_mul_const (μ := μ) (r := Real.exp (-Real.pi * x)) (f := bound))
      exact this.trans (le_of_eq hconst)
    calc
      ‖G n x‖ ≤ 2 * (Kn * Real.exp (-Real.pi * x)) := by
        simpa [G, mul_assoc] using!
          (SpherePacking.ForMathlib.norm_neg_two_mul_le
            (z := F n x) (B := Kn * Real.exp (-Real.pi * x)) hFn)
      _ = 2 * Kn * Real.exp (-Real.pi * x) := by ring_nf
  have hpoly : x ^ k * Real.exp (-Real.pi * x) ≤ B := hB x hx
  have hpow0 : 0 ≤ 2 * Kn := by nlinarith [hKn_nonneg]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₆' x‖
        = x ^ k * ‖iteratedDeriv n RealIntegrals.J₆' x‖ := by simp [hxabs, hnorm_iter]
    _ = x ^ k * ‖G n x‖ := by simp [hiter]
    _ ≤ x ^ k * (2 * Kn * Real.exp (-Real.pi * x)) := by gcongr
    _ = (2 * Kn) * (x ^ k * Real.exp (-Real.pi * x)) := by ring_nf
    _ ≤ (2 * Kn) * B := by simpa using! (mul_le_mul_of_nonneg_left hpoly hpow0)
    _ ≤ (2 * Kn * B) * 1 := by nlinarith
    _ = C := by simp [C, mul_assoc]

end SpherePacking.Dim24.Schwartz.J6Smooth

end
