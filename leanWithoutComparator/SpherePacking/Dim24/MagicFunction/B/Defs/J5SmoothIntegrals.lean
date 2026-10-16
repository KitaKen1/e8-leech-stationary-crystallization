-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
import SpherePacking.Dim24.MagicFunction.B.Defs.J5Smooth
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSDecay
import SpherePacking.MagicFunction.PsiTPrimeZ1
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.ForMathlib.ExpBounds
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.Integration.Measure


/-!
# Smoothness and one-sided Schwartz decay for `RealIntegrals.J₅'`

We define the integral functional `I n x := ∫ gN n x t dt` over `t ∈ (0,1)` and use
differentiation under the integral to compute iterated derivatives. In particular, `J₅'` is
smooth on `ℝ` and satisfies a one-sided Schwartz decay bound on `x ≥ 0`.

## Main statements
* `Schwartz.J5Smooth.contDiff_J₅'`
* `Schwartz.J5Smooth.decay_J₅'`
-/

noncomputable section


namespace SpherePacking.Dim24.Schwartz.J5Smooth

open Set
open MeasureTheory
open scoped Complex

open MagicFunction.Parametrisations
open intervalIntegral
open SpherePacking.Integration (μIoo01)

private def μ : Measure ℝ := μIoo01

private instance : IsFiniteMeasure μ := by
  refine ⟨by simp [μ, μIoo01]⟩

def I (n : ℕ) (x : ℝ) : ℂ := ∫ t, gN n x t ∂μ

lemma hasDerivAt_integral_gN (n : ℕ) (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ I n x) (I (n + 1) x₀) x₀ := by
  have hψ : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) * ψI' (z₅' t)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.mul continuousOn_ψI'_z₅'
  have hexists_hf :
      ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖((Complex.I : ℂ) * ψI' (z₅' t))‖ ≤ M := by
    rcases exists_bound_norm_ψI'_z₅' with ⟨Mψ, hMψ⟩
    refine ⟨Mψ, ?_⟩
    intro t ht
    have h : ‖ψI' (z₅' t)‖ ≤ Mψ := hMψ t ht
    have : ‖(Complex.I : ℂ)‖ * ‖ψI' (z₅' t)‖ ≤ Mψ := by simpa using! h
    simpa [norm_mul] using! this
  simpa [I, μ, μIoo01, gN, g, coeff,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g,
    mul_assoc, mul_left_comm, mul_comm] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.hasDerivAt_integral_gN_Ioo
      (coeff := coeff) (hf := fun t => (Complex.I : ℂ) * ψI' (z₅' t))
      hψ continuous_coeff hexists_hf (fun t => coeff_norm_le t) n x₀)

lemma J₅'_eq_integral_g_Ioo (x : ℝ) :
    RealIntegrals.J₅' x = (-2 : ℂ) * I 0 x := by
  -- Replace the interval integral over `Ioc` by an integral over `Ioo`
  -- endpoints have measure zero.
  simp [RealIntegrals.J₅', I, g, gN, coeff, μ, μIoo01,
    intervalIntegral_eq_integral_uIoc, zero_le_one, uIoc_of_le, integral_Ioc_eq_integral_Ioo,
    mul_assoc, mul_left_comm, mul_comm]

/-- The contour-integral term `J₅'` is smooth on `ℝ`. -/
public theorem contDiff_J₅' : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.J₅' := by
  -- We deduce smoothness of `J₅'` from the integral representation and smoothness of `I 0`.
  have hI : ∀ n x, HasDerivAt (fun y : ℝ => I n y) (I (n + 1) x) x := by
    intro n x
    simpa using! hasDerivAt_integral_gN (n := n) (x₀ := x)
  have hcontI : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => I 0 x) :=
    SpherePacking.ForMathlib.contDiff_of_hasDerivAt_succ (I := I) hI
  have hmul : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ (-2 : ℂ) * I 0 x) :=
    contDiff_const.mul hcontI
  -- `simp` tends to rewrite `(-2) * f` as `-(2 * f)`, so match that normal form.
  have hEq : (fun x : ℝ ↦ -(2 * I 0 x)) = RealIntegrals.J₅' := by
    funext x
    simpa [mul_assoc] using! (J₅'_eq_integral_g_Ioo (x := x)).symm
  simpa [hEq] using! hmul

/-- One-sided Schwartz decay for `J₅'` on `x ≥ 0`. -/
public theorem decay_J₅' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₅' x‖ ≤ C := by
  intro k n
  obtain ⟨B, hB⟩ :=
    SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul_sqrt (k := k) (b := 2 * Real.pi)
      (by positivity)
  rcases PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with ⟨Cψ, hCψ⟩
  have hCψ0 : 0 ≤ Cψ := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖ψS.resToImagAxis 1‖)
      (b := Real.exp (-Real.pi * (1 : ℝ))) (C := Cψ) (norm_nonneg _) (by positivity) ?_
    simpa using! (hCψ 1 (le_rfl : (1 : ℝ) ≤ 1))
  have hμmem : ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 := by
    simpa [μ, μIoo01] using!
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo)
  -- Bound the integral defining `I n x` using the exponential decay of `ψS` at infinity.
  let bound : ℝ → ℝ := fun t ↦ ((2 * Real.pi) ^ n) * Cψ * t ^ (10 : ℕ)
  have hbound_int : Integrable bound μ := by
    have hA : 0 ≤ ((2 * Real.pi) ^ n) * Cψ := by positivity [hCψ0]
    simpa [bound, μ, μIoo01, mul_assoc, mul_left_comm, mul_comm] using!
      (SpherePacking.Integration.integrable_const_mul_pow_muIoo01
        (((2 * Real.pi) ^ n) * Cψ) 10 hA)
  let Kn : ℝ := ∫ t, bound t ∂μ
  have hKn_nonneg : 0 ≤ Kn := by
    have hA : 0 ≤ ((2 * Real.pi) ^ n) * Cψ := by positivity [hCψ0]
    simpa [Kn, bound, μ, μIoo01, mul_assoc, mul_left_comm, mul_comm] using!
      (SpherePacking.Integration.integral_nonneg_const_mul_pow_muIoo01
        (((2 * Real.pi) ^ n) * Cψ) 10 hA)
  let C : ℝ := 2 * Kn * B
  refine ⟨C, ?_⟩
  intro x hx
  have hxabs : ‖x‖ = x := by simp [Real.norm_eq_abs, abs_of_nonneg hx]
  have hnorm_iter :
      ‖iteratedFDeriv ℝ n RealIntegrals.J₅' x‖ = ‖iteratedDeriv n RealIntegrals.J₅' x‖ :=
    norm_iteratedFDeriv_eq_norm_iteratedDeriv
  -- Express `iteratedDeriv n J₅'` in terms of `I n`.
  have hJfun : RealIntegrals.J₅' = fun x : ℝ ↦ (-2 : ℂ) * I 0 x := by
    funext y
    simpa [mul_assoc] using! (J₅'_eq_integral_g_Ioo (x := y))
  have hiterJ :
      iteratedDeriv n RealIntegrals.J₅' x = (-2 : ℂ) * I n x := by
    let J : ℕ → ℝ → ℂ := fun m y => (-2 : ℂ) * I m y
    have hJ : ∀ m y, HasDerivAt (fun z : ℝ => J m z) (J (m + 1) y) y := by
      intro m y
      simpa [J, mul_assoc] using! (hasDerivAt_integral_gN (n := m) (x₀ := y)).const_mul (-2 : ℂ)
    have hiterJfun : iteratedDeriv n (fun y : ℝ => J 0 y) = fun y : ℝ => J n y := by
      simpa using! (SpherePacking.ForMathlib.iteratedDeriv_eq_of_hasDerivAt_succ (I := J) hJ n)
    lia
  -- Bound the integral `I n x` by `Kn * exp(-2π*sqrt x)`.
  have hIn :
      ‖I n x‖ ≤ Kn * Real.exp (-2 * Real.pi * Real.sqrt x) := by
    have hnorm : ‖I n x‖ ≤ ∫ t, ‖gN n x t‖ ∂μ := by
      simpa [I] using! (MeasureTheory.norm_integral_le_integral_norm (μ := μ) (f := gN n x))
    have hbound_ae :
        ∀ᵐ t ∂μ, ‖gN n x t‖ ≤ bound t * Real.exp (-2 * Real.pi * Real.sqrt x) := by
      filter_upwards [hμmem] with t ht
      have htIoc : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
      have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioo ht
      have hcoeff : ‖coeff t‖ ^ n ≤ (2 * Real.pi) ^ n :=
        pow_le_pow_left₀ (norm_nonneg _) (coeff_norm_le t) n
      have hψI : ‖ψI' (z₅' t)‖ ≤ Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (10 : ℕ) := by
        simpa [one_div] using!
          (MagicFunction.norm_modular_rewrite_Ioc_exp_bound (k := 10) (Cψ := Cψ) (ψS := ψS)
            (ψZ := ψI') (z := z₅') (hCψ := hCψ)
            (hEq := fun s hs => ψI'_z₅'_eq (t := s) hs) (t := t) htIoc)
      have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₅'_eq_of_mem (t := t) htIcc)
      have hcexp : ‖cexp ((x : ℂ) * coeff t)‖ = Real.exp (-Real.pi * x * t) := by
        have hcoeff' : coeff t = (-Real.pi * t : ℂ) := by
          have hII : (Complex.I : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) = -(t : ℂ) :=
            I_mul_I_mul ↑t
          calc
            coeff t = ((Real.pi : ℂ) * (Complex.I : ℂ)) * ((Complex.I : ℂ) * (t : ℂ)) := by
              simp [coeff, hz5]
            _ = (Real.pi : ℂ) * ((Complex.I : ℂ) * ((Complex.I : ℂ) * (t : ℂ))) := by
              simp [mul_assoc]
            _ = (Real.pi : ℂ) * (-(t : ℂ)) := by simp [hII]
            _ = (-Real.pi * t : ℂ) := by ring_nf
        have : ((x : ℂ) * coeff t).re = -Real.pi * x * t := by
          -- `Re (x * (-π*t)) = -(π*x*t)`.
          simp [hcoeff', mul_left_comm, mul_comm]
        simp [Complex.norm_exp, this]
      have hcexp_le :
          Real.exp (-Real.pi / t) * Real.exp (-Real.pi * x * t) ≤
            Real.exp (-2 * Real.pi * Real.sqrt x) :=
        SpherePacking.ForMathlib.exp_neg_pi_div_mul_exp_neg_pi_mul_le (x := x) (t := t) hx ht.1
      have hg :
          ‖g x t‖ ≤
            (Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (10 : ℕ)) *
              Real.exp (-Real.pi * x * t) := by
        calc
          ‖g x t‖ =
              ‖((Complex.I : ℂ) * ψI' (z₅' t)) *
                  cexp ((x : ℂ) * coeff t)‖ := by
            simp [g, mul_assoc]
          _ ≤ ‖(Complex.I : ℂ) * ψI' (z₅' t)‖ * ‖cexp ((x : ℂ) * coeff t)‖ := by
            simp
          _ = ‖ψI' (z₅' t)‖ * ‖cexp ((x : ℂ) * coeff t)‖ := by simp
          _ ≤
              (Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (10 : ℕ)) *
                Real.exp (-Real.pi * x * t) := by
            simpa [hcexp] using! (mul_le_mul_of_nonneg_right hψI (by positivity))
      calc
        ‖gN n x t‖ = ‖coeff t‖ ^ n * ‖g x t‖ := by simp [gN, norm_pow]
        _ ≤ (2 * Real.pi) ^ n * ((Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (10 : ℕ)) *
              Real.exp (-Real.pi * x * t)) := by gcongr
        _ ≤ (((2 * Real.pi) ^ n) * Cψ * t ^ (10 : ℕ)) * Real.exp (-2 * Real.pi * Real.sqrt x) := by
          -- swap in the AM-GM estimate on exponentials, then reassociate.
          have hExp :
              Real.exp (-Real.pi * (1 / t)) * Real.exp (-Real.pi * x * t) ≤
                Real.exp (-2 * Real.pi * Real.sqrt x) := by
            lia
          have htpow_nonneg : 0 ≤ t ^ (10 : ℕ) := pow_nonneg (le_of_lt ht.1) 10
          have hconst_nonneg : 0 ≤ ((2 * Real.pi) ^ n) * Cψ := by positivity [hCψ0]
          -- rearrange
          calc
            (2 * Real.pi) ^ n *
                ((Cψ * Real.exp (-Real.pi * (1 / t)) * t ^ (10 : ℕ)) *
                  Real.exp (-Real.pi * x * t)) =
                (((2 * Real.pi) ^ n) * Cψ * t ^ (10 : ℕ)) *
                  (Real.exp (-Real.pi * (1 / t)) *
                    Real.exp (-Real.pi * x * t)) := by
                    ring_nf
            _ ≤ (((2 * Real.pi) ^ n) * Cψ * t ^ (10 : ℕ)) *
                  Real.exp (-2 * Real.pi * Real.sqrt x) := by
                    gcongr
        _ = bound t * Real.exp (-2 * Real.pi * Real.sqrt x) := by
          simp [bound, mul_assoc, mul_left_comm, mul_comm]
    have hle :
        ∫ t, ‖gN n x t‖ ∂μ ≤ ∫ t, bound t * Real.exp (-2 * Real.pi * Real.sqrt x) ∂μ := by
      refine integral_mono_of_nonneg ?_ ?_ hbound_ae
      · exact Filter.Eventually.of_forall (fun t => norm_nonneg (gN n x t))
      · have := hbound_int.mul_const (Real.exp (-2 * Real.pi * Real.sqrt x))
        simpa [mul_assoc, mul_left_comm, mul_comm] using! this
    have :
        ‖I n x‖ ≤ ∫ t, bound t * Real.exp (-2 * Real.pi * Real.sqrt x) ∂μ := hnorm.trans hle
    have hconst :
        (∫ t, bound t * Real.exp (-2 * Real.pi * Real.sqrt x) ∂μ) =
          Kn * Real.exp (-2 * Real.pi * Real.sqrt x) := by
      exact MeasureTheory.integral_mul_const (Real.exp (-2 * Real.pi * √x)) bound
    exact this.trans (le_of_eq hconst)
  have hpoly : x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x) ≤ B := by
    simpa [mul_assoc] using! (hB x hx)
  have hpow0 : 0 ≤ 2 * Kn := by nlinarith [hKn_nonneg]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₅' x‖
        = x ^ k * ‖iteratedDeriv n RealIntegrals.J₅' x‖ := by simp [hxabs, hnorm_iter]
    _ = x ^ k * ‖-(2 * I n x)‖ := by simp [hiterJ]
    _ = x ^ k * (2 * ‖I n x‖) := by simp
    _ ≤ x ^ k * (2 * (Kn * Real.exp (-2 * Real.pi * Real.sqrt x))) := by gcongr
    _ = (2 * Kn) * (x ^ k * Real.exp (-2 * Real.pi * Real.sqrt x)) := by ring_nf
    _ ≤ (2 * Kn) * B := by
          simpa using! (mul_le_mul_of_nonneg_left hpoly hpow0)
    _ ≤ (2 * Kn * B) * 1 := by nlinarith
    _ = C := by simp [C, mul_assoc]

end SpherePacking.Dim24.Schwartz.J5Smooth

end
