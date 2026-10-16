-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.Radial
import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Dim24.MagicFunction.F.Laplace.Kernels
import SpherePacking.Dim24.MagicFunction.F.Laplace.Equality.B
import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.B
import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.BSubLeading
import SpherePacking.Dim24.MagicFunction.F.Laplace.Apply
import SpherePacking.Dim24.MagicFunction.F.Laplace.Profiles.BProfile.Bounds
import SpherePacking.Dim24.MagicFunction.A.VarphiBounds
import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Basic
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.CuspAtInfinity
import SpherePacking.Dim24.MagicFunction.F.Sign.Auxiliary
import SpherePacking.Integration.Measure
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas


/-!
# Root structure of the auxiliary function `f`

This file provides the analytic inputs used in the dimension-24 uniqueness argument:
radiality of the auxiliary function `f` and a one-variable classification of the roots of
`f (axisVec r)` for `r ≥ 2`.

These results are used to extract the Leech distance spectrum from the equality case of the
Cohn-Elkies linear programming bound.

## Main statements
* `f_eq_f_axisVec_norm`
* `norm_sq_eq_two_mul_of_f_axisVec_eq_zero_of_two_le`
-/

/-!
## Nonvanishing of the Laplace factor

For `r > 2`, the Laplace representation of `f (axisVec r)` involves the factor
`∫₀^∞ A(t) e^{-π r^2 t} dt`.  We show this factor has strictly negative real part using:

* strict negativity of `Re(A(t))` for all `t > 0`,
* integrability of the integrand (bounded on `(0,1]`, exponential decay on `[1,∞)`).
-/


namespace SpherePacking.Dim24

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

noncomputable section

namespace UniquenessRootsAux

open scoped SchwartzMap
open SchwartzMap Complex Real

end UniquenessRootsAux

namespace UniquenessRootsLaplaceAux

open scoped ModularForm Topology
open MeasureTheory Complex Real Filter UpperHalfPlane
open SpherePacking.Integration (μIoi0)

lemma iOverT_im (t : ℝ) (ht : 0 < t) : (iOverT t ht).im = 1 / t := by
  -- `iOverT t = it (1/t)`, so the imaginary part is `1/t`.
  have ht' : 0 < 1 / t := by simpa using! (one_div_pos.2 ht)
  simpa [iOverT] using! (it_im (t := 1 / t) ht')

lemma AKernel_re_neg (t : ℝ) (ht : 0 < t) : (Dim24.AKernel t ht).re < 0 := by
  have ht' : 0 < 1 / t := by simpa using! (one_div_pos.2 ht)
  have hvar : (varphi (iOverT t ht)).re < 0 := by
    simpa [iOverT] using! (varphi_imagAxis_neg (t := 1 / t) ht')
  have hψ : 0 ≤ (ψI (it t ht)).re := SpherePacking.Dim24.ψI_imagAxis_re_nonneg (t := t) ht
  have hpi : 0 < (Real.pi / 28304640 : ℝ) := by positivity [Real.pi_pos]
  have ht10 : 0 ≤ t ^ (10 : ℕ) := pow_nonneg (le_of_lt ht) _
  have hA :
      (((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)).re < 0 := by
    have hre :
        (((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)).re =
          (Real.pi / 28304640 : ℝ) * t ^ (10 : ℕ) * (varphi (iOverT t ht)).re := by
      -- The prefactor is real.
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ← Complex.ofReal_pow]
    rw [hre]
    have hscale : 0 < (Real.pi / 28304640 : ℝ) * t ^ (10 : ℕ) :=
      mul_pos hpi (pow_pos ht _)
    exact mul_neg_of_pos_of_neg hscale hvar
  have hB :
      0 ≤ (((1 / ((65520 : ℂ) * π)) * ψI (it t ht)).re) := by
    -- The prefactor is real and nonnegative.
    have hscale : 0 ≤ (1 / (65520 * Real.pi) : ℝ) := by positivity [Real.pi_pos]
    -- Convert the coefficient to `ofReal` and simplify.
    have hre :
        (((1 / ((65520 : ℂ) * π)) * ψI (it t ht)).re) =
          (1 / (65520 * Real.pi) : ℝ) * (ψI (it t ht)).re := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, Complex.mul_re]
    rw [hre]
    exact mul_nonneg hscale hψ
  -- Combine: `re(A - B) < 0` when `re(A) < 0` and `0 ≤ re(B)`.
  have hrew :
      (Dim24.AKernel t ht).re =
        (((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)).re -
          (((1 / ((65520 : ℂ) * π)) * ψI (it t ht)).re) := by
    simp [Dim24.AKernel, sub_eq_add_neg]
  rw [hrew]
  linarith

lemma tendsto_pow_mul_exp_neg_mul_atTop_nhds_zero (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-(c * x))) atTop (𝓝 0) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n)
  have hcomp :
      Tendsto (fun x : ℝ => (c * x) ^ n * Real.exp (-(c * x))) atTop (𝓝 0) :=
    hbase.comp (tendsto_id.const_mul_atTop hc)
  -- Rewrite `x^n * exp(-c*x)` as a constant multiple of `(c*x)^n * exp(-(c*x))`.
  have hrew :
      (fun x : ℝ => x ^ n * Real.exp (-(c * x))) =
        fun x : ℝ => (c ^ n)⁻¹ * ((c * x) ^ n * Real.exp (-(c * x))) := by
    funext x
    have hcPow : (c ^ n) ≠ 0 := pow_ne_zero _ hc0
    calc
      x ^ n * Real.exp (-(c * x))
          = ((c ^ n)⁻¹ * (c ^ n)) * (x ^ n * Real.exp (-(c * x))) := by simp [hcPow]
      _ = (c ^ n)⁻¹ * ((c ^ n * x ^ n) * Real.exp (-(c * x))) := by ring
      _ = (c ^ n)⁻¹ * ((c * x) ^ n * Real.exp (-(c * x))) := by
            simp [mul_pow]
  -- Conclude by multiplying a convergent sequence by a constant.
  have : Tendsto (fun x : ℝ => (c ^ n)⁻¹ * ((c * x) ^ n * Real.exp (-(c * x)))) atTop (𝓝 0) := by
    simpa using! (tendsto_const_nhds.mul hcomp)
  simpa [hrew] using! this

lemma integrableOn_quadratic_mul_exp_neg_Ioi_one {b : ℝ} (hb : 0 < b) :
    IntegrableOn
      (fun x : ℝ => (x ^ (2 : ℕ) + x + 1) * Real.exp (-b * x))
      (Set.Ioi (1 : ℝ)) volume := by
  have hb2 : 0 < b / 2 := by nlinarith
  have hcont :
      ContinuousOn (fun x : ℝ => (x ^ (2 : ℕ) + x + 1) * Real.exp (-b * x)) (Set.Ici (1 : ℝ)) := by
    fun_prop
  -- Show `f = o(exp (-(b/2)*x))` at `∞` using the ratio test.
  have hlim :
      Tendsto (fun x : ℝ => ((x ^ (2 : ℕ) + x + 1) * Real.exp (-b * x)) /
        Real.exp (-(b / 2) * x)) atTop (𝓝 0) := by
    -- Simplify the ratio to `(x^2 + x + 1) * exp (-(b/2) * x)`.
    have hsim :
        (fun x : ℝ =>
            ((x ^ (2 : ℕ) + x + 1) * Real.exp (-b * x)) / Real.exp (-(b / 2) * x)) =
          fun x : ℝ => (x ^ (2 : ℕ) + x + 1) * Real.exp (-(b / 2) * x) := by
      funext x
      have hdiv :
          Real.exp (-b * x) / Real.exp (-(b / 2) * x) = Real.exp (-(b / 2) * x) := by
        -- `exp a / exp b = exp (a - b)` and simplify the exponent.
        have hratio :
            Real.exp (-(b * x)) / Real.exp (-(b / 2 * x)) =
              Real.exp (-(b * x) + (b / 2) * x) := by
          -- `exp a / exp b = exp (a - b)`; here `a = -(b*x)` and `b = -(b/2*x)`.
          simpa [sub_eq_add_neg, neg_mul, mul_assoc] using!
            (Real.exp_sub (-(b * x)) (-(b / 2 * x))).symm
        have hexp : -(b * x) + (b / 2) * x = -(b / 2) * x := by ring
        simpa [hexp, mul_assoc] using! hratio
      -- Fold the exponential ratio into the product without cancelling the polynomial factor.
      grind only
    rw [hsim]
    -- Each term tends to `0`, so their sum tends to `0`.
    have h2 : Tendsto (fun x : ℝ => x ^ (2 : ℕ) * Real.exp (-(b / 2) * x)) atTop (𝓝 0) := by
      simpa [neg_mul, mul_assoc] using!
        (tendsto_pow_mul_exp_neg_mul_atTop_nhds_zero (n := 2) (c := b / 2) hb2)
    have h1 : Tendsto (fun x : ℝ => x * Real.exp (-(b / 2) * x)) atTop (𝓝 0) :=
      by
        simpa [pow_one, neg_mul, mul_assoc] using!
          (tendsto_pow_mul_exp_neg_mul_atTop_nhds_zero (n := 1) (c := b / 2) hb2)
    have h0 : Tendsto (fun x : ℝ => (1 : ℝ) * Real.exp (-(b / 2) * x)) atTop (𝓝 0) := by
      simpa [pow_zero, neg_mul, mul_assoc] using!
        (tendsto_pow_mul_exp_neg_mul_atTop_nhds_zero (n := 0) (c := b / 2) hb2)
    have hadd :
        Tendsto (fun x : ℝ => (x ^ (2 : ℕ) + x + 1) * Real.exp (-(b / 2) * x)) atTop (𝓝 0) := by
      -- Expand as a sum of three terms.
      have :
          (fun x : ℝ => (x ^ (2 : ℕ) + x + 1) * Real.exp (-(b / 2) * x)) =
            fun x : ℝ => x ^ (2 : ℕ) * Real.exp (-(b / 2) * x) +
              (x * Real.exp (-(b / 2) * x) + (1 : ℝ) * Real.exp (-(b / 2) * x)) := by
        funext x
        ring
      rw [this]
      simpa using! (h2.add (h1.add h0))
    exact hadd
  have hLittle :
      (fun x : ℝ => (x ^ (2 : ℕ) + x + 1) * Real.exp (-b * x)) =o[atTop]
        fun x : ℝ => Real.exp (-(b / 2) * x) := by
    refine
      (Asymptotics.isLittleO_iff_tendsto
          (f := fun x : ℝ => (x ^ (2 : ℕ) + x + 1) * Real.exp (-b * x))
          (g := fun x : ℝ => Real.exp (-(b / 2) * x)) (l := atTop) ?_).2 hlim
    intro x hx
    have : (Real.exp (-(b / 2) * x)) ≠ 0 := (Real.exp_pos _).ne'
    exact (this hx).elim
  have hBigO :
      (fun x : ℝ => (x ^ (2 : ℕ) + x + 1) * Real.exp (-b * x)) =O[atTop]
        fun x : ℝ => Real.exp (-(b / 2) * x) :=
    hLittle.isBigO
  -- Apply the integrability criterion for exponential decay.
  exact integrable_of_isBigO_exp_neg (a := (1 : ℝ)) (b := b / 2) hb2 hcont (by simpa using! hBigO)


open LaplaceZerosTail

lemma continuousOn_varphi_resToImagAxis_Ioi :
    ContinuousOn (fun t : ℝ => varphi.resToImagAxis t) (Set.Ioi (0 : ℝ)) := by
  exact Function.continuousOn_resToImagAxis_Ioi_of (F := varphi) varphi_holo'.continuous

lemma continuousOn_ψI_resToImagAxis_Ioi :
    ContinuousOn (fun t : ℝ => ψI.resToImagAxis t) (Set.Ioi (0 : ℝ)) :=
  Function.continuousOn_resToImagAxis_Ioi_of (F := ψI) SpherePacking.Dim24.continuous_ψI

lemma AKernel0_eq_resToImagAxis (t : ℝ) (ht : 0 < t) :
    AKernel0 t =
      ((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi.resToImagAxis (1 / t)
        - (1 / ((65520 : ℂ) * π)) * ψI.resToImagAxis t := by
  have ht' : 0 < (1 / t : ℝ) := one_div_pos.2 ht
  have hvar : varphi.resToImagAxis (1 / t) = varphi (it (1 / t) ht') := by
    simpa [Function.resToImagAxis] using! (resToImagAxis_eq_it (F := varphi) (t := 1 / t) ht')
  have hψ : ψI.resToImagAxis t = ψI (it t ht) := by
    simpa [Function.resToImagAxis] using! (resToImagAxis_eq_it (F := ψI) (t := t) ht)
  simp [AKernel0, ht, Dim24.AKernel, AKernel, iOverT, sub_eq_add_neg, mul_assoc, mul_comm]
  have htinv : 0 < (t⁻¹ : ℝ) := by
    simpa [one_div] using! (one_div_pos.2 ht : 0 < (1 / t : ℝ))
  -- Rewrite the remaining `ResToImagAxis` terms to evaluations, then finish by commutative
  -- ring normalization.
  have hResVar : ResToImagAxis varphi t⁻¹ = varphi (it (t⁻¹) htinv) :=
    resToImagAxis_eq_it (F := varphi) (t := t⁻¹) htinv
  have hResPsi : ResToImagAxis ψI t = ψI (it t ht) :=
    resToImagAxis_eq_it (F := ψI) (t := t) ht
  simp [hResVar, hResPsi]
  ring_nf

lemma continuousOn_AKernel0_Ioi :
    ContinuousOn AKernel0 (Set.Ioi (0 : ℝ)) := by
  -- Use the `ResToImagAxis` descriptions on `t > 0` to avoid proof arguments.
  have hEq :
      Set.EqOn AKernel0
        (fun t : ℝ =>
          ((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi.resToImagAxis (1 / t)
            - (1 / ((65520 : ℂ) * π)) * ψI.resToImagAxis t)
        (Set.Ioi (0 : ℝ)) := by
    intro t ht
    simpa using! (AKernel0_eq_resToImagAxis (t := t) ht)
  have hcont_pow : Continuous fun t : ℝ => (t : ℂ) ^ (10 : ℕ) := by
    simpa using! (Complex.continuous_ofReal.pow 10)
  have hcont_inv : ContinuousOn (fun t : ℝ => (1 / t : ℝ)) (Set.Ioi (0 : ℝ)) := by
    simpa [one_div] using! (continuousOn_inv₀ : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) ({0}ᶜ)).mono
      (by
        norm_num)
  have hcont_var :
      ContinuousOn (fun t : ℝ => varphi.resToImagAxis (1 / t)) (Set.Ioi (0 : ℝ)) :=
    continuousOn_varphi_resToImagAxis_Ioi.comp hcont_inv (by
      intro t ht
      exact one_div_pos.2 (by simpa using! ht))
  have hcont_ψ : ContinuousOn (fun t : ℝ => ψI.resToImagAxis t) (Set.Ioi (0 : ℝ)) :=
    continuousOn_ψI_resToImagAxis_Ioi
  have hcont :
      ContinuousOn
          (fun t : ℝ =>
            ((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi.resToImagAxis (1 / t)
              - (1 / ((65520 : ℂ) * π)) * ψI.resToImagAxis t)
          (Set.Ioi (0 : ℝ)) := by
    -- Each piece is continuous on `t > 0`.
    have hconst1 : Continuous fun _ : ℝ => ((π : ℂ) / (28304640 : ℂ)) := continuous_const
    have hconst2 : Continuous fun _ : ℝ => (1 / ((65520 : ℂ) * π)) := continuous_const
    have hmul1 :
        ContinuousOn
            (fun t : ℝ =>
              ((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi.resToImagAxis (1 / t))
            (Set.Ioi (0 : ℝ)) := by
      simpa [mul_assoc] using!
        ((hconst1.continuousOn.mul hcont_pow.continuousOn).mul hcont_var)
    have hmul2 :
        ContinuousOn
            (fun t : ℝ => (1 / ((65520 : ℂ) * π)) * ψI.resToImagAxis t) (Set.Ioi (0 : ℝ)) := by
      simpa using! (hconst2.continuousOn.mul hcont_ψ)
    simpa [sub_eq_add_neg] using! hmul1.sub hmul2
  exact hcont.congr hEq

lemma continuousOn_AKernel0_mul_exp_neg_pi_sq (r : ℝ) :
    ContinuousOn
        (fun t : ℝ => AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t))
        (Set.Ioi (0 : ℝ)) := by
  have hexpR : Continuous fun t : ℝ => Real.exp (-Real.pi * (r ^ 2) * t) := by
    fun_prop
  have hexp :
      ContinuousOn (fun t : ℝ => (Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    (Complex.continuous_ofReal.comp hexpR).continuousOn
  simpa [mul_assoc] using! (continuousOn_AKernel0_Ioi.mul hexp)

lemma integrableOn_AKernel0_mul_exp_neg_pi_sq_Ioc_zero_one (r : ℝ) :
    IntegrableOn (fun t : ℝ => AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t))
      (Set.Ioc (0 : ℝ) 1) volume := by
  let g : ℝ → ℂ := fun t : ℝ => AKernel0 t * (Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)
  have hcont : ContinuousOn g (Set.Ioc (0 : ℝ) 1) :=
    (continuousOn_AKernel0_mul_exp_neg_pi_sq (r := r)).mono (by
      intro t ht
      exact ht.1)
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  have hfinite : volume (Set.Ioc (0 : ℝ) 1) < (⊤ : ENNReal) := by
    simp [Real.volume_Ioc]
  -- Uniform bounds on the modular-form pieces for large imaginary part.
  rcases VarphiBounds.varphi_isBigO_exp_neg_two_pi.exists_pos with ⟨cφ, hcφ, hφ⟩
  rcases (Filter.eventually_atImInfty).1 hφ.bound with ⟨Aφ, hAφ⟩
  have hψS0 : Tendsto ψS UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) :=
    SpherePacking.Dim24.tendsto_ψS_atImInfty
  have hψS_ev : ∀ᶠ z in UpperHalfPlane.atImInfty, ‖ψS z‖ ≤ (1 : ℝ) := by
    have hlt : ∀ᶠ z in UpperHalfPlane.atImInfty, ‖ψS z‖ < (1 : ℝ) :=
      (tendsto_zero_iff_norm_tendsto_zero.1 hψS0).eventually (Iio_mem_nhds (by norm_num))
    exact hlt.mono fun _ hz => le_of_lt hz
  rcases (Filter.eventually_atImInfty).1 hψS_ev with ⟨Aψ, hAψ⟩
  let A0 : ℝ := max (max Aφ Aψ) 1
  have hA0_pos : 0 < A0 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let δ : ℝ := 1 / A0
  have hδ_pos : 0 < δ := one_div_pos.2 hA0_pos
  have hδ_le_one : δ ≤ 1 := by
    have : (1 : ℝ) ≤ A0 := le_max_right (max Aφ Aψ) 1
    simpa [δ] using! (one_div_le_one_div_of_le (by norm_num) this)
  -- On the compact interval `[δ,1]`, `‖g t‖` attains a maximum.
  have hcontIcc : ContinuousOn (fun t : ℝ => ‖g t‖) (Set.Icc δ 1) := by
    have : ContinuousOn g (Set.Icc δ 1) := by
      refine (continuousOn_AKernel0_mul_exp_neg_pi_sq (r := r)).mono ?_
      intro t ht
      exact lt_of_lt_of_le hδ_pos ht.1
    exact this.norm
  have hne : (Set.Icc δ 1).Nonempty := ⟨δ, ⟨le_rfl, hδ_le_one⟩⟩
  obtain ⟨t0, ht0, htmax⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc δ 1)).exists_isMaxOn hne (f := fun t => ‖g t‖)
      (by simpa using! hcontIcc)
  let Mbig : ℝ := ‖g t0‖ + 1
  have hbound_big : ∀ t ∈ Set.Icc δ 1, ‖g t‖ ≤ Mbig := by
    intro t ht
    have : ‖g t‖ ≤ ‖g t0‖ := htmax ht
    linarith [this]
  -- For small `t`, `Im (i/t)` is large, so `varphi(i/t)` and `ψS(i/t)` are uniformly bounded.
  let c1 : ℝ := ‖((π : ℂ) / (28304640 : ℂ))‖
  let c2 : ℝ := ‖(1 / ((65520 : ℂ) * π))‖
  let Msmall : ℝ := c1 * cφ + c2
  have hbound_small : ∀ t ∈ Set.Ioc (0 : ℝ) δ, ‖g t‖ ≤ Msmall := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht_le_one : t ≤ 1 := le_trans ht.2 hδ_le_one
    have hA0_le : A0 ≤ 1 / t := by
      have hmul : A0 * t ≤ 1 := by
        have := mul_le_mul_of_nonneg_left ht.2 (le_of_lt hA0_pos)
        simpa [δ, one_div, mul_assoc, hA0_pos.ne'] using! this
      -- `A0 ≤ 1 / t ↔ A0 * t ≤ 1` for `t > 0`.
      exact (le_div_iff₀ ht0).2 (by simpa using! hmul)
    have hAφ' : Aφ ≤ (iOverT t ht0).im := by
      have : (iOverT t ht0).im = 1 / t := iOverT_im (t := t) ht0
      have hAφ0 : Aφ ≤ A0 := le_trans (le_trans (le_max_left Aφ Aψ) (le_max_left _ _)) (le_rfl)
      exact by simpa [this] using! le_trans hAφ0 hA0_le
    have hAψ' : Aψ ≤ (iOverT t ht0).im := by
      have : (iOverT t ht0).im = 1 / t := iOverT_im (t := t) ht0
      have hAψ0 : Aψ ≤ A0 := le_trans (le_trans (le_max_right Aφ Aψ) (le_max_left _ _)) (le_rfl)
      exact by simpa [this] using! le_trans hAψ0 hA0_le
    have hvarphi_le : ‖varphi (iOverT t ht0)‖ ≤ cφ := by
      have hb := hAφ (iOverT t ht0) hAφ'
      -- `exp (-(2π)*Im) ≤ 1` since `Im ≥ 0`.
      have hexp : ‖Real.exp (-(2 * Real.pi) * (iOverT t ht0).im)‖ ≤ (1 : ℝ) := by
        -- `Real.exp` is nonnegative, so its norm is itself.
        have : Real.exp (-(2 * Real.pi) * (iOverT t ht0).im) ≤ 1 := by
          refine (Real.exp_le_one_iff.2 ?_)
          have : 0 ≤ (iOverT t ht0).im := by
            positivity
          nlinarith [Real.two_pi_pos, this]
        simpa using! this
      -- Turn the `IsBigOWith` bound into a crude uniform bound.
      calc
        ‖varphi (iOverT t ht0)‖ ≤ cφ * ‖Real.exp (-(2 * Real.pi) * (iOverT t ht0).im)‖ := hb
        _ ≤ cφ * 1 := by gcongr
        _ = cφ := by simp
    have hψS_le : ‖ψS (iOverT t ht0)‖ ≤ 1 := hAψ (iOverT t ht0) hAψ'
    have ht10_le : ‖(t : ℂ) ^ (10 : ℕ)‖ ≤ 1 := by
      have ht0' : (0 : ℝ) ≤ t := le_of_lt ht0
      have hnorm : ‖(t : ℂ) ^ (10 : ℕ)‖ = t ^ (10 : ℕ) := by
        simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0']
      have : t ^ (10 : ℕ) ≤ 1 := pow_le_one₀ ht0' ht_le_one
      simpa [hnorm] using! this
    have hψI_le : ‖ψI (it t ht0)‖ ≤ 1 := by
      have hψIeq :=
        SpherePacking.Dim24.SignAux.ψI_it_eq_neg_t10_mul_ψS_iOverT (t := t) ht0
      calc
        ‖ψI (it t ht0)‖ = ‖-((t : ℂ) ^ (10 : ℕ)) * ψS (iOverT t ht0)‖ := by simp [hψIeq]
        _ = ‖(t : ℂ) ^ (10 : ℕ)‖ * ‖ψS (iOverT t ht0)‖ := by simp
        _ ≤ (1 : ℝ) * (1 : ℝ) := by gcongr
        _ = 1 := by ring
    have hexp_le : ‖(Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)‖ ≤ (1 : ℝ) := by
      set u : ℝ := -Real.pi * (r ^ 2) * t
      have hu_nonpos : u ≤ 0 := by
        have ht0' : 0 ≤ t := le_of_lt ht0
        have : 0 ≤ Real.pi * (r ^ 2) * t := by
          positivity [Real.pi_pos, ht0']
        -- `u = -(Real.pi * (r^2) * t)`.
        nlinarith [this]
      have hExp : Real.exp u ≤ 1 := (Real.exp_le_one_iff).2 hu_nonpos
      have hn : ‖Complex.exp (u : ℂ)‖ = Real.exp u := Complex.norm_exp_ofReal u
      have : ‖Complex.exp (u : ℂ)‖ ≤ (1 : ℝ) := by
        exact le_of_eq_of_le hn hExp
      simpa [u, Complex.ofReal_exp] using! this
    have hAK :
        ‖AKernel0 t‖ ≤ Msmall := by
      -- Expand `AKernel` and apply the triangle inequality with the crude bounds above.
      have hpos : AKernel0 t = Dim24.AKernel t ht0 := by simp [AKernel0, ht0]
      have hterm1 :
          ‖((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖ ≤ c1 * cφ := by
        calc
          ‖((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖
              = c1 * ‖(t : ℂ) ^ (10 : ℕ)‖ * ‖varphi (iOverT t ht0)‖ := by
                    simp [c1, mul_assoc, mul_left_comm, mul_comm]
          _ ≤ c1 * 1 * cφ := by gcongr
          _ = c1 * cφ := by ring
      have hterm2 :
          ‖(1 / ((65520 : ℂ) * π)) * ψI (it t ht0)‖ ≤ c2 := by
        calc
          ‖(1 / ((65520 : ℂ) * π)) * ψI (it t ht0)‖ = c2 * ‖ψI (it t ht0)‖ := by
                simp [c2, mul_assoc]
          _ ≤ c2 * 1 := by gcongr
          _ = c2 := by ring
      have htri :
          ‖Dim24.AKernel t ht0‖ ≤
            ‖((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖ +
              ‖(1 / ((65520 : ℂ) * π)) * ψI (it t ht0)‖ := by
        -- `‖a - b‖ ≤ ‖a‖ + ‖b‖`.
        simpa [Dim24.AKernel, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using!
          (norm_add_le
            (((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0))
            (-(1 / ((65520 : ℂ) * π)) * ψI (it t ht0)))
      calc
        ‖AKernel0 t‖ = ‖Dim24.AKernel t ht0‖ := by simp [hpos]
        _ ≤ ‖((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖ +
              ‖(1 / ((65520 : ℂ) * π)) * ψI (it t ht0)‖ := htri
        _ ≤ c1 * cφ + c2 := by gcongr
        _ = Msmall := by simp [Msmall]
    -- Finally, multiply by the exponential factor (bounded by `1` on `t ≥ 0`).
    have : ‖g t‖ ≤ ‖AKernel0 t‖ := by
      dsimp [g]
      have hmul :=
        norm_mul_le (AKernel0 t) (Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)
      have hmul' :
          ‖AKernel0 t‖ * ‖(Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)‖ ≤ ‖AKernel0 t‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hexp_le
      exact hmul.trans hmul'
    exact le_trans this hAK
  let M : ℝ := max Msmall Mbig
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖g t‖ ≤ M := by
    refine
      (MeasureTheory.ae_restrict_iff' (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))).2 ?_
    refine ae_of_all _ ?_
    intro t ht
    by_cases htδ : t ≤ δ
    · have : ‖g t‖ ≤ Msmall := hbound_small t ⟨ht.1, htδ⟩
      exact le_trans this (le_max_left _ _)
    · have htδ' : δ < t := lt_of_not_ge htδ
      have htIcc : t ∈ Set.Icc δ 1 := ⟨le_of_lt htδ', ht.2⟩
      have : ‖g t‖ ≤ Mbig := hbound_big t htIcc
      exact le_trans this (le_max_right _ _)
  exact IntegrableOn.of_bound hfinite hg_meas M hbound

lemma I_pow_ten : (Complex.I : ℂ) ^ (10 : ℕ) = (-1 : ℂ) := by
  -- `I^n` is periodic mod `4`.
  calc
    (Complex.I : ℂ) ^ (10 : ℕ) = (Complex.I : ℂ) ^ (10 % 4) := by
      simpa using! (Complex.I_pow_eq_pow_mod 10)
    _ = (-1 : ℂ) := by simp

lemma integrableOn_AKernel0_mul_exp_neg_pi_sq_Ioi_one_of_two_lt (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t))
      (Set.Ioi (1 : ℝ)) volume := by
  -- Tail bounds: `t^10 * varphi(i/t)` and `ψI(it)` grow at most like `exp(4π t)`.
  rcases LaplaceZerosTail.TailBounds.exists_bound_norm_pow_ten_varphi_S with ⟨Kφ, Aφ, hKφ, hφ⟩
  rcases SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile.exists_ψI_bound_exp with
    ⟨Cψ, Aψ, hCψ, hψ⟩
  let A : ℝ := max 1 (max Aφ Aψ)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAφ : Aφ ≤ A := le_trans (le_max_left Aφ Aψ) (le_max_right 1 (max Aφ Aψ))
  have hAψ : Aψ ≤ A := le_trans (le_max_right Aφ Aψ) (le_max_right 1 (max Aφ Aψ))
  -- On `[1,A]`, integrability follows from continuity on a compact interval.
  have hcomp :
      IntegrableOn (fun t : ℝ => AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t))
        (Set.Ioc (1 : ℝ) A) volume := by
    have hcont :
        ContinuousOn (fun t : ℝ => AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t))
          (Set.Icc 1 A) := by
      refine (continuousOn_AKernel0_mul_exp_neg_pi_sq (r := r)).mono ?_
      intro t ht
      have : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
      exact this
    have hintIcc :
        IntegrableOn (fun t : ℝ => AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t))
          (Set.Icc 1 A) volume :=
      (ContinuousOn.integrableOn_compact (μ := volume) isCompact_Icc hcont)
    exact hintIcc.mono_set (Set.Ioc_subset_Icc_self)
  -- On `[A,∞)`, dominate by a polynomial times `exp(-π(r^2-4)t)`.
  have hr4 : 0 < r ^ 2 - 4 := by nlinarith
  let b : ℝ := Real.pi * (r ^ 2 - 4)
  have hb : 0 < b := by positivity [Real.pi_pos, hr4]
  let C : ℝ := ‖((π : ℂ) / (28304640 : ℂ))‖ * Kφ + ‖(1 / ((65520 : ℂ) * π))‖ * Cψ
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdom :
      ∀ t ∈ Set.Ioi A,
        ‖AKernel0 t * (Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)‖ ≤
          C * (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hA1) (le_of_lt ht)
    have htA : A ≤ t := le_of_lt ht
    have ht1 : 1 ≤ t := le_trans hA1 htA
    have htAφ : Aφ ≤ (it t ht0).im := by
      -- `Im(it t) = t`.
      simpa [it_im (t := t) ht0] using! le_trans hAφ htA
    have htAψ : Aψ ≤ (it t ht0).im := by
      simpa [it_im (t := t) ht0] using! le_trans hAψ htA
    have hψI :
        ‖ψI (it t ht0)‖ ≤ Cψ * Real.exp (4 * Real.pi * t) := by
      -- Apply the global bound to `z = it t`.
      have := hψ (it t ht0) (by simpa [it_im (t := t) ht0] using! htAψ)
      simpa [it_im (t := t) ht0] using! this
    have hvarphi :
        ‖((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht0)‖ ≤
          Kφ * (t ^ (2 : ℕ) + t + 1) * Real.exp (4 * Real.pi * t) := by
      -- Use the `S`-transform bound with `z = it t`, then rewrite `S • it = i/t`.
      have hz := hφ (it t ht0) (by simpa [it_im (t := t) ht0] using! htAφ)
      have hS : ModularGroup.S • it t ht0 = iOverT t ht0 := S_smul_it (t := t) ht0
      have hnorm_it : ‖((it t ht0 : ℍ) : ℂ)‖ = t := by
        simp [Dim24.it, Real.norm_eq_abs, abs_of_pos ht0]
      have him : (it t ht0).im = t := it_im (t := t) ht0
      have habs : |t| = t := abs_of_pos ht0
      -- `simp` normalizes `‖(t : ℂ) ^ 10 * varphi _‖` to `|t| ^ 10 * ‖varphi _‖`.
      simpa [hS, hnorm_it, him, habs, pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc,
        add_left_comm, add_comm] using! hz
    -- Now bound `‖AKernel0 t‖` and multiply by the exponential factor.
    have hA0 : AKernel0 t = Dim24.AKernel t ht0 := by simp [AKernel0, ht0]
    have htri :
        ‖AKernel0 t‖ ≤
          ‖((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖ +
            ‖(1 / ((65520 : ℂ) * π)) * ψI (it t ht0)‖ := by
      -- `‖a - b‖ ≤ ‖a‖ + ‖b‖`.
      have :=
        norm_add_le
          (((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0))
          (-(1 / ((65520 : ℂ) * π)) * ψI (it t ht0))
      simpa [hA0, Dim24.AKernel, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! this
    have hterm1 :
        ‖((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖ ≤
          ‖((π : ℂ) / (28304640 : ℂ))‖ *
            (Kφ * (t ^ (2 : ℕ) + t + 1) * Real.exp (4 * Real.pi * t)) := by
      calc
        ‖((π : ℂ) / (28304640 : ℂ)) * (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖
            = ‖((π : ℂ) / (28304640 : ℂ))‖ * ‖((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht0)‖ := by
                simp [mul_assoc, mul_left_comm]
        _ ≤ ‖((π : ℂ) / (28304640 : ℂ))‖ *
              (Kφ * (t ^ (2 : ℕ) + t + 1) * Real.exp (4 * Real.pi * t)) :=
              mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using! hvarphi) (by positivity)
    have hterm2 :
        ‖(1 / ((65520 : ℂ) * π)) * ψI (it t ht0)‖ ≤
          ‖(1 / ((65520 : ℂ) * π))‖ * (Cψ * Real.exp (4 * Real.pi * t)) := by
      calc
        ‖(1 / ((65520 : ℂ) * π)) * ψI (it t ht0)‖
            = ‖(1 / ((65520 : ℂ) * π))‖ * ‖ψI (it t ht0)‖ := by simp [mul_assoc]
        _ ≤ ‖(1 / ((65520 : ℂ) * π))‖ * (Cψ * Real.exp (4 * Real.pi * t)) :=
              mul_le_mul_of_nonneg_left hψI (by positivity)
    have hAK :
        ‖AKernel0 t‖ ≤
          C * (t ^ (2 : ℕ) + t + 1) * Real.exp (4 * Real.pi * t) := by
      have htpoly : (1 : ℝ) ≤ t ^ (2 : ℕ) + t + 1 := by
        have : (0 : ℝ) ≤ t ^ (2 : ℕ) := pow_nonneg (le_trans (by norm_num) ht1) _
        have : (0 : ℝ) ≤ t := le_trans (by norm_num) ht1
        nlinarith
      have hExp : 0 ≤ Real.exp (4 * Real.pi * t) := by positivity
      have hE :
          Real.exp (4 * Real.pi * t) ≤ (t ^ (2 : ℕ) + t + 1) * Real.exp (4 * Real.pi * t) := by
        simpa [one_mul] using! (mul_le_mul_of_nonneg_right htpoly hExp)
      have hBE :
          ‖(1 / ((65520 : ℂ) * π))‖ * (Cψ * Real.exp (4 * Real.pi * t)) ≤
            (‖(1 / ((65520 : ℂ) * π))‖ * Cψ) * (t ^ (2 : ℕ) + t + 1) *
              Real.exp (4 * Real.pi * t) := by
        have hBnonneg : 0 ≤ ‖(1 / ((65520 : ℂ) * π))‖ * Cψ := by positivity
        have h :=
          mul_le_mul_of_nonneg_left hE hBnonneg
        -- Normalize associativity/commutativity of multiplication.
        simpa [mul_assoc, mul_left_comm, mul_comm] using! h
      grind only
    -- Multiply by the Gaussian factor and combine exponents.
    have hexp :
        ‖(Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)‖ = Real.exp (-Real.pi * (r ^ 2) * t) := by
      have hx : 0 ≤ Real.exp (-Real.pi * (r ^ 2) * t) := by positivity
      exact Complex.norm_of_nonneg hx
    have hmul :
        ‖AKernel0 t * (Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)‖ =
          ‖AKernel0 t‖ * Real.exp (-Real.pi * (r ^ 2) * t) := by
      calc
        ‖AKernel0 t * (Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)‖ =
            ‖AKernel0 t‖ * ‖(Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)‖ := by
              simp [mul_assoc]
          _ = ‖AKernel0 t‖ * Real.exp (-Real.pi * (r ^ 2) * t) := by
                simpa using! congrArg (fun x => ‖AKernel0 t‖ * x) hexp
    -- Combine the exponential factors: `exp(4π t) * exp(-π r^2 t) = exp(-b t)`.
    have hexp' :
        Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * (r ^ 2) * t) = Real.exp (-b * t) := by
      calc
        Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * (r ^ 2) * t) =
            Real.exp ((4 * Real.pi * t) + (-Real.pi * (r ^ 2) * t)) := by
              simp [Real.exp_add]
        _ = Real.exp (-b * t) := by
              congr 1
              dsimp [b]
              ring
    calc
      ‖AKernel0 t * (Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)‖
          = ‖AKernel0 t‖ * Real.exp (-Real.pi * (r ^ 2) * t) := hmul
      _ ≤ (C * (t ^ (2 : ℕ) + t + 1) * Real.exp (4 * Real.pi * t)) *
            Real.exp (-Real.pi * (r ^ 2) * t) := by
            gcongr
      _ =
          C * (t ^ (2 : ℕ) + t + 1) *
            (Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * (r ^ 2) * t)) := by
          ring
      _ = C * (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t) := by
            -- Avoid `simp` turning this into `mul_eq_mul_left_iff`.
            simpa [mul_assoc] using! congrArg (fun x => C * (t ^ (2 : ℕ) + t + 1) * x) hexp'
  -- Integrable dominating function on `Ioi A`.
  have hdomInt :
      IntegrableOn (fun t : ℝ => C * (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t))
        (Set.Ioi A) volume := by
    have hbase :
        IntegrableOn (fun t : ℝ => (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t)) (Set.Ioi (1 : ℝ))
          volume :=
      integrableOn_quadratic_mul_exp_neg_Ioi_one (b := b) hb
    have hbase' :
        IntegrableOn (fun t : ℝ => C * ((t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t)))
          (Set.Ioi (1 : ℝ)) volume := by
      simpa [mul_assoc] using! (hbase.const_mul C)
    have hsub : Set.Ioi A ⊆ Set.Ioi (1 : ℝ) := by
      intro t ht
      exact lt_of_le_of_lt hA1 ht
    have hbase'' :
        IntegrableOn (fun t : ℝ => C * (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t))
          (Set.Ioi (1 : ℝ)) volume := by
      simpa [mul_assoc] using! hbase'
    exact hbase''.mono_set hsub
  -- Deduce integrability on `Ioi A` by domination, then glue the pieces.
  have htail :
      IntegrableOn (fun t : ℝ => AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t))
        (Set.Ioi A) volume := by
    -- Use `Integrable.mono'` on the restricted measure.
    let f : ℝ → ℂ := fun t : ℝ => AKernel0 t * (Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)
    have hf_meas :
        AEStronglyMeasurable f (volume.restrict (Set.Ioi A)) := by
      have hcont : ContinuousOn f (Set.Ioi A) := by
        refine (continuousOn_AKernel0_mul_exp_neg_pi_sq (r := r)).mono ?_
        intro t ht
        exact lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hA1) (le_of_lt ht)
      exact hcont.aestronglyMeasurable (by measurability)
    have hbound :
        ∀ᵐ t ∂(volume.restrict (Set.Ioi A)),
          ‖f t‖ ≤ C * (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t) := by
      -- Use `ae_restrict_iff'` to get the membership hypothesis needed for `hdom`.
      have h' :
          ∀ᵐ t ∂volume, t ∈ Set.Ioi A → ‖f t‖ ≤ C * (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t) := by
        exact ae_of_all volume hdom
      exact (MeasureTheory.ae_restrict_iff' (by measurability)).2 h'
    -- Convert the dominating integrability to an `IntegrableOn` hypothesis.
    have hdomInt' :
        Integrable (fun t : ℝ => C * (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t))
          (volume.restrict (Set.Ioi A)) := hdomInt
    exact (Integrable.mono' hdomInt' hf_meas hbound)
  -- Glue `Ioi 1 = Ioc 1 A ∪ Ioi A`.
  have hunion : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A :=
    Eq.symm (Set.Ioc_union_Ioi_eq_Ioi hA1)
  have htail' :
      IntegrableOn (fun t : ℝ => AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t))
        (Set.Ioi A) volume :=
    htail
  have hall :
      IntegrableOn (fun t : ℝ => AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t))
        (Set.Ioc (1 : ℝ) A ∪ Set.Ioi A) volume :=
    hcomp.union htail'
  simpa [hunion] using! hall

lemma integrableOn_AKernel0_mul_exp_neg_pi_sq_Ioi_zero_of_two_lt (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun t : ℝ => AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t)) (Set.Ioi (0 : ℝ))
      volume := by
  -- `Ioi 0 = Ioc 0 1 ∪ Ioi 1`.
  have h₁ := integrableOn_AKernel0_mul_exp_neg_pi_sq_Ioc_zero_one (r := r)
  have h₂ := integrableOn_AKernel0_mul_exp_neg_pi_sq_Ioi_one_of_two_lt (r := r) hr
  have hunion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) :=
    LaplaceTmp.LaplaceEqA.Ioi_eq_Ioc_union_Ioi_one
  -- Avoid `simp` loops by rewriting the goal with `rw`.
  rw [hunion]
  exact h₁.union h₂

lemma laplaceIntegral_re_neg_of_two_lt (r : ℝ) (hr : 2 < r) :
    (∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t)).re < 0 := by
  let f : ℝ → ℂ := fun t : ℝ => AKernel0 t * (Real.exp (-Real.pi * (r ^ 2) * t) : ℂ)
  have hf_int : Integrable f μIoi0 := by
    have hf_int_on : IntegrableOn (fun t : ℝ => f t) (Set.Ioi (0 : ℝ)) volume := by
      dsimp [f]
      exact integrableOn_AKernel0_mul_exp_neg_pi_sq_Ioi_zero_of_two_lt (r := r) hr
    assumption
  -- Consider `g = -Re(f)`, which is strictly positive on `(0,∞)`.
  let g : ℝ → ℝ := fun t : ℝ => -((f t).re)
  have hg_int : Integrable g μIoi0 := hf_int.re.neg
  have hg_nonneg : 0 ≤ᵐ[μIoi0] g := by
    -- Pointwise positivity on `t > 0`.
    dsimp [μIoi0]
    refine
      (MeasureTheory.ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))).2 ?_
    refine ae_of_all _ ?_
    intro t ht
    have ht0 : 0 < t := ht
    have hA : (AKernel0 t).re < 0 := by
      simpa [AKernel0, ht0] using! (AKernel_re_neg t ht0)
    have hExp : 0 < Real.exp (-Real.pi * (r ^ 2) * t) := Real.exp_pos _
    have hre :
        (f t).re = (AKernel0 t).re * Real.exp (-Real.pi * (r ^ 2) * t) := by
      exact Complex.re_mul_ofReal _ _
    have hft : (f t).re < 0 := by
      simpa [hre] using! (mul_neg_of_neg_of_pos hA hExp)
    exact le_of_lt (by simpa [g] using! (neg_pos.2 hft))
  have hsupport : 0 < μIoi0 (Function.support g) := by
    -- Since `g t > 0` for all `t > 0`, its support contains `Ioi 0`.
    have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support g := by
      intro t ht
      have ht0 : 0 < t := ht
      have hA : (AKernel0 t).re < 0 := by
        simpa [AKernel0, ht0] using! (AKernel_re_neg t ht0)
      have hExp : 0 < Real.exp (-Real.pi * (r ^ 2) * t) := Real.exp_pos _
      have hre :
          (f t).re = (AKernel0 t).re * Real.exp (-Real.pi * (r ^ 2) * t) := by
        exact Complex.re_mul_ofReal _ _
      have hft : (f t).re < 0 := by
        simpa [hre] using! (mul_neg_of_neg_of_pos hA hExp)
      have : g t ≠ 0 := by
        dsimp [g]
        exact (neg_ne_zero.2 (ne_of_lt hft))
      exact this
    have hμpos : (0 : ENNReal) < μIoi0 (Set.Ioi (0 : ℝ)) := by
      -- The interval `(0,∞)` has infinite (hence positive) volume.
      simp [μIoi0, Measure.restrict_apply, measurableSet_Ioi]
    exact pos_mono hsub hμpos
  have hpos : (0 : ℝ) < ∫ t in Set.Ioi (0 : ℝ), g t ∂volume := by
    -- Positivity criterion for a nonnegative integrable function.
    exact (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hg_nonneg hg_int).2 hsupport
  -- Convert `0 < ∫ -Re(f)` into `∫ Re(f) < 0`.
  have hnegRe : (∫ t in Set.Ioi (0 : ℝ), (f t).re ∂volume) < 0 := by
    have : (0 : ℝ) < ∫ t in Set.Ioi (0 : ℝ), -((f t).re) ∂volume := by
      simpa [g] using! hpos
    have hneg :
        (∫ t in Set.Ioi (0 : ℝ), -((f t).re) ∂volume) =
          -∫ t in Set.Ioi (0 : ℝ), (f t).re ∂volume := by
          simpa using!
            (integral_neg (μ := (volume.restrict (Set.Ioi (0 : ℝ)))) (f := fun t : ℝ => (f t).re))
    have : (0 : ℝ) < -∫ t in Set.Ioi (0 : ℝ), (f t).re ∂volume := by simpa [hneg] using! this
    nlinarith
  -- Commute `re` with the integral.
  have hre :
      (∫ t in Set.Ioi (0 : ℝ), (f t).re ∂volume) =
        (∫ t in Set.Ioi (0 : ℝ), f t ∂volume).re := by
    simpa [μIoi0] using! (integral_re (μ := μIoi0) (f := f) hf_int)
  have : (∫ t in Set.Ioi (0 : ℝ), f t ∂volume).re < 0 := by simpa [hre] using! hnegRe
  simpa [f] using! this

lemma laplaceIntegral_ne_zero_of_two_lt (r : ℝ) (hr : 2 < r) :
    (∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t)) ≠ 0 := by
  intro h
  have hre : (∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t)).re < 0 :=
    laplaceIntegral_re_neg_of_two_lt (r := r) hr
  simp_all

end UniquenessRootsLaplaceAux

/-- Invariance of the auxiliary function `f` under orthogonal transformations. -/
theorem f_invariant_linearIsometryEquiv (e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴) (x : ℝ²⁴) :
    f (e x) = f x := by
  -- `f` is a radial Schwartz function of the form `x ↦ F(‖x‖^2)`.
  have hnorm : ‖e x‖ = ‖x‖ := by simp
  -- Use the explicit radial profile formula for `f`.
  simp [LaplaceTmp.LaplaceApply.f_apply, hnorm]

/-- Radiality of the auxiliary function: `f` depends only on `‖x‖`. -/
public theorem f_eq_f_axisVec_norm (x : ℝ²⁴) : f x = f (axisVec ‖x‖) := by
  -- Both sides are obtained by plugging in `‖x‖^2` into the same one-variable profile.
  simp [LaplaceTmp.LaplaceApply.f_apply, norm_axisVec_sq]

/-- One-variable root classification for `f` at radii `r ≥ 2`. -/
public theorem norm_sq_eq_two_mul_of_f_axisVec_eq_zero_of_two_le (r : ℝ) (hr : (2 : ℝ) ≤ r)
    (hf : f (axisVec r) = 0) :
    ∃ k : ℕ, 2 ≤ k ∧ r ^ 2 = (2 : ℝ) * k := by
  /- For `2 < r`, use the Laplace representation of `f (axisVec r)` to isolate the factor
  `sin(π r^2/2)^2`; nonvanishing of the Laplace integral then forces the sine factor to vanish. -/
  have hr0 : 0 ≤ r := le_trans (by norm_num : (0 : ℝ) ≤ 2) hr
  have hnorm_axis : ‖axisVec r‖ = r := by
    simp [axisVec, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_eq_self.mpr hr0]
  rcases lt_or_eq_of_le hr with hrlt | hreq
  · -- Main case: `2 < r`, use the Laplace representation and nonvanishing of the Laplace factor.
    have hx : 2 < ‖axisVec r‖ := by simpa [hnorm_axis] using! hrlt
    have hfLap := LaplaceTmp.f_eq_laplace_A (x := axisVec r) hx
    -- Abbreviate the Laplace integral factor.
    set I : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * (r ^ 2) * t)
    have hI : I ≠ 0 := by
      -- Strict negativity of the real part implies nonzero.
      exact UniquenessRootsLaplaceAux.laplaceIntegral_ne_zero_of_two_lt (r := r) hrlt
    -- Rewrite `f (axisVec r)` using the Laplace representation.
    have hf0 :
        (((Real.sin (Real.pi * (r ^ 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) * I = 0 := by
      have hf0' :
          (((Real.sin (Real.pi * (‖axisVec r‖ ^ 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
              (∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * (‖axisVec r‖ ^ 2) * t)) =
            0 := by
        simpa [hfLap] using! hf
      have hnorm_sq : ‖axisVec r‖ ^ 2 = r ^ 2 := by simp [hnorm_axis]
      -- Rewrite the integral and the sine factor using `‖axisVec r‖ = r`.
      simpa [I, hnorm_sq] using! hf0'
    have hsin_sqC :
        (((Real.sin (Real.pi * (r ^ 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) = 0 := by
      exact (mul_eq_zero.mp hf0).resolve_right hI
    have hsin_sq : (Real.sin (Real.pi * (r ^ 2) / 2)) ^ (2 : ℕ) = 0 :=
      (Complex.ofReal_eq_zero).1 hsin_sqC
    have hsin : Real.sin (Real.pi * (r ^ 2) / 2) = 0 := by
      -- `a^2 = 0` implies `a = 0`.
      exact eq_zero_of_pow_eq_zero hsin_sq
    rcases (Real.sin_eq_zero_iff).1 hsin with ⟨n, hn⟩
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    -- Cancel `π` from `π * r^2 / 2 = n * π` by multiplying by `2` and dividing by `π`.
    have hn2 : Real.pi * (r ^ 2) / 2 = (n : ℝ) * Real.pi := by
      -- `Real.sin_eq_zero_iff` may return the equality in the opposite direction.
      simpa [mul_comm] using! hn.symm
    have hn3 : Real.pi * (r ^ 2) = (2 : ℝ) * (n : ℝ) * Real.pi := by
      have hn3' := congrArg (fun x : ℝ => x * (2 : ℝ)) hn2
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! hn3'
    have hr2 : r ^ 2 = (2 : ℝ) * (n : ℝ) := by
      have hn4 := congrArg (fun x : ℝ => x / Real.pi) hn3
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hpi] using! hn4
    -- Convert the integer `n` to a natural number.
    have hn_nonneg : 0 ≤ n := by
      have : (0 : ℝ) ≤ (n : ℝ) := by
        have : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
        nlinarith [hr2, this]
      exact (Int.cast_nonneg_iff).1 this
    let k : ℕ := Int.toNat n
    have hn_cast : (n : ℝ) = (k : ℝ) := by
      have hn_int : (Int.ofNat k) = n := by
        simpa [k] using! (Int.toNat_of_nonneg hn_nonneg)
      have hn_real := congrArg (fun z : ℤ => (z : ℝ)) hn_int
      simpa using! hn_real.symm
    have hr2k : r ^ 2 = (2 : ℝ) * k := by simpa [hn_cast] using! hr2
    have hk_ge : 2 ≤ k := by
      have : (4 : ℝ) ≤ r ^ 2 := by nlinarith [hr]
      have : (4 : ℝ) ≤ (2 : ℝ) * k := by simpa [hr2k] using! this
      have : (2 : ℝ) ≤ (k : ℝ) := by nlinarith
      exact_mod_cast this
    exact ⟨k, hk_ge, hr2k⟩
  · -- Boundary case: `r = 2`.
    have hrEq : r = 2 := by simpa [eq_comm] using! hreq
    refine ⟨2, by decide, ?_⟩
    -- `r^2 = 4 = 2*2`.
    norm_num [hrEq]

end

end SpherePacking.Dim24
