-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.EvenU.BProfileZeros
public import SpherePacking.Dim24.MagicFunction.F.BKernelAsymptotics
public import SpherePacking.Dim24.MagicFunction.F.Laplace.KernelTools
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.LeadingCorrection
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingBounds.BKernelSubLeadingBound
public import SpherePacking.Dim24.MagicFunction.F.ProfileComplex.B
public import SpherePacking.Dim24.MagicFunction.F.Laplace.TopologyDomains
public import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Tactic.NormNumI
public import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
public import SpherePacking.Dim24.MagicFunction.Radial
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Profiles.AProfile
public import SpherePacking.Dim24.MagicFunction.F.Laplace.A.Basic
import SpherePacking.ForMathlib.DerivHelpers


/-!
# The integrand `gV` for the `A`-kernel

This file defines the Laplace integrand `gV u t` corresponding to the `varphi` contribution in the
`AKernel0` Laplace formula, and records basic integrability lemmas on `(0,1]` and `(1,∞)`.

## Main definitions
* `gV`

## Main statements
* `integrableOn_gV_Ioc`
* `integrableOn_gV_Ioi_one`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceEqA

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Interval

open Complex MeasureTheory Real SchwartzMap Set
open RealIntegrals RealIntegrals.ComplexIntegrands
open UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The Laplace integrand corresponding to the `varphi` part of `AKernel0`. -/
@[expose] public def gV (u : ℝ) (t : ℝ) : ℂ :=
  LaplaceProfiles.varphiKernel0 t * Real.exp (-Real.pi * u * t)

lemma gV_eq_neg_Φ₅' (u t : ℝ) (ht : 0 < t) :
    gV u t = -Φ₅' u ((t : ℂ) * Complex.I) := by
  have hΦ := LaplaceA.Φ₅'_imag_axis_eq_laplace (u := u) (t := t) ht
  have hexp : Complex.exp (-Real.pi * u * t : ℂ) = (Real.exp (-Real.pi * u * t) : ℂ) := by
    simp [mul_assoc]
  have hker : LaplaceProfiles.varphiKernel0 t = ((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht) := by
    simp [LaplaceProfiles.varphiKernel0, ht]
  have hΦ' :
      -Φ₅' u ((t : ℂ) * Complex.I) =
        ((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht) * (Real.exp (-Real.pi * u * t) : ℂ) := by
    have := congrArg Neg.neg hΦ
    simpa [hexp, mul_assoc, mul_left_comm, mul_comm] using! this
  calc
    gV u t =
        ((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht) * (Real.exp (-Real.pi * u * t) : ℂ) := by
          simp [gV, hker, mul_assoc]
    _ = -Φ₅' u ((t : ℂ) * Complex.I) := by
          simpa [mul_assoc] using! hΦ'.symm

/-- Integrability of `gV u` on the tail `t > 1` in the convergent range `u > 4`. -/
public lemma integrableOn_gV_Ioi_one (u : ℝ) (hu : 4 < u) :
    IntegrableOn (gV u) (Set.Ioi (1 : ℝ)) volume := by
  have hIntΦ :
      Integrable (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (volume.restrict (Set.Ioi (1 : ℝ))) :=
    LaplaceZerosTail.TailDeform.integrable_imag_axis_Φ₅' (u := u) hu
  have hEq :
      (fun t : ℝ => gV u t) =ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
        fun t : ℝ => -Φ₅' u ((t : ℂ) * Complex.I) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht
    simpa using! (gV_eq_neg_Φ₅' (u := u) (t := t) ht0)
  have hInt : Integrable (fun t : ℝ => -Φ₅' u ((t : ℂ) * Complex.I))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    hIntΦ.neg
  simpa [IntegrableOn] using! (hInt.congr hEq.symm)

lemma varphi_iOverT_eq_resToImagAxis (t : ℝ) (ht : 0 < t) :
    varphi (iOverT t ht) = varphi.resToImagAxis (1 / t) := by
  have htInv : 0 < (1 / t : ℝ) := one_div_pos.2 ht
  let z : ℍ :=
    ⟨(Complex.I : ℂ) * ((1 / t : ℝ) : ℂ), by
      simpa [Complex.mul_im] using! htInv⟩
  have hRes : varphi.resToImagAxis (1 / t) = varphi z := by
    -- `simp` may rewrite the `if`-condition `0 < (1/t)` to `0 < t`, so supply both.
    simp [Function.resToImagAxis, ResToImagAxis, ht, z]
  have hArg : iOverT t ht = z := by
    ext1
    simp [iOverT, it, z]
  exact Mathlib.Meta.NormNumI.eq_of_eq_of_eq_of_eq (congrArg varphi hArg) hRes rfl rfl

/-- Integrability of `gV u` on the segment `(0,1]` for `0 ≤ u`. -/
public lemma integrableOn_gV_Ioc (u : ℝ) (hu0 : 0 ≤ u) :
    IntegrableOn (gV u) (Set.Ioc (0 : ℝ) 1) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by infer_instance
  -- Measurability from continuity on `(0,1]` after rewriting through `varphi.resToImagAxis (1/t)`.
  have hcont :
      ContinuousOn (gV u) (Set.Ioc (0 : ℝ) 1) := by
    -- First show continuity of `t ↦ varphi.resToImagAxis (1/t)` on `(0,1]`.
    have hinv :
        ContinuousOn (fun t : ℝ => (1 / t : ℝ)) (Set.Ioc (0 : ℝ) 1) := by
      have hinv0 : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Ioc (0 : ℝ) 1) := by
        refine (continuousOn_inv₀ (G₀ := ℝ)).mono ?_
        intro t ht
        exact ne_of_gt ht.1
      simpa [one_div] using! hinv0
    have hmap : Set.MapsTo (fun t : ℝ => (1 / t : ℝ)) (Set.Ioc (0 : ℝ) 1) (Set.Ici (1 : ℝ)) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have : (1 : ℝ) ≤ 1 / t := by simpa using! (one_le_one_div ht0 ht1)
      exact this
    have hres :
        ContinuousOn (fun t : ℝ => varphi.resToImagAxis (1 / t)) (Set.Ioc (0 : ℝ) 1) :=
      (VarphiExpBounds.continuousOn_varphi_resToImagAxis_Ici_one.comp hinv hmap)
    -- The explicit expression (valid on `t>0`) is continuous, hence so is `gV u`.
    let h1 : ℝ → ℂ :=
      fun t : ℝ =>
        ((t : ℂ) ^ (10 : ℕ)) * varphi.resToImagAxis (1 / t) *
          (Real.exp (-Real.pi * u * t) : ℂ)
    have h1_cont : ContinuousOn h1 (Set.Ioc (0 : ℝ) 1) := by
      have hpow : Continuous fun t : ℝ => ((t : ℂ) ^ (10 : ℕ)) := by fun_prop
      have hexp : Continuous fun t : ℝ => (Real.exp (-Real.pi * u * t) : ℂ) := by fun_prop
      -- product of continuous-on factors
      simpa [h1, mul_assoc] using! (hpow.continuousOn.mul (hres.mul hexp.continuousOn))
    refine h1_cont.congr ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    have hEq : varphi (iOverT t ht0) = varphi.resToImagAxis (1 / t) :=
      (varphi_iOverT_eq_resToImagAxis (t := t) ht0)
    have hker : LaplaceProfiles.varphiKernel0 t = ((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht0) := by
      simp [LaplaceProfiles.varphiKernel0, ht0]
    simp [gV, h1, hker, hEq, mul_left_comm, mul_comm]
  have hmeas :
      AEStronglyMeasurable (gV u) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ)) hcont measurableSet_Ioc
  -- Uniform bound from the exponential decay estimate on the imaginary axis.
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨C0, hC0⟩
  have hC0nonneg : 0 ≤ C0 := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖varphi.resToImagAxis 1‖)
      (b := Real.exp (-(2 * Real.pi) * (1 : ℝ))) (C := C0) (norm_nonneg _) (by positivity) ?_
    simpa using! (hC0 1 (le_rfl : (1 : ℝ) ≤ 1))
  let C : ℝ := max C0 0
  have hbound :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖gV u t‖ ≤ C := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hone : (1 : ℝ) ≤ 1 / t := by simpa using! (one_le_one_div ht0 ht1)
    have hEq : varphi (iOverT t ht0) = varphi.resToImagAxis (1 / t) :=
      (varphi_iOverT_eq_resToImagAxis (t := t) ht0)
    have hvar' :
        ‖varphi (iOverT t ht0)‖ ≤ C0 := by
      have h0 := hC0 (1 / t) hone
      have hexp_le : Real.exp (-(2 * Real.pi) * (1 / t)) ≤ 1 := by
        have : (-(2 * Real.pi) * (1 / t) : ℝ) ≤ 0 := by
          have htInv : 0 < (1 / t : ℝ) := one_div_pos.2 ht0
          have : 0 ≤ (1 / t : ℝ) := le_of_lt htInv
          nlinarith [Real.pi_pos, this]
        simpa using! (Real.exp_le_one_iff.2 this)
      have hle : C0 * Real.exp (-(2 * Real.pi) * (1 / t)) ≤ C0 :=
        (mul_le_mul_of_nonneg_left hexp_le hC0nonneg).trans (by simp)
      exact (by simpa [hEq] using! (le_trans h0 hle))
    have hpow : ‖(t : ℂ) ^ (10 : ℕ)‖ ≤ 1 := by
      have ht' : ‖(t : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, abs_of_nonneg (le_of_lt ht0)] using! ht1
      have : ‖(t : ℂ)‖ ^ (10 : ℕ) ≤ 1 ^ (10 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg (t : ℂ)) ht' 10
      simpa [norm_pow] using! this
    have hexpU : ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ ≤ 1 := by
      have hle : Real.exp (-Real.pi * u * t) ≤ 1 := by
        refine Real.exp_le_one_iff.2 ?_
        have hpos : 0 ≤ Real.pi * u * t := by positivity [hu0, le_of_lt ht0]
        linarith
      have hnorm : ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ = Real.exp (-Real.pi * u * t) := by
        calc
          ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ = ‖Complex.exp (-Real.pi * u * t)‖ := by
            simp [Complex.ofReal_exp]
          _ = Real.exp (-Real.pi * u * t) := by
            simpa using! (Complex.norm_exp_ofReal (-Real.pi * u * t))
      rw [hnorm]
      exact hle
    have hker : LaplaceProfiles.varphiKernel0 t = ((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht0) := by
      simp [LaplaceProfiles.varphiKernel0, ht0]
    calc
      ‖gV u t‖ = ‖LaplaceProfiles.varphiKernel0 t * (Real.exp (-Real.pi * u * t) : ℂ)‖ := by
            simp [gV, mul_assoc]
      _ ≤ ‖LaplaceProfiles.varphiKernel0 t‖ * ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ := by
            exact
              norm_mul_le (LaplaceProfiles.varphiKernel0 t) (Real.exp (-Real.pi * u * t) : ℂ)
      _ ≤ ‖LaplaceProfiles.varphiKernel0 t‖ * 1 := by gcongr
      _ = ‖LaplaceProfiles.varphiKernel0 t‖ := by simp
      _ = ‖((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht0)‖ := by simp [hker]
      _ ≤ ‖(t : ℂ) ^ (10 : ℕ)‖ * ‖varphi (iOverT t ht0)‖ := by
            exact norm_mul_le ((t : ℂ) ^ (10 : ℕ)) (varphi (iOverT t ht0))
      _ ≤ 1 * C0 := by gcongr
      _ ≤ 1 * C := by gcongr; exact le_max_left _ _
      _ = C := by simp
  refine ⟨hmeas, ?_⟩
  exact HasFiniteIntegral.of_bounded hbound

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceEqA
