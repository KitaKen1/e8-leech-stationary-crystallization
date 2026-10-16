-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegralDefs
import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderLargeBound
import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.Function
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivDefs
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import Mathlib.MeasureTheory.Integral.ExpDecay
public import SpherePacking.ForMathlib.CancelDenomsCompat

/-!
# Domination for the `eq:avalues` remainder integrand

This file provides integrable domination estimates for `avaluesRemainderIntegrandFull u t`,
uniform for `u` in a neighborhood of `2`.

## Main statements
* `exists_integrable_bound_Ici_one`
* `exists_integrable_bound_Ioc_zero_one`
* `exists_integrable_bound_Ioi_zero`

## Implementation notes
The large-`t` bound uses the `q`-expansion remainder estimate from `dim_24.tex`.
The small-`t` bound uses the `S`-transform identity.
-/

namespace SpherePacking.Dim24
noncomputable section
namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex MeasureTheory Set

theorem avaluesRemainderIntegrandFull_eq_of_pos {u t : ℝ} (ht : 0 < t) :
    avaluesRemainderIntegrandFull u t =
      ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) - pPaper t) *
        (Real.exp (-Real.pi * u * t) : ℂ) := by
  simp [avaluesRemainderIntegrandFull, ht]

theorem avaluesRemainderIntegrandFull_eq_zero_of_not_pos {u t : ℝ} (ht : ¬ 0 < t) :
    avaluesRemainderIntegrandFull u t = 0 := by
  simp [avaluesRemainderIntegrandFull, ht]

/-!
### Large-`t` bounds
-/

/- `q`-expansion remainder bound from `dim_24.tex` (eq. `eq:phip`), stated for norms.

We use the bound `‖t^10*varphi(i/t) - p(t)‖ ≤ C * t^2 * exp (-2π t)` for `t ≥ 1`. -/
/-- Domination on `[1,∞)` for `u` near `2`, using exponential decay. -/
public theorem exists_integrable_bound_Ici_one :
    ∃ bound : ℝ → ℝ,
      IntegrableOn bound (Set.Ici (1 : ℝ)) volume ∧
      (∀ᶠ u in 𝓝 (2 : ℝ), ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ici (1 : ℝ))),
        ‖avaluesRemainderIntegrandFull u t‖ ≤ bound t) := by
  rcases exists_bound_remainder_large_proof with ⟨C, hCnonneg, hC⟩
  -- Fix a decay rate using the neighborhood `u > 3/2`.
  let a : ℝ := (7 / 2) * Real.pi
  let bound : ℝ → ℝ := fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-a * t)
  refine ⟨bound, ?_, ?_⟩
  · -- Integrability on `[1, ∞)`: polynomial times exponential decay.
    have ha : 0 < a := by
      have h72 : 0 < (7 / 2 : ℝ) := by norm_num
      exact mul_pos h72 Real.pi_pos
    have hb : 0 < a / 2 := half_pos ha
    have hcont :
        ContinuousOn (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-a * t)) (Set.Ici (1 : ℝ)) := by
      fun_prop
    have hpow :
        (fun t : ℝ => C * (t ^ (2 : ℕ))) =O[atTop] fun t : ℝ => Real.exp ((a / 2) * t) :=
      ((isLittleO_pow_exp_pos_mul_atTop (k := 2) hb).const_mul_left C).isBigO
    have hexp :
        (fun t : ℝ => Real.exp (-a * t)) =O[atTop] fun t : ℝ => Real.exp (-a * t) :=
      Asymptotics.isBigO_refl _ _
    have hmul :
        (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-a * t)) =O[atTop]
          fun t : ℝ => Real.exp ((a / 2) * t) * Real.exp (-a * t) := by
      simpa [mul_assoc] using! hpow.mul hexp
    have hmul' :
        (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-a * t)) =O[atTop]
          fun t : ℝ => Real.exp (-(a / 2) * t) := by
      refine hmul.congr_right ?_
      intro t
      have : (a / 2) * t + (-a * t) = (-(a / 2) * t) := by ring_nf
      calc
        Real.exp ((a / 2) * t) * Real.exp (-a * t) = Real.exp ((a / 2) * t + (-a * t)) := by
          simp [Real.exp_add]
        _ = Real.exp (-(a / 2) * t) := by rw [this]
    have hIoi :
        IntegrableOn (fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-a * t)) (Set.Ioi (1 : ℝ))
          volume :=
      integrable_of_isBigO_exp_neg (a := (1 : ℝ)) (b := a / 2) hb hcont hmul'
    exact (integrableOn_Ici_iff_integrableOn_Ioi (μ := volume)
      (f := fun t : ℝ => C * (t ^ (2 : ℕ)) * Real.exp (-a * t)) (b := (1 : ℝ))).2 hIoi
  · -- Pointwise domination on `[1, ∞)` for `u` near `2`.
    have hU : Set.Ioi ((3 / 2 : ℝ)) ∈ 𝓝 (2 : ℝ) := by
      refine Ioi_mem_nhds ?_
      norm_num
    filter_upwards [hU] with u hu
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
    have hdef :
        avaluesRemainderIntegrandFull u t =
          ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t) *
            (Real.exp (-Real.pi * u * t) : ℂ) := by
      simp [avaluesRemainderIntegrandFull, ht0]
    have hrem :
        ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ ≤
          C * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) :=
      hC t ht1 ht0
    have hExp_le :
        Real.exp (-Real.pi * u * t) ≤ Real.exp (-Real.pi * (3 / 2) * t) := by
      have hmul : Real.pi * (3 / 2) * t ≤ Real.pi * u * t := by
        have hpi : 0 ≤ Real.pi := Real.pi_pos.le
        have hu' : (3 / 2 : ℝ) ≤ u := hu.le
        have hmul1 : Real.pi * (3 / 2) ≤ Real.pi * u := mul_le_mul_of_nonneg_left hu' hpi
        exact mul_le_mul_of_nonneg_right hmul1 ht0.le
      have hneg : -(Real.pi * u * t) ≤ -(Real.pi * (3 / 2) * t) :=
        neg_le_neg hmul
      have hneg' : (-Real.pi) * u * t ≤ (-Real.pi) * (3 / 2) * t := by
        simpa [mul_assoc, neg_mul, mul_left_comm, mul_comm] using! hneg
      exact Real.exp_le_exp.2 hneg'
    have hExp_norm :
        ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ = Real.exp (-Real.pi * u * t) := by
      -- Prevent simp from rewriting `(Real.exp x : ℂ)` as `Complex.exp (x : ℂ)`.
      simp [-Complex.ofReal_exp, Complex.norm_real, abs_of_nonneg (Real.exp_pos _).le]
    have hcoeff0 : 0 ≤ C * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
      have ht2 : 0 ≤ t ^ (2 : ℕ) := pow_nonneg ht0.le 2
      have hexp : 0 ≤ Real.exp (-(2 * Real.pi) * t) := by positivity
      exact mul_nonneg (mul_nonneg hCnonneg ht2) hexp
    have hExpProd :
        Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * (3 / 2) * t) =
          Real.exp (-a * t) := by
      have : (-(2 * Real.pi) * t) + (-Real.pi * (3 / 2) * t) = -a * t := by
        simp [a]
        ring_nf
      calc
        Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * (3 / 2) * t) =
            Real.exp ((-(2 * Real.pi) * t) + (-Real.pi * (3 / 2) * t)) := by
              simp [Real.exp_add]
        _ = Real.exp (-a * t) := by rw [this]
    calc
      ‖avaluesRemainderIntegrandFull u t‖ =
          ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ *
            ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ := by
              simp [hdef, -Complex.ofReal_exp]
      _ ≤ (C * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) *
            ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ :=
              mul_le_mul_of_nonneg_right hrem (norm_nonneg _)
      _ = (C * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) * Real.exp (-Real.pi * u * t) := by
              rw [hExp_norm]
      _ ≤
          (C * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) *
            Real.exp (-Real.pi * (3 / 2) * t) :=
              mul_le_mul_of_nonneg_left hExp_le hcoeff0
      _ = bound t := by
              -- Rewrite the product of exponentials to `exp (-a * t)`.
              unfold bound
              have :
                  (C * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) *
                      Real.exp (-Real.pi * (3 / 2) * t) =
                    (C * (t ^ (2 : ℕ))) *
                      (Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * (3 / 2) * t)) := by
                simp [mul_assoc]
              exact Eq.symm (CancelDenoms.derive_trans (id (Eq.symm hExpProd)) (id (Eq.symm this)))

/-!
### Small-`t` bounds
-/

/-- S-transform identity (paper eq. `eq:10overt`) specialized to the imaginary axis. -/
theorem ten_pow_varphi_iOverT_eq_transform (t : ℝ) (ht : 0 < t) :
    (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) =
      (t : ℂ) ^ (2 : ℕ) * varphi (it t ht) -
        (Complex.I : ℂ) * (t : ℂ) * varphi₁ (it t ht) - varphi₂ (it t ht) := by
  -- This is exactly `tPow10_varphi_iOverT` from `VarphiNeg.LeOne.Transform`.
  simpa using! (Dim24.tPow10_varphi_iOverT (t := t) ht)

/-- A coarse domination on `(0,1]` for `u` near `2`. -/
public theorem exists_integrable_bound_Ioc_zero_one :
    ∃ bound : ℝ → ℝ,
      IntegrableOn bound (Set.Ioc (0 : ℝ) 1) volume ∧
      (∀ᶠ u in 𝓝 (2 : ℝ), ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        ‖avaluesRemainderIntegrandFull u t‖ ≤ bound t) := by
  rcases Dim24.VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ, hCφ⟩
  -- Make the constant nonnegative for monotonicity arguments.
  let C : ℝ := max Cφ 0
  have hCnonneg : 0 ≤ C := by simp [C]
  have hCφ' : ∀ s : ℝ, 1 ≤ s → ‖varphi.resToImagAxis s‖ ≤ C * rexp (-(2 * π) * s) := by
    intro s hs
    have h := hCφ s hs
    have hexp0 : 0 ≤ rexp (-(2 * π) * s) := by positivity
    have hcoef : Cφ * rexp (-(2 * π) * s) ≤ C * rexp (-(2 * π) * s) := by
      exact mul_le_mul_of_nonneg_right (le_max_left Cφ 0) hexp0
    exact le_trans h hcoef
  -- Bound `pPaper` on `[0,1]` by compactness.
  have hpPaper_cont : Continuous pPaper := by
    unfold pPaper
    fun_prop
  have hcont_pPaperIcc : Continuous fun t : Set.Icc (0 : ℝ) 1 => pPaper (t : ℝ) :=
    hpPaper_cont.comp continuous_subtype_val
  rcases SpecialValuesDeriv.exists_bound_norm_of_continuous (X := Set.Icc (0 : ℝ) 1) hcont_pPaperIcc
    with ⟨Mp, hMp⟩
  -- A constant dominator on `(0,1]`.
  let K : ℝ := C * rexp (-(2 * π)) + Mp
  let bound : ℝ → ℝ := fun _ => K
  have hbound_int : IntegrableOn bound (Set.Ioc (0 : ℝ) 1) volume := by
    dsimp [bound]
    have hs : volume (Set.Ioc (0 : ℝ) 1) ≠ ⊤ :=
      (ne_of_lt (measure_Ioc_lt_top : volume (Set.Ioc (0 : ℝ) 1) < ⊤))
    have hK : ‖(K : ℝ)‖ₑ ≠ ⊤ := (enorm_ne_top : ‖(K : ℝ)‖ₑ ≠ ⊤)
    exact (integrableOn_const (s := Set.Ioc (0 : ℝ) 1) (μ := volume) (C := K) hs hK)
  refine ⟨bound, hbound_int, ?_⟩
  have hupos : Set.Ioi (0 : ℝ) ∈ 𝓝 (2 : ℝ) := Ioi_mem_nhds (by norm_num)
  filter_upwards [hupos] with u hu0
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| Filter.Eventually.of_forall ?_
  intro t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2
  -- Kernel norm bound.
  have hExp_norm : ‖(rexp (-π * u * t) : ℂ)‖ ≤ 1 := by
    have hnonneg : 0 ≤ π * u * t := by
      have hpi : 0 ≤ (π : ℝ) := Real.pi_pos.le
      have hu : 0 ≤ u := (show (0 : ℝ) < u from hu0).le
      exact mul_nonneg (mul_nonneg hpi hu) ht0.le
    have hnonpos : -π * u * t ≤ 0 := by
      simpa [neg_mul, mul_assoc] using! (neg_nonpos.2 hnonneg)
    have hle : rexp (-π * u * t) ≤ 1 := by
      simpa using! (Real.exp_le_one_iff.2 hnonpos)
    simpa [-Complex.ofReal_exp, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using! hle
  -- Bound `‖varphi(i/t)‖` from the tail decay estimate with `s = 1/t ≥ 1`.
  have hs : 1 ≤ (1 / t : ℝ) := one_le_one_div ht0 ht1
  have htinv_pos : 0 < (1 / t : ℝ) := by simpa using! (one_div_pos.2 ht0)
  have hres : varphi (iOverT t ht0) = varphi.resToImagAxis (1 / t) := by
    set s : ℝ := 1 / t
    have hspos : 0 < s := by simpa [s] using! htinv_pos
    have haxis : varphi.resToImagAxis s = varphi (it s hspos) := by
      simp [Function.resToImagAxis, ResToImagAxis, hspos, it]
    have hio : iOverT t ht0 = it s hspos := by
      ext1
      simp [iOverT, it, s]
    simpa [s, hio] using! haxis.symm
  have hvarphi_bound :
      ‖varphi (iOverT t ht0)‖ ≤ C * rexp (-(2 * π) * (1 / t)) := by
    simpa [hres] using! hCφ' (1 / t) hs
  have hvarphi_bound_const : ‖varphi (iOverT t ht0)‖ ≤ C * rexp (-(2 * π)) := by
    have hle : (-(2 * π) : ℝ) * (1 / t) ≤ (-(2 * π) : ℝ) * 1 := by
      have hneg : (-(2 * π) : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
      exact mul_le_mul_of_nonpos_left hs hneg
    have hexp : rexp ((-(2 * π) : ℝ) * (1 / t)) ≤ rexp ((-(2 * π) : ℝ) * 1) :=
      Real.exp_le_exp.2 hle
    have hexp' : rexp (-(2 * π) * (1 / t)) ≤ rexp (-(2 * π)) := by
      simpa [mul_assoc] using! hexp
    exact le_trans hvarphi_bound (mul_le_mul_of_nonneg_left hexp' hCnonneg)
  -- Bound `‖pPaper t‖` on `[0,1]`.
  have hpPaper : ‖pPaper t‖ ≤ Mp := by
    have htIcc : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
    simpa using! hMp ⟨t, htIcc⟩
  -- Bound the remainder term.
  have hrem : ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ ≤ K := by
    have hsub := norm_sub_le ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)) (pPaper t)
    refine le_trans hsub ?_
    have ht10_norm : ‖(t : ℂ) ^ (10 : ℕ)‖ ≤ 1 := by
      -- `‖(t:ℂ)^10‖ = |t|^10 ≤ 1` since `0 < t ≤ 1`.
      have habs : |t| ≤ 1 := by simpa [abs_of_nonneg ht0.le] using! ht1
      have : |t| ^ (10 : ℕ) ≤ (1 : ℝ) ^ (10 : ℕ) := pow_le_pow_left₀ (abs_nonneg t) habs 10
      have : |t| ^ (10 : ℕ) ≤ 1 := by simpa using! this
      simpa [Complex.norm_real, abs_of_nonneg ht0.le] using! this
    have hterm :
        ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖ ≤ C * rexp (-(2 * π)) := by
      have hmul :
          ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖ ≤
            ‖(t : ℂ) ^ (10 : ℕ)‖ * ‖varphi (iOverT t ht0)‖ := by
        exact norm_mul_le ((t : ℂ) ^ (10 : ℕ)) (varphi (iOverT t ht0))
      calc
        ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0)‖ ≤
            ‖(t : ℂ) ^ (10 : ℕ)‖ * ‖varphi (iOverT t ht0)‖ := hmul
        _ ≤ 1 * (C * rexp (-(2 * π))) := by
            exact
              mul_le_mul ht10_norm hvarphi_bound_const (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)
        _ = C * rexp (-(2 * π)) := by ring_nf
    exact add_le_add hterm hpPaper
  -- Multiply by the kernel (≤ 1).
  have hmul :
      ‖avaluesRemainderIntegrandFull u t‖ ≤ K := by
    have hdef :
        avaluesRemainderIntegrandFull u t =
          ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t) * (rexp (-π * u * t) : ℂ) := by
      simp [avaluesRemainderIntegrandFull, ht0]
    calc
      ‖avaluesRemainderIntegrandFull u t‖ =
          ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ *
            ‖(rexp (-π * u * t) : ℂ)‖ := by
              simp [hdef]
      _ ≤ ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ := by
              simpa [mul_one] using! (mul_le_of_le_one_right (norm_nonneg _) hExp_norm)
      _ ≤ K := hrem
  simpa [bound] using! hmul

/-!
### Global domination on `(0,∞)`
-/

/-- Combine the small/large bounds into a single integrable dominator on `(0,∞)`. -/
public theorem exists_integrable_bound_Ioi_zero :
    ∃ bound : ℝ → ℝ,
      IntegrableOn bound (Set.Ioi (0 : ℝ)) volume ∧
      (∀ᶠ u in 𝓝 (2 : ℝ), ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖avaluesRemainderIntegrandFull u t‖ ≤ bound t) := by
  rcases exists_integrable_bound_Ioc_zero_one with ⟨bound0, hbound0_int, hbound0⟩
  rcases exists_integrable_bound_Ici_one with ⟨bound1, hbound1_int, hbound1⟩
  -- Nonnegative dominator built from the two local dominators.
  let bound : ℝ → ℝ :=
    fun t : ℝ =>
      |(Set.Ioc (0 : ℝ) 1).indicator bound0 t| + |(Set.Ici (1 : ℝ)).indicator bound1 t|
  refine ⟨bound, ?_, ?_⟩
  · -- Integrability: absolute values preserve integrability, and we restrict to `Ioi 0`.
    -- Convert `IntegrableOn` assumptions to global integrability of indicators.
    have h0 : MeasureTheory.Integrable ((Set.Ioc (0 : ℝ) 1).indicator bound0) volume :=
      hbound0_int.integrable_indicator measurableSet_Ioc
    have h1 : MeasureTheory.Integrable ((Set.Ici (1 : ℝ)).indicator bound1) volume :=
      hbound1_int.integrable_indicator measurableSet_Ici
    have h0abs :
        MeasureTheory.Integrable (fun t : ℝ => |(Set.Ioc (0 : ℝ) 1).indicator bound0 t|) volume :=
      h0.abs
    have h1abs :
        MeasureTheory.Integrable (fun t : ℝ => |(Set.Ici (1 : ℝ)).indicator bound1 t|) volume :=
      h1.abs
    have habs_sum :
        MeasureTheory.Integrable
          (fun t : ℝ =>
            |(Set.Ioc (0 : ℝ) 1).indicator bound0 t| + |(Set.Ici (1 : ℝ)).indicator bound1 t|)
          volume :=
      h0abs.add h1abs
    -- Restrict to `Ioi 0`.
    exact Integrable.integrableOn habs_sum
  · -- Dominance on `Ioi 0`: combine the two AE bounds via the union decomposition.
    have hIoi_union : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) := by
      norm_num
    filter_upwards [hbound0, hbound1] with u hu0 hu1
    -- Reduce to `ae` bounds on the two pieces.
    have h0' :
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
          ‖avaluesRemainderIntegrandFull u t‖ ≤ bound t := by
      have hmem0 :
          ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
            t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa using!
          (ae_restrict_mem measurableSet_Ioc :
            ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
              t ∈ Set.Ioc (0 : ℝ) 1)
      filter_upwards [hu0, hmem0] with t ht htmem
      have hle_abs : bound0 t ≤ |bound0 t| := le_abs_self _
      have hle0 : 0 ≤ |(Set.Ici (1 : ℝ)).indicator bound1 t| := abs_nonneg _
      have hbound_ge :
          |bound0 t| ≤ bound t := by
        dsimp [bound]
        simp [Set.indicator_of_mem htmem]
      -- Combine.
      exact le_trans (le_trans ht hle_abs) hbound_ge
    have h1' :
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ici (1 : ℝ))),
          ‖avaluesRemainderIntegrandFull u t‖ ≤ bound t := by
      have hmem1 :
          ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ici (1 : ℝ))),
            t ∈ Set.Ici (1 : ℝ) := by
        simpa using!
          (ae_restrict_mem measurableSet_Ici :
            ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ici (1 : ℝ))),
              t ∈ Set.Ici (1 : ℝ))
      filter_upwards [hu1, hmem1] with t ht htmem
      have hle_abs : bound1 t ≤ |bound1 t| := le_abs_self _
      have hle0 : 0 ≤ |(Set.Ioc (0 : ℝ) 1).indicator bound0 t| := abs_nonneg _
      have hbound_ge :
          |bound1 t| ≤ bound t := by
        dsimp [bound]
        simp [Set.indicator_of_mem htmem]
      exact le_trans (le_trans ht hle_abs) hbound_ge
    -- Combine the two AE statements on the union.
    have hUnion :
        (∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
            ‖avaluesRemainderIntegrandFull u t‖ ≤ bound t) := by
      -- Rewrite `Ioi 0` as a union and use `ae_restrict_union_iff`.
      rw [hIoi_union]
      exact
        (MeasureTheory.ae_restrict_union_iff (μ := volume)
          (s := Set.Ioc (0 : ℝ) 1) (t := Set.Ici (1 : ℝ))
          (p := fun t : ℝ => ‖avaluesRemainderIntegrandFull u t‖ ≤ bound t)).2 ⟨h0', h1'⟩
    exact hUnion

end SpecialValuesDerivTwoLaurent

end
end SpherePacking.Dim24
