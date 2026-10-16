-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.CCancel
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Defs
public import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegralDefs
import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesConvergentRange
import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegral
import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderLargeBound
import SpherePacking.Dim24.MagicFunction.F.Laplace.TopologyDomains
import SpherePacking.Dim24.MagicFunction.F.ProfileComplex.B
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.ExpDecay
import SpherePacking.ForMathlib.IntegrablePowMulExp

/-!
# Proofs for the `eq:avalues` interface lemmas

This file proves the auxiliary identities used to bridge the paper's equation `eq:avalues`
between the convergent range `u > 4` and a right-neighborhood of `u = 2`.

## Main statements
* `fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_of_mem_Ioo_four_six`
* `fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_nhdsGT_two_impl`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology Complex UpperHalfPlane
open Filter Complex MeasureTheory Set

/-! ## Convergent-range (`u > 4`) identity for `aProfile` -/

theorem aProfile_eq_neg_I_mul_coeffExp_mul_pTildeProfile_add_remainderIntegral_of_lt
    {u : ℝ} (hu : 4 < u) :
    aProfile u =
      -(Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u) *
        (pTildeProfile u + avaluesRemainderIntegral u) := by
  have ha :
      aProfile u =
        -(Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u) *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            (if ht : 0 < t then
                (((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht)) * (Real.exp (-Real.pi * u * t) : ℂ)
              else 0)) :=
    aProfile_eq_neg_I_mul_coeffExp_mul_integral_pow_ten_varphi (u := u) hu
  have hsplit :
      (∫ t : ℝ in Set.Ioi (0 : ℝ),
          (if ht : 0 < t then
              (((t : ℂ) ^ (10 : ℕ)) * varphi (iOverT t ht)) * (Real.exp (-Real.pi * u * t) : ℂ)
            else 0)) =
        pTildeIntegral u + avaluesRemainderIntegral u :=
    integral_pow_ten_varphi_eq_pTildeIntegral_add_avaluesRemainderIntegral (u := u) hu
  have hpt : pTildeIntegral u = pTildeProfile u := pTildeIntegral_eq_pTildeProfile_of_lt (u := u) hu
  -- Rewrite the integral using `hsplit`, then replace `pTildeIntegral` by `pTildeProfile`.
  have ha' := ha
  -- `simp` can rewrite the exponential kernel; use `rw` for this bookkeeping step.
  rw [hsplit] at ha'
  simpa [hpt] using! ha'

/-! ## `coeffExp` non-vanishing on small intervals -/

lemma coeffExp_ne_zero_of_Ioo_two_three {u : ℝ} (hu2 : 2 < u) (hu3 : u < 3) :
    SpecialValuesDeriv.coeffExp u ≠ 0 := by
  intro h0
  have h0' : ((2 * Real.cos (Real.pi * u) - 2 : ℝ) : ℂ) = 0 := by
    simpa [SpecialValuesDeriv.coeffExp_eq_two_mul_cos_sub_two u] using! h0
  have h0'' : 2 * Real.cos (Real.pi * u) - 2 = 0 := by
    exact_mod_cast h0'
  have hcos : Real.cos (Real.pi * u) = 1 := by linarith
  rcases (Real.cos_eq_one_iff (Real.pi * u)).1 hcos with ⟨n, hn⟩
  have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have h2n : u = 2 * (n : ℝ) := by
    have h := congrArg (fun x : ℝ => x / Real.pi) hn
    -- `simp` gives `((n:ℝ)*2) = u`; swap and commute.
    have : (n : ℝ) * 2 = u := by
      simpa [hpi0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! h
    simpa [mul_comm] using! this.symm
  have hn_gt1r : (1 : ℝ) < (n : ℝ) := by nlinarith [hu2, h2n]
  have hn_gt1 : (1 : ℤ) < n := by exact_mod_cast hn_gt1r
  have hn_lt2r : (n : ℝ) < 2 := by nlinarith [hu3, h2n]
  have hn_lt2 : n < 2 := by exact_mod_cast hn_lt2r
  have hn_le1 : n ≤ 1 := (Int.lt_add_one_iff).1 (by simpa using! hn_lt2)
  have hn_ge2 : (2 : ℤ) ≤ n := by
    have : (1 : ℤ) + 1 ≤ n := (Int.add_one_le_iff).2 hn_gt1
    simpa using! this
  have : (2 : ℤ) ≤ 1 := le_trans hn_ge2 hn_le1
  exact (by decide : ¬ (2 : ℤ) ≤ 1) this

lemma coeffExp_ne_zero_of_Ioo_four_six {u : ℝ} (hu4 : 4 < u) (hu6 : u < 6) :
    SpecialValuesDeriv.coeffExp u ≠ 0 := by
  intro h0
  have h0' : ((2 * Real.cos (Real.pi * u) - 2 : ℝ) : ℂ) = 0 := by
    simpa [SpecialValuesDeriv.coeffExp_eq_two_mul_cos_sub_two u] using! h0
  have h0'' : 2 * Real.cos (Real.pi * u) - 2 = 0 := by
    exact_mod_cast h0'
  have hcos : Real.cos (Real.pi * u) = 1 := by linarith
  rcases (Real.cos_eq_one_iff (Real.pi * u)).1 hcos with ⟨n, hn⟩
  have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have h2n : u = 2 * (n : ℝ) := by
    have h := congrArg (fun x : ℝ => x / Real.pi) hn
    have : (n : ℝ) * 2 = u := by
      simpa [hpi0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! h
    simpa [mul_comm] using! this.symm
  have hn_gt2r : (2 : ℝ) < (n : ℝ) := by nlinarith [hu4, h2n]
  have hn_gt2 : (2 : ℤ) < n := by exact_mod_cast hn_gt2r
  have hn_lt3r : (n : ℝ) < 3 := by nlinarith [hu6, h2n]
  have hn_lt3 : n < 3 := by exact_mod_cast hn_lt3r
  have hn_le2 : n ≤ 2 := (Int.lt_add_one_iff).1 (by simpa using! hn_lt3)
  have hn_ge3 : (3 : ℤ) ≤ n := by
    have : (2 : ℤ) + 1 ≤ n := (Int.add_one_le_iff).2 hn_gt2
    simpa using! this
  have : (3 : ℤ) ≤ 2 := le_trans hn_ge3 hn_le2
  exact (by decide : ¬ (3 : ℤ) ≤ 2) this

/-! ## Convergent-range identity for `fProfile` on `(4,6)` -/

/-- Convergent-range (`u ∈ (4,6)`) form of `eq:avalues`, rewritten for `fProfile`. -/
public theorem fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_of_mem_Ioo_four_six
    {u : ℝ} (hu : u ∈ Set.Ioo (4 : ℝ) 6) :
    fProfile u = -pTildeProfile u - coeffConstTerm u - avaluesRemainderIntegral u := by
  have hu4 : 4 < u := hu.1
  have hu6 : u < 6 := hu.2
  have hcoeff : SpecialValuesDeriv.coeffExp u ≠ 0 :=
    coeffExp_ne_zero_of_Ioo_four_six (u := u) hu4 hu6
  have hden0 : (Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u ≠ 0 := mul_ne_zero (by simp) hcoeff
  have ha :
      aProfile u =
        -(Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u) *
          (pTildeProfile u + avaluesRemainderIntegral u) :=
    aProfile_eq_neg_I_mul_coeffExp_mul_pTildeProfile_add_remainderIntegral_of_lt (u := u) hu4
  -- Pure algebra: `fProfile + coeffConstTerm = aProfile / (I*coeffExp)`.
  have hsum :
      fProfile u + coeffConstTerm u =
        aProfile u / ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u) := by
    set den : ℂ := (Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u
    calc
      fProfile u + coeffConstTerm u =
          (aProfile u - constA2_av) / den + constA2_av / den := by
            simp [fProfile, coeffConstTerm, den]
      _ = ((aProfile u - constA2_av) + constA2_av) / den := by
            simpa [add_div] using! (add_div (aProfile u - constA2_av) constA2_av den).symm
      _ = aProfile u / den := by
            simp [sub_eq_add_neg, den, add_assoc]
  have hmain :
      fProfile u + coeffConstTerm u = -(pTildeProfile u + avaluesRemainderIntegral u) := by
    rw [hsum, ha]
    field_simp [hden0]
  have hsub := congrArg (fun z : ℂ => z - coeffConstTerm u) hmain
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hsub

/-! ## Analytic continuation down to `(2,3)` -/

def coeffExpC (u : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * u * Complex.I) +
      Complex.exp (-((Real.pi : ℂ) * u * Complex.I)) - (2 : ℂ)

lemma coeffExpC_ofReal (u : ℝ) : coeffExpC (u : ℂ) = SpecialValuesDeriv.coeffExp u := by
  simp [coeffExpC, SpecialValuesDeriv.coeffExp, mul_comm, sub_eq_add_neg]

def pTildeProfileC (u : ℂ) : ℂ :=
  ((-864 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (u - 4) +
    ((725760 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 2) ^ (2 : ℕ)) +
      ((-2218752 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (u - 2) +
        ((113218560 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (u ^ (2 : ℕ)) +
          ((-223140096 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / u

lemma pTildeProfileC_ofReal (u : ℝ) : pTildeProfileC (u : ℂ) = pTildeProfile u := by
  simp [pTildeProfileC, pTildeProfile, sub_eq_add_neg, add_assoc]

def avaluesRemainderIntegralC (u : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioi (0 : ℝ),
    (if ht : 0 < t then
        ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) - pPaper t) *
          Complex.exp (-(π : ℂ) * u * (t : ℂ))
      else 0)

lemma avaluesRemainderIntegralC_ofReal (u : ℝ) :
    avaluesRemainderIntegralC (u : ℂ) = avaluesRemainderIntegral u := by
  simp [avaluesRemainderIntegralC, avaluesRemainderIntegral, avaluesRemainderIntegrandFull]

def aProfileRhsC (u : ℂ) : ℂ :=
  -(Complex.I : ℂ) * coeffExpC u * (pTildeProfileC u + avaluesRemainderIntegralC u)

lemma aProfileRhsC_ofReal (u : ℝ) :
    aProfileRhsC (u : ℂ) =
      -(Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u) *
        (pTildeProfile u + avaluesRemainderIntegral u) := by
  simp [aProfileRhsC, coeffExpC_ofReal, pTildeProfileC_ofReal, avaluesRemainderIntegralC_ofReal,
    mul_assoc]

def domainTwoMinusFour : Set ℂ := LaplaceDomains.domainTwo \ {4}

lemma domainTwoMinusFour_isPreconnected : IsPreconnected domainTwoMinusFour := by
  -- Translate `domainPosNeTwo` by `+2` to get `domainTwo \ {4}`.
  have hpre : IsPreconnected LaplaceDomains.domainPosNeTwo :=
    LaplaceDomains.domainPosNeTwo_isPreconnected
  have hcont : Continuous fun z : ℂ => z + (2 : ℂ) := by
    simpa using! (continuous_id.add continuous_const)
  have himage :
      (fun z : ℂ => z + (2 : ℂ)) '' LaplaceDomains.domainPosNeTwo = domainTwoMinusFour := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, ?_⟩
      · -- `2 < (w+2).re`.
        have hwRe : 0 < w.re := by simpa [LaplaceDomains.domainPosNeTwo] using! hw.1
        have : 2 < (w + (2 : ℂ)).re := by
          -- `w.re + 2 > 2` since `w.re > 0`.
          simpa [Complex.add_re] using! (lt_add_of_pos_left 2 hwRe)
        simpa [LaplaceDomains.domainTwo] using! this
      · -- `w + 2 ≠ 4` since `w ≠ 2`.
        intro hz
        have hw2 : w = (2 : ℂ) := by
          have hz' := congrArg (fun x : ℂ => x - (2 : ℂ)) hz
          have hw2' : w = (-2 : ℂ) + 4 := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hz'
          have h24 : (-2 : ℂ) + 4 = (2 : ℂ) := by norm_num
          simpa [h24] using! hw2'
        have hwne : w ≠ (2 : ℂ) := by simpa [LaplaceDomains.domainPosNeTwo] using! hw.2
        exact hwne hw2
    · intro hz
      -- Preimage point `w = z - 2`.
      refine ⟨z - (2 : ℂ), ?_, by simp [sub_eq_add_neg, add_left_comm, add_comm]⟩
      refine ⟨?_, ?_⟩
      · -- `0 < (z-2).re`.
        have hzRe : 2 < z.re := by simpa [domainTwoMinusFour, LaplaceDomains.domainTwo] using! hz.1
        have : 0 < (z.re - 2) := sub_pos.2 hzRe
        simpa [SpherePacking.rightHalfPlane, Complex.sub_re] using! this
      · -- `z-2 ≠ 2` since `z ≠ 4`.
        intro hw
        have hz4 : z = (4 : ℂ) := by
          have hw' := congrArg (fun x : ℂ => x + (2 : ℂ)) hw
          have hz4' : z = (2 : ℂ) + 2 := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hw'
          have h22 : (2 : ℂ) + 2 = (4 : ℂ) := by norm_num
          simpa [h22] using! hz4'
        exact hz.2 hz4
  -- Conclude by preservation of preconnectedness under continuous images.
  have : IsPreconnected ((fun z : ℂ => z + (2 : ℂ)) '' LaplaceDomains.domainPosNeTwo) :=
    hpre.image (f := fun z : ℂ => z + (2 : ℂ)) hcont.continuousOn
  simpa [himage] using! this

/-! ### Analyticity of the remainder integral on `Re u > 2` -/

def avaluesRemainderIntegrandC (u : ℂ) (t : ℝ) : ℂ :=
  if ht : 0 < t then
      ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) - pPaper t) * Complex.exp (-(π : ℂ) * u * (t : ℂ))
    else 0

lemma avaluesRemainderIntegralC_eq_integral_integrandC (u : ℂ) :
    avaluesRemainderIntegralC u =
      ∫ t : ℝ in Set.Ioi (0 : ℝ), avaluesRemainderIntegrandC u t := by
  simp [avaluesRemainderIntegralC, avaluesRemainderIntegrandC]

def avaluesRemainderIntegrandCDeriv (u : ℂ) (t : ℝ) : ℂ :=
  avaluesRemainderIntegrandC u t * (-(π : ℂ) * (t : ℂ))

lemma hasDerivAt_avaluesRemainderIntegrandC (u : ℂ) (t : ℝ) :
    HasDerivAt
      (fun u : ℂ => avaluesRemainderIntegrandC u t)
      (avaluesRemainderIntegrandCDeriv u t) u := by
  by_cases ht : 0 < t
  · -- On `t>0`, the integrand is a constant factor times `exp (-(π)*u*t)`.
    have hconst :
        HasDerivAt (fun u : ℂ => Complex.exp (-(π : ℂ) * u * (t : ℂ)))
          ((-(π : ℂ) * (t : ℂ)) * Complex.exp (-(π : ℂ) * u * (t : ℂ))) u := by
      -- Write `exp (c*u)` with `c = -(π)*t`.
      let c : ℂ := -(π : ℂ) * (t : ℂ)
      let g : ℂ → ℂ := fun u : ℂ => c * u
      have hg : HasDerivAt g c u := by
        simpa [g] using! (hasDerivAt_id u).const_mul c
      have hexp : HasDerivAt (fun u : ℂ => Complex.exp (g u)) (Complex.exp (g u) * c) u :=
        (Complex.hasDerivAt_exp (g u)).comp u hg
      -- Commute factors to match the target shape.
      simpa [g, c, mul_assoc, mul_left_comm, mul_comm] using! hexp
    -- Multiply by the `t`-dependent prefactor.
    let K : ℂ := ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) - pPaper t)
    have hK :
        HasDerivAt (fun u : ℂ => K * Complex.exp (-(π : ℂ) * u * (t : ℂ)))
          (K * ((-(π : ℂ) * (t : ℂ)) * Complex.exp (-(π : ℂ) * u * (t : ℂ)))) u :=
      hconst.const_mul K
    -- Unfold `avaluesRemainderIntegrandC` and rewrite the derivative target.
    simpa
        [ avaluesRemainderIntegrandC
        , avaluesRemainderIntegrandCDeriv
        , ht
        , K
        , mul_assoc
        , mul_left_comm
        , mul_comm
        ]
      using! hK
  · -- If `t ≤ 0`, the integrand is identically `0`.
    simpa [avaluesRemainderIntegrandC, avaluesRemainderIntegrandCDeriv, ht] using!
      (hasDerivAt_const u (0 : ℂ))

lemma aestronglyMeasurable_avaluesRemainderIntegrandC (u : ℂ) :
    MeasureTheory.AEStronglyMeasurable (avaluesRemainderIntegrandC u)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hpPaper : Continuous pPaper := by
    unfold pPaper
    fun_prop
  let s : Set ℝ := Set.Ioi (0 : ℝ)
  have hs : MeasurableSet s := isOpen_Ioi.measurableSet
  let f : s → ℂ := fun p =>
    (((p.1 : ℝ) : ℂ) ^ (10 : ℕ) * varphi (iOverT p.1 (by exact p.2)) - pPaper p.1) *
      Complex.exp (-(π : ℂ) * u * ((p.1 : ℝ) : ℂ))
  have hf_cont : Continuous f := by
    have hvarphi : Continuous (varphi : ℍ → ℂ) := varphi_holo'.continuous
    have hio : Continuous fun p : s => (iOverT p.1 ( p.2) : ℍ) := by
      -- This is `continuous_iOverT_pos` with a definitional identification of the domain.
      simpa [s] using! (continuous_iOverT_pos :
        Continuous fun p : {t : ℝ // 0 < t} => (iOverT p.1 p.2 : ℍ))
    have ht10 : Continuous fun p : s => ((p.1 : ℝ) : ℂ) ^ (10 : ℕ) := by fun_prop
    have hpp : Continuous fun p : s => pPaper (p.1 : ℝ) := hpPaper.comp continuous_subtype_val
    have hexp : Continuous fun p : s =>
        Complex.exp (-(π : ℂ) * u * ((p.1 : ℝ) : ℂ)) := by
      fun_prop
    have hterm : Continuous fun p : s =>
        ((p.1 : ℝ) : ℂ) ^ (10 : ℕ) * varphi (iOverT p.1 ( p.2)) := by
      simpa [mul_assoc] using! ht10.mul (hvarphi.comp hio)
    have hsub : Continuous fun p : s =>
        ((p.1 : ℝ) : ℂ) ^ (10 : ℕ) * varphi (iOverT p.1 ( p.2)) - pPaper p.1 := by
      simpa [sub_eq_add_neg] using! hterm.add (continuous_neg.comp hpp)
    exact Continuous.fun_mul hsub hexp
  have hf : Measurable f := hf_cont.measurable
  have hg : Measurable (fun _t : (sᶜ : Set ℝ) => (0 : ℂ)) := measurable_const
  have hmeas : Measurable fun t : ℝ => if ht : t ∈ s then f ⟨t, ht⟩ else (0 : ℂ) :=
    (Measurable.dite (s := s) hf hg hs)
  have hEq :
      (fun t : ℝ => if ht : t ∈ s then f ⟨t, ht⟩ else (0 : ℂ)) = avaluesRemainderIntegrandC u := by
    rfl
  have hAES :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => if ht : t ∈ s then f ⟨t, ht⟩ else (0 : ℂ))
        (MeasureTheory.volume.restrict s) :=
    hmeas.aestronglyMeasurable
  simpa [hEq, s] using! hAES

lemma exists_bound_diff_Ioc_zero_one :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ∀ ht : 0 < t, t ≤ 1 →
        ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) - pPaper t‖ ≤ C := by
  -- Uniform bound for `varphi` on the imaginary axis for `s ≥ 1`.
  rcases Dim24.VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨C0, hC0⟩
  let Cφ : ℝ := max C0 0
  have hCφnonneg : 0 ≤ Cφ := le_max_right _ _
  have hvarphi_le : ∀ s : ℝ, 1 ≤ s → ‖varphi.resToImagAxis s‖ ≤ Cφ := by
    intro s hs
    have h := hC0 s hs
    have hexp_le : Real.exp (-(2 * Real.pi) * s) ≤ 1 := by
      -- `exp` is ≤ 1 on nonpositive arguments.
      have hs0 : 0 ≤ s := le_trans (by norm_num) hs
      have hmul : 0 ≤ (2 * Real.pi) * s := mul_nonneg (by positivity) hs0
      have : (-(2 * Real.pi) * s) ≤ 0 := by nlinarith
      simpa using! (Real.exp_le_one_iff.2 this)
    have hmul : C0 * Real.exp (-(2 * Real.pi) * s) ≤ Cφ := by
      have : C0 * Real.exp (-(2 * Real.pi) * s) ≤ Cφ * Real.exp (-(2 * Real.pi) * s) :=
        mul_le_mul_of_nonneg_right (le_max_left C0 0) (by positivity)
      nlinarith
    exact le_trans h hmul
  -- Bound `pPaper` on the compact interval `[0,1]`.
  have hpPaper : Continuous pPaper := by
    unfold pPaper
    fun_prop
  have hcomp : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hnonempty : (Set.Icc (0 : ℝ) 1).Nonempty := by
    refine ⟨0, ?_⟩
    simp
  have hcont : ContinuousOn (fun t : ℝ => ‖pPaper t‖) (Set.Icc (0 : ℝ) 1) :=
    (continuous_norm.comp hpPaper).continuousOn
  rcases hcomp.exists_isMaxOn hnonempty hcont with ⟨t0, ht0, ht0max⟩
  let Mp : ℝ := ‖pPaper t0‖
  have hMp : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖pPaper t‖ ≤ Mp := by
    intro t ht
    exact ht0max ht
  -- Assemble the bound.
  let C : ℝ := Cφ + Mp
  have hCnonneg : 0 ≤ C := by nlinarith [hCφnonneg, norm_nonneg (pPaper t0)]
  refine ⟨C, hCnonneg, ?_⟩
  intro t ht ht1
  have ht0le : (0 : ℝ) ≤ t := le_of_lt ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0le, ht1⟩
  have hs : (1 : ℝ) ≤ 1 / t := by
    -- `t ≤ 1` and `t > 0` implies `1 ≤ 1/t` by order-reversing of `x ↦ 1/x` on `0 < x`.
    simpa [one_div] using! (one_div_le_one_div_of_le ht ht1)
  have hvarphi :
      ‖varphi (iOverT t ht)‖ ≤ Cφ := by
    -- `iOverT t = it (1/t)` and `resToImagAxis` is `it`.
    have : varphi (iOverT t ht) = varphi.resToImagAxis (1 / t) := by
      simp [Dim24.iOverT, Dim24.it, Function.resToImagAxis, ResToImagAxis, ht]
    simpa [this] using! hvarphi_le (1 / t) hs
  have hpow : ‖(t : ℂ) ^ (10 : ℕ)‖ ≤ (1 : ℝ) := by
    -- `‖(t:ℂ)^10‖ = |t|^10 ≤ 1` for `0 < t ≤ 1`.
    have htabs : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, abs_of_pos ht] using! ht1
    simpa [norm_pow] using! pow_le_pow_left₀ (norm_nonneg (t : ℂ)) htabs 10
  have hterm :
      ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)‖ ≤ Cφ := by
    calc
      ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht)‖ =
          ‖(t : ℂ) ^ (10 : ℕ)‖ * ‖varphi (iOverT t ht)‖ :=
            norm_mul ((t : ℂ) ^ (10 : ℕ)) (varphi (iOverT t ht))
      _ ≤ 1 * Cφ := by gcongr
      _ = Cφ := by simp
  exact norm_sub_le_of_le hterm (hMp t htIcc)

lemma analyticOnNhd_avaluesRemainderIntegralC_domainTwo :
    AnalyticOnNhd ℂ avaluesRemainderIntegralC LaplaceDomains.domainTwo := by
  have hopen : IsOpen LaplaceDomains.domainTwo := by
    simpa [LaplaceDomains.domainTwo] using! isOpen_lt continuous_const Complex.continuous_re
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hmeasF (u : ℂ) : AEStronglyMeasurable (avaluesRemainderIntegrandC u) μ := by
    simpa [μ] using! aestronglyMeasurable_avaluesRemainderIntegrandC (u := u)
  have hmeasF' (u : ℂ) : AEStronglyMeasurable (avaluesRemainderIntegrandCDeriv u) μ := by
    have hm : AEStronglyMeasurable (fun t : ℝ => (-(π : ℂ) * (t : ℂ))) μ := by
      have hcont : Continuous fun t : ℝ => (-(π : ℂ) * (t : ℂ)) := by fun_prop
      exact hcont.aestronglyMeasurable
    have hmul :
        AEStronglyMeasurable
          (fun t : ℝ => avaluesRemainderIntegrandC u t * (-(π : ℂ) * (t : ℂ))) μ :=
      (hmeasF u).mul hm
    assumption
  have hdiff : DifferentiableOn ℂ avaluesRemainderIntegralC LaplaceDomains.domainTwo := by
    intro u0 hu0
    have hu0' : 2 < u0.re := hu0
    let ε : ℝ := (u0.re - 2) / 2
    have hεpos : 0 < ε := by
      dsimp [ε]
      nlinarith [hu0']
    let m : ℝ := u0.re - ε
    have hm2 : 2 < m := by
      grind only
    have hre_lower : ∀ u ∈ Metric.ball u0 ε, m < u.re := by
      intro u hu
      have hnorm : ‖u - u0‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using! hu
      have hle : |u.re - u0.re| ≤ ‖u - u0‖ := by
        simpa [Complex.sub_re] using! (Complex.abs_re_le_norm (u - u0))
      have hlt : |u.re - u0.re| < ε := lt_of_le_of_lt hle hnorm
      have : u0.re - ε < u.re := by nlinarith [(abs_lt.1 hlt).1]
      simpa [m] using! this
    rcases exists_bound_diff_Ioc_zero_one with ⟨Csmall, hCsmall0, hCsmall⟩
    rcases exists_bound_remainder_large_proof with ⟨Clarge, hClarge0, hClarge⟩
    let diffBound : ℝ → ℝ :=
      fun t : ℝ => Csmall + Clarge * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t)
    have hdiffBound :
        ∀ t : ℝ, ∀ ht : 0 < t,
          ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) - pPaper t‖ ≤ diffBound t := by
      intro t ht
      by_cases ht1 : t ≤ 1
      · have h := hCsmall t ht ht1
        have hnonneg : 0 ≤ Clarge * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by positivity
        exact le_add_of_le_of_nonneg (hCsmall t ht ht1) hnonneg
      · have ht1' : 1 ≤ t := le_of_not_ge ht1
        exact le_add_of_nonneg_of_le hCsmall0 (hClarge t ht1' ht)
    have hexp_bound :
        ∀ u ∈ Metric.ball u0 ε, ∀ t : ℝ, 0 < t →
          ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ Real.exp (-Real.pi * m * t) := by
      intro u hu t ht0
      have hre : m ≤ u.re := le_of_lt (hre_lower u hu)
      have hRe :
          (-(π : ℂ) * u * (t : ℂ)).re = -Real.pi * u.re * t := by
        simp [Complex.mul_re, Complex.mul_im, mul_left_comm, mul_comm]
      have hn :
          ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ = Real.exp (-Real.pi * u.re * t) := by
        rw [Complex.norm_exp, hRe]
      have hmul : Real.pi * m * t ≤ Real.pi * u.re * t := by
        have hpi : 0 ≤ (Real.pi : ℝ) := Real.pi_pos.le
        have : Real.pi * m ≤ Real.pi * u.re := mul_le_mul_of_nonneg_left hre hpi
        exact mul_le_mul_of_nonneg_right this ht0.le
      have hneg : -Real.pi * u.re * t ≤ -Real.pi * m * t := by nlinarith [hmul]
      have hmono : Real.exp (-Real.pi * u.re * t) ≤ Real.exp (-Real.pi * m * t) :=
        Real.exp_le_exp.2 hneg
      rw [hn]
      exact hmono
    let b : ℝ := 2 * Real.pi + Real.pi * m
    have hb : 0 < b := by nlinarith [Real.pi_pos, hm2]
    have hexp_int : Integrable (fun t : ℝ => Real.exp (-Real.pi * m * t)) μ := by
      have : IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * m * t)) (Set.Ioi (0 : ℝ)) volume := by
        simpa [mul_assoc] using!
          (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) (b := Real.pi * m)
            (by positivity [Real.pi_pos, hm2]))
      simpa [MeasureTheory.IntegrableOn, μ] using! this
    have hpoly_int :
        Integrable (fun t : ℝ => (t ^ (2 : ℕ)) * Real.exp (-b * t)) μ := by
      have :
          IntegrableOn (fun t : ℝ => (t ^ (2 : ℕ)) * Real.exp (-b * t)) (Set.Ioi (0 : ℝ))
            volume := by
        simpa using!
          (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ioi (n := 2) (b := b) hb)
      simpa [MeasureTheory.IntegrableOn, μ] using! this
    have hboundF_int : Integrable (fun t : ℝ => diffBound t * Real.exp (-Real.pi * m * t)) μ := by
      have h0 : Integrable (fun t : ℝ => Csmall * Real.exp (-Real.pi * m * t)) μ :=
        hexp_int.const_mul Csmall
      have h1a : Integrable (fun t : ℝ => Clarge * ((t ^ (2 : ℕ)) * Real.exp (-b * t))) μ := by
        simpa [mul_assoc] using! (hpoly_int.const_mul Clarge)
      have h1 :
          Integrable (fun t : ℝ =>
            Clarge * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) *
              Real.exp (-Real.pi * m * t)) μ := by
        have hexp_mul :
            (fun t : ℝ => Clarge * ((t ^ (2 : ℕ)) * Real.exp (-b * t))) =ᵐ[μ]
              fun t : ℝ => Clarge * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) *
                Real.exp (-Real.pi * m * t) := by
          refine (ae_of_all _ ?_)
          intro t
          have h' :
              Real.exp (-b * t) =
                Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * m * t) := by
            have hab : (-b * t) = (-(2 * Real.pi) * t) + (-Real.pi * m * t) := by
              dsimp [b]
              ring
            calc
              Real.exp (-b * t) = Real.exp ((-(2 * Real.pi) * t) + (-Real.pi * m * t)) := by
                simp [hab]
              _ = Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * m * t) := by
                simpa using! Real.exp_add (-(2 * Real.pi) * t) (-Real.pi * m * t)
          calc
            Clarge * ((t ^ (2 : ℕ)) * Real.exp (-b * t)) =
                (Clarge * (t ^ (2 : ℕ))) * Real.exp (-b * t) := by ring
            _ = (Clarge * (t ^ (2 : ℕ))) *
                  (Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * m * t)) := by
                rw [h']
            _ =
                Clarge * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) *
                  Real.exp (-Real.pi * m * t) := by
              ring
        exact h1a.congr hexp_mul
      have hsum_int :
          Integrable
            (fun t : ℝ =>
              Csmall * Real.exp (-Real.pi * m * t) +
                Clarge * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) *
                  Real.exp (-Real.pi * m * t)) μ :=
        h0.add h1
      grind only
    have hF_int : Integrable (avaluesRemainderIntegrandC u0) μ := by
      refine Integrable.mono' hboundF_int (hmeasF u0) ?_
      refine (ae_restrict_mem (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).mono ?_
      intro t ht0
      have htpos : 0 < t := by simpa [Set.mem_Ioi] using! ht0
      have hdiff := hdiffBound t htpos
      have hexp := hexp_bound u0 (Metric.mem_ball_self hεpos) t htpos
      have hnorm :
          ‖avaluesRemainderIntegrandC u0 t‖ ≤ diffBound t * Real.exp (-Real.pi * m * t) := by
        have hdiffBound_nonneg : 0 ≤ diffBound t := by
          dsimp [diffBound]
          exact add_nonneg hCsmall0 (by positivity [hClarge0])
        have hnorm_eq :
            ‖avaluesRemainderIntegrandC u0 t‖ =
              ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t htpos) - pPaper t‖ *
                ‖Complex.exp (-(π : ℂ) * (u0 : ℂ) * (t : ℂ))‖ := by
          simp [avaluesRemainderIntegrandC, htpos, mul_assoc]
        have hmul :
            ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t htpos) - pPaper t‖ *
                ‖Complex.exp (-(π : ℂ) * (u0 : ℂ) * (t : ℂ))‖ ≤
              diffBound t * Real.exp (-Real.pi * m * t) := by
          refine mul_le_mul hdiff hexp (by positivity) hdiffBound_nonneg
        simpa [hnorm_eq] using! hmul
      exact hnorm
    let bound : ℝ → ℝ := fun t : ℝ => Real.pi * |t| * diffBound t * Real.exp (-Real.pi * m * t)
    have hbound_int : Integrable bound μ := by
      let bound' : ℝ → ℝ := fun t : ℝ => Real.pi * t * diffBound t * Real.exp (-Real.pi * m * t)
      have hboundEq : bound =ᵐ[μ] bound' := by
        refine (ae_restrict_mem (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).mono ?_
        grind only [= mem_Ioi, = abs.eq_1, = max_def]
      have hpoly1_int : Integrable (fun t : ℝ => t * Real.exp (-Real.pi * m * t)) μ := by
        have :
            IntegrableOn (fun t : ℝ => (t ^ (1 : ℕ)) * Real.exp (-(Real.pi * m) * t))
              (Set.Ioi (0 : ℝ)) volume := by
          have hb' : 0 < Real.pi * m := by positivity [Real.pi_pos, hm2]
          exact ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ioi 1 hb'
        have :
            IntegrableOn (fun t : ℝ => t * Real.exp (-Real.pi * m * t)) (Set.Ioi (0 : ℝ))
              volume := by
          simpa [pow_one] using! this
        simpa [MeasureTheory.IntegrableOn, μ] using! this
      have hpoly3_int : Integrable (fun t : ℝ => (t ^ (3 : ℕ)) * Real.exp (-b * t)) μ := by
        have :
            IntegrableOn (fun t : ℝ => (t ^ (3 : ℕ)) * Real.exp (-b * t)) (Set.Ioi (0 : ℝ))
              volume := by
          simpa using!
            (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ioi (n := 3) (b := b) hb)
        simpa [MeasureTheory.IntegrableOn, μ] using! this
      have h0 :
          Integrable
            (fun t : ℝ => (Real.pi * Csmall) * (t * Real.exp (-Real.pi * m * t))) μ := by
        simpa [mul_assoc] using! (hpoly1_int.const_mul (Real.pi * Csmall))
      have h1a :
          Integrable
            (fun t : ℝ => (Real.pi * Clarge) * ((t ^ (3 : ℕ)) * Real.exp (-b * t))) μ := by
        simpa [mul_assoc] using! (hpoly3_int.const_mul (Real.pi * Clarge))
      have h1 :
          Integrable (fun t : ℝ =>
            (Real.pi * Clarge) *
              ((t ^ (3 : ℕ)) * Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * m * t))) μ := by
        have hexp_mul :
            (fun t : ℝ => (Real.pi * Clarge) * ((t ^ (3 : ℕ)) * Real.exp (-b * t))) =ᵐ[μ]
              fun t : ℝ => (Real.pi * Clarge) *
                ((t ^ (3 : ℕ)) * Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * m * t)) := by
          refine (ae_of_all _ ?_)
          intro t
          have h' :
              Real.exp (-b * t) =
                Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * m * t) := by
            have hab : (-b * t) = (-(2 * Real.pi) * t) + (-Real.pi * m * t) := by
              dsimp [b]
              ring
            calc
              Real.exp (-b * t) = Real.exp ((-(2 * Real.pi) * t) + (-Real.pi * m * t)) := by
                simp [hab]
              _ = Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * m * t) := by
                simpa using! Real.exp_add (-(2 * Real.pi) * t) (-Real.pi * m * t)
          calc
            (Real.pi * Clarge) * ((t ^ (3 : ℕ)) * Real.exp (-b * t)) =
                ((Real.pi * Clarge) * (t ^ (3 : ℕ))) * Real.exp (-b * t) := by ring
            _ = ((Real.pi * Clarge) * (t ^ (3 : ℕ))) *
                  (Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * m * t)) := by
                rw [h']
            _ =
                (Real.pi * Clarge) *
                  ((t ^ (3 : ℕ)) * Real.exp (-(2 * Real.pi) * t) *
                    Real.exp (-Real.pi * m * t)) := by
                ring
        exact h1a.congr hexp_mul
      have hEq :
          bound' = fun t : ℝ =>
            (Real.pi * Csmall) * (t * Real.exp (-Real.pi * m * t)) +
              (Real.pi * Clarge) *
                ((t ^ (3 : ℕ)) * Real.exp (-(2 * Real.pi) * t) * Real.exp (-Real.pi * m * t)) := by
        funext t
        dsimp [bound', diffBound]
        ring
      have hbound'_int : Integrable bound' μ := by simpa [hEq] using! h0.add h1
      exact (hbound'_int.congr hboundEq.symm)
    have hbound :
        ∀ᵐ t : ℝ ∂μ, ∀ u ∈ Metric.ball u0 ε, ‖avaluesRemainderIntegrandCDeriv u t‖ ≤ bound t := by
      refine (ae_restrict_mem (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).mono ?_
      intro t ht0 u hu
      have htpos : 0 < t := by simpa [Set.mem_Ioi] using! ht0
      have hdiff := hdiffBound t htpos
      have hexp := hexp_bound u hu t htpos
      have habs : |t| = t := abs_of_pos htpos
      have hdiffBound_nonneg : 0 ≤ diffBound t := by
        dsimp [diffBound]
        exact add_nonneg hCsmall0 (by positivity [hClarge0])
      have hbase :
          ‖avaluesRemainderIntegrandC u t‖ ≤ diffBound t * Real.exp (-Real.pi * m * t) := by
        have hnorm_eq :
            ‖avaluesRemainderIntegrandC u t‖ =
              ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t htpos) - pPaper t‖ *
                ‖Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))‖ := by
          simp [avaluesRemainderIntegrandC, htpos, mul_assoc]
        have hmul :
            ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t htpos) - pPaper t‖ *
                ‖Complex.exp (-(π : ℂ) * (u : ℂ) * (t : ℂ))‖ ≤
              diffBound t * Real.exp (-Real.pi * m * t) := by
          refine mul_le_mul hdiff hexp (by positivity) hdiffBound_nonneg
        simpa [hnorm_eq] using! hmul
      have hnπt : ‖(-(π : ℂ) * (t : ℂ))‖ = Real.pi * |t| := by
        simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
      have hmult :
          ‖avaluesRemainderIntegrandCDeriv u t‖ ≤
            Real.pi * |t| * (diffBound t * Real.exp (-Real.pi * m * t)) := by
        -- `‖F * (-(π*t))‖ = ‖F‖ * ‖-(π*t)‖`.
        have hnorm :
            ‖avaluesRemainderIntegrandCDeriv u t‖ =
              ‖avaluesRemainderIntegrandC u t‖ * ‖(-(π : ℂ) * (t : ℂ))‖ := by
          simp [avaluesRemainderIntegrandCDeriv]
        -- Apply `mul_le_mul` to the bound on `‖F‖`.
        have hmul :
            ‖avaluesRemainderIntegrandC u t‖ * ‖(-(π : ℂ) * (t : ℂ))‖ ≤
              (diffBound t * Real.exp (-Real.pi * m * t)) * (Real.pi * |t|) := by
          -- Rewrite the norm of `-(π*t)`.
          rw [hnπt]
          refine mul_le_mul hbase (le_rfl) (by positivity) ?_
          -- `0 ≤ diffBound t * exp(...)`.
          exact mul_nonneg hdiffBound_nonneg (by positivity)
        -- Rearrange the RHS.
        rw [hnorm]
        linarith [hmul]
      have hbnd : Real.pi * |t| * (diffBound t * Real.exp (-Real.pi * m * t)) = bound t := by
        dsimp [bound]
        ring
      exact le_trans hmult (le_of_eq hbnd)
    have hdiff_ae :
        ∀ᵐ t : ℝ ∂μ, ∀ u ∈ Metric.ball u0 ε,
          HasDerivAt
            (fun u : ℂ => avaluesRemainderIntegrandC u t)
            (avaluesRemainderIntegrandCDeriv u t) u := by
      refine ae_of_all _ ?_
      intro t u hu
      exact hasDerivAt_avaluesRemainderIntegrandC u t
    have hF_meas : ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (avaluesRemainderIntegrandC u) μ :=
      Filter.Eventually.of_forall hmeasF
    have hF'_meas : AEStronglyMeasurable (avaluesRemainderIntegrandCDeriv u0) μ := hmeasF' u0
    have hderiv :
        HasDerivAt (fun u : ℂ => ∫ t, avaluesRemainderIntegrandC u t ∂μ)
          (∫ t, avaluesRemainderIntegrandCDeriv u0 t ∂μ) u0 := by
      exact
        ProfileComplex.hasDerivAt_integral_of_dominated_ball hεpos hF_meas hF_int (hmeasF' u0)
          hbound hbound_int hdiff_ae
    have hEq :
        (fun u : ℂ => ∫ t, avaluesRemainderIntegrandC u t ∂μ) = avaluesRemainderIntegralC := by
      funext u
      simp [μ, avaluesRemainderIntegralC_eq_integral_integrandC]
    have hD :
        DifferentiableAt ℂ (fun u : ℂ => ∫ t, avaluesRemainderIntegrandC u t ∂μ) u0 :=
      hderiv.differentiableAt
    simpa [hEq] using! hD.differentiableWithinAt
  exact (Complex.analyticOnNhd_iff_differentiableOn hopen).2 hdiff

/-! ## Analytic continuation: extend the identity down to `𝓝[>] 2` -/

lemma analyticOnNhd_aPrimeC_domainTwoMinusFour :
    AnalyticOnNhd ℂ ProfileComplex.A.aPrimeC domainTwoMinusFour := by
  refine (ProfileComplex.A.analyticOnNhd_aPrimeC).mono ?_
  intro z hz
  have hz2 : 2 < z.re := by
    simpa [domainTwoMinusFour, LaplaceDomains.domainTwo] using! hz.1
  have : 0 < z.re := lt_trans (by norm_num : (0 : ℝ) < 2) hz2
  simpa [SpherePacking.rightHalfPlane] using! this

lemma analyticOnNhd_coeffExpC : AnalyticOnNhd ℂ coeffExpC univ := by
  intro z hz
  have h₁ : AnalyticAt ℂ (fun u : ℂ => Complex.exp ((Real.pi : ℂ) * u * Complex.I)) z := by
    fun_prop
  have h₂ : AnalyticAt ℂ (fun u : ℂ => Complex.exp (-((Real.pi : ℂ) * u * Complex.I))) z := by
    fun_prop
  have h₃ : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) z := by
    fun_prop
  -- `fun_prop` proves analyticity of each term; assemble them in the exact parenthesization
  -- matching `coeffExpC`.
  simpa [coeffExpC] using! ((h₁.add h₂).sub h₃)

lemma analyticOnNhd_coeffExpC_domainTwoMinusFour :
    AnalyticOnNhd ℂ coeffExpC domainTwoMinusFour := by
  refine analyticOnNhd_coeffExpC.mono ?_
  intro _ _; simp

lemma analyticOnNhd_pTildeProfileC_domainTwoMinusFour :
    AnalyticOnNhd ℂ pTildeProfileC domainTwoMinusFour := by
  have hid : AnalyticOnNhd ℂ (fun u : ℂ => u) domainTwoMinusFour := analyticOnNhd_id
  have hsub4 : AnalyticOnNhd ℂ (fun u : ℂ => u - (4 : ℂ)) domainTwoMinusFour :=
    hid.sub (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (4 : ℂ)) domainTwoMinusFour)
  have hsub2 : AnalyticOnNhd ℂ (fun u : ℂ => u - (2 : ℂ)) domainTwoMinusFour :=
    hid.sub (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (2 : ℂ)) domainTwoMinusFour)
  have hpowSub2 : AnalyticOnNhd ℂ (fun u : ℂ => (u - (2 : ℂ)) ^ (2 : ℕ)) domainTwoMinusFour :=
    hsub2.pow 2
  have hpowId : AnalyticOnNhd ℂ (fun u : ℂ => u ^ (2 : ℕ)) domainTwoMinusFour :=
    hid.pow 2
  have hterm1 :
      AnalyticOnNhd ℂ (fun u : ℂ => ((-864 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (u - 4))
        domainTwoMinusFour := by
    refine (analyticOnNhd_const.div hsub4 ?_)
    intro u hu
    have hu4 : u ≠ (4 : ℂ) := by
      have : u ∉ ({4} : Set ℂ) := hu.2
      simpa [Set.mem_singleton_iff] using! this
    exact sub_ne_zero.2 hu4
  have hterm2 :
      AnalyticOnNhd ℂ (fun u : ℂ => ((725760 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 2) ^ (2 : ℕ)))
        domainTwoMinusFour := by
    refine (analyticOnNhd_const.div hpowSub2 ?_)
    intro u hu
    have hre : 2 < u.re := by simpa [domainTwoMinusFour, LaplaceDomains.domainTwo] using! hu.1
    have hu2 : u ≠ (2 : ℂ) := by
      intro h
      have : u.re = 2 := by simp [h]
      linarith
    exact pow_ne_zero 2 (sub_ne_zero.2 hu2)
  have hterm3 :
      AnalyticOnNhd ℂ (fun u : ℂ => ((-2218752 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (u - 2))
        domainTwoMinusFour := by
    refine (analyticOnNhd_const.div hsub2 ?_)
    intro u hu
    have hre : 2 < u.re := by simpa [domainTwoMinusFour, LaplaceDomains.domainTwo] using! hu.1
    have hu2 : u ≠ (2 : ℂ) := by
      intro h
      have : u.re = 2 := by simp [h]
      linarith
    exact sub_ne_zero.2 hu2
  have hterm4 :
      AnalyticOnNhd ℂ (fun u : ℂ => ((113218560 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (u ^ (2 : ℕ)))
        domainTwoMinusFour := by
    refine (analyticOnNhd_const.div hpowId ?_)
    intro u hu
    have hre : 2 < u.re := by simpa [domainTwoMinusFour, LaplaceDomains.domainTwo] using! hu.1
    have hu0 : u ≠ 0 := by
      intro h
      have : u.re = 0 := by simp [h]
      linarith
    exact pow_ne_zero 2 hu0
  have hterm5 :
      AnalyticOnNhd ℂ (fun u : ℂ => ((-223140096 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / u)
        domainTwoMinusFour := by
    refine (analyticOnNhd_const.div hid ?_)
    intro u hu
    have hre : 2 < u.re := by simpa [domainTwoMinusFour, LaplaceDomains.domainTwo] using! hu.1
    intro h
    have : u.re = 0 := by simp [h]
    linarith
  have hsum :
      AnalyticOnNhd ℂ
        (fun u : ℂ =>
          (((( (-864 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (u - 4) +
                ((725760 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / ((u - 2) ^ (2 : ℕ)))
              + ((-2218752 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (u - 2))
            + ((113218560 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / (u ^ (2 : ℕ)))
          + ((-223140096 : ℂ) / ((π : ℂ) ^ (3 : ℕ))) / u)
        domainTwoMinusFour :=
    ((((hterm1.add hterm2).add hterm3).add hterm4).add hterm5)
  simpa [pTildeProfileC] using! hsum

lemma analyticOnNhd_aProfileRhsC_domainTwoMinusFour :
    AnalyticOnNhd ℂ aProfileRhsC domainTwoMinusFour := by
  have hcoeff :
      AnalyticOnNhd ℂ coeffExpC domainTwoMinusFour :=
    analyticOnNhd_coeffExpC_domainTwoMinusFour
  have hpt : AnalyticOnNhd ℂ pTildeProfileC domainTwoMinusFour :=
    analyticOnNhd_pTildeProfileC_domainTwoMinusFour
  have hrem : AnalyticOnNhd ℂ avaluesRemainderIntegralC domainTwoMinusFour :=
    (analyticOnNhd_avaluesRemainderIntegralC_domainTwo.mono (by
      intro z hz
      exact hz.1))
  have hsum :
      AnalyticOnNhd ℂ
        (fun u : ℂ => pTildeProfileC u + avaluesRemainderIntegralC u)
        domainTwoMinusFour :=
    hpt.add hrem
  -- Multiply in the same parenthesization as `aProfileRhsC`.
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => (-(Complex.I : ℂ))) domainTwoMinusFour :=
    (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (-(Complex.I : ℂ))) domainTwoMinusFour)
  have hmul1 :
      AnalyticOnNhd ℂ (fun u : ℂ => (-(Complex.I : ℂ)) * coeffExpC u) domainTwoMinusFour :=
    hconst.mul hcoeff
  have hmul2 :
      AnalyticOnNhd ℂ
        (fun u : ℂ =>
          ((-(Complex.I : ℂ)) * coeffExpC u) * (pTildeProfileC u + avaluesRemainderIntegralC u))
        domainTwoMinusFour :=
    hmul1.mul hsum
  assumption

lemma aPrimeC_eq_aProfileRhsC_ofReal_of_lt {u : ℝ} (hu : 4 < u) :
    ProfileComplex.A.aPrimeC (u : ℂ) = aProfileRhsC (u : ℂ) := by
  have ha :
      aProfile u =
        -(Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u) *
          (pTildeProfile u + avaluesRemainderIntegral u) :=
    aProfile_eq_neg_I_mul_coeffExp_mul_pTildeProfile_add_remainderIntegral_of_lt (u := u) hu
  simpa [ProfileComplex.A.aPrimeC_ofReal, aProfileRhsC_ofReal] using! ha

lemma five_mem_closure_eqset :
    (5 : ℂ) ∈ closure ({z : ℂ | ProfileComplex.A.aPrimeC z = aProfileRhsC z} \ {(5 : ℂ)}) := by
  refine Metric.mem_closure_iff.2 ?_
  intro ε hε
  let u : ℝ := 5 + ε / 2
  refine ⟨(u : ℂ), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- equality holds for all real `u > 4`
      have hu : 4 < u := by
        dsimp [u]
        nlinarith
      simpa [Set.mem_setOf_eq] using! (aPrimeC_eq_aProfileRhsC_ofReal_of_lt (u := u) hu)
    · -- and `u ≠ 5`
      have hne : u ≠ 5 := by
        dsimp [u]
        nlinarith
      have hneC : (u : ℂ) ≠ (5 : ℂ) := by
        intro h
        have : u = 5 := by
          have := congrArg Complex.re h
          simpa using! this
        exact hne this
      simpa [Set.mem_singleton_iff] using! hneC
  · -- `dist (u,5) < ε`
    have hε2pos : 0 < ε / 2 := by nlinarith
    have hdist : dist (5 : ℂ) (u : ℂ) = ε / 2 := by
      -- `5 - u = -(ε/2)` and `‖(ε/2 : ℂ)‖ = ε/2`.
      have h₁ : dist (5 : ℂ) (u : ℂ) = ‖((-(ε / 2) : ℝ) : ℂ)‖ := by
        simp [u, dist_eq_norm]
      rw [h₁]
      -- Stop simplification at the real absolute value, to avoid rewriting into `|ε| / 2`.
      rw [Complex.norm_real]
      -- `Complex.norm_real` leaves a real norm; rewrite to an absolute value and evaluate.
      rw [Real.norm_eq_abs, abs_neg]
      have hε2nonneg : 0 ≤ ε / 2 := le_of_lt hε2pos
      simpa using! (abs_of_nonneg hε2nonneg)
    rw [hdist]
    nlinarith

lemma aPrimeC_eq_aProfileRhsC_on_domainTwoMinusFour :
    EqOn ProfileComplex.A.aPrimeC aProfileRhsC domainTwoMinusFour := by
  have hf : AnalyticOnNhd ℂ ProfileComplex.A.aPrimeC domainTwoMinusFour :=
    analyticOnNhd_aPrimeC_domainTwoMinusFour
  have hg : AnalyticOnNhd ℂ aProfileRhsC domainTwoMinusFour :=
    analyticOnNhd_aProfileRhsC_domainTwoMinusFour
  have h0 : (5 : ℂ) ∈ domainTwoMinusFour := by
    refine ⟨?_, ?_⟩
    · -- `2 < (5:ℂ).re`
      simpa [domainTwoMinusFour, LaplaceDomains.domainTwo] using! (by norm_num : (2 : ℝ) < (5 : ℝ))
    · -- `5 ≠ 4`
      have : (5 : ℂ) ≠ (4 : ℂ) := by norm_num
      simp [Set.mem_singleton_iff]
  exact
    AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure (hf := hf) (hg := hg)
      domainTwoMinusFour_isPreconnected h0 five_mem_closure_eqset

lemma fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_of_Ioo_two_three
    {u : ℝ} (hu2 : 2 < u) (hu3 : u < 3) :
    fProfile u = -pTildeProfile u - coeffConstTerm u - avaluesRemainderIntegral u := by
  have hz : (u : ℂ) ∈ domainTwoMinusFour := by
    refine ⟨?_, ?_⟩
    · simpa [domainTwoMinusFour, LaplaceDomains.domainTwo] using! hu2
    · have hu4 : u ≠ 4 := by linarith
      have hu4C : (u : ℂ) ≠ (4 : ℂ) := by
        intro h
        have : u = 4 := by
          have := congrArg Complex.re h
          simpa using! this
        exact hu4 this
      simpa [Set.mem_singleton_iff] using! hu4C
  have ha :
      aProfile u =
        -(Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u) *
          (pTildeProfile u + avaluesRemainderIntegral u) := by
    have hEq := aPrimeC_eq_aProfileRhsC_on_domainTwoMinusFour hz
    simpa [ProfileComplex.A.aPrimeC_ofReal, aProfileRhsC_ofReal] using! hEq
  have hcoeff : SpecialValuesDeriv.coeffExp u ≠ 0 :=
    coeffExp_ne_zero_of_Ioo_two_three (u := u) hu2 hu3
  have hden0 : (Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u ≠ 0 := mul_ne_zero (by simp) hcoeff
  -- Same algebra as in the convergent-range lemma: clear denominators.
  have hsum :
      fProfile u + coeffConstTerm u =
        aProfile u / ((Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u) := by
    set den : ℂ := (Complex.I : ℂ) * SpecialValuesDeriv.coeffExp u
    calc
      fProfile u + coeffConstTerm u =
          (aProfile u - constA2_av) / den + constA2_av / den := by
            simp [fProfile, coeffConstTerm, den]
      _ = ((aProfile u - constA2_av) + constA2_av) / den := by
            simpa [add_div] using! (add_div (aProfile u - constA2_av) constA2_av den).symm
      _ = aProfile u / den := by
            simp [sub_eq_add_neg, den, add_assoc]
  have hmain :
      fProfile u + coeffConstTerm u = -(pTildeProfile u + avaluesRemainderIntegral u) := by
    rw [hsum, ha]
    field_simp [hden0]
  have hsub := congrArg (fun z : ℂ => z - coeffConstTerm u) hmain
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hsub
 
/-- Analytic continuation step: extend the convergent-range identity to a right-neighborhood of
`u = 2`. -/
public theorem fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_nhdsGT_two_impl :
    (fun u : ℝ => fProfile u) =ᶠ[𝓝[>] (2 : ℝ)]
      fun u : ℝ => -pTildeProfile u - coeffConstTerm u - avaluesRemainderIntegral u := by
  have hIoo : Set.Ioo (2 : ℝ) 3 ∈ 𝓝[>] (2 : ℝ) :=
    inter_mem_nhdsWithin (Set.Ioi (2 : ℝ)) (Iio_mem_nhds (by norm_num : (2 : ℝ) < 3))
  filter_upwards [hIoo] with u hu
  exact
    fProfile_eq_neg_pTilde_sub_coeffConstTerm_sub_remainderIntegral_of_Ioo_two_three
      (u := u) hu.1 hu.2

end SpecialValuesDerivTwoLaurent

end
end SpherePacking.Dim24
