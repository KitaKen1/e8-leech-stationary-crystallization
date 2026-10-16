-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims
import SpherePacking.Dim24.MagicFunction.B.Defs.J5Smooth
import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
import SpherePacking.Dim24.ModularForms.Psi.Relations
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
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Equality.A.Defs
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Kernels
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Profiles.BProfile.Bounds

/-!
# Decomposing the `gV`/`gψ` Laplace integrals

We split the integral on `Set.Ioi 0` into a segment part on `(0,1]` and a tail part on `t > 1`,
and we define the Laplace integrand `gψ u t = ψI' (i t) * exp (-π * u * t)` used in the
`BKernel0` term.

## Main definitions
* `gψ`

## Main statements
* `Ioi_eq_Ioc_union_Ioi_one`
* `integral_gV_Ioi_eq_interval_add_Ioi_one`
* `integrableOn_gψ_Ioc`
* `integrableOn_ψS'_imag_mul_exp`
* `integrableOn_ψT'_imag_mul_exp`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceEqA

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped Interval

open Complex MeasureTheory Real SchwartzMap Set
open UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Decompose `Set.Ioi 0` into the disjoint union of `(0,1]` and the tail `t > 1`. -/
public lemma Ioi_eq_Ioc_union_Ioi_one :
    Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
  ext t
  constructor
  · intro ht
    by_cases ht1 : t ≤ (1 : ℝ)
    · exact Or.inl ⟨ht, ht1⟩
    · exact Or.inr (lt_of_not_ge ht1)
  · intro ht
    rcases ht with ht | ht
    · exact ht.1
    · exact lt_trans (by norm_num : (0 : ℝ) < 1) ht

lemma disjoint_Ioc_Ioi_one :
    Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) :=
  Ioc_disjoint_Ioi_same

/-- Split the `gV` integral on `Set.Ioi 0` into the segment integral on `[0,1]` plus the tail. -/
public lemma integral_gV_Ioi_eq_interval_add_Ioi_one (u : ℝ) (hu : 4 < u) :
    (∫ t in (0 : ℝ)..1, gV u t) + ∫ t in Set.Ioi (1 : ℝ), gV u t =
      ∫ t in Set.Ioi (0 : ℝ), gV u t := by
  have hu0 : 0 ≤ u := le_trans (by linarith) (le_of_lt hu)
  have hseg :
      (∫ t in (0 : ℝ)..1, gV u t) = ∫ t in Set.Ioc (0 : ℝ) 1, gV u t :=
    Eq.symm (Integration.integral_restrict_Ioc01_eq_intervalIntegral (gV u))
  have hIntIoc : IntegrableOn (gV u) (Set.Ioc (0 : ℝ) 1) volume :=
    integrableOn_gV_Ioc (u := u) hu0
  have hIntIoi : IntegrableOn (gV u) (Set.Ioi (1 : ℝ)) volume :=
    integrableOn_gV_Ioi_one (u := u) hu
  have hUnion := Ioi_eq_Ioc_union_Ioi_one
  have hdisj := disjoint_Ioc_Ioi_one
  have hIntegralUnion :
      (∫ t in (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)), gV u t) =
        (∫ t in Set.Ioc (0 : ℝ) 1, gV u t) + ∫ t in Set.Ioi (1 : ℝ), gV u t :=
    (MeasureTheory.setIntegral_union (μ := volume) (f := gV u) hdisj measurableSet_Ioi hIntIoc
    hIntIoi)
  -- Rewrite the interval integral as a set integral and use the union decomposition of `Ioi 0`.
  grind only

/-- The Laplace integrand corresponding to the `ψI'` term on the imaginary axis. -/
@[expose] public def gψ (u : ℝ) (t : ℝ) : ℂ :=
  ψI' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ)

/-- Integrability of `gψ u` on the segment `(0,1]` for `0 ≤ u`. -/
public lemma integrableOn_gψ_Ioc (u : ℝ) (hu0 : 0 ≤ u) :
    IntegrableOn (gψ u) (Set.Ioc (0 : ℝ) 1) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by infer_instance
  -- Measurability from continuity on `(0,1]` after rewriting `ψI'` through `ψI ∘ ofComplex`.
  have hcont :
      ContinuousOn (gψ u) (Set.Ioc (0 : ℝ) 1) := by
    let γ : ℝ → ℂ := fun t : ℝ => (t : ℂ) * Complex.I
    have hexp : Continuous fun t : ℝ => (Real.exp (-Real.pi * u * t) : ℂ) := by fun_prop
    have h1 : ContinuousOn (fun t : ℝ => ψI' (γ t)) (Set.Ioc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      -- Work on the restricted function `t : Ioc(0,1] ↦ ψI(it t)`.
      let s : Set.Ioc (0 : ℝ) 1 → ℍ :=
        fun x =>
          ⟨γ (x : ℝ), by
            have hx0 : (0 : ℝ) < (x : ℝ) := x.property.1
            simpa [γ] using! hx0⟩
      have hs : Continuous s := by
        fun_prop
      have hψ : Continuous fun x : Set.Ioc (0 : ℝ) 1 => ψI (s x) :=
        ((SpherePacking.Dim24.continuous_ψI).comp hs)
      refine hψ.congr ?_
      intro x
      have hx0 : (0 : ℝ) < (x : ℝ) := x.property.1
      have hz : 0 < (γ (x : ℝ)).im := by simpa [γ] using! hx0
      have hsx : s x = (⟨γ (x : ℝ), hz⟩ : ℍ) := by
        ext1
        rfl
      -- `ψI'` agrees with `ψI` on the upper half-plane.
      rw [hsx]
      simp [ψI', hz]
    -- Multiply by the (continuous) exponential factor.
    -- `simp` may rewrite `(Real.exp _ : ℂ)` to `Complex.exp _`, so use `convert`.
    have hprod :
        ContinuousOn (fun t : ℝ => ψI' (γ t) * (Real.exp (-Real.pi * u * t) : ℂ))
          (Set.Ioc (0 : ℝ) 1) :=
      h1.mul hexp.continuousOn
    -- Avoid `simp` rewriting `Real.exp` into `Complex.exp` here.
    assumption
  have hmeas :
      AEStronglyMeasurable (gψ u) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ)) hcont measurableSet_Ioc
  -- Uniform bound on `(0,1]` from the `z₅'` rewrite.
  rcases PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one with ⟨M, hM⟩
  have hbound :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖gψ u t‖ ≤ M := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc ?_
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht0' : 0 ≤ t := le_of_lt ht0
    have ht1 : t ≤ 1 := ht.2
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0', ht1⟩
    have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht0, ht1⟩
    have hz5 :
        MagicFunction.Parametrisations.z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using!
        (MagicFunction.Parametrisations.z₅'_eq_of_mem (t := t) htIcc)
    have hψEq :
        ψI' ((t : ℂ) * Complex.I) =
          ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) := by
      have h := SpherePacking.Dim24.Schwartz.J5Smooth.ψI'_z₅'_eq (t := t) htIoc
      -- `ψI'_z₅'_eq` is stated at `z₅' t`; rewrite `z₅' t = I*t = t*I`.
      have hz5' : MagicFunction.Parametrisations.z₅' t = (t : ℂ) * Complex.I := by
        simp [hz5, mul_comm]
      simpa [hz5', mul_assoc, mul_left_comm, mul_comm] using! h
    have hone : (1 : ℝ) ≤ 1 / t := by
      simpa using! (one_le_one_div ht0 ht1)
    have hψS : ‖ψS.resToImagAxis (1 / t)‖ ≤ M := hM (1 / t) hone
    have hM0 : 0 ≤ M :=
      le_trans (norm_nonneg (ψS.resToImagAxis (1 : ℝ)))
        (hM 1 (le_rfl : (1 : ℝ) ≤ 1))
    have hpow :
        ‖((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ)‖ ≤ 1 := by
      have hbase : ‖(Complex.I : ℂ) * (t : ℂ)‖ ≤ 1 := by
        -- `‖I * t‖ = |t| = t` since `t ≥ 0`.
        simpa [Complex.norm_mul, Complex.norm_real, abs_of_nonneg ht0'] using! ht1
      have : ‖(Complex.I : ℂ) * (t : ℂ)‖ ^ (10 : ℕ) ≤ 1 ^ (10 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg ((Complex.I : ℂ) * (t : ℂ))) hbase 10
      simpa [norm_pow] using! this
    have hexpU : ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ ≤ 1 := by
      have hle : Real.exp (-Real.pi * u * t) ≤ 1 := by
        refine Real.exp_le_one_iff.2 ?_
        have hpos : 0 ≤ Real.pi * u * t := by positivity [hu0, ht0']
        linarith
      have hnorm : ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ = Real.exp (-Real.pi * u * t) := by
        calc
          ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ = ‖Complex.exp (-Real.pi * u * t)‖ := by
            simp [Complex.ofReal_exp]
          _ = Real.exp (-Real.pi * u * t) := by
            simpa using! (Complex.norm_exp_ofReal (-Real.pi * u * t))
      rw [hnorm]
      exact hle
    calc
      ‖gψ u t‖ = ‖ψI' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ)‖ := by
            simp [gψ]
      _ ≤ ‖ψI' ((t : ℂ) * Complex.I)‖ * ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ :=
            norm_mul_le (ψI' ((t : ℂ) * Complex.I)) (Real.exp (-Real.pi * u * t) : ℂ)
      _ ≤ ‖ψI' ((t : ℂ) * Complex.I)‖ * 1 := by gcongr
      _ = ‖ψI' ((t : ℂ) * Complex.I)‖ := by simp
      _ = ‖ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ)‖ := by
            simp [hψEq]
      _ ≤ ‖ψS.resToImagAxis (1 / t)‖ *
            ‖((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ)‖ := by
            exact
              norm_mul_le (ψS.resToImagAxis (1 / t)) (((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ))
      _ ≤ M * 1 := by
            gcongr
      _ = M := by simp
  refine ⟨hmeas, ?_⟩
  exact HasFiniteIntegral.of_bounded hbound

/-- Integrability of `ψS'(i t) * exp (-π * u * t)` on `t > 1` for `0 ≤ u`. -/
public lemma integrableOn_ψS'_imag_mul_exp (u : ℝ) (hu0 : 0 ≤ u) :
    IntegrableOn
        (fun t : ℝ =>
          ψS' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
        (Set.Ioi (1 : ℝ)) volume := by
  have hf :
      Integrable (fun t : ℝ => ψS' (t * Complex.I)) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    simpa [IntegrableOn] using!
      SpherePacking.Dim24.PsiSPrelims.integrableOn_ψS'_vertical_left
  have hg :
      AEStronglyMeasurable (fun t : ℝ => (Real.exp (-Real.pi * u * t) : ℂ))
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have : Continuous fun t : ℝ => (Real.exp (-Real.pi * u * t) : ℂ) := by fun_prop
    exact this.aestronglyMeasurable
  have hbound :
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi (1 : ℝ))),
        ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ ≤ 1 := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) ht)
    have hle : Real.exp (-Real.pi * u * t) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have hpos : 0 ≤ Real.pi * u * t := by positivity [hu0, ht0]
      linarith
    have hnorm :
        ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ = Real.exp (-Real.pi * u * t) := by
      rw [Complex.norm_real]
      simp [abs_of_nonneg (Real.exp_pos _).le]
    rw [hnorm]
    exact hle
  have hmul :
      Integrable
          (fun t : ℝ =>
            ψS' (t * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
          (volume.restrict (Set.Ioi (1 : ℝ))) :=
    hf.mul_bdd hg hbound
  simpa [IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using! hmul

/-- Integrability of `ψT'(i t) * exp (-π * u * t)` on `t > 1` in the convergent range `u > 4`. -/
public lemma integrableOn_ψT'_imag_mul_exp (u : ℝ) (hu : 4 < u) :
    IntegrableOn
        (fun t : ℝ =>
          ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
        (Set.Ioi (1 : ℝ)) volume := by
  have hu0 : 0 ≤ u := le_trans (by linarith) (le_of_lt hu)
  rcases LaplaceProfiles.LaplaceBProfile.exists_ψT_bound_exp with ⟨Cψ, Aψ, hCψ, hψT⟩
  let A : ℝ := max Aψ 1
  have hAψ : Aψ ≤ A := le_max_left _ _
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  -- Integrability on the bounded interval `(1, A]` by continuity.
  have hcont_Icc :
      ContinuousOn
          (fun t : ℝ =>
            ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
          (Set.Icc (1 : ℝ) A) := by
    let γ : ℝ → ℂ := fun t : ℝ => (t : ℂ) * Complex.I
    have hT :
        ContinuousOn (fun t : ℝ => ψT' (γ t)) (Set.Icc (1 : ℝ) A) := by
      rw [continuousOn_iff_continuous_restrict]
      let s : Set.Icc (1 : ℝ) A → ℍ :=
        fun x =>
          ⟨γ (x : ℝ), by
            have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) x.property.1
            simpa [γ] using! hx0⟩
      have hs : Continuous s := by
          fun_prop
      have hψ : Continuous fun x : Set.Icc (1 : ℝ) A => ψT (s x) :=
        ((SpherePacking.Dim24.continuous_ψT).comp hs)
      refine hψ.congr ?_
      intro x
      have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) x.property.1
      have hz : 0 < (γ (x : ℝ)).im := by simpa [γ] using! hx0
      have hsx : s x = (⟨γ (x : ℝ), hz⟩ : ℍ) := by
        ext1
        rfl
      rw [hsx]
      simp [ψT', hz]
    have hexp : Continuous fun t : ℝ => (Real.exp (-Real.pi * u * t) : ℂ) := by fun_prop
    have hmul :
        ContinuousOn
            (fun t : ℝ => ψT' (γ t) * (Real.exp (-Real.pi * u * t) : ℂ))
            (Set.Icc (1 : ℝ) A) :=
      hT.mul hexp.continuousOn
    simpa [γ, mul_assoc] using! hmul
  have hInt_Ioc : IntegrableOn
        (fun t : ℝ =>
          ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
        (Set.Ioc (1 : ℝ) A) volume := by
    have hIcc :
        IntegrableOn
            (fun t : ℝ =>
              ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
            (Set.Icc (1 : ℝ) A) volume :=
      hcont_Icc.integrableOn_Icc (μ := volume)
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  -- Tail integrability on `(A, ∞)` by exponential domination.
  have hInt_IoiA : IntegrableOn
        (fun t : ℝ =>
          ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
        (Set.Ioi A) volume := by
    have ha : (-(Real.pi * (u - 4)) : ℝ) < 0 := by nlinarith [Real.pi_pos, hu]
    have hg0 :
        IntegrableOn
          (fun t : ℝ => Real.exp ((-(Real.pi * (u - 4)) : ℝ) * t)) (Set.Ioi A) volume :=
      integrableOn_exp_mul_Ioi (a := (-(Real.pi * (u - 4)) : ℝ)) ha A
    have hg :
        Integrable (fun t : ℝ => Cψ * Real.exp ((-(Real.pi * (u - 4)) : ℝ) * t))
          (volume.restrict (Set.Ioi A)) := by
      have hg0' :
          Integrable (fun t : ℝ => Real.exp ((-(Real.pi * (u - 4)) : ℝ) * t))
            (volume.restrict (Set.Ioi A)) := by
        simpa [IntegrableOn] using! hg0
      exact hg0'.const_mul Cψ
    have hf_meas :
        AEStronglyMeasurable
            (fun t : ℝ =>
              ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
            (volume.restrict (Set.Ioi A)) := by
      have hcont :
          ContinuousOn
              (fun t : ℝ =>
                ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
              (Set.Ioi A) := by
        let γ : ℝ → ℂ := fun t : ℝ => (t : ℂ) * Complex.I
        have hT :
            ContinuousOn (fun t : ℝ => ψT' (γ t)) (Set.Ioi A) := by
          rw [continuousOn_iff_continuous_restrict]
          let s : Set.Ioi A → ℍ :=
            fun x =>
              ⟨γ (x : ℝ), by
                have hx0 : (0 : ℝ) < (x : ℝ) :=
                  lt_trans (lt_of_lt_of_le (by norm_num) hA1) x.property
                simpa [γ] using! hx0⟩
          have hs : Continuous s := by
              fun_prop
          have hψ : Continuous fun x : Set.Ioi A => ψT (s x) :=
            ((SpherePacking.Dim24.continuous_ψT).comp hs)
          refine hψ.congr ?_
          intro x
          have hx0 : (0 : ℝ) < (x : ℝ) :=
            lt_trans (lt_of_lt_of_le (by norm_num) hA1) x.property
          have hz : 0 < (γ (x : ℝ)).im := by simpa [γ] using! hx0
          have hsx : s x = (⟨γ (x : ℝ), hz⟩ : ℍ) := by
            ext1
            rfl
          rw [hsx]
          simp [ψT', hz]
        have hexp : Continuous fun t : ℝ => (Real.exp (-Real.pi * u * t) : ℂ) := by fun_prop
        have hmul :
            ContinuousOn
                (fun t : ℝ => ψT' (γ t) * (Real.exp (-Real.pi * u * t) : ℂ))
                (Set.Ioi A) :=
          hT.mul hexp.continuousOn
        simpa [γ, mul_assoc] using! hmul
      exact ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ)) hcont measurableSet_Ioi
    have hbound :
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi A)),
          ‖ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ)‖ ≤
            Cψ * Real.exp ((-(Real.pi * (u - 4)) : ℝ) * t) := by
      refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have htA : A ≤ t := le_of_lt ht
      have ht0 : 0 < t := lt_trans (lt_of_lt_of_le (by norm_num) hA1) ht
      have hz : 0 < (((t : ℂ) * Complex.I).im) := by simpa using! ht0
      have hψT' :
          ψT' ((t : ℂ) * Complex.I) = ψT (it t ht0) := by
        let z : ℂ := (t : ℂ) * Complex.I
        have hz' : 0 < z.im := by simpa [z] using! hz
        have hEq : ψT' z = ψT (⟨z, hz'⟩ : ℍ) := by
          simp [ψT', hz']
        have hit : (⟨z, hz'⟩ : ℍ) = it t ht0 := by
          ext1
          simp [z, it, mul_comm]
        simp [z, hEq, hit]
      have hψTnorm :
          ‖ψT' ((t : ℂ) * Complex.I)‖ ≤ Cψ * Real.exp (4 * Real.pi * t) := by
        have hAψt : Aψ ≤ t := le_trans hAψ htA
        have hψT0 : ‖ψT (it t ht0)‖ ≤ Cψ * Real.exp (4 * Real.pi * (it t ht0).im) :=
          hψT (it t ht0) (by simpa [it_im (t := t) ht0] using! hAψt)
        have hitIm : (it t ht0).im = t := it_im (t := t) ht0
        have hψT1 : ‖ψT (it t ht0)‖ ≤ Cψ * Real.exp (4 * Real.pi * t) := by
          simpa [hitIm] using! hψT0
        simpa [hψT'] using! hψT1
      have hnormExp :
          ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ = Real.exp (-Real.pi * u * t) := by
        rw [Complex.norm_real]
        simp [abs_of_nonneg (Real.exp_pos _).le]
      calc
        ‖ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ)‖ =
            ‖ψT' ((t : ℂ) * Complex.I)‖ * ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ := by
              simp []
        _ ≤ (Cψ * Real.exp (4 * Real.pi * t)) * Real.exp (-Real.pi * u * t) := by
              have h1 :
                  ‖ψT' ((t : ℂ) * Complex.I)‖ *
                      ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ ≤
                    (Cψ * Real.exp (4 * Real.pi * t)) *
                      ‖(Real.exp (-Real.pi * u * t) : ℂ)‖ :=
                mul_le_mul_of_nonneg_right hψTnorm (norm_nonneg _)
              exact le_of_le_of_eq h1 (congrArg (HMul.hMul (Cψ * rexp (4 * π * t))) hnormExp)
        _ = Cψ * Real.exp ((-(Real.pi * (u - 4)) : ℝ) * t) := by
              -- combine exponentials
              calc
                (Cψ * Real.exp (4 * Real.pi * t)) * Real.exp (-Real.pi * u * t)
                    = Cψ * (Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * u * t)) := by ring
                _ = Cψ * Real.exp ((4 * Real.pi * t) + (-Real.pi * u * t)) := by
                      simpa [mul_assoc] using!
                        congrArg (fun r : ℝ => Cψ * r)
                          ((Real.exp_add (4 * Real.pi * t) (-Real.pi * u * t)).symm)
                _ = Cψ * Real.exp ((-(Real.pi * (u - 4)) : ℝ) * t) := by
                      congr 2
                      ring
    have hInt :
        Integrable
            (fun t : ℝ =>
              ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
            (volume.restrict (Set.Ioi A)) :=
      Integrable.mono' hg hf_meas hbound
    simpa [IntegrableOn] using! hInt
  -- Combine the bounded and tail parts.
  have hUnion : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A := by
    simpa using! (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) hA1).symm
  -- Use `integrableOn_union` and rewrite by `hUnion`.
  have hIntUnion :
      IntegrableOn
          (fun t : ℝ =>
            ψT' ((t : ℂ) * Complex.I) * (Real.exp (-Real.pi * u * t) : ℂ))
          (Set.Ioc (1 : ℝ) A ∪ Set.Ioi A) volume := by
    exact (MeasureTheory.integrableOn_union).2 ⟨hInt_Ioc, hInt_IoiA⟩
  simpa [hUnion] using! hIntUnion


end

end SpherePacking.Dim24.LaplaceTmp.LaplaceEqA
