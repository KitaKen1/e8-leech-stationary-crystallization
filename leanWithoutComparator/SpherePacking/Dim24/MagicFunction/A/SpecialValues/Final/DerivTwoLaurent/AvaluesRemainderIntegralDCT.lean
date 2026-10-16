-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegralDefs
import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemIntDom
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated convergence at `u = 2`

This file proves continuity of `avaluesRemainderIntegral` at `u = 2` by dominated convergence,
with domination supplied by `AvaluesRemIntDom`.

## Main definitions
* `avaluesRemainderIntegrand`

## Main statements
* `continuousAt_avaluesRemainderIntegral_two_dct`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology UpperHalfPlane
open Filter Complex MeasureTheory Set

/-- Continuity of `iOverT` on the positive real axis, viewed as a map into `ℍ`. -/
public lemma continuous_iOverT_pos :
    Continuous fun p : {t : ℝ // 0 < t} => (iOverT p.1 p.2 : ℍ) := by
  -- `iOverT t = it (1/t)`.
  have hcont_inv : Continuous fun p : {t : ℝ // 0 < t} => (1 / (p.1 : ℝ)) := by
    simpa [one_div] using! (continuous_subtype_val.inv₀ fun p => ne_of_gt p.2)
  have hbase :
      Continuous fun p : {t : ℝ // 0 < t} =>
        (Complex.I : ℂ) * ((1 / (p.1 : ℝ) : ℝ) : ℂ) := by
    have hcast : Continuous fun p : {t : ℝ // 0 < t} => ((1 / (p.1 : ℝ) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp hcont_inv
    simpa [mul_assoc] using! (continuous_const.mul hcast)
  simpa [iOverT, it] using!
    Continuous.upperHalfPlaneMk hbase (fun p => by
      have : 0 < (1 / (p.1 : ℝ) : ℝ) := one_div_pos.2 p.2; simpa [Complex.mul_im] using! this)

/--
The integrand used for dominated convergence. This is a definitional alias of
`avaluesRemainderIntegrandFull`.
-/
@[expose] public def avaluesRemainderIntegrand (u t : ℝ) : ℂ :=
  avaluesRemainderIntegrandFull u t

/-- Rewrite `avaluesRemainderIntegral` as the set integral of `avaluesRemainderIntegrand`. -/
public theorem avaluesRemainderIntegral_eq_integral_integrand (u : ℝ) :
    avaluesRemainderIntegral u =
      ∫ t : ℝ in Set.Ioi (0 : ℝ), avaluesRemainderIntegrand u t := by
  -- Just unfold the definitions.
  simp [avaluesRemainderIntegral, avaluesRemainderIntegrand, avaluesRemainderIntegrandFull]

/--
`avaluesRemainderIntegrand u` is `AEStronglyMeasurable` for the restricted measure on `(0,∞)`.
-/
public theorem aestronglyMeasurable_avaluesRemainderIntegrand (u : ℝ) :
    MeasureTheory.AEStronglyMeasurable (avaluesRemainderIntegrand u)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  -- Prove measurability on `ℝ`, then use `Measurable.aestronglyMeasurable`.
  have hpPaper : Continuous pPaper := by unfold pPaper; fun_prop
  let s : Set ℝ := Set.Ioi (0 : ℝ)
  have hs : MeasurableSet s := isOpen_Ioi.measurableSet
  -- Positive branch, as a function on the subtype `s`.
  let f : s → ℂ := fun p =>
    (((p.1 : ℝ) : ℂ) ^ (10 : ℕ) * varphi (iOverT p.1 (by
          -- `p.2` already records `0 < p.1` since `s = Ioi 0`.
          exact p.2) ) - pPaper p.1) *
      (Real.exp (-Real.pi * u * p.1) : ℂ)
  have hf_cont : Continuous f := by
    have hvarphi : Continuous (varphi : ℍ → ℂ) := varphi_holo'.continuous
    have hio : Continuous fun p : s => (iOverT p.1 (by exact p.2) : ℍ) := by
      simpa using! (continuous_iOverT_pos :
        Continuous fun p : {t : ℝ // 0 < t} => (iOverT p.1 p.2 : ℍ))
    have ht10 : Continuous fun p : s => ((p.1 : ℝ) : ℂ) ^ (10 : ℕ) := by
      fun_prop
    have hpp : Continuous fun p : s => pPaper (p.1 : ℝ) := hpPaper.comp continuous_subtype_val
    have hexp : Continuous fun p : s => (Real.exp (-Real.pi * u * (p.1 : ℝ)) : ℂ) := by
      fun_prop
    have hterm : Continuous fun p : s =>
        ((p.1 : ℝ) : ℂ) ^ (10 : ℕ) * varphi (iOverT p.1 (by exact p.2)) := by
      simpa [mul_assoc] using! ht10.mul (hvarphi.comp hio)
    have hsub : Continuous fun p : s =>
        ((p.1 : ℝ) : ℂ) ^ (10 : ℕ) * varphi (iOverT p.1 (by exact p.2)) - pPaper p.1 := by
      simpa [sub_eq_add_neg] using! hterm.add (continuous_neg.comp hpp)
    exact Continuous.fun_mul hsub hexp
  have hf : Measurable f := hf_cont.measurable
  have hg : Measurable (fun _t : (sᶜ : Set ℝ) => (0 : ℂ)) := measurable_const
  have hmeas : Measurable fun t : ℝ => if ht : t ∈ s then f ⟨t, ht⟩ else (0 : ℂ) :=
    (Measurable.dite (s := s) hf hg hs)
  have hEq :
      (fun t : ℝ => if ht : t ∈ s then f ⟨t, ht⟩ else (0 : ℂ)) =
        avaluesRemainderIntegrand u := by
    rfl
  have hAES :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => if ht : t ∈ s then f ⟨t, ht⟩ else (0 : ℂ))
        (MeasureTheory.volume.restrict s) :=
    hmeas.aestronglyMeasurable
  simpa [hEq, s] using! hAES

theorem integrable_norm_bound_avaluesRemainderIntegrand :
    ∃ bound : ℝ → ℝ,
      MeasureTheory.Integrable bound (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
      (∀ᶠ u in 𝓝 (2 : ℝ), ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ‖avaluesRemainderIntegrand u t‖ ≤ bound t) := by
  -- Use the domination lemmas in `AvaluesRemIntDom.lean`.
  rcases exists_integrable_bound_Ioi_zero with ⟨bound, hIntOn, hbound⟩
  tauto

theorem tendsto_avaluesRemainderIntegrand_two (t : ℝ) :
    Tendsto (fun u : ℝ => avaluesRemainderIntegrand u t) (𝓝 (2 : ℝ))
      (𝓝 (avaluesRemainderIntegrand (2 : ℝ) t)) := by
  -- Pointwise continuity in `u` of the exponential kernel.
  by_cases ht : 0 < t
  · have hexp : ContinuousAt (fun u : ℝ => (Real.exp (-Real.pi * u * t) : ℂ)) (2 : ℝ) := by
      fun_prop
    have hconst :
        ContinuousAt
          (fun _u : ℝ =>
            ((t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) - pPaper t))
          (2 : ℝ) :=
      continuousAt_const
    -- The integrand is a constant factor times the exponential kernel.
    simpa [avaluesRemainderIntegrand, avaluesRemainderIntegrandFull, ht, mul_assoc, mul_left_comm,
      mul_comm] using!
      (hconst.mul hexp).tendsto
  · -- If `t ≤ 0`, the integrand is identically `0` as a function of `u`.
    simp [avaluesRemainderIntegrand, avaluesRemainderIntegrandFull, ht]

/-- Continuity of `avaluesRemainderIntegral` at `u = 2`, proved using dominated convergence. -/
public theorem continuousAt_avaluesRemainderIntegral_two_dct :
    ContinuousAt avaluesRemainderIntegral (2 : ℝ) := by
  -- DCT on `μ = volume.restrict (Ioi 0)`.
  rcases integrable_norm_bound_avaluesRemainderIntegrand with ⟨bound, hboundInt, hbound⟩
  -- Package the dominated convergence theorem.
  have hMeas : ∀ᶠ u in 𝓝 (2 : ℝ),
      MeasureTheory.AEStronglyMeasurable (avaluesRemainderIntegrand u)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Filter.Eventually.of_forall aestronglyMeasurable_avaluesRemainderIntegrand
  have hLim :
      ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        Tendsto (fun u : ℝ => avaluesRemainderIntegrand u t) (𝓝 (2 : ℝ))
          (𝓝 (avaluesRemainderIntegrand (2 : ℝ) t)) := by
    -- Pointwise convergence holds everywhere.
    exact Filter.Eventually.of_forall tendsto_avaluesRemainderIntegrand_two
  have hTendsto :
      Tendsto
          (fun u : ℝ =>
            ∫ t : ℝ,
              avaluesRemainderIntegrand u t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
          (𝓝 (2 : ℝ))
          (𝓝
            (∫ t : ℝ,
              avaluesRemainderIntegrand (2 : ℝ) t ∂
                (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))) := by
    -- Apply DCT for a countably generated filter.
    exact tendsto_integral_filter_of_dominated_convergence bound hMeas hbound hboundInt hLim
  -- Convert back to the set integral definition.
  -- `ContinuousAt` is by definition `Tendsto` into `𝓝 (f 2)`.
  assumption

end SpecialValuesDerivTwoLaurent

end
end SpherePacking.Dim24
