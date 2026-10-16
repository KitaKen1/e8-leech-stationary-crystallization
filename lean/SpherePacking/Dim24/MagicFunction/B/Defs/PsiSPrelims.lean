-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSDecay
import SpherePacking.Dim24.ModularForms.Psi.Relations
import Mathlib.MeasureTheory.Integral.ExpDecay


/-!
# Preliminaries about `ψS'` on vertical lines/strips

These lemmas are used in multiple places (zero set for `b`, special values, and the Laplace
profile), so we keep them in a single central module.

## Main statements
* `PsiSPrelims.htendsto_ψS'`
* `PsiSPrelims.ψS'_add_one`
* `PsiSPrelims.integrableOn_ψS'_vertical_left`
* `PsiSPrelims.integrableOn_ψS'_vertical_right`

-/

noncomputable section

namespace SpherePacking.Dim24.PsiSPrelims

open scoped UpperHalfPlane Topology

open UpperHalfPlane
open Set
open MeasureTheory
open Filter

/-- A tail estimate for `ψS'`: large imaginary part implies small norm. -/
public lemma htendsto_ψS' :
    ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖ψS' z‖ < ε := by
  intro ε hε
  have hlim : Tendsto ψS atImInfty (𝓝 (0 : ℂ)) := SpherePacking.Dim24.tendsto_ψS_atImInfty
  have hEv : ∀ᶠ z in atImInfty, ‖ψS z‖ < ε := by
    have hEv' : ∀ᶠ z in atImInfty, dist (ψS z) (0 : ℂ) < ε :=
      (Metric.tendsto_nhds.1 hlim) ε hε
    simpa [dist_eq_norm] using! hEv'
  rcases (Filter.eventually_atImInfty).1 hEv with ⟨M, hM⟩
  refine ⟨max M 1, ?_⟩
  intro z hz
  have hzpos : 0 < z.im :=
    lt_of_lt_of_le (by simp : (0 : ℝ) < 1) (le_trans (le_max_right _ _) hz)
  have hMz : M ≤ z.im := le_trans (le_max_left _ _) hz
  have := hM (UpperHalfPlane.mk z hzpos) hMz
  simpa [ψS', hzpos, UpperHalfPlane.mk] using! this

/-! ### Translation on vertical lines -/

/-- Shift by `1` in the real direction: on the vertical line, `ψS'(1 + it) = -ψS'(it)`. -/
public lemma ψS'_add_one (t : ℝ) (ht : 0 < t) :
    ψS' ((1 : ℂ) + t * Complex.I) = -ψS' (t * Complex.I) := by
  set z0 : ℂ := (t : ℂ) * Complex.I
  set z1 : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I
  have hz0 : 0 < z0.im := by simpa [z0] using! ht
  have hz1 : 0 < z1.im := by simpa [z1] using! ht
  let z0H : ℍ := UpperHalfPlane.mk z0 hz0
  let z1H : ℍ := UpperHalfPlane.mk z1 hz1
  have hT : ψS (((1 : ℝ) +ᵥ z0H) : ℍ) = -ψS z0H := by
    simpa using! (SpherePacking.Dim24.ψS_add_one (z := z0H))
  have hvadd : ((1 : ℝ) +ᵥ z0H : ℍ) = z1H := by
    ext1
    simp [z0H, z1H, z0, z1, UpperHalfPlane.coe_vadd, add_comm]
  have hT' : ψS z1H = -ψS z0H := by
    simpa [hvadd] using! hT
  have hS1 : ψS' z1 = ψS z1H := by simp [ψS', z1H, hz1]
  have hS0 : ψS' z0 = ψS z0H := by simp [ψS', z0H, hz0]
  simp_all

/-! ### Integrability on vertical rays -/

/-- Integrability of `t ↦ ψS'(it)` on the ray `t ∈ (1,∞)`. -/
public lemma integrableOn_ψS'_vertical_left :
    MeasureTheory.IntegrableOn (fun t : ℝ => ψS' (t * Complex.I)) (Ioi (1 : ℝ))
      MeasureTheory.volume := by
  rcases PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with ⟨C0, hC0⟩
  let C : ℝ := max C0 0
  have hC :
      ∀ t : ℝ, 1 ≤ t → ‖ψS.resToImagAxis t‖ ≤ C * Real.exp (-Real.pi * t) := by
    intro t ht
    have := hC0 t ht
    exact this.trans (by gcongr; exact le_max_left _ _)
  have hbound :
      ∀ t : ℝ, t ∈ Ioi (1 : ℝ) → ‖ψS' (t * Complex.I)‖ ≤ C * Real.exp (-Real.pi * t) := by
    intro t ht
    have ht' : 1 ≤ t := le_of_lt ht
    have ht0 : 0 < t := lt_of_lt_of_le (by simp : (0 : ℝ) < 1) ht'
    have hEq : ψS' (t * Complex.I) = ψS.resToImagAxis t := by
      simp [ψS', Function.resToImagAxis, ResToImagAxis, ht0, mul_comm]
    simpa [hEq] using! hC t ht'
  have hgi :
      MeasureTheory.IntegrableOn (fun t : ℝ => C * Real.exp (-Real.pi * t)) (Ioi (1 : ℝ))
        MeasureTheory.volume := by
    have hExp :
        MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * t)) (Ioi (1 : ℝ))
          MeasureTheory.volume := by
      simpa using! (exp_neg_integrableOn_Ioi (a := (1 : ℝ)) (b := Real.pi) Real.pi_pos)
    have hExp' :
        MeasureTheory.Integrable (fun t : ℝ => Real.exp (-Real.pi * t))
          (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using! hExp
    have hmul' :
        MeasureTheory.Integrable (fun t : ℝ => C * Real.exp (-Real.pi * t))
          (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
      hExp'.const_mul C
    simpa [MeasureTheory.IntegrableOn] using! hmul'
  have hmeas :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => ψS' (t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    refine (ContinuousOn.aestronglyMeasurable (f := fun t : ℝ => ψS' (t * Complex.I))
      (s := Ioi (1 : ℝ)) ?_ measurableSet_Ioi)
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by simp : (0 : ℝ) < 1) (le_of_lt ht)
    have hEq :
        (fun u : ℝ => ψS' (u * Complex.I)) =ᶠ[𝓝 t]
          fun u : ℝ => ψS (UpperHalfPlane.ofComplex (u * Complex.I)) := by
      filter_upwards [lt_mem_nhds ht0] with u hu
      have huIm : 0 < ((u : ℂ) * Complex.I).im := by simpa using! hu
      have hof :
          UpperHalfPlane.ofComplex (u * Complex.I) = ⟨(u : ℂ) * Complex.I, huIm⟩ :=
        UpperHalfPlane.ofComplex_apply_of_im_pos huIm
      have hψS' : ψS' (u * Complex.I) = ψS ⟨(u : ℂ) * Complex.I, huIm⟩ := by
        simp [ψS', hu]
      simpa [hof] using! hψS'
    have hcont :
        ContinuousAt (fun u : ℝ => ψS (UpperHalfPlane.ofComplex (u * Complex.I))) t := by
      have hψ : Continuous ψS := SpherePacking.Dim24.PsiRewrites.continuous_ψS
      have hmul : ContinuousAt (fun u : ℝ => (u : ℂ) * Complex.I) t := by fun_prop
      have hIm : 0 < ((t : ℂ) * Complex.I).im := by simpa using! ht0
      have hof : ContinuousAt UpperHalfPlane.ofComplex (t * Complex.I) :=
        (UpperHalfPlane.contMDiffAt_ofComplex (n := ⊤) hIm).continuousAt
      have hψAt : ContinuousAt ψS (UpperHalfPlane.ofComplex (t * Complex.I)) := hψ.continuousAt
      have hof' :
          ContinuousAt (fun u : ℝ => UpperHalfPlane.ofComplex (u * Complex.I)) t :=
        ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) * Complex.I) (x := t) hof hmul
      exact ContinuousAt.comp' hψAt hof'
    exact (hcont.congr_of_eventuallyEq hEq).continuousWithinAt
  have hgi' :
      MeasureTheory.Integrable (fun t : ℝ => C * Real.exp (-Real.pi * t))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn] using! hgi
  refine MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict (Ioi (1 : ℝ)))
    hgi' hmeas ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro t ht
  exact hbound t ht

/-! ### Integrability on the translated ray -/

/-- Integrability of `t ↦ ψS'(1 + it)` on the ray `t ∈ (1,∞)`. -/
public lemma integrableOn_ψS'_vertical_right :
    MeasureTheory.IntegrableOn (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I)) (Ioi (1 : ℝ))
      MeasureTheory.volume := by
  have hleft :
      MeasureTheory.Integrable (fun t : ℝ => ψS' (t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    simpa [MeasureTheory.IntegrableOn] using! integrableOn_ψS'_vertical_left
  have hneg :
      MeasureTheory.Integrable (fun t : ℝ => -ψS' (t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := hleft.neg
  have hEq :
      (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Ioi (1 : ℝ))]
        fun t : ℝ => -ψS' (t * Complex.I) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 < t := lt_trans (by simp : (0 : ℝ) < 1) ht
    simpa using! (ψS'_add_one (t := t) ht0)
  have hright :
      MeasureTheory.Integrable (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I))
        (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
    hneg.congr hEq.symm
  simpa [MeasureTheory.IntegrableOn] using! hright

end SpherePacking.Dim24.PsiSPrelims

end
