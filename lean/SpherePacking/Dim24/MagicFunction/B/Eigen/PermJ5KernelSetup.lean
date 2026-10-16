-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ5ChangeOfVariables
import SpherePacking.ForMathlib.ExpNormSqDiv
import SpherePacking.ForMathlib.GaussianRexpIntegrable
public import SpherePacking.Integration.Measure


/-!
# Kernel setup for `perm_J₅`

This file defines the two-variable kernel used in the `J₅/J₆` permutation argument and proves the
basic continuity, measurability, and Gaussian integrability facts needed to apply Fubini.

## Main definitions
* `PermJ5.kernel`

## Main statements
* `PermJ5.aestronglyMeasurable_kernel`
* `PermJ5.integrable_gaussian_rexp`
-/

open scoped Real
open Complex

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.BFourier
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace PermJ5

open MeasureTheory Set
open SpherePacking.Integration (μIciOne)

/-- Auxiliary kernel for the Fubini argument in `perm_J₅`. -/
@[expose] public def kernel (w : ℝ²⁴) (p : ℝ²⁴ × ℝ) : ℂ :=
  Complex.exp (↑(-2 * (π * ⟪p.1, w⟫)) * I) * J5Change.g (‖p.1‖ ^ 2) p.2

lemma continuousOn_ψS'_I_mul :
    ContinuousOn (fun s : ℝ ↦ ψS' ((Complex.I : ℂ) * (s : ℂ))) (Ici (1 : ℝ)) := by
  -- Use the continuous restriction `ψS.resToImagAxis` on `Ici 1` and rewrite `ψS' (I*s)`.
  have hψS : Continuous ψS := SpherePacking.Dim24.PsiRewrites.continuous_ψS
  have hres : ContinuousOn ψS.resToImagAxis (Ici (1 : ℝ)) :=
    Function.continuousOn_resToImagAxis_Ici_one_of (F := ψS) hψS
  refine hres.congr ?_
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  simp [ψS', Function.resToImagAxis, ResToImagAxis, hs0, mul_comm]

/-- Continuity of the integrand `J5Change.g (‖x‖^2) s` on `ℝ²⁴ × Ici 1`. -/
public lemma continuousOn_J₅_g :
    ContinuousOn (fun p : ℝ²⁴ × ℝ ↦ J5Change.g (‖p.1‖ ^ 2) p.2) (univ ×ˢ Ici (1 : ℝ)) := by
  have hψ : ContinuousOn (fun s : ℝ ↦ ψS' ((Complex.I : ℂ) * (s : ℂ))) (Ici (1 : ℝ)) :=
    continuousOn_ψS'_I_mul
  have hzpow : ContinuousOn (fun s : ℝ ↦ (s : ℂ) ^ (-12 : ℤ)) (Ici (1 : ℝ)) := by
    intro s hs
    have hs0 : s ≠ 0 := by
      have : (0 : ℝ) < s := lt_of_lt_of_le (by norm_num) hs
      exact ne_of_gt this
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
    have hzC : ContinuousAt (fun z : ℂ => z ^ (-12 : ℤ)) (s : ℂ) :=
      continuousAt_zpow₀ (s : ℂ) (-12 : ℤ) (Or.inl hsC)
    have hof : ContinuousAt (fun t : ℝ => (t : ℂ)) s := Complex.continuous_ofReal.continuousAt
    exact (hzC.comp hof).continuousWithinAt
  have hψ' :
      ContinuousOn (fun p : ℝ²⁴ × ℝ ↦ ψS' ((Complex.I : ℂ) * (p.2 : ℂ)))
        (univ ×ˢ Ici (1 : ℝ)) := by
    refine hψ.comp continuousOn_snd ?_
    intro p hp
    exact (Set.mem_prod.mp hp).2
  have hzpow' :
      ContinuousOn (fun p : ℝ²⁴ × ℝ ↦ (p.2 : ℂ) ^ (-12 : ℤ))
        (univ ×ˢ Ici (1 : ℝ)) := by
    refine hzpow.comp continuousOn_snd ?_
    intro p hp
    exact (Set.mem_prod.mp hp).2
  have hconst :
      ContinuousOn (fun _ : ℝ²⁴ × ℝ ↦ (-I : ℂ)) (univ ×ˢ Ici (1 : ℝ)) :=
    continuousOn_const
  have hprod1 :
      ContinuousOn (fun p : ℝ²⁴ × ℝ ↦ (-I : ℂ) * ψS' ((Complex.I : ℂ) * (p.2 : ℂ)))
        (univ ×ˢ Ici (1 : ℝ)) :=
    hconst.mul hψ'
  have hprod2 :
      ContinuousOn
        (fun p : ℝ²⁴ × ℝ ↦
          (-I : ℂ) * ψS' ((Complex.I : ℂ) * (p.2 : ℂ)) * ((p.2 : ℂ) ^ (-12 : ℤ)))
        (univ ×ˢ Ici (1 : ℝ)) := by
    exact hprod1.mul hzpow'
  have hprod3 :
      ContinuousOn
        (fun p : ℝ²⁴ × ℝ ↦
          (-I : ℂ) * ψS' ((Complex.I : ℂ) * (p.2 : ℂ)) * ((p.2 : ℂ) ^ (-12 : ℤ)) *
            Complex.exp ((-π : ℂ) * ((‖p.1‖ : ℂ) ^ 2) / (p.2 : ℂ)))
        (univ ×ˢ Ici (1 : ℝ)) := by
    exact hprod2.mul (SpherePacking.ForMathlib.continuousOn_exp_norm_sq_div (E := ℝ²⁴))
  refine hprod3.congr ?_
  intro p hp
  -- Reconcile `Complex.exp ((-π:ℂ)*((‖x‖:ℂ)^2)/(s:ℂ))` with `Complex.exp (-π * ‖x‖^2 / s)`.
  have hs : (1 : ℝ) ≤ p.2 := by
    simpa [Set.mem_prod, Set.mem_univ, true_and] using! hp
  have hs0 : 0 < p.2 := lt_of_lt_of_le (by norm_num) hs
  have hs_ne0 : (p.2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs0)
  have hexp :
      Complex.exp ((-π : ℂ) * ((‖p.1‖ : ℂ) ^ 2) / (p.2 : ℂ)) =
        Complex.exp (-π * (‖p.1‖ ^ 2) / p.2) := by
    rfl
  simp [J5Change.g, mul_assoc, mul_left_comm, mul_comm]

/-- Almost-strong measurability of `PermJ5.kernel` for the product measure on `ℝ²⁴ × Ici 1`. -/
public lemma aestronglyMeasurable_kernel (w : ℝ²⁴) :
    AEStronglyMeasurable (kernel w) ((volume : Measure ℝ²⁴).prod μIciOne) := by
  have hphase : ContinuousOn (fun p : ℝ²⁴ × ℝ => Complex.exp (↑(-2 * (π * ⟪p.1, w⟫)) * I))
      (univ ×ˢ Ici (1 : ℝ)) := by
    -- Continuity of the complex phase on the product set.
    have hinner : Continuous fun p : ℝ²⁴ × ℝ => (⟪p.1, w⟫ : ℝ) := by
      simpa using! (continuous_fst.inner continuous_const)
    have hreal : Continuous fun p : ℝ²⁴ × ℝ => ((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ))) :=
      continuous_const.mul (continuous_const.mul hinner)
    have hofReal : Continuous fun p : ℝ²⁴ × ℝ => (↑(((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ)))) : ℂ) :=
      Complex.continuous_ofReal.comp hreal
    have harg : Continuous fun p : ℝ²⁴ × ℝ =>
        (↑(((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ)))) : ℂ) * I :=
      hofReal.mul continuous_const
    exact (Complex.continuous_exp.comp harg).continuousOn
  have hker : ContinuousOn (kernel w) (univ ×ˢ Ici (1 : ℝ)) := by
    refine (hphase.mul continuousOn_J₅_g).congr ?_
    intro p hp
    simp [kernel]
  have hmeas :
      AEStronglyMeasurable (kernel w)
        (((volume : Measure ℝ²⁴).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ici (1 : ℝ))) := by
    have hs : MeasurableSet (Set.univ : Set ℝ²⁴) := MeasurableSet.univ
    have ht : MeasurableSet (Ici (1 : ℝ)) := measurableSet_Ici
    exact ContinuousOn.aestronglyMeasurable hker (hs.prod ht)
  have hμ :
      ((volume : Measure ℝ²⁴).prod μIciOne) =
        (((volume : Measure ℝ²⁴).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ici (1 : ℝ))) := by
    simpa [μIciOne, Measure.restrict_univ] using!
      (Measure.prod_restrict (μ := (volume : Measure ℝ²⁴)) (ν := (volume : Measure ℝ))
        (s := (univ : Set ℝ²⁴)) (t := Ici (1 : ℝ)))
  simpa [hμ] using! hmeas

/-- Integrability of the Gaussian factor `exp (-π * ‖x‖^2 / s)` on `ℝ²⁴`. -/
public lemma integrable_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ²⁴ ↦ Real.exp (-π * (‖x‖ ^ 2) / s)) (volume : Measure ℝ²⁴) := by
  simpa using! SpherePacking.ForMathlib.integrable_gaussian_rexp_even (k := 12) (s := s) hs


end PermJ5

end
end SpherePacking.Dim24.BFourier
