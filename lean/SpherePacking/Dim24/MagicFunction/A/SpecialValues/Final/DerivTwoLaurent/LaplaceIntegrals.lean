-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Elementary Laplace-type integrals on `(0, ∞)`

These lemmas record closed forms for the basic Laplace integrals in `ℝ` and `ℂ`. They are used
to compute the explicit Laplace transform of `pPaper` from `dim_24.tex`.
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter MeasureTheory Set

/-- `∫₀^∞ exp(-(r*t)) dt = 1/r` for `r > 0`. -/
public lemma integral_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(r * t)) = 1 / r := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 : ℝ)) (r := r) (by norm_num) hr
  -- `t^(1-1)=1`, `(1/r)^1 = 1/r`, `Γ(1)=1`.
  simpa [Real.rpow_zero, Real.rpow_one, Real.Gamma_one, sub_self] using! h

/-- `∫₀^∞ t * exp(-(r*t)) dt = 1/r^2` for `r > 0`. -/
public lemma integral_mul_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ), t * Real.exp (-(r * t)) = 1 / r ^ (2 : ℕ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := r) (by norm_num) hr
  have hcongr :
      (∫ t : ℝ in Set.Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t))) =
        ∫ t : ℝ in Set.Ioi (0 : ℝ), t * Real.exp (-(r * t)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have : (2 : ℝ) - 1 = (1 : ℝ) := by norm_num
    simp [this]
  -- `t^(2-1)=t`, `Γ(2)=1`, and convert (postTransparency := .instances) the `rpow` to a `Nat` power.
  simp_all

/-- Complex form of `integral_exp_neg_mul_Ioi`, written using `Complex.exp`. -/
public lemma integral_exp_neg_mul_Ioi_complex {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(r : ℂ) * (t : ℂ)) = (1 : ℂ) / (r : ℂ) := by
  have hfun :
      (fun t : ℝ => Complex.exp (-(r : ℂ) * (t : ℂ))) =
        fun t : ℝ => (Real.exp (-(r * t)) : ℂ) := by
    norm_num
  have hcast :
      (∫ t : ℝ in Set.Ioi (0 : ℝ), (Real.exp (-(r * t)) : ℂ)) =
        ((∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(r * t)) : ℝ) : ℂ) := by
    simpa using!
      (integral_ofReal (𝕜 := ℂ)
        (μ := (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
        (f := fun t : ℝ => Real.exp (-(r * t))))
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(r : ℂ) * (t : ℂ))) =
        ∫ t : ℝ in Set.Ioi (0 : ℝ), (Real.exp (-(r * t)) : ℂ) := by
          rw [hfun]
    _ = ((∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(r * t)) : ℝ) : ℂ) := hcast
    _ = (1 : ℂ) / (r : ℂ) := by
          simp [integral_exp_neg_mul_Ioi hr, one_div]

/-- Complex form of `integral_mul_exp_neg_mul_Ioi`, written using `Complex.exp`. -/
public lemma integral_mul_exp_neg_mul_Ioi_complex {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ), (t : ℂ) * Complex.exp (-(r : ℂ) * (t : ℂ)) =
      (1 : ℂ) / (r : ℂ) ^ (2 : ℕ) := by
  have hfun :
      (fun t : ℝ => (t : ℂ) * Complex.exp (-(r : ℂ) * (t : ℂ))) =
        fun t : ℝ => ((t * Real.exp (-(r * t)) : ℝ) : ℂ) := by
    funext t
    simp
  have hcast :
      (∫ t : ℝ in Set.Ioi (0 : ℝ), (t : ℂ) * Complex.exp (-(r : ℂ) * (t : ℂ))) =
        ((∫ t : ℝ in Set.Ioi (0 : ℝ), t * Real.exp (-(r * t)) : ℝ) : ℂ) := by
    simpa [hfun] using!
      (integral_ofReal (𝕜 := ℂ)
        (μ := (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
        (f := fun t : ℝ => t * Real.exp (-(r * t))))
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ), (t : ℂ) * Complex.exp (-(r : ℂ) * (t : ℂ))) =
        ((∫ t : ℝ in Set.Ioi (0 : ℝ), t * Real.exp (-(r * t)) : ℝ) : ℂ) := hcast
    _ = (1 : ℂ) / (r : ℂ) ^ (2 : ℕ) := by
          simp [integral_mul_exp_neg_mul_Ioi hr, one_div]

end SpecialValuesDerivTwoLaurent

end
end SpherePacking.Dim24
